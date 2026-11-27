// Transport: WebRTC data channels between devices paired by the user (docs/net-design.md).
//
// Interface used by the host (main.mjs, links.mjs, ui.mjs):
//   transport.start({ onLink(link), onStatus(text) })    transport.setOnline(bool)    transport.stop()
//   link: { id, remoteLabel, send(frame) → bool, close(), bufferedAmount,
//           onFrame(cb(frame)), onClose(cb()), onDrain(cb()) }
// plus pairing (manual signalling: the codes travel through the user, as text):
//   invite() → Invitation { code, expiresAt, state, noSrflx, accept(replyText) → Promise, cancel() }
//   respond(inviteText) → Response { code, state, noSrflx, onCode(cb), done: Promise, keep(), cancel() }
//     keep(): the user copied the current reply: stop renewing and keep that attempt; if it fails
//     (the browser's ICE agent gives up), renewal resumes and onCode reports a new reply.
//   connections() → [{ id, role, state, since, linkId }]    disconnect(id)    onChange(cb)
//
// One pairing = one RTCPeerConnection ("connection") with
//   - a negotiated control channel `ctl` (id 0), open for the connection's life: carries only
//     {t:'online', v} so that a device that goes offline is not re-linked until it comes back;
//   - at most one `sync` channel at a time = one link (ordered, reliable). The device that made the
//     invitation opens it; the other accepts it. A link that closes while the connection lives
//     (engine restart, protocol error, the other side's restart) is replaced after a back-off
//     (0.5 s doubling to 30 s, reset after a link lived 20 s), so no re-pairing is needed.
// Promises kept (relay-era interface, unchanged): links are ordered and reliable; frames ≤ 16 KiB +
// a few bytes; onClose exactly once per announced link, whoever closed it; bufferedAmount and
// onDrain give back-pressure (the channel's own buffer and `bufferedamountlow`).
// Loss: a Chromium receiver keeps a channel `open` after its peer vanished (measured), so a link
// is closed when the connection is `failed` or `closed`, or `disconnected` for LOSS_MS, not only
// when its channel closes. `failed` is final: the user pairs again (no signalling channel exists
// for an ICE restart).
import { extractSdp, selectCandidates, rebuildSdp, encodePayload, formatCode, parseCode, offerTag, sameBytes, CodeError } from '../netcode.mjs';

export const T = {
  RENEW_MS: 2500,            // a reply is renewed this often while shown and not yet copied (measured: a Firefox answerer
                             // gives up 5 s after it starts if it cannot reach the offerer's candidates)
  MAX_ATTEMPTS: 6,           // live reply attempts kept (the newest shown)
  RESPOND_MS: 120000,        // the joining device stops making replies after this
  CONNECT_MS: 30000,         // after a reply is accepted: give up if no channel by then
  INVITE_MS: 10 * 60000,     // an invitation is valid this long
  LOSS_MS: 5000,             // `disconnected` this long = link down
  GATHER_CAP_MS: 2000,       // candidates: gathering complete, or first srflx + SRFLX_QUIET_MS, or this
  SRFLX_QUIET_MS: 300,
  DRAIN_AT: 256 * 1024,      // bufferedamountlow threshold
  REOPEN_MIN: 500, REOPEN_MAX: 30000, REOPEN_RESET_AFTER: 20000,
};

export function createWebRTCTransport({ getIceServers = () => [], log = () => {}, RTC = globalThis.RTCPeerConnection, timing = {} } = {}) {
  const t = { ...T, ...timing };
  let handlers = null, online = true, stopped = false;
  let nextLink = 1, nextConn = 1;
  const conns = new Map();            // id -> connection (paired; attempts and open invitations are not listed)
  const pending = new Set();          // connections of open invitations and reply attempts
  const responses = new Set();        // replies still being made or waiting
  const changeListeners = new Set();
  const changed = () => { for (const f of changeListeners) { try { f(); } catch {} } };
  const status = (s) => handlers?.onStatus?.(s);

  // ---------------------------------------------------------------- candidates
  function gather(pc) {
    return new Promise((resolve) => {
      let done = false, quiet = null;
      const finish = () => { if (done) return; done = true; clearTimeout(cap); clearTimeout(quiet); resolve(); };
      const cap = setTimeout(finish, t.GATHER_CAP_MS);
      if (pc.iceGatheringState === 'complete') return finish();
      pc.addEventListener('icegatheringstatechange', () => { if (pc.iceGatheringState === 'complete') finish(); });
      pc.addEventListener('icecandidate', (e) => {
        if (!e.candidate) return finish();
        if (/ typ srflx/.test(e.candidate.candidate) && !quiet) quiet = setTimeout(finish, t.SRFLX_QUIET_MS);
      });
    });
  }
  function describe(pc, kind, tag) {
    const x = extractSdp(pc.localDescription.sdp);
    x.cands = selectCandidates(x.cands);
    const payload = encodePayload({ kind, tag, ...x });
    return { x, payload, code: formatCode(kind, payload), noSrflx: getIceServers().length > 0 && !x.cands.some((c) => c.type === 'srflx') };
  }

  // ---------------------------------------------------------------- connections
  function makeConn(role) {
    const pc = new RTC({ iceServers: getIceServers() });
    const c = { id: nextConn++, pc, role, state: 'pairing', since: Date.now(), link: null, remoteOnline: true,
      backoff: 0, nextAt: 0, reopenTimer: null, lossTimer: null, dropped: false, onUp: [], onDown: [] };
    c.ctl = pc.createDataChannel('ctl', { negotiated: true, id: 0 });
    c.ctl.onopen = () => {
      if (c.dropped) return;
      sendCtl(c);
      if (c.state === 'pairing') { c.state = 'connected'; c.since = Date.now(); for (const f of c.onUp.splice(0)) f(); changed(); }
      maybeOpen(c);
    };
    // The control channel lives as long as the association: when it closes, the other device closed
    // its connection (Disconnect, page closed) and no further link is possible.
    c.ctl.onclose = () => { if (c.state !== 'pairing') dropConn(c, 'closed by the other device'); };
    c.ctl.onmessage = (e) => {
      let m; try { m = JSON.parse(e.data); } catch { return; }
      if (m?.t !== 'online') return;
      c.remoteOnline = !!m.v;
      if (c.remoteOnline) { c.backoff = 0; c.nextAt = 0; maybeOpen(c); }
      changed();
    };
    pc.addEventListener('connectionstatechange', () => onPcState(c));
    pc.addEventListener('datachannel', (e) => onIncoming(c, e.channel));
    return c;
  }
  function sendCtl(c) { try { if (c.ctl.readyState === 'open') c.ctl.send(JSON.stringify({ t: 'online', v: online })); } catch {} }
  function onPcState(c) {
    if (c.dropped) return;
    const s = c.pc.connectionState;
    if (s === 'connected') {
      if (c.lossTimer) { clearTimeout(c.lossTimer); c.lossTimer = null; }
      if (c.state === 'interrupted') { c.state = 'connected'; log(`connection ${c.id}: back`); maybeOpen(c); changed(); }
    } else if (s === 'disconnected') {
      if (!c.lossTimer && c.state !== 'pairing') c.lossTimer = setTimeout(() => {
        c.lossTimer = null;
        if (c.dropped || c.pc.connectionState !== 'disconnected') return;
        log(`connection ${c.id}: interrupted for ${t.LOSS_MS} ms; link down`);
        c.state = 'interrupted'; closeLink(c.link, 'connection interrupted'); changed();
      }, t.LOSS_MS);
    } else if (s === 'failed' || s === 'closed') {
      dropConn(c, `connection ${s}`);
    }
  }
  function dropConn(c, why) {
    if (c.dropped) return;
    c.dropped = true;
    clearTimeout(c.lossTimer); clearTimeout(c.reopenTimer);
    closeLink(c.link, why);
    try { c.pc.close(); } catch {}
    const listed = conns.delete(c.id);
    pending.delete(c);
    if (listed) log(`connection ${c.id}: ${why}`);
    const wasUp = c.state !== 'pairing';
    c.state = 'lost';
    for (const f of c.onDown.splice(0)) f(why, wasUp);
    if (listed) changed();
  }

  // ---------------------------------------------------------------- links (sync channels)
  function maybeOpen(c) {
    if (c.role !== 'offerer' || c.dropped || stopped || !online || !c.remoteOnline || c.link || c.state !== 'connected' || c.reopenTimer) return;
    if (!conns.has(c.id)) return;
    c.reopenTimer = setTimeout(() => {
      c.reopenTimer = null;
      if (c.role !== 'offerer' || c.dropped || stopped || !online || !c.remoteOnline || c.link || c.state !== 'connected') return;
      let dc;
      try { dc = c.pc.createDataChannel('sync'); } catch (e) { log(`connection ${c.id}: cannot open a channel (${e.message})`); return; }
      attach(c, dc);
    }, Math.max(0, c.nextAt - Date.now()));
  }
  function onIncoming(c, dc) {
    if (dc.label !== 'sync' || c.role !== 'answerer' || c.dropped || stopped || !online || !conns.has(c.id)) { try { dc.close(); } catch {} return; }
    // The inviting device opens a channel only once its previous link is down: a new channel
    // replaces ours even if ours still looks open (its close may not have arrived, or never will).
    if (c.link) closeLink(c.link, 'replaced by a new channel from the other device');
    attach(c, dc);
  }
  function attach(c, dc) {
    dc.binaryType = 'arraybuffer';
    dc.bufferedAmountLowThreshold = t.DRAIN_AT;
    const L = { id: nextLink++, remoteLabel: 'paired device', connId: c.id, closed: false, announced: false, upAt: 0,
      _onFrame: null, _onClose: null, _drain: [], _dc: dc, _conn: c,
      send(frame) {
        if (L.closed) return false;
        // A channel that stopped being open (e.g. stuck in `closing`, measured between Chromium and
        // Firefox when closed with data buffered) would drop frames silently: the link is down.
        if (dc.readyState !== 'open') { if (L.announced) closeLink(L, `channel ${dc.readyState}`); return false; }
        try { dc.send(frame); return true; }
        catch (e) { log(`link ${L.id}: send failed (${e.name}: ${e.message}); closing`); closeLink(L, 'send failed'); return false; }
      },
      close() { closeLink(L, 'closed by this device'); },
      get bufferedAmount() { return L.closed ? 0 : dc.bufferedAmount; },
      onFrame(cb) { L._onFrame = cb; },
      onClose(cb) { L._onClose = cb; },
      onDrain(cb) {
        L._drain.push(cb);
        // the threshold may have been crossed before this registration: never wait for an event that already fired
        if (dc.bufferedAmount <= t.DRAIN_AT) queueMicrotask(fireDrain);
      },
    };
    const fireDrain = () => { if (L.closed) { L._drain = []; return; } const w = L._drain; L._drain = []; for (const f of w) f(); };
    c.link = L;
    const up = () => {
      if (L.closed || L.announced) return;
      L.announced = true; L.upAt = Date.now();
      log(`link ${L.id} up (connection ${c.id})`);
      handlers?.onLink(L);
      changed();
    };
    dc.onopen = up;
    dc.onmessage = (e) => { if (!L.closed && L.announced) L._onFrame?.(new Uint8Array(e.data)); };
    dc.onbufferedamountlow = fireDrain;
    dc.onclose = () => closeLink(L, 'channel closed');
    if (dc.readyState === 'open') queueMicrotask(up);
  }
  function closeLink(L, why) {
    if (!L || L.closed) return;
    L.closed = true;
    try { L._dc.close(); } catch {}
    const c = L._conn;
    if (c.link === L) c.link = null;
    if (L.announced) { log(`link ${L.id} down: ${why}`); L._drain = []; L._onClose?.(); }
    // back-off before the next link on this connection (the relay's rule): reset if this one lived a while
    c.backoff = L.upAt && Date.now() - L.upAt > t.REOPEN_RESET_AFTER ? t.REOPEN_MIN : Math.min(Math.max(t.REOPEN_MIN, c.backoff * 2), t.REOPEN_MAX);
    c.nextAt = Date.now() + c.backoff;
    if (!c.dropped) maybeOpen(c);
    changed();
  }

  // ---------------------------------------------------------------- pairing: the inviting device
  async function invite() {
    if (stopped) throw new Error('transport stopped');
    const c = makeConn('offerer');
    pending.add(c);
    try {
      await c.pc.setLocalDescription(await c.pc.createOffer());
      await gather(c.pc);
    } catch (e) { dropConn(c, 'invitation failed'); throw e; }
    const d = describe(c.pc, 'offer');
    const tag = await offerTag(d.payload);
    const inv = {
      code: d.code, noSrflx: d.noSrflx, expiresAt: Date.now() + t.INVITE_MS, state: 'waiting', connId: c.id,
      async accept(text) {
        if (inv.state === 'expired') throw new CodeError('expired', 'This invitation has expired. Make a new one.');
        if (inv.state === 'cancelled') throw new CodeError('cancelled', 'This invitation was cancelled. Make a new one.');
        if (inv.state !== 'waiting') throw new CodeError('used', 'This invitation was already used. Make a new invitation to pair another device.');
        const r = parseCode(text, 'answer');
        if (!sameBytes(r.tag, tag)) throw new CodeError('stale', 'This reply belongs to another invitation. Use the reply the other device shows for this invitation.');
        inv.state = 'connecting'; clearTimeout(expiry);
        conns.set(c.id, c); pending.delete(c); changed();
        try { await c.pc.setRemoteDescription({ type: 'answer', sdp: rebuildSdp(r, 'answer', d.x.mid) }); }
        catch (e) { inv.state = 'failed'; dropConn(c, 'reply refused by the browser'); throw new CodeError('refused', `The browser refused this reply (${e.message}).`); }
        return awaitUp(c, inv);
      },
      cancel() { if (inv.state === 'waiting' || inv.state === 'connecting') { inv.state = 'cancelled'; clearTimeout(expiry); dropConn(c, 'invitation cancelled'); } },
    };
    const expiry = setTimeout(() => { if (inv.state === 'waiting') { inv.state = 'expired'; dropConn(c, 'invitation expired'); } }, t.INVITE_MS);
    return inv;
  }
  /** Resolves when the connection's control channel opens; rejects after CONNECT_MS or on loss. */
  function awaitUp(c, owner) {
    return new Promise((resolve, reject) => {
      if (c.state === 'connected') { owner.state = 'connected'; return resolve({ connId: c.id }); }
      const timer = setTimeout(() => { owner.state = 'failed'; dropConn(c, 'could not connect'); }, t.CONNECT_MS);
      c.onUp.push(() => { clearTimeout(timer); owner.state = 'connected'; resolve({ connId: c.id }); });
      c.onDown.push(() => { clearTimeout(timer); if (owner.state !== 'connected') { owner.state = 'failed'; reject(new Error('could not connect')); } });
    });
  }

  // ---------------------------------------------------------------- pairing: the joining device
  function respond(text) {
    if (stopped) throw new Error('transport stopped');
    const r = parseCode(text, 'offer');                     // throws CodeError before anything starts
    const listeners = new Set(), attempts = [];
    let renew = null, giveUp = null, resolveDone, rejectDone, current = null, kept = null;
    const resp = {
      code: null, noSrflx: false, state: 'preparing', attempts: 0,
      onCode(cb) { listeners.add(cb); if (resp.code) cb(resp.code); return () => listeners.delete(cb); },
      done: new Promise((res, rej) => { resolveDone = res; rejectDone = rej; }),
      keep() {
        if (resp.state !== 'waiting' || !current || current.dropped || kept) return;
        const k = kept = current;
        clearInterval(renew); renew = null;
        log(`reply ${attempts.indexOf(k) + 1} copied: renewal stopped`);
        k.onDown.push(() => {
          if (kept !== k || resp.state !== 'waiting') return;
          log('the copied reply failed: renewal resumes');
          kept = null; attempt(); renew = setInterval(attempt, t.RENEW_MS);
        });
      },
      cancel() { finish('cancelled'); },
    };
    responses.add(resp);
    resp.done.catch(() => {});
    const finish = (state, winner = null) => {
      if (resp.state === 'connected' || resp.state === 'failed' || resp.state === 'cancelled') return;
      resp.state = state; clearInterval(renew); clearTimeout(giveUp); responses.delete(resp);
      for (const a of attempts) if (a !== winner) dropConn(a, state === 'connected' ? 'another reply was used' : `reply ${state}`);
      if (winner) resolveDone({ connId: winner.id });
      else rejectDone(new Error(state === 'failed' ? 'The other device did not answer. Start again on the device that made the invitation.' : 'cancelled'));
    };
    let tag = null;
    const attempt = async () => {
      if ((resp.state !== 'preparing' && resp.state !== 'waiting') || kept) return;
      const c = makeConn('answerer');
      pending.add(c); attempts.push(c);
      // keep at most MAX_ATTEMPTS replies alive: the oldest are dropped
      while (attempts.filter((a) => !a.dropped).length > t.MAX_ATTEMPTS) dropConn(attempts.find((a) => !a.dropped), 'reply replaced');
      c.onUp.push(() => {
        if (resp.state === 'connected') { dropConn(c, 'another reply was used'); return; }
        conns.set(c.id, c); pending.delete(c); changed();
        finish('connected', c);
        log(`connection ${c.id}: joined (reply ${attempts.indexOf(c) + 1} of ${attempts.length})`);
        maybeOpen(c);
      });
      try {
        tag ??= await offerTag(r.payload);
        await c.pc.setRemoteDescription({ type: 'offer', sdp: rebuildSdp(r, 'offer', '0') });
        const ans = await c.pc.createAnswer();
        // passive DTLS role: the inviting device starts the handshake when it applies this reply
        // (measured: an active answerer's early ClientHello is lost and its retransmissions back off)
        await c.pc.setLocalDescription({ type: 'answer', sdp: ans.sdp.replace(/a=setup:(active|actpass)/g, 'a=setup:passive') });
        await gather(c.pc);
        if (c.dropped || (resp.state !== 'preparing' && resp.state !== 'waiting')) return;
        if (kept) { dropConn(c, 'not needed: a reply was copied'); return; }
        const d = describe(c.pc, 'answer', tag);
        current = c;
        resp.code = d.code; resp.noSrflx = d.noSrflx; resp.attempts = attempts.length;
        if (resp.state === 'preparing') resp.state = 'waiting';
        for (const f of listeners) { try { f(d.code); } catch (e) { log(`reply display failed: ${e.message}`); } }
      } catch (e) {
        log(`reply attempt failed: ${e.message}`);
        dropConn(c, 'reply attempt failed');
        if (!resp.code) finish('failed');
      }
    };
    attempt();
    renew = setInterval(attempt, t.RENEW_MS);
    giveUp = setTimeout(() => finish('failed'), t.RESPOND_MS);
    return resp;
  }

  // ---------------------------------------------------------------- the rest of the interface
  function setOnline(v) {
    online = !!v;
    for (const c of conns.values()) {
      sendCtl(c);
      if (!online) closeLink(c.link, 'offline (by you)');
      else { c.backoff = 0; c.nextAt = 0; maybeOpen(c); }
    }
    status(online ? 'online' : 'offline (by you)');
    changed();
  }
  return {
    start(h) { handlers = h; stopped = false; },
    stop() {
      stopped = true;
      for (const r of [...responses]) r.cancel();
      for (const c of [...conns.values(), ...pending]) dropConn(c, 'stopped');
    },
    setOnline,
    get online() { return online; },
    invite, respond,
    connections: () => [...conns.values()].map((c) => ({ id: c.id, role: c.role, state: c.state, since: c.since, linkId: c.link?.announced ? c.link.id : null, remoteOnline: c.remoteOnline })),
    disconnect(id) { const c = conns.get(id); if (c) dropConn(c, 'disconnected by you'); },
    onChange(cb) { changeListeners.add(cb); return () => changeListeners.delete(cb); },
    timing: t,
  };
}
