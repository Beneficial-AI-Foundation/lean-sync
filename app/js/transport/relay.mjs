// Transport: the development/test WebSocket relay (server: dev/serve.mjs, not shipped).
//
// This is the only transport of this version, and the one the next task replaces with WebRTC
// data channels. Any transport implements the same small interface:
//
//   transport.start({ onLink(link), onStatus(text) })    transport.setOnline(bool)    transport.stop()
//   link: { id, remoteLabel, send(frame: Uint8Array), close(), bufferedAmount,
//           onFrame(cb(frame)), onClose(cb()), onDrain(cb()) }
//
// Links are ordered and reliable; frames are at most 16 KiB + a few bytes (the host's framing,
// app/js/links.mjs). `onClose` fires exactly once per link, whoever closed it. `bufferedAmount`
// and `onDrain` give backpressure (here the WebSocket's buffer, shared by the links of one
// socket, polled because WebSocket has no drain event).
//
// Who links to whom: the relay announces the devices in the room; the device with the smaller
// relay id asks for the link, with an exponential back-off per remote after a link goes down, so
// a session that is closed for a protocol error cannot spin.

const DRAIN_POLL_MS = 30;

export function createRelayTransport({ url, room = '', label = 'device' }) {
  let ws = null, myId = null, handlers = null, online = true, stopped = false;
  let reconnectDelay = 500, reconnectTimer = null;
  const links = new Map();            // link id -> link object
  const remotes = new Map();          // remote id -> { delay, nextAt, timer, linkedAt }
  let devices = [];

  function status(s) { handlers?.onStatus?.(s); }

  function connect() {
    if (stopped) return;
    const u = new URL(url); if (room) u.searchParams.set('room', room); u.searchParams.set('label', label);
    try { ws = new WebSocket(u); } catch (e) { status(`no relay (${e.message})`); return scheduleReconnect(); }
    ws.binaryType = 'arraybuffer';
    ws.onopen = () => { reconnectDelay = 500; status('relay connected'); if (!online) ws.send(JSON.stringify({ op: 'online', value: false })); };
    ws.onclose = () => { status('relay unreachable'); for (const l of [...links.values()]) linkDown(l.id); myId = null; scheduleReconnect(); };
    ws.onerror = () => {};
    ws.onmessage = (m) => {
      if (typeof m.data === 'string') return control(JSON.parse(m.data));
      const b = new Uint8Array(m.data);
      if (b.length < 4) return;
      const id = b[0] | (b[1] << 8) | (b[2] << 16) | (b[3] << 24) >>> 0;
      const l = links.get(id >>> 0);
      if (l) l._frame(b.subarray(4));
    };
  }
  function scheduleReconnect() {
    if (stopped || reconnectTimer) return;
    reconnectTimer = setTimeout(() => { reconnectTimer = null; connect(); }, reconnectDelay);
    reconnectDelay = Math.min(reconnectDelay * 2, 10000);
  }

  function control(m) {
    if (m.op === 'welcome') myId = m.id;
    else if (m.op === 'devices') { devices = m.list; planLinks(); }
    else if (m.op === 'link-up') linkUp(m.link, m.remote);
    else if (m.op === 'link-down') linkDown(m.link);
  }

  function planLinks() {
    if (!myId || !online) return;
    for (const d of devices) {
      if (!(myId < d.id)) continue;
      if ([...links.values()].some((l) => l.remoteId === d.id)) continue;
      const r = remotes.get(d.id) ?? { delay: 0, nextAt: 0, timer: null };
      remotes.set(d.id, r);
      if (r.timer) continue;
      const wait = Math.max(0, r.nextAt - Date.now());
      r.timer = setTimeout(() => {
        r.timer = null;
        if (ws?.readyState === 1 && devices.some((x) => x.id === d.id) && ![...links.values()].some((l) => l.remoteId === d.id)) {
          ws.send(JSON.stringify({ op: 'link', to: d.id }));
        }
      }, wait);
    }
  }

  function linkUp(id, remote) {
    const l = {
      id, remoteId: remote.id, remoteLabel: remote.label, closed: false, upAt: Date.now(),
      _onFrame: null, _onClose: null, _drainWaiters: [],
      send(frame) {
        if (l.closed || ws?.readyState !== 1) return false;
        const out = new Uint8Array(4 + frame.length);
        out[0] = id & 255; out[1] = (id >>> 8) & 255; out[2] = (id >>> 16) & 255; out[3] = (id >>> 24) & 255;
        out.set(frame, 4);
        ws.send(out);
        return true;
      },
      close() { if (!l.closed && ws?.readyState === 1) ws.send(JSON.stringify({ op: 'unlink', link: id })); },
      get bufferedAmount() { return ws?.bufferedAmount ?? 0; },
      onFrame(cb) { l._onFrame = cb; },
      onClose(cb) { l._onClose = cb; },
      onDrain(cb) {
        l._drainWaiters.push(cb);
        if (l._drainWaiters.length === 1) {
          const poll = () => {
            if (l.closed) { l._drainWaiters = []; return; }
            if ((ws?.bufferedAmount ?? 0) < 256 * 1024) { const w = l._drainWaiters; l._drainWaiters = []; for (const f of w) f(); }
            else setTimeout(poll, DRAIN_POLL_MS);
          };
          setTimeout(poll, DRAIN_POLL_MS);
        }
      },
      _frame(f) { l._onFrame?.(f); },
    };
    links.set(id, l);
    handlers?.onLink(l);
  }

  function linkDown(id) {
    const l = links.get(id);
    if (!l) return;
    links.delete(id);
    l.closed = true;
    // back-off before asking for this remote again; reset if the link lived a while
    const r = remotes.get(l.remoteId) ?? { delay: 0, nextAt: 0, timer: null };
    r.delay = Date.now() - l.upAt > 20000 ? 500 : Math.min(Math.max(500, r.delay * 2), 30000);
    r.nextAt = Date.now() + r.delay;
    remotes.set(l.remoteId, r);
    l._onClose?.();
    planLinks();
  }

  return {
    start(h) { handlers = h; stopped = false; connect(); },
    stop() { stopped = true; clearTimeout(reconnectTimer); for (const l of [...links.values()]) linkDown(l.id); try { ws?.close(); } catch {} },
    setOnline(v) {
      online = !!v;
      if (ws?.readyState === 1) ws.send(JSON.stringify({ op: 'online', value: online }));
      if (!online) for (const l of [...links.values()]) linkDown(l.id);
      status(online ? 'online' : 'offline (by you)');
    },
    get online() { return online; },
    /** Close every link now (engine restart); the remotes reconnect after their back-off. */
    closeAll() { for (const l of [...links.values()]) { l.close(); } },
  };
}
