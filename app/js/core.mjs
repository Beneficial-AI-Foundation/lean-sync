// The host core: one queue of events, fed to the Lean engine strictly one at a time; effects
// executed in order; async completions come back as events (docs/app-design.md §3, §4, §8).
//
// Invariants:
// - `processOne` is the only caller of `engine.process`, and it is synchronous: an event's effects
//   are all dispatched (bytes queued, async jobs started) before the next event is processed.
// - Every async completion is tagged with the epoch that started it. A restart (trap, rollback
//   restart, reset) bumps the epoch; stale completions are dropped, except that a blob that became
//   durable is re-reported as `blobsStored [h]`. A stale `persisted` is never delivered (the new
//   machine's tags start again at 0).
// - `persisted` is emitted only after storage.saveRecord resolved, which happens only from the
//   IndexedDB transaction's `complete` event; any failure becomes `persistFailed`.
// - Peers are accepted (`connected`) only after the whole blob inventory was reported.
import { encodeEvent, decodeEffects, replicaKey } from './codec.mjs';
import { EngineTrap } from './engine.mjs';
import { sha256, hex, fromHex } from './hash.mjs';

const INVENTORY_CHUNK = 10000;

export function newReplicaId() {
  const b = new BigUint64Array(2);
  crypto.getRandomValues(b);
  return { hi: b[0], lo: b[1] };
}

/**
 * @param o.makeEngine()   async () => engine (app/js/engine.mjs createEngine with the wasm factory)
 * @param o.storage        app/js/storage.mjs instance (or a fake in unit tests)
 * @param o.links          app/js/links.mjs instance (created with this core's emit/epoch)
 * @param o.ui             callbacks: onPhase, onFiles, onPending, onStatus, onPeers, onNotice, onLog
 */
export function createCore(o) {
  const ui = new Proxy(o.ui ?? {}, { get: (t, k) => t[k] ?? (() => {}) });
  const now = o.now ?? (() => Date.now());
  const maxTraps = o.maxTraps ?? 3, trapWindowMs = o.trapWindowMs ?? 5 * 60 * 1000;

  const st = {
    phase: 'idle',           // idle | starting | running | startupFailed | failed
    epoch: 0, engine: null, instances: 0, traps: [], replica: null, clearRotateOnSave: false,
    queue: [], pumping: false, persist: null, saveFailed: false, saveBackoff: 0, nudgeTimer: null,
    rollback: false, startupError: null, failure: null, lastSnapshot: null, refreshTimer: null, refreshWhat: new Set(),
    log: [],
  };
  const log = (m) => { const line = `${new Date(now()).toISOString().slice(11, 23)} ${m}`; st.log.push(line); if (st.log.length > 500) st.log.shift(); ui.onLog(line); };
  const setPhase = (p, extra) => { st.phase = p; ui.onPhase(p, extra); };

  // ------------------------------------------------------------ events
  function emit(ev, ep = st.epoch) {
    if (ep !== st.epoch) {
      if (ev.type === 'blobStored') ev = { type: 'blobsStored', hashes: [ev.hash] };   // durable fact survives
      else return;                                                                       // peer- or persist-bound: stale
    }
    st.queue.push(ev);
    schedulePump();
  }
  function schedulePump() { if (!st.pumping) { st.pumping = true; queueMicrotask(pump); } }
  function pump() {
    try {
      while (st.queue.length && st.phase === 'running') {
        const ev = st.queue.shift();
        if (!processOne(ev)) return;
      }
    } finally { st.pumping = false; }
  }

  /** Feed one event; execute its effects. Returns false if the engine trapped. */
  function processOne(ev) {
    let out;
    try { out = st.engine.process(encodeEvent(ev)); }
    catch (e) {
      if (e instanceof EngineTrap || e?.name === 'EngineDead') { onTrap(e); return false; }
      throw e;                                   // a host bug (e.g. a malformed event): surface it
    }
    const effects = decodeEffects(out);
    for (const eff of effects) execute(eff);
    return true;
  }

  // ------------------------------------------------------------ effects
  function execute(e) {
    switch (e.type) {
      case 'send': o.links.sendMessage(e.peer, e.bytes); break;
      case 'close': o.links.closePeer(e.peer); log(`closing peer ${e.peer}: ${e.reason}`); break;
      case 'fetch': o.links.expect(e.peer, e.hashes); o.links.sendMessage(e.peer, e.bytes); break;
      case 'serveBlob': o.links.serve(e.peer, e.hash); break;
      case 'persist': startPersist(e.tag, e.state); break;
      case 'notify': notice(e); break;
      case 'reply': reply(e); break;
    }
  }

  function startPersist(tag, state) {
    if (st.persist) log(`host check: a second persist (tag ${tag}) while one is in flight`);
    const ep = st.epoch, replica = st.replica, clearRotate = st.clearRotateOnSave;
    const job = (async () => {
      const digest = await sha256(state);           // SHA-256 of exactly the bytes stored
      await o.storage.saveRecord(replica, state, { clearRotate });   // resolves only on `complete`
      return digest;
    })();
    // The slot is cleared BEFORE the acknowledgement is emitted, and only if it still holds this
    // write: processing `persisted` can start the next persist, which takes the slot.
    const done = () => { if (st.persist === slot) st.persist = null; };
    const slot = job.then((digest) => {
      done();
      if (ep !== st.epoch) return;
      if (clearRotate) st.clearRotateOnSave = false;
      if (st.saveFailed) { st.saveFailed = false; st.saveBackoff = 0; clearTimeout(st.nudgeTimer); st.nudgeTimer = null; log('saving works again'); ui.onNotice({ notice: 'saveRecovered' }); }
      emit({ type: 'persisted', tag, digest }, ep);
      refresh('status', ...st.refreshWhat);
    }, (err) => {
      done();
      if (ep !== st.epoch) return;
      log(`persist ${tag} failed: ${err?.message ?? err}`);
      emit({ type: 'persistFailed', tag }, ep);
    });
    st.persist = slot;
  }

  function notice(e) {
    switch (e.notice) {
      case 'startupFailed': st.startupFailedNotice = e; break;
      case 'indexChanged': refresh('snapshot', 'pending', 'status'); break;
      case 'blobsChanged': refresh('snapshot', 'pending'); break;
      case 'saveFailed': {
        st.saveFailed = true;
        // Lean retries on the next event; if no other event comes, nudge it after a back-off
        // (1, 2, 4 ... 60 s). The back-off grows only with the nudges themselves, so failures
        // caused by a burst of real events do not push the next scheduled retry far away.
        if (!st.nudgeTimer) {
          st.saveBackoff = st.saveBackoff || 1000;
          const ep = st.epoch;
          st.nudgeTimer = setTimeout(() => { st.nudgeTimer = null; st.saveBackoff = Math.min(st.saveBackoff * 2, 60000); nudge(ep); }, st.saveBackoff);
        }
        break;
      }
      case 'rollbackDetected':
        st.rollback = true;
        log('rollback detected: edits are blocked; a restart under a new identity is required');
        o.storage.setRotate().catch((err) => log(`could not record the identity change: ${err.message}`));
        break;
      case 'peerClosed': if (e.reason === 'sameReplicaId') log(`peer ${e.peer} uses this device's replica id: session refused`); break;
      case 'badEvent': log(`host bug: Lean rejected an event (${e.error} ${e.value})`); break;
      case 'notInitialized': case 'alreadyInitialized': log(`host check: ${e.notice}`); break;
      case 'peerError': log(`peer ${e.peer}: protocol error ${e.error}`); break;
      case 'opRejected': log(`operation rejected: ${e.why}`); break;
    }
    if (e.notice === 'peerStatus' || e.notice === 'peerLeft' || e.notice === 'peerClosed') ui.onPeers(peerList(e));
    // Where each missing blob is requested changes with the peers (a disconnect moves requests to
    // other peers or to `waiting`) without any index or blob change: re-query the pending list.
    if (['peerStatus', 'peerLeft', 'peerClosed', 'pendingSummary'].includes(e.notice)) refresh('pending');
    ui.onNotice(e);
  }

  const peerState = new Map();
  function peerList(e) {
    if (e.notice === 'peerStatus') peerState.set(e.peer, { peer: e.peer, status: e.status, replica: e.replica, label: o.links.labelOf(e.peer) });
    else peerState.delete(e.peer);
    return [...peerState.values()];
  }

  function reply(e) {
    if (e.reply === 'snapshot') { st.lastSnapshot = e.files; ui.onFiles(e.files); }
    else if (e.reply === 'pending') ui.onPending(e.items);
    else if (e.reply === 'status') ui.onStatus({ ...e, saveFailed: st.saveFailed, rollback: st.rollback || e.rollback });
  }

  // While saves fail, every event makes Lean retry the write, so the host must not generate events
  // of its own (UI queries) in reaction: they wait for the back-off nudge.
  function nudge(ep) {
    if (ep !== st.epoch) return;
    st.refreshWhat.add('status');
    const ws = [...st.refreshWhat]; st.refreshWhat.clear();
    for (const q of ['status', 'snapshot', 'pending']) if (ws.includes(q)) emit({ type: 'query', q }, ep);
  }
  function refresh(...what) {
    for (const w of what) st.refreshWhat.add(w);
    if (st.refreshTimer || st.saveFailed) return;
    const ep = st.epoch;
    st.refreshTimer = setTimeout(() => {
      st.refreshTimer = null;
      if (st.saveFailed) return;                     // deferred to the nudge
      const ws = [...st.refreshWhat]; st.refreshWhat.clear();
      for (const q of ['snapshot', 'pending', 'status']) if (ws.includes(q)) emit({ type: 'query', q }, ep);
    }, 60);
  }

  // ------------------------------------------------------------ start-up
  async function start({ reset = false } = {}) {
    setPhase('starting');
    st.rollback = false; st.startupError = null; st.failure = null; peerState.clear(); ui.onPeers([]);
    clearTimeout(st.refreshTimer); st.refreshTimer = null; st.refreshWhat.clear(); st.lastSnapshot = null;
    let rec, rotate, hashes;
    try {
      await o.storage.cleanIncoming();
      rec = await o.storage.loadRecord();
      rotate = await o.storage.getRotate();
      hashes = (await o.storage.listBlobs()).map(fromHex);
    } catch (e) { return fail(`storage could not be read: ${e.message ?? e}`); }
    try { st.engine = await o.makeEngine(); st.instances++; }
    catch (e) { return fail(`the sync engine could not be loaded: ${e.message ?? e}`); }

    let ev;
    if (reset || !rec) { st.replica = newReplicaId(); ev = { type: 'initFresh', replica: st.replica }; }
    else if (rotate || rec.corrupt) { st.replica = newReplicaId(); ev = { type: 'init', replica: st.replica, stored: rec.state }; }
    else { st.replica = rec.replica; ev = { type: 'init', replica: st.replica, stored: rec.state }; }
    st.clearRotateOnSave = !rec || reset || rotate || !!rec.corrupt;
    ev.blobs = hashes.slice(0, INVENTORY_CHUNK);
    log(`start: ${ev.type} as ${replicaKey(st.replica).slice(0, 8)}${rotate ? ' (new identity)' : ''}, ${hashes.length} blobs on disk`);

    // Start-up events are processed here directly, in order, before any peer is accepted.
    st.startupFailedNotice = null;
    st.phase = 'running-startup';
    if (!processOne(ev)) return;
    for (let i = INVENTORY_CHUNK; i < hashes.length && !st.startupFailedNotice; i += INVENTORY_CHUNK) {
      if (!processOne({ type: 'blobsStored', hashes: hashes.slice(i, i + INVENTORY_CHUNK) })) return;
    }
    const failedNotice = st.startupFailedNotice;
    if (failedNotice) {
      st.startupError = `${failedNotice.error}${failedNotice.value ? ' ' + failedNotice.value : ''}`;
      log(`start-up failed: the stored index does not decode (${st.startupError})`);
      return setPhase('startupFailed', st.startupError);
    }
    setPhase('running');
    o.links.setAccepting(true);
    refresh('snapshot', 'pending', 'status');
    schedulePump();
  }

  function fail(msg) {
    st.failure = msg; log(msg);
    o.links.setAccepting(false);
    setPhase('failed', msg);
  }

  async function restart(why, opts = {}) {
    log(`restarting the engine: ${why}`);
    setPhase('starting');                  // leave `running` first: no edits, no pump, no queries
    st.epoch++;
    st.queue = [];
    o.links.setAccepting(false);
    o.links.resetAll();
    st.engine = null;
    clearTimeout(st.nudgeTimer); st.nudgeTimer = null; st.saveFailed = false; st.saveBackoff = 0;
    const p = st.persist; st.persist = null;
    if (p) await p.catch(() => {});        // let the in-flight write settle before re-reading storage
    await start(opts);
  }

  function onTrap(e) {
    const during = st.phase !== 'running';
    st.traps.push(now());
    log(`the sync engine trapped${during ? ' during start-up' : ''}: ${e.cause?.message ?? e.message}`);
    st.engine = null;
    if (during) {                          // deterministic on the stored state? never loop
      st.epoch++; st.queue = []; o.links.setAccepting(false); o.links.resetAll();
      return fail('The sync engine failed while starting. Nothing was changed on disk.');
    }
    const recent = st.traps.filter((t) => now() - t < trapWindowMs).length;
    if (recent >= maxTraps) {
      st.epoch++; st.queue = []; o.links.setAccepting(false); o.links.resetAll();
      return fail(`The sync engine failed ${recent} times in a few minutes; sync is stopped.`);
    }
    ui.onNotice({ notice: 'engineRestarted', count: st.traps.length });
    restart('trap').catch((err) => fail(`restart failed: ${err.message}`));
  }

  // ------------------------------------------------------------ user operations
  const canEdit = () => st.phase === 'running' && !st.rollback;
  function versionsOf(path) { return (st.lastSnapshot?.find((f) => f.path === path)?.versions ?? []).map((v) => v.hash); }

  return {
    st, emit, start, restart, log,
    epoch: () => st.epoch,
    replica: () => st.replica,
    canEdit,
    // Supersession rule: every operation supersedes exactly the versions the user was shown when
    // acting. They are captured synchronously, before any await; a version that arrives later
    // (e.g. a peer's edit during an upload) is not superseded and becomes a conflict.
    // `shown` (path -> [hash]) comes from the UI; versionsOf() is the snapshot the UI last rendered.

    /** Store each file (verified), then one putMany superseding the versions shown for that name. */
    async addFiles(files) {
      if (!canEdit()) throw new Error('editing is not possible right now');
      const seen = files.map((f) => f.supersedes ?? versionsOf(f.name));     // before the first await
      const ep = st.epoch;                                                    // the machine the user acted on
      const items = [], errors = [];
      for (let i = 0; i < files.length; i++) {
        const { name, blob } = files[i];
        try {
          const r = await o.storage.storeLocal(blob);
          items.push({ path: name, hash: r.hash, supersedes: seen[i] });
        } catch (e) { errors.push({ name, error: e.message ?? String(e) }); log(`could not add ${name}: ${e.message}`); }
      }
      if (items.length) {
        // The engine restarted while the files were being stored: the versions the user saw belong to
        // the old machine, so the edit is not applied. The stored blobs are durable: report them.
        if (st.epoch !== ep) {
          emit({ type: 'blobsStored', hashes: items.map((it) => it.hash) });   // queued until running
          log('an add was dropped: the engine restarted while its files were being stored');
          errors.push(...items.map((it) => ({ name: it.path, error: 'the sync engine restarted meanwhile; please add it again' })));
          return { added: 0, errors };
        }
        if (!canEdit()) { errors.push(...items.map((it) => ({ name: it.path, error: 'editing was blocked meanwhile' }))); return { added: 0, errors }; }
        emit({ type: 'putMany', items });
      }
      return { added: items.length, errors };
    },
    /** items: [{path, versions: [hash] shown}] */
    deleteFiles(items) {
      if (!canEdit()) throw new Error('editing is not possible right now');
      emit({ type: 'deleteMany', items: items.map(({ path, versions }) => ({ path, supersedes: versions ?? versionsOf(path) })) });
    },
    keepVersion(path, hash, shown) {
      if (!canEdit()) throw new Error('editing is not possible right now');
      emit({ type: 'putMany', items: [{ path, hash, supersedes: shown ?? versionsOf(path) }] });
    },
    keepBoth(path, keepHash, otherHash, otherName, shown) {
      if (!canEdit()) throw new Error('editing is not possible right now');
      if (st.lastSnapshot?.some((f) => f.path === otherName)) throw new Error(`${otherName} already exists`);
      emit({ type: 'putMany', items: [{ path, hash: keepHash, supersedes: shown ?? versionsOf(path) }, { path: otherName, hash: otherHash, supersedes: [] }] });
    },
    /** Read a stored version, verify it, return a Blob (or throw). A missing or damaged copy is
     *  reported lost (Lean then fetches it again); other read errors are treated as transient. */
    async readVerified(hash) {
      const hx = hex(hash);
      let data;
      try { data = new Uint8Array(await (await o.storage.blobFile(hx)).arrayBuffer()); }
      catch (e) {
        if (e?.name === 'NotFoundError') {
          emit({ type: 'blobLost', hash });
          throw new Error('the stored copy is missing; it will be fetched again');
        }
        throw new Error(`could not read the stored copy (${e?.name ?? e}); try again`);
      }
      if (hex(await sha256(data)) !== hx) {
        await o.storage.deleteBlob(hx);
        emit({ type: 'blobLost', hash });
        throw new Error('the stored copy is damaged; it was removed and will be fetched again');
      }
      return new Blob([data]);
    },
    retrySave() { if (st.phase === 'running') { clearTimeout(st.nudgeTimer); st.nudgeTimer = null; nudge(st.epoch); } },
    resetIndex: () => restart('reset confirmed by the user', { reset: true }),
    async newIdentity() { await o.storage.setRotate(); await restart('new identity confirmed by the user'); },
    retryStart: () => restart('retry'),
  };
}
