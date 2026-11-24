// Links: the host's side of each transport link (docs/app-design.md §6, §7).
//
// - Host framing on a link (Lean never sees it). Every frame starts with a type byte:
//     1 MSG    more:u8 bytes          a fragment of one Lean message (more=1: more fragments follow)
//     2 START  hash:32 size:u64le     a blob stream begins
//     3 DATA   hash:32 bytes          blob bytes
//     4 END    hash:32                the stream is complete
//     5 ABORT  hash:32                sender: cannot serve it / receiver: stop sending it
//     6 CREDIT hash:32 n:u32le        receiver allows n more bytes of that stream
//     7 HELLO  replica:16 label:utf8  host-level greeting, before anything else
//   Frames carry at most FRAME_PAYLOAD bytes of payload (safe for WebRTC data channels).
// - PeerIds: a page-lifetime counter, never reused (not even across engine restarts). A link
//   becomes a Lean peer (`connected p`) only after the remote's HELLO, only while the core accepts
//   peers (after the start-up inventory), and never if the remote presents this device's own
//   replica id (two profiles restored from the same storage): such a link is closed at once.
// - Lean messages are fragmented and reassembled here; a message over MAX_MESSAGE_BYTES closes
//   the link. `close p` closes after the bytes already queued.
// - Blob streams: one outgoing blob at a time per device (bounded memory: the blob is read and
//   verified whole, then streamed), interleaved behind Lean messages, sent only while the link's
//   buffer is below HIGH_WATER and the receiver's credit allows. The receiver grants credit as
//   it writes, so a peer can never make this device buffer more than WINDOW bytes per stream,
//   and a stream announcing more than MAX_FILE_BYTES is refused before any byte is accepted.
import { MAX_MESSAGE_BYTES, replicaKey } from './codec.mjs';
import { MAX_FILE_BYTES } from './storage.mjs';
import { sha256, hex, fromHex } from './hash.mjs';

export const FRAME_PAYLOAD = 16 * 1024;
const HIGH_WATER = 1024 * 1024;
const WINDOW = 4 * 1024 * 1024;
const T = { MSG: 1, START: 2, DATA: 3, END: 4, ABORT: 5, CREDIT: 6, HELLO: 7 };

const u8 = (...parts) => {
  const n = parts.reduce((s, p) => s + (typeof p === 'number' ? 1 : p.length), 0);
  const out = new Uint8Array(n); let o = 0;
  for (const p of parts) { if (typeof p === 'number') out[o++] = p; else { out.set(p, o); o += p.length; } }
  return out;
};
const u32le = (n) => Uint8Array.of(n & 255, (n >>> 8) & 255, (n >>> 16) & 255, (n >>> 24) & 255);
const readU32 = (b, o) => (b[o] | (b[o + 1] << 8) | (b[o + 2] << 16) | (b[o + 3] << 24)) >>> 0;
const replicaBytes = (r) => { const b = new Uint8Array(16); const v = new DataView(b.buffer); v.setBigUint64(0, r.hi); v.setBigUint64(8, r.lo); return b; };
const replicaOf = (b) => { const v = new DataView(b.buffer, b.byteOffset, 16); return { hi: v.getBigUint64(0), lo: v.getBigUint64(8) }; };

/**
 * @param o.emit(ev, epoch)   deliver an event to the core (tagged with the epoch it belongs to)
 * @param o.storage           storage.mjs instance
 * @param o.self()            {replica, label} of this device (replica may be null before start)
 * @param o.epoch()           the core's current epoch
 * @param o.onRefused(info)   a link presented our own replica id
 * @param o.log(msg)
 */
export function createLinks(o) {
  const stallMs = o.stallMs ?? 60000;
  let nextPeer = 1;
  let accepting = false;
  const conns = new Set();             // every live link
  const byPeer = new Map();            // PeerId -> conn (announced to Lean)
  const serveQueue = [];               // [{conn, hx}] waiting for the single outgoing slot
  let serving = null;                  // {conn, hx, hash, data, offset, credit}

  function attach(link) {
    const c = { link, peer: null, epoch: o.epoch(), remote: null, label: link.remoteLabel, alive: true,
      q: [], drainWait: false, inParts: [], inSize: 0, expected: new Set(), recv: new Map() };
    conns.add(c);
    link.onFrame((f) => { try { onFrame(c, f); } catch (e) { o.log(`link ${link.id}: bad frame (${e.message}); closing`); kill(c); } });
    link.onClose(() => onClosed(c));
    const self = o.self();
    if (self.replica) push(c, u8(T.HELLO, replicaBytes(self.replica), new TextEncoder().encode(self.label ?? '')));
    else kill(c);
  }

  // ------------------------------------------------------------ outgoing
  function push(c, frame) { c.q.push(frame); pump(c); }
  function pump(c) {
    if (!c.alive) return;
    while (c.link.bufferedAmount < HIGH_WATER) {
      if (c.q.length) {
        const f = c.q.shift();
        if (f === 'CLOSE') { kill(c); return; }
        c.link.send(f);
        continue;
      }
      if (serving && serving.conn === c && serving.data && serving.credit > 0 && serving.offset < serving.data.length) {
        const n = Math.min(FRAME_PAYLOAD, serving.credit, serving.data.length - serving.offset);
        c.link.send(u8(T.DATA, serving.hash, serving.data.subarray(serving.offset, serving.offset + n)));
        serving.offset += n; serving.credit -= n;
        if (serving.offset === serving.data.length) { c.q.push(u8(T.END, serving.hash)); finishServing(); }
        continue;
      }
      return;
    }
    if (!c.drainWait) { c.drainWait = true; c.link.onDrain(() => { c.drainWait = false; pump(c); }); }
  }

  function sendMessage(peer, bytes) {
    const c = byPeer.get(peer);
    if (!c || !c.alive) return;                 // closed peer: drop silently (Lean gets disconnected)
    if (bytes.length === 0) { push(c, u8(T.MSG, 0)); return; }
    for (let off = 0; off < bytes.length; off += FRAME_PAYLOAD) {
      const end = Math.min(bytes.length, off + FRAME_PAYLOAD);
      c.q.push(u8(T.MSG, end < bytes.length ? 1 : 0, bytes.subarray(off, end)));
    }
    pump(c);
  }
  function closePeer(peer) { const c = byPeer.get(peer); if (c && c.alive) push(c, 'CLOSE'); }

  // ------------------------------------------------------------ serving blobs
  function serve(peer, hash) {
    const c = byPeer.get(peer);
    if (!c || !c.alive) return;
    serveQueue.push({ conn: c, hash: hash.slice(), hx: hex(hash) });
    nextServe();
  }
  async function nextServe() {
    if (serving) return;
    let job;
    while ((job = serveQueue.shift()) && !job.conn.alive) {}
    if (!job) return;
    serving = { ...job, data: null, offset: 0, credit: 0 };
    const s = serving, ep = job.conn.epoch;
    let data = null, lost = null;
    try {
      const file = await o.storage.blobFile(job.hx);
      if (file.size > MAX_FILE_BYTES) lost = 'over the size limit';
      else {
        data = new Uint8Array(await file.arrayBuffer());
        if (hex(await sha256(data)) !== job.hx) { lost = 'content does not match its hash (deleted)'; await o.storage.deleteBlob(job.hx); data = null; }
      }
    } catch (e) { lost = `unreadable (${e.name ?? e})`; }
    if (serving !== s) return;                         // connection went away meanwhile
    if (lost) {
      o.log(`blob ${job.hx.slice(0, 8)}: ${lost}; reporting it lost`);
      if (s.conn.alive) push(s.conn, u8(T.ABORT, s.hash));
      o.emit({ type: 'blobLost', hash: s.hash }, ep);
      finishServing();
      return;
    }
    s.data = data;
    push(s.conn, u8(T.START, s.hash, u32le(data.length), u32le(Math.floor(data.length / 2 ** 32))));
    if (data.length === 0) { push(s.conn, u8(T.END, s.hash)); finishServing(); return; }   // no credit will come
    armStall(s);
  }
  // The serving slot is single: whatever happens, it must be released. Paths: END sent; ABORT from
  // the receiver; the link closes (discard); the blob cannot be read (ABORT + blobLost); and, if the
  // receiver grants no credit for STALL_MS (a receiver that stopped writing), ABORT and move on.
  function armStall(s) {
    clearTimeout(s.stall);
    s.stall = setTimeout(() => {
      if (serving !== s) return;
      o.log(`blob ${s.hx.slice(0, 8)}: no credit from the receiver for ${stallMs} ms; aborting the transfer`);
      if (s.conn.alive) push(s.conn, u8(T.ABORT, s.hash));
      finishServing();
    }, stallMs);
    s.stall?.unref?.();                                   // (Node unit tests) don't hold the process
  }
  function finishServing() { if (serving) clearTimeout(serving.stall); serving = null; queueMicrotask(nextServe); }

  // ------------------------------------------------------------ incoming
  function onFrame(c, f) {
    if (!c.alive || f.length === 0) return;
    const t = f[0];
    if (c.remote === null) {
      if (t !== T.HELLO || f.length < 17) throw new Error('expected HELLO');
      c.remote = replicaOf(f.subarray(1, 17));
      c.label = new TextDecoder().decode(f.subarray(17)) || c.label;
      const self = o.self();
      if (self.replica && replicaKey(self.replica) === replicaKey(c.remote)) {
        o.log(`refused link from "${c.label}": it presents this device's own replica id`);
        o.onRefused?.({ label: c.label });
        kill(c);
        return;
      }
      if (!accepting || c.epoch !== o.epoch()) { kill(c); return; }
      c.peer = nextPeer++;
      byPeer.set(c.peer, c);
      o.emit({ type: 'connected', peer: c.peer }, c.epoch);
      return;
    }
    if (c.peer === null) return;
    switch (t) {
      case T.MSG: {
        const more = f[1] === 1; const part = f.subarray(2);
        // Our framing sends every fragment but the last at exactly FRAME_PAYLOAD bytes; anything else
        // (e.g. a stream of empty continuations) would let a peer grow inParts without bound.
        if (more && part.length !== FRAME_PAYLOAD) { o.log(`peer ${c.peer}: malformed message fragment (${part.length} bytes); closing`); kill(c); return; }
        c.inSize += part.length;
        if (c.inSize > MAX_MESSAGE_BYTES) { o.log(`peer ${c.peer}: message over ${MAX_MESSAGE_BYTES} bytes; closing`); kill(c); return; }
        c.inParts.push(part.slice());
        if (!more) {
          const msg = new Uint8Array(c.inSize); let off = 0;
          for (const p of c.inParts) { msg.set(p, off); off += p.length; }
          c.inParts = []; c.inSize = 0;
          o.emit({ type: 'received', peer: c.peer, bytes: msg }, c.epoch);
        }
        return;
      }
      case T.START: return onStart(c, f.subarray(1, 33), readU32(f, 33) + readU32(f, 37) * 2 ** 32);
      case T.DATA: return onData(c, hex(f.subarray(1, 33)), f.subarray(33));
      case T.END: return onEnd(c, f.subarray(1, 33));
      case T.ABORT: {
        const h = f.subarray(1, 33), hx = hex(h);
        if (serving && serving.conn === c && serving.hx === hx) { finishServing(); return; }   // receiver: stop
        if (c.recv.has(hx) || c.expected.has(hx)) failStream(c, h.slice(), 'the sender aborted');
        return;
      }
      case T.CREDIT: {
        const hx = hex(f.subarray(1, 33));
        if (serving && serving.conn === c && serving.hx === hx) { serving.credit += readU32(f, 33); armStall(serving); pump(c); }
        return;
      }
      default: throw new Error(`unknown frame type ${t}`);
    }
  }

  function expect(peer, hashes) {
    const c = byPeer.get(peer);
    if (c) for (const h of hashes) c.expected.add(hex(h));
  }

  function onStart(c, h, size) {
    const hx = hex(h), hash = h.slice();
    if (!c.expected.has(hx) || c.recv.has(hx)) { push(c, u8(T.ABORT, hash)); return; }   // not asked for
    if (size > MAX_FILE_BYTES) {
      o.log(`peer ${c.peer}: refused blob ${hx.slice(0, 8)} of ${size} bytes (limit ${MAX_FILE_BYTES})`);
      push(c, u8(T.ABORT, hash));
      c.expected.delete(hx);
      o.emit({ type: 'blobFailed', peer: c.peer, hash }, c.epoch);
      return;
    }
    const s = { hash, size, received: 0, written: 0, granted: 0, sink: o.storage.beginIncoming(), chain: null, failed: false };
    s.chain = s.sink;
    c.recv.set(hx, s);
    // If no file can be created for the stream, nothing would ever be written, so no more credit
    // would be granted and the sender could never finish: fail the stream and tell the sender.
    s.sink.catch((e) => {
      if (c.recv.get(hx) !== s || s.failed) return;
      o.onStorageError?.(e);
      failStream(c, hash, `could not create a file for it (${e?.name ?? e})`, true);
      if (c.alive) push(c, u8(T.ABORT, hash));
    });
    grant(c, s);
  }
  function grant(c, s) {
    // keep at most WINDOW bytes accepted but not yet written
    const target = Math.min(s.size, s.written + WINDOW);
    if (target > s.granted) { push(c, u8(T.CREDIT, s.hash, u32le(target - s.granted))); s.granted = target; }
  }
  function onData(c, hx, bytes) {
    const s = c.recv.get(hx);
    if (!s || s.failed) return;
    if (s.received + bytes.length > s.granted) { failStream(c, s.hash, 'sent beyond its credit'); push(c, u8(T.ABORT, s.hash)); return; }
    s.received += bytes.length;
    const chunk = bytes.slice();
    s.chain = s.chain.then(async (sink) => {
      await sink.write(chunk);                          // rejects on a storage error
      s.written += chunk.length;
      if (c.alive && !s.failed) grant(c, s);
      return sink;
    });
    // On the first storage error: no more credit, report the failure, tell the sender to stop.
    s.chain.catch((e) => {
      if (c.recv.get(hx) !== s || s.failed) return;
      o.onStorageError?.(e);
      failStream(c, s.hash, `could not write it (${e?.message ?? e})`, true);
      if (c.alive) push(c, u8(T.ABORT, s.hash));
    });
  }
  function onEnd(c, h) {
    const hx = hex(h), s = c.recv.get(hx);
    if (!s || s.failed) return;
    if (s.received !== s.size) { failStream(c, s.hash, `ended at ${s.received} of ${s.size} bytes`); return; }
    c.recv.delete(hx); c.expected.delete(hx);
    const ep = c.epoch, peer = c.peer;
    s.chain.then((sink) => sink.finish(hx)).then((r) => {
      if (r.ok) o.emit({ type: 'blobStored', hash: s.hash, peer }, ep);
      else { o.log(`peer ${peer}: blob ${hx.slice(0, 8)} failed verification (got ${r.hex.slice(0, 8)})`); o.emit({ type: 'blobFailed', peer, hash: s.hash }, ep); }
    }, (e) => {
      // A write that was still pending at END may have failed, in which case finish() never ran:
      // abort the sink so the writer and the temp file go away (a no-op after finish()).
      s.sink.then((sink) => sink.abort(), () => {});
      o.log(`peer ${peer}: could not store blob ${hx.slice(0, 8)}: ${e.message}`);
      o.onStorageError?.(e);
      // Not the peer's fault. If the connection is gone, Lean has already re-planned the hash
      // (possibly to another peer, whose transfer the peerless event would cancel): say nothing.
      if (c.alive) o.emit({ type: 'blobStoreFailed', hash: s.hash }, ep);
    });
  }
  /** A stream that will not end in a stored blob. `local`: the bytes were fine but this device
   *  could not store them (quota, I/O error): `blobStoreFailed`, which does not blame the peer;
   *  otherwise the transfer itself failed: `blobFailed`, the peer is not asked again this session. */
  function failStream(c, hash, why, local = false) {
    const hx = hex(hash), s = c.recv.get(hx);
    o.log(`peer ${c.peer}: blob ${hx.slice(0, 8)} failed: ${why}`);
    c.recv.delete(hx); c.expected.delete(hx);
    if (s) { s.failed = true; s.sink.then((sink) => sink.abort(), () => {}); }
    o.emit(local ? { type: 'blobStoreFailed', hash } : { type: 'blobFailed', peer: c.peer, hash }, c.epoch);
  }

  // ------------------------------------------------------------ teardown
  function discard(c) {
    for (const s of c.recv.values()) { s.failed = true; s.sink.then((sink) => sink.abort(), () => {}); }
    c.recv.clear(); c.expected.clear(); c.q = [];
    if (serving && serving.conn === c) finishServing();
  }
  function kill(c) {
    if (!c.alive) return;
    c.alive = false;
    try { c.link.close(); } catch {}
    onClosed(c);
  }
  function onClosed(c) {
    if (!conns.delete(c)) return;
    c.alive = false;
    discard(c);                        // partial blobs are discarded and reported nothing more
    if (c.peer !== null && byPeer.get(c.peer) === c) {
      byPeer.delete(c.peer);
      o.emit({ type: 'disconnected', peer: c.peer }, c.epoch);
    }
  }

  return {
    attach, sendMessage, closePeer, expect, serve,
    setAccepting(v) { accepting = v; },
    /** Engine restart: close every link without telling Lean (the old machine is gone). */
    resetAll() {
      for (const c of [...conns]) { byPeer.delete(c.peer); c.peer = null; kill(c); }
      serveQueue.length = 0;
    },
    peers: () => [...byPeer.entries()].map(([peer, c]) => ({ peer, label: c.label, replica: c.remote })),
    labelOf: (peer) => byPeer.get(peer)?.label,
  };
}
