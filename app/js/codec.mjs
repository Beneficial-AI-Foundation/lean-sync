// Envelope codec, JS side: encodes events (host -> Lean) and decodes effect lists (Lean -> host).
//
// Hand-written against the layouts documented in LeanSync/Envelope.lean (events) and
// LeanSync/EffectsWire.lean (effects, notices, replies); wire version 1. It is checked against
// bytes produced by Lean (test/codec-vectors.mjs, test/wasm-replay.mjs). Peer messages and state
// records are opaque byte strings here: the host stores, hashes and forwards them, never parses them.
//
// JS representations:
//   replica id  {hi: BigInt, lo: BigInt}       hash / digest  Uint8Array(32)
//   peer        Number (< 2^32)                tag            Number
//   event       {type: 'init' | 'initFresh' | 'connected' | ... , ...fields}   (see encodeEvent)
//   effect      {type: 'send' | 'close' | 'persist' | 'fetch' | 'serveBlob' | 'notify' | 'reply', ...}
// A `sendAgain p` effect is resolved here into {type:'send', peer:p, bytes, again:true}, where
// `bytes` is the same Uint8Array as the last state message written in full in this envelope.

export const WIRE_VERSION = 1;
export const KIND_STATE = 1, KIND_MESSAGE = 2, KIND_EVENT = 3, KIND_EFFECTS = 4;
export const HASH_LEN = 32;
export const MAX_PATH_BYTES = 4096;
export const MAX_STATE_BYTES = 64 * 1024 * 1024;
export const MAX_MESSAGE_BYTES = MAX_STATE_BYTES + 64;
export const MAX_EVENT_BYTES = 2 * MAX_STATE_BYTES;
export const MAX_BATCH = 1024;

export const DECODE_ERRORS = ['truncated', 'trailing', 'tooLarge', 'badVersion', 'badKind', 'badTag', 'nonCanonical', 'badUtf8'];
export const CLOSE_REASONS = ['protocolError', 'incompatible', 'sameReplicaId', 'tooManyPeers', 'stateTooLarge'];
export const PEER_STATUS = ['handshaking', 'syncing', 'inSync'];
export const QUERIES = { snapshot: 0, pending: 1, status: 2 };
// What this codec handles; test/unit/codec.test.mjs checks these against Lean's constructor lists.
// Event `localOp` is flattened into its three operations.
export const EVENT_TYPES = ['init', 'initFresh', 'connected', 'disconnected', 'received', 'putMany', 'deleteMany', 'resolve',
  'persisted', 'persistFailed', 'blobStored', 'blobsStored', 'blobFailed', 'blobLost', 'query'];
export const EFFECT_TYPES = ['send', 'close', 'persist', 'fetch', 'serveBlob', 'notify', 'reply'];   // + sendAgain (encoding only)
export const NOTICES = ['indexChanged', 'blobsChanged', 'peerStatus', 'peerClosed', 'peerLeft', 'peerError', 'rollbackDetected',
  'opRejected', 'badEvent', 'startupFailed', 'notInitialized', 'alreadyInitialized', 'pendingSummary', 'saveFailed'];  // by tag
export const REPLIES = ['snapshot', 'pending', 'status'];                                   // by tag
export const PENDING_STATUS = ['waiting', 'requested', 'queued'];                           // by tag

export class CodecError extends Error {
  constructor(msg) { super(msg); this.name = 'CodecError'; }
}

// ---------------------------------------------------------------- writer

class Writer {
  constructor(cap = 256) { this.buf = new Uint8Array(cap); this.len = 0; }
  ensure(n) {
    if (this.len + n <= this.buf.length) return;
    let cap = this.buf.length * 2;
    while (cap < this.len + n) cap *= 2;
    const b = new Uint8Array(cap); b.set(this.buf.subarray(0, this.len)); this.buf = b;
  }
  byte(x) { this.ensure(1); this.buf[this.len++] = x & 0xff; return this; }
  raw(bytes) { this.ensure(bytes.length); this.buf.set(bytes, this.len); this.len += bytes.length; return this; }
  /** Canonical unsigned LEB128 of a non-negative Number (safe integer) or BigInt. */
  nat(v) {
    if (typeof v === 'number') {
      if (!Number.isSafeInteger(v) || v < 0) throw new CodecError(`not a natural number: ${v}`);
      if (v < 0x80) return this.byte(v);
      v = BigInt(v);
    }
    if (typeof v !== 'bigint' || v < 0n) throw new CodecError(`not a natural number: ${v}`);
    do {
      let b = Number(v & 0x7fn); v >>= 7n;
      if (v !== 0n) b |= 0x80;
      this.byte(b);
    } while (v !== 0n);
    return this;
  }
  bytes(b) { return this.nat(b.length).raw(b); }   // length-prefixed
  done() { return this.buf.slice(0, this.len); }
}

const U64_MAX = (1n << 64n) - 1n;
const utf8 = new TextEncoder();

function wReplica(w, r) {
  for (const x of [r.hi, r.lo]) {
    if (typeof x !== 'bigint' || x < 0n || x > U64_MAX) throw new CodecError('replica id halves must be BigInt u64');
  }
  w.nat(r.hi).nat(r.lo);
}
function wPeer(w, p) {
  if (!Number.isInteger(p) || p < 0 || p >= 2 ** 32) throw new CodecError(`bad peer id ${p}`);
  w.nat(p);
}
function wHash(w, h) {
  if (!(h instanceof Uint8Array) || h.length !== HASH_LEN) throw new CodecError('hash must be 32 bytes');
  w.bytes(h);
}
function wHashes(w, hs) { w.nat(hs.length); for (const h of hs) wHash(w, h); }
function wStr(w, s) { w.bytes(utf8.encode(s)); }
function wBool(w, b) { w.byte(b ? 1 : 0); }

/** Encode one event (kind 3). Throws CodecError on a malformed JS value. */
export function encodeEvent(ev) {
  const w = new Writer();
  w.byte(WIRE_VERSION).byte(KIND_EVENT);
  switch (ev.type) {
    case 'init': w.byte(0); wReplica(w, ev.replica); w.bytes(ev.stored); wHashes(w, ev.blobs ?? []); break;
    case 'initFresh': w.byte(1); wReplica(w, ev.replica); wHashes(w, ev.blobs ?? []); break;
    case 'connected': w.byte(2); wPeer(w, ev.peer); break;
    case 'disconnected': w.byte(3); wPeer(w, ev.peer); break;
    case 'received': w.byte(4); wPeer(w, ev.peer); w.bytes(ev.bytes); break;
    case 'putMany':
      w.byte(5).byte(0).nat(ev.items.length);
      for (const it of ev.items) { wStr(w, it.path); wHash(w, it.hash); wHashes(w, it.supersedes ?? []); }
      break;
    case 'deleteMany':
      w.byte(5).byte(1).nat(ev.items.length);
      for (const it of ev.items) {
        wStr(w, it.path);
        if (it.supersedes == null) wBool(w, false); else { wBool(w, true); wHashes(w, it.supersedes); }
      }
      break;
    case 'resolve': w.byte(5).byte(2); wStr(w, ev.path); wHash(w, ev.hash); break;
    case 'persisted':
      w.byte(6).nat(ev.tag);
      if (!(ev.digest instanceof Uint8Array) || ev.digest.length !== 32) throw new CodecError('digest must be 32 bytes');
      w.raw(ev.digest);                                  // digest: 32 raw bytes, no length prefix
      break;
    case 'persistFailed': w.byte(7).nat(ev.tag); break;
    case 'blobStored':
      w.byte(8); wHash(w, ev.hash);
      if (ev.peer == null) wBool(w, false); else { wBool(w, true); wPeer(w, ev.peer); }
      break;
    case 'blobFailed': w.byte(9); wPeer(w, ev.peer); wHash(w, ev.hash); break;
    case 'blobLost': w.byte(10); wHash(w, ev.hash); break;
    case 'query':
      if (!(ev.q in QUERIES)) throw new CodecError(`unknown query ${ev.q}`);
      w.byte(11).byte(QUERIES[ev.q]);
      break;
    case 'blobsStored': w.byte(12); wHashes(w, ev.hashes); break;
    default: throw new CodecError(`unknown event type ${ev.type}`);
  }
  return w.done();
}

// ---------------------------------------------------------------- reader

const utf8d = new TextDecoder('utf-8', { fatal: true });

class Reader {
  constructor(b) { this.b = b; this.pos = 0; }
  byte() {
    if (this.pos >= this.b.length) throw new CodecError('truncated');
    return this.b[this.pos++];
  }
  /** LEB128 of any length, canonical (no trailing zero group), as BigInt. */
  natBig() {
    let v = 0n, shift = 0n;
    for (;;) {
      const x = this.byte();
      v |= BigInt(x & 0x7f) << shift;
      if (x < 0x80) {
        if (x === 0 && shift > 0n) throw new CodecError('non-canonical varint');
        return v;
      }
      shift += 7n;
    }
  }
  nat() {
    const v = this.natBig();
    if (v > BigInt(Number.MAX_SAFE_INTEGER)) throw new CodecError('integer exceeds 2^53');
    return Number(v);
  }
  raw(n) {
    if (this.pos + n > this.b.length) throw new CodecError('truncated');
    const out = this.b.subarray(this.pos, this.pos + n); this.pos += n; return out;
  }
  bytes() { return this.raw(this.nat()); }
  bool() { const x = this.byte(); if (x > 1) throw new CodecError(`bad bool ${x}`); return x === 1; }
  peer() { const p = this.nat(); if (p >= 2 ** 32) throw new CodecError('peer id too large'); return p; }
  str() { try { return utf8d.decode(this.bytes()); } catch { throw new CodecError('bad UTF-8'); } }
  replica() { const hi = this.natBig(); const lo = this.natBig(); return { hi, lo }; }
  list(f) { const k = this.nat(); const out = []; for (let i = 0; i < k; i++) out.push(f()); return out; }
  hash() { return this.bytes(); }      // in effects, hashes are length-prefixed byte strings
}

function rErr(r) {
  const code = r.byte(); const value = r.nat();
  if (code >= DECODE_ERRORS.length) throw new CodecError(`bad error code ${code}`);
  return { error: DECODE_ERRORS[code], value };
}
function rReason(r) {
  const x = r.byte(); if (x >= CLOSE_REASONS.length) throw new CodecError(`bad close reason ${x}`);
  return CLOSE_REASONS[x];
}
function rStatus(r) {
  const x = r.byte(); if (x >= PEER_STATUS.length) throw new CodecError(`bad peer status ${x}`);
  return PEER_STATUS[x];
}

function rNotice(r) {
  const t = r.byte();
  switch (t) {
    case 0: return { notice: 'indexChanged' };
    case 1: return { notice: 'blobsChanged' };
    case 2: { const peer = r.peer(); const status = rStatus(r); const replica = r.bool() ? r.replica() : null; return { notice: 'peerStatus', peer, status, replica }; }
    case 3: { const peer = r.peer(); const reason = rReason(r); const byPeer = r.bool(); return { notice: 'peerClosed', peer, reason, byPeer }; }
    case 4: return { notice: 'peerLeft', peer: r.peer() };
    case 5: { const peer = r.peer(); return { notice: 'peerError', peer, ...rErr(r) }; }
    case 6: return { notice: 'rollbackDetected' };
    case 7: return { notice: 'opRejected', why: r.str() };
    case 8: return { notice: 'badEvent', ...rErr(r) };
    case 9: return { notice: 'startupFailed', ...rErr(r) };
    case 10: return { notice: 'notInitialized' };
    case 11: return { notice: 'alreadyInitialized' };
    case 12: { const fetching = r.nat(); const queued = r.nat(); const waiting = r.nat(); return { notice: 'pendingSummary', fetching, queued, waiting }; }
    case 13: return { notice: 'saveFailed' };
    default: throw new CodecError(`bad notice tag ${t}`);
  }
}

function rReply(r) {
  const t = r.byte();
  switch (t) {
    case 0: return {
      reply: 'snapshot',
      files: r.list(() => ({ path: r.str(), versions: r.list(() => ({ hash: r.hash(), present: r.bool() })) })),
    };
    case 1: return {
      reply: 'pending',
      items: r.list(() => {
        const hash = r.hash(); const s = r.byte();
        if (s === 0) return { hash, status: 'waiting' };
        if (s === 1) return { hash, status: 'requested', peer: r.peer() };
        if (s === 2) return { hash, status: 'queued' };
        throw new CodecError(`bad pending status ${s}`);
      }),
    };
    case 2: {
      const persistInFlight = r.bool(); const dirty = r.bool(); const rollback = r.bool();
      const peers = r.list(() => ({ peer: r.peer(), status: rStatus(r) }));
      return { reply: 'status', persistInFlight, dirty, rollback, peers };
    }
    default: throw new CodecError(`bad reply tag ${t}`);
  }
}

/** Is `msg` (an encoded peer message) a state message? (01 02 02 ...) */
export function isStateMessage(msg) {
  return msg.length >= 3 && msg[0] === WIRE_VERSION && msg[1] === KIND_MESSAGE && msg[2] === 2;
}

/**
 * Decode an effects envelope (kind 4). No total size cap: this is Lean's own output.
 * Returned byte strings are subarrays of `b` (copy them if `b` is reused).
 */
export function decodeEffects(b) {
  const r = new Reader(b);
  if (r.byte() !== WIRE_VERSION) throw new CodecError('bad version');
  if (r.byte() !== KIND_EFFECTS) throw new CodecError('bad kind');
  const k = r.nat();
  const out = [];
  let lastState = null;            // the last state message written in full (for sendAgain)
  for (let i = 0; i < k; i++) {
    const t = r.byte();
    switch (t) {
      case 0: {
        const peer = r.peer(); const bytes = r.bytes();
        if (isStateMessage(bytes)) lastState = bytes;
        out.push({ type: 'send', peer, bytes });
        break;
      }
      case 1: { const peer = r.peer(); out.push({ type: 'close', peer, reason: rReason(r) }); break; }
      case 2: { const tag = r.nat(); out.push({ type: 'persist', tag, state: r.bytes() }); break; }
      case 3: {
        const peer = r.peer(); const hashes = r.list(() => r.hash()); const bytes = r.bytes();
        out.push({ type: 'fetch', peer, hashes, bytes });
        break;
      }
      case 4: { const peer = r.peer(); out.push({ type: 'serveBlob', peer, hash: r.hash() }); break; }
      case 5: out.push({ type: 'notify', ...rNotice(r) }); break;
      case 6: out.push({ type: 'reply', ...rReply(r) }); break;
      case 7: {
        const peer = r.peer();
        if (!lastState) throw new CodecError('sendAgain with no earlier state message');
        out.push({ type: 'send', peer, bytes: lastState, again: true });
        break;
      }
      default: throw new CodecError(`bad effect tag ${t}`);
    }
  }
  if (r.pos !== b.length) throw new CodecError('trailing bytes');
  return out;
}

// ---------------------------------------------------------------- helpers

export const hex = (b) => Array.from(b, (x) => x.toString(16).padStart(2, '0')).join('');
export function fromHex(s) {
  if (s.length % 2) throw new CodecError('odd hex length');
  const out = new Uint8Array(s.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(s.slice(2 * i, 2 * i + 2), 16);
  return out;
}
export const replicaKey = (r) => `${r.hi.toString(16).padStart(16, '0')}${r.lo.toString(16).padStart(16, '0')}`;
export function bytesEqual(a, b) {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
  return true;
}
