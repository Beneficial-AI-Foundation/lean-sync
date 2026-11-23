// JS envelope codec vs Lean (node --test). Needs build/vectors/codec.jsonl and ctors.json, which
// scripts/test-app.sh regenerates from the current Lean build before every run:
//   .lake/build/bin/sync-tests vectors build/vectors/codec.jsonl
//   lake env lean --run scripts/wasm/Ctors.lean > build/vectors/ctors.json
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import * as C from '../../app/js/codec.mjs';

const root = join(dirname(fileURLToPath(import.meta.url)), '../..');
const vectors = readFileSync(join(root, 'build/vectors/codec.jsonl'), 'utf8').trim().split('\n').map((l) => JSON.parse(l));
const ctors = JSON.parse(readFileSync(join(root, 'build/vectors/ctors.json'), 'utf8'));

// JSON (hex strings, decimal replica halves) -> the JS event value the app would build.
const HEXKEYS = new Set(['stored', 'bytes', 'hash', 'digest']);
function toJs(v, key) {
  if (Array.isArray(v)) return v.map((x) => toJs(x, key));
  if (v && typeof v === 'object') {
    if (key === 'replica') return { hi: BigInt(v.hi), lo: BigInt(v.lo) };
    return Object.fromEntries(Object.entries(v).map(([k, x]) => [k, toJs(x, k)]));
  }
  if (typeof v === 'string' && (HEXKEYS.has(key) || key === 'blobs' || key === 'supersedes' || key === 'hashes')) return C.fromHex(v);
  return v;
}
// decoded JS value -> JSON shape (Uint8Array -> hex, BigInt -> decimal string, `again` dropped)
function toJson(v) {
  if (v instanceof Uint8Array) return C.hex(v);
  if (typeof v === 'bigint') return v.toString();
  if (Array.isArray(v)) return v.map(toJson);
  if (v && typeof v === 'object') return Object.fromEntries(Object.entries(v).filter(([k]) => k !== 'again').map(([k, x]) => [k, toJson(x)]));
  return v;
}

test('JS tables cover exactly the constructors Lean defines', () => {
  const same = (a, b, what) => assert.deepEqual([...a].sort(), [...b].sort(), what);
  same(C.EVENT_TYPES, [...ctors.Event.filter((c) => c !== 'localOp'), ...ctors.LocalOp], 'events');
  same(Object.keys(C.QUERIES), ctors.Query, 'queries');
  same(C.EFFECT_TYPES, ctors.Effect, 'effects');
  same(C.NOTICES, ctors.Notice, 'notices');
  same(C.REPLIES, ctors.Reply, 'replies');
  same(C.PENDING_STATUS, ctors.PendingStatus, 'pending statuses');
  same(C.PEER_STATUS, ctors.PeerStatus, 'peer statuses');
  same(C.CLOSE_REASONS, ctors.CloseReason, 'close reasons');
  same(C.DECODE_ERRORS, ctors.DecodeError, 'decode errors');
});

test('every event encodes to exactly Lean\'s bytes', () => {
  const seen = new Set();
  for (const v of vectors.filter((x) => x.event)) {
    seen.add(v.event.type);
    assert.equal(C.hex(C.encodeEvent(toJs(v.event))), v.hex, JSON.stringify(v.event).slice(0, 200));
  }
  assert.deepEqual([...seen].sort(), [...C.EVENT_TYPES].sort(), 'vectors cover every event type');
});

test('every effects envelope decodes to exactly Lean\'s effects', () => {
  const seen = { effect: new Set(), notice: new Set(), reply: new Set(), pending: new Set(), sendAgain: 0 };
  for (const v of vectors.filter((x) => x.effects)) {
    const bytes = C.fromHex(v.hex);
    const got = C.decodeEffects(bytes);
    assert.deepEqual(toJson(got), v.effects);
    for (const e of got) {
      seen.effect.add(e.type);
      if (e.again) seen.sendAgain++;
      if (e.notice) seen.notice.add(e.notice);
      if (e.reply) seen.reply.add(e.reply);
      for (const it of e.items ?? []) if (it.status) seen.pending.add(it.status);
    }
  }
  assert.deepEqual([...seen.effect].sort(), [...C.EFFECT_TYPES].sort());
  assert.deepEqual([...seen.notice].sort(), [...C.NOTICES].sort());
  assert.deepEqual([...seen.reply].sort(), [...C.REPLIES].sort());
  assert.deepEqual([...seen.pending].sort(), [...C.PENDING_STATUS].sort());
  assert.ok(seen.sendAgain > 0, 'sendAgain covered');
});

test('every proper prefix of every effects envelope is rejected', () => {
  let n = 0;
  for (const v of vectors.filter((x) => x.effects)) {
    const b = C.fromHex(v.hex);
    for (let i = 0; i < b.length; i++) { assert.throws(() => C.decodeEffects(b.subarray(0, i)), C.CodecError); n++; }
    const extra = new Uint8Array(b.length + 1); extra.set(b);
    assert.throws(() => C.decodeEffects(extra), /trailing/);
  }
  assert.ok(n > 1000);
});

test('encoder rejects malformed JS values', () => {
  assert.throws(() => C.encodeEvent({ type: 'blobLost', hash: new Uint8Array(31) }), C.CodecError);
  assert.throws(() => C.encodeEvent({ type: 'connected', peer: 2 ** 32 }), C.CodecError);
  assert.throws(() => C.encodeEvent({ type: 'initFresh', replica: { hi: 1, lo: 2n }, blobs: [] }), C.CodecError);
  assert.throws(() => C.encodeEvent({ type: 'nope' }), C.CodecError);
  assert.throws(() => C.decodeEffects(Uint8Array.from([1, 4, 1, 7, 0])), /sendAgain/);
  assert.throws(() => C.decodeEffects(Uint8Array.from([1, 4, 1, 2, 0x80, 0x00, 0])), /non-canonical/);
});

test('paths round-trip byte for byte: leading U+FEFF kept, invalid UTF-8 rejected', () => {
  const bom = '\uFEFFnotes.txt';
  const ev = C.encodeEvent({ type: 'resolve', path: bom, hash: new Uint8Array(32) });
  assert.deepEqual([...ev.subarray(5, 8)], [0xef, 0xbb, 0xbf], 'BOM encoded');
  // a snapshot reply carrying that path: 01 04 | 1 effect | 6 reply | 0 snapshot | 1 file | path | 0 versions
  const pb = new TextEncoder().encode(bom);
  const env = Uint8Array.from([1, 4, 1, 6, 0, 1, pb.length, ...pb, 0]);
  assert.equal(C.decodeEffects(env)[0].files[0].path, bom);
  const bad = Uint8Array.from([1, 4, 1, 6, 0, 1, 2, 0xc3, 0x28, 0]);   // invalid UTF-8
  assert.throws(() => C.decodeEffects(bad), C.CodecError);
});
