// Host framing, peers, blob streams (app/js/links.mjs) with a fake transport link and storage.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createLinks, FRAME_PAYLOAD } from '../../app/js/links.mjs';
import { MAX_FILE_BYTES } from '../../app/js/storage.mjs';
import { MAX_MESSAGE_BYTES } from '../../app/js/codec.mjs';
import { sha256, hex } from '../../app/js/hash.mjs';
import { memoryStorage, fakeLink, sleep } from './fakes.mjs';

const ME = { hi: 1n, lo: 2n }, OTHER = { hi: 3n, lo: 4n };
const repl = (r) => { const b = new Uint8Array(16); const v = new DataView(b.buffer); v.setBigUint64(0, r.hi); v.setBigUint64(8, r.lo); return b; };
const hello = (r, label = 'R') => Uint8Array.from([7, ...repl(r), ...new TextEncoder().encode(label)]);
const u32 = (n) => [n & 255, (n >>> 8) & 255, (n >>> 16) & 255, (n >>> 24) & 255];
const start = (h, size) => Uint8Array.from([2, ...h, ...u32(size % 2 ** 32), ...u32(Math.floor(size / 2 ** 32))]);
const data = (h, b) => Uint8Array.from([3, ...h, ...b]);
const end = (h) => Uint8Array.from([4, ...h]);

function setup({ accepting = true } = {}) {
  const events = []; const refused = []; const storage = memoryStorage();
  const links = createLinks({ emit: (ev) => events.push(ev), storage, self: () => ({ replica: ME, label: 'me' }), epoch: () => 0,
    onRefused: (r) => refused.push(r), log: () => {} });
  links.setAccepting(accepting);
  const link = fakeLink(); links.attach(link);
  return { events, refused, storage, links, link };
}
const types = (evs) => evs.map((e) => e.type);

test('HELLO is sent first; the remote becomes a peer only after its HELLO', () => {
  const { events, link } = setup();
  assert.equal(link.sent[0][0], 7);
  assert.deepEqual(events, []);
  link.deliver(hello(OTHER));
  assert.deepEqual(events, [{ type: 'connected', peer: 1 }]);
});

test('a link presenting our own replica id is refused, never a peer', async () => {
  const { events, refused, link } = setup();
  link.deliver(hello(ME, 'twin'));
  await sleep(1);
  assert.equal(link.closed, true); assert.deepEqual(events, []); assert.deepEqual(refused, [{ label: 'twin' }]);
});

test('links are refused while the core does not accept peers (inventory not complete)', async () => {
  const { events, link } = setup({ accepting: false });
  link.deliver(hello(OTHER));
  await sleep(1);
  assert.equal(link.closed, true); assert.deepEqual(events, []);
});

test('messages are fragmented and reassembled exactly', () => {
  const a = setup(), msg = Uint8Array.from({ length: 2 * FRAME_PAYLOAD + 5 }, (_, i) => i & 255);
  a.link.deliver(hello(OTHER));
  a.link.sent.length = 0;
  a.links.sendMessage(1, msg);
  assert.deepEqual(a.link.sent.map((f) => [f[0], f[1]]), [[1, 1], [1, 1], [1, 0]]);
  const b = setup(); b.link.deliver(hello(OTHER));
  for (const f of a.link.sent) b.link.deliver(f);
  assert.deepEqual(b.events[1], { type: 'received', peer: 1, bytes: msg });
  a.links.sendMessage(99, msg);                     // unknown / closed peer: dropped silently
});

test('a message over the limit closes the link', async () => {
  const { events, link } = setup(); link.deliver(hello(OTHER));
  const frag = new Uint8Array(2 + FRAME_PAYLOAD); frag[0] = 1; frag[1] = 1;      // well-formed continuations
  for (let n = 0; n * FRAME_PAYLOAD <= MAX_MESSAGE_BYTES && !link.closed; n++) link.deliver(frag);
  await sleep(1);
  assert.equal(link.closed, true);
  assert.deepEqual(types(events), ['connected', 'disconnected']);
});

test('a stream announcing more than the size limit is refused before any byte is accepted', () => {
  const { events, link, links, storage } = setup(); link.deliver(hello(OTHER));
  const h = new Uint8Array(32).fill(9);
  links.expect(1, [h]);
  link.sent.length = 0;
  link.deliver(start(h, MAX_FILE_BYTES + 1));
  assert.equal(link.sent[0][0], 5, 'ABORT sent');
  assert.equal(link.sent.filter((f) => f[0] === 6).length, 0, 'no credit granted');
  assert.equal(storage.incoming.length, 0, 'nothing written');
  assert.deepEqual(types(events), ['connected', 'blobFailed']);
});

test('unexpected streams are aborted without events', () => {
  const { events, link } = setup(); link.deliver(hello(OTHER));
  link.sent.length = 0;
  link.deliver(start(new Uint8Array(32).fill(1), 10));
  assert.equal(link.sent[0][0], 5); assert.deepEqual(types(events), ['connected']);
});

test('a verified stream is stored and reported; credit bounds what the sender may send', async () => {
  const { events, link, links, storage } = setup(); link.deliver(hello(OTHER));
  const body = Uint8Array.from({ length: 50000 }, (_, i) => (i * 7) & 255), h = await sha256(body);
  links.expect(1, [h]);
  link.sent.length = 0;
  link.deliver(start(h, body.length));
  const credit = link.sent.find((f) => f[0] === 6);
  assert.ok(credit, 'credit granted'); assert.equal(credit[33] | (credit[34] << 8) | (credit[35] << 16), body.length);
  for (let o = 0; o < body.length; o += 16384) link.deliver(data(h, body.subarray(o, o + 16384)));
  link.deliver(end(h));
  await sleep(10);
  assert.deepEqual(events.at(-1), { type: 'blobStored', hash: h, peer: 1 });
  assert.ok(storage.blobs.has(hex(h)));
});

test('content that does not match its hash is reported as failed, never stored', async () => {
  const { events, link, links, storage } = setup(); link.deliver(hello(OTHER));
  const body = new Uint8Array(100).fill(1), h = await sha256(body);
  links.expect(1, [h]);
  link.deliver(start(h, 100)); link.deliver(data(h, new Uint8Array(100).fill(2))); link.deliver(end(h));
  await sleep(10);
  assert.deepEqual(types(events), ['connected', 'blobFailed']); assert.equal(storage.blobs.size, 0);
});

test('bytes beyond the granted credit fail the stream', async () => {
  const { events, link, links } = setup(); link.deliver(hello(OTHER));
  const h = new Uint8Array(32).fill(4);
  links.expect(1, [h]);
  link.deliver(start(h, 10));
  link.deliver(data(h, new Uint8Array(11)));
  assert.deepEqual(types(events), ['connected', 'blobFailed']);
});

test('a link dropped mid-stream discards the partial blob and reports only the disconnect', async () => {
  const { events, link, links, storage } = setup(); link.deliver(hello(OTHER));
  const h = new Uint8Array(32).fill(5);
  links.expect(1, [h]);
  link.deliver(start(h, 1000)); link.deliver(data(h, new Uint8Array(100)));
  link.drop();
  await sleep(10);
  assert.deepEqual(types(events), ['connected', 'disconnected']); assert.equal(storage.aborted, 1); assert.equal(storage.blobs.size, 0);
});

test('serving: an unreadable blob is aborted and reported lost; a readable one is streamed under credit', async () => {
  const { events, link, links, storage } = setup(); link.deliver(hello(OTHER));
  const missing = new Uint8Array(32).fill(6);
  link.sent.length = 0;
  links.serve(1, missing);
  await sleep(10);
  assert.equal(link.sent[0][0], 5); assert.deepEqual(events.at(-1), { type: 'blobLost', hash: missing });
  const body = new Uint8Array(40000).fill(3), h = await sha256(body);
  storage.blobs.set(hex(h), body);
  link.sent.length = 0;
  links.serve(1, h);
  await sleep(10);
  assert.deepEqual(link.sent.map((f) => f[0]), [2], 'START only, no data before credit');
  link.deliver(Uint8Array.from([6, ...h, ...u32(20000)]));
  await sleep(5);
  const sentData = link.sent.filter((f) => f[0] === 3).reduce((n, f) => n + f.length - 33, 0);
  assert.equal(sentData, 20000, 'exactly the credit');
  link.deliver(Uint8Array.from([6, ...h, ...u32(20000)]));
  await sleep(5);
  assert.equal(link.sent.at(-1)[0], 4, 'END after the last byte');
});

test('PeerIds are never reused; connected/disconnected once per link', async () => {
  const events = []; const storage = memoryStorage();
  const links = createLinks({ emit: (ev) => events.push(ev), storage, self: () => ({ replica: ME, label: 'me' }), epoch: () => 0, log: () => {} });
  links.setAccepting(true);
  const l1 = fakeLink(1), l2 = fakeLink(2), l3 = fakeLink(3);
  links.attach(l1); l1.deliver(hello(OTHER));
  links.attach(l2); l2.deliver(hello({ hi: 5n, lo: 6n }));
  l1.drop(); l1.drop();
  links.attach(l3); l3.deliver(hello(OTHER));
  assert.deepEqual(events.map((e) => `${e.type} ${e.peer}`), ['connected 1', 'connected 2', 'disconnected 1', 'connected 3']);
});

test('close goes out after the bytes already queued', async () => {
  const { link, links } = setup(); link.deliver(hello(OTHER));
  link.sent.length = 0;
  link.bufferedAmount = 2 * 1024 * 1024;                 // congested: frames wait in the queue
  links.sendMessage(1, new Uint8Array(100));
  links.closePeer(1);
  assert.equal(link.closed, false, 'not closed before the queued message');
  link.bufferedAmount = 0;
  await sleep(5);
  assert.deepEqual(link.sent.map((f) => f[0]), [1]); assert.equal(link.closed, true);
});

// ---- the single serving slot is always released ----
function server({ stallMs } = {}) {
  const events = []; const storage = memoryStorage();
  const links = createLinks({ emit: (ev) => events.push(ev), storage, self: () => ({ replica: ME, label: 'me' }), epoch: () => 0, log: () => {}, stallMs });
  links.setAccepting(true);
  const a = fakeLink(1), b = fakeLink(2);
  links.attach(a); a.deliver(hello(OTHER));
  links.attach(b); b.deliver(hello({ hi: 7n, lo: 8n }));
  a.sent.length = 0; b.sent.length = 0;
  return { events, storage, links, a, b };
}
const put = async (storage, bytes) => { const h = await sha256(bytes); storage.blobs.set(hex(h), bytes); return h; };

test('an empty blob is served as START + END and frees the slot', async () => {
  const t = server();
  const empty = await put(t.storage, new Uint8Array(0)), next = await put(t.storage, new Uint8Array(10).fill(1));
  t.links.serve(1, empty); t.links.serve(2, next);
  await sleep(20);
  assert.deepEqual(t.a.sent.map((f) => f[0]), [2, 4], 'START then END, no credit needed');
  assert.deepEqual(t.b.sent.map((f) => f[0]), [2], 'the next blob is served');
});

test('an empty blob is received and stored', async () => {
  const { events, link, links, storage } = setup(); link.deliver(hello(OTHER));
  const h = await sha256(new Uint8Array(0));
  links.expect(1, [h]);
  link.deliver(start(h, 0)); link.deliver(end(h));
  await sleep(10);
  assert.deepEqual(events.at(-1), { type: 'blobStored', hash: h, peer: 1 }); assert.ok(storage.blobs.has(hex(h)));
});

test('if no file can be created for a stream: blobStoreFailed (not the peer\'s fault), and ABORT so the sender moves on', async () => {
  const { events, link, links, storage } = setup(); link.deliver(hello(OTHER));
  storage.beginIncoming = async () => { throw Object.assign(new Error('quota'), { name: 'QuotaExceededError' }); };
  const h = new Uint8Array(32).fill(3);
  links.expect(1, [h]);
  link.sent.length = 0;
  link.deliver(start(h, 10 * 1024 * 1024));                 // larger than the initial credit window
  await sleep(10);
  assert.deepEqual(types(events), ['connected', 'blobStoreFailed']);
  assert.deepEqual(events.at(-1), { type: 'blobStoreFailed', hash: h });
  assert.ok(link.sent.some((f) => f[0] === 5), 'ABORT sent');
});

test('a receiver that grants no credit is abandoned after the stall timeout, freeing the slot', async () => {
  const t = server({ stallMs: 50 });
  const big = await put(t.storage, new Uint8Array(1000).fill(2)), next = await put(t.storage, new Uint8Array(10).fill(3));
  t.links.serve(1, big); t.links.serve(2, next);
  await sleep(20);
  assert.deepEqual(t.a.sent.map((f) => f[0]), [2]); assert.deepEqual(t.b.sent.map((f) => f[0]), []);
  await sleep(100);
  assert.deepEqual(t.a.sent.map((f) => f[0]), [2, 5], 'ABORT after the stall');
  assert.equal(t.b.sent[0]?.[0], 2, 'next blob served');
});

test('the slot is freed when the receiving link closes, when the receiver aborts, and when a blob is unreadable', async () => {
  const t = server();
  const x = await put(t.storage, new Uint8Array(100).fill(4)), y = await put(t.storage, new Uint8Array(100).fill(5));
  const z = await put(t.storage, new Uint8Array(100).fill(6)), gone = new Uint8Array(32).fill(9);
  t.links.serve(1, x); t.links.serve(2, gone); t.links.serve(2, y); t.links.serve(2, z);
  await sleep(20);
  t.a.drop();                                              // receiver of x goes away mid-transfer
  await sleep(20);
  assert.deepEqual(t.b.sent.map((f) => f[0]), [5, 2], 'gone: ABORT (+ blobLost); then y starts');
  t.b.deliver(Uint8Array.from([5, ...y]));                 // the receiver aborts y
  await sleep(20);
  assert.deepEqual(t.b.sent.map((f) => f[0]), [5, 2, 2], 'z starts');
  assert.ok(t.events.some((e) => e.type === 'blobLost'));
});

test('a continuation fragment of the wrong size closes the link (fragment count is bounded)', async () => {
  const { events, link } = setup(); link.deliver(hello(OTHER));
  link.deliver(Uint8Array.of(1, 1, 7, 7, 7));          // more=1 but not a full fragment
  await sleep(1);
  assert.equal(link.closed, true); assert.deepEqual(types(events), ['connected', 'disconnected']);
  const b = setup(); b.link.deliver(hello(OTHER));
  for (let i = 0; i < 1000 && !b.link.closed; i++) b.link.deliver(Uint8Array.of(1, 1));   // empty continuations
  await sleep(1);
  assert.equal(b.link.closed, true);
});

test('a storage write error stops the transfer: blobStoreFailed, ABORT, no more credit, temp file removed', async () => {
  const { events, link, links, storage } = setup(); link.deliver(hello(OTHER));
  let writes = 0, aborted = 0;
  storage.beginIncoming = async () => ({
    async write() { if (++writes >= 2) throw new Error('disk full'); },
    async finish() { throw new Error('should not finish'); },
    async abort() { aborted++; },
  });
  const h = new Uint8Array(32).fill(8);
  links.expect(1, [h]);
  link.deliver(start(h, 10 * 1024 * 1024));
  await sleep(5);
  link.sent.length = 0;
  for (let i = 0; i < 8; i++) link.deliver(data(h, new Uint8Array(16384)));
  await sleep(20);
  assert.deepEqual(types(events), ['connected', 'blobStoreFailed']);
  assert.ok(link.sent.some((f) => f[0] === 5), 'ABORT sent');
  const kinds = link.sent.map((f) => f[0]);
  assert.ok(kinds.lastIndexOf(6) < kinds.indexOf(5), 'no credit after the failure');
  assert.ok(kinds.filter((k) => k === 6).length <= 1, 'at most the one grant earned by the successful write');
  assert.equal(aborted, 1, 'the partial file is discarded');
});

test('a write still pending at END that then fails: blobStoreFailed once, and the sink is aborted', async () => {
  const { events, link, links, storage } = setup(); link.deliver(hello(OTHER));
  let aborted = 0, failLast;
  storage.beginIncoming = async () => ({
    write() { return new Promise((res, rej) => { failLast = rej; }); },   // the write stays pending
    async finish() { throw new Error('should not finish'); },
    async abort() { aborted++; },
  });
  const h = new Uint8Array(32).fill(9);
  links.expect(1, [h]);
  link.deliver(start(h, 100)); await sleep(5);
  link.deliver(data(h, new Uint8Array(100))); link.deliver(end(h));   // END while the write is pending
  await sleep(5);
  failLast(new Error('disk full'));
  await sleep(20);
  assert.deepEqual(types(events), ['connected', 'blobStoreFailed']);
  assert.equal(aborted, 1, 'writer and temp file discarded');
});
