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
  link.deliver(new Uint8Array(2 + MAX_MESSAGE_BYTES + 1).fill(0).map((x, i) => (i === 0 ? 1 : i === 1 ? 1 : 0)));
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
