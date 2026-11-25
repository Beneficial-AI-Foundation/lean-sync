// The WebRTC transport (app/js/transport/webrtc.mjs) against an in-memory fake RTCPeerConnection
// (fakertc.mjs): pairing, reply renewal, link lifecycle, loss, back-off, offline (docs/net-design.md §5).
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createWebRTCTransport } from '../../app/js/transport/webrtc.mjs';
import { parseCode } from '../../app/js/netcode.mjs';
import { fakeRTC } from './fakertc.mjs';

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const FAST = { RENEW_MS: 40, MAX_ATTEMPTS: 3, RESPOND_MS: 3000, CONNECT_MS: 500, INVITE_MS: 2000, LOSS_MS: 60,
  GATHER_CAP_MS: 50, SRFLX_QUIET_MS: 5, REOPEN_MIN: 20, REOPEN_MAX: 160, REOPEN_RESET_AFTER: 400 };
async function until(fn, ms = 2000, what = 'condition') {
  const t0 = Date.now();
  while (Date.now() - t0 < ms) { if (await fn()) return; await sleep(5); }
  throw new Error(`timed out: ${what}`);
}
function device(world, name, timing = {}) {
  const d = { name, links: [], closes: new Map(), frames: [], logs: [] };
  d.t = createWebRTCTransport({ RTC: world.RTC, getIceServers: () => d.ice ?? [], log: (m) => d.logs.push(m), timing: { ...FAST, ...timing } });
  d.t.start({
    onLink(l) {
      d.links.push(l); d.closes.set(l.id, 0);
      l.onFrame((f) => d.frames.push({ link: l.id, data: Array.from(f) }));
      l.onClose(() => d.closes.set(l.id, d.closes.get(l.id) + 1));
    },
    onStatus() {},
  });
  d.live = () => d.links.filter((l) => !l.closedFlag && d.closes.get(l.id) === 0);
  return d;
}
async function pair(world, A, B) {
  const inv = await A.t.invite();
  const resp = B.t.respond(inv.code);
  await until(() => resp.code, 1000, 'reply code');
  const [a, b] = await Promise.all([inv.accept(resp.code), resp.done]);
  await until(() => A.live().length === 1 && B.live().length === 1, 2000, 'link up on both sides');
  return { inv, resp, a, b };
}

test('pairing by codes: one link per side, frames flow both ways in order, answerer passive', async () => {
  const w = fakeRTC(), A = device(w, 'A'), B = device(w, 'B');
  const { inv, resp } = await pair(w, A, B);
  assert.equal(inv.state, 'connected'); assert.equal(resp.state, 'connected');
  assert.equal(w.activeAnswers ?? 0, 0, 'every reply takes the passive DTLS role');
  assert.equal(parseCode(resp.code, 'answer').cands.length, 1);
  for (let i = 0; i < 20; i++) A.live()[0].send(Uint8Array.of(i));
  B.live()[0].send(Uint8Array.of(99));
  await until(() => B.frames.length === 20 && A.frames.length === 1);
  assert.deepEqual(B.frames.map((f) => f.data[0]), [...Array(20).keys()]);
  assert.equal(A.t.connections().length, 1); assert.equal(B.t.connections()[0].role, 'answerer');
  assert.deepEqual(A.t.connections()[0].state, 'connected');
});

test('an invitation accepts one reply; a reply for another invitation, an invitation as reply, a used or expired invitation are refused', async () => {
  const w = fakeRTC(), A = device(w, 'A', { INVITE_MS: 150 }), B = device(w, 'B'), C = device(w, 'C');
  const inv = await A.t.invite(), other = await A.t.invite();
  const rB = B.t.respond(inv.code), rC = C.t.respond(inv.code), rOther = C.t.respond(other.code);
  await until(() => rB.code && rC.code && rOther.code);
  await assert.rejects(inv.accept(inv.code), { reason: 'kind' });
  await assert.rejects(inv.accept(rOther.code), { reason: 'stale' });
  await inv.accept(rB.code);
  await assert.rejects(inv.accept(rC.code), { reason: 'used' });
  await assert.rejects(inv.accept(rB.code), { reason: 'used' });
  await sleep(200);
  await assert.rejects(other.accept(rOther.code), { reason: 'expired' });
  assert.throws(() => B.t.respond(rB.code), { reason: 'kind' });
  rC.cancel(); rOther.cancel();
});

test('the reply is renewed while shown; at most MAX_ATTEMPTS stay alive; an older live reply still works and the others are closed', async () => {
  const w = fakeRTC(), A = device(w, 'A'), B = device(w, 'B');
  const inv = await A.t.invite();
  const resp = B.t.respond(inv.code), codes = [];
  resp.onCode((c) => codes.push(c));
  await until(() => codes.length >= 6, 2000, 'six replies');
  assert.equal(new Set(codes).size, codes.length, 'each reply is a new one');
  const answerers = () => w.pcs.filter((p) => p.remoteDescription?.type === 'offer' && !p.closedHere);
  assert.ok(answerers().length <= 3, `${answerers().length} live attempts (max 3)`);
  const older = codes.at(-2);                                    // scanned just before a renewal
  await inv.accept(older);
  await resp.done;
  await until(() => answerers().length === 1, 1000, 'other attempts closed');
  await until(() => A.live().length === 1 && B.live().length === 1);
  const n = codes.length; await sleep(150);
  assert.equal(codes.length, n, 'no renewal after connecting');
});

test('a reply that nobody accepts: renewal stops after RESPOND_MS with a message', async () => {
  const w = fakeRTC(), A = device(w, 'A'), B = device(w, 'B', { RESPOND_MS: 150 });
  const inv = await A.t.invite();
  const resp = B.t.respond(inv.code);
  await assert.rejects(resp.done, /did not answer/);
  assert.equal(resp.state, 'failed');
  assert.equal(w.pcs.filter((p) => p.remoteDescription?.type === 'offer' && !p.closedHere).length, 0, 'every attempt closed');
});

test('onClose exactly once per link, for every way a link ends', async () => {
  const cases = {
    'remote closes the channel': async (A, B) => B.live()[0]._dc.close(),
    'link.close() here': async (A) => A.live()[0].close(),
    'connection failed (channel still open)': async (A) => A.live()[0]._conn.pc._state('failed'),
    'disconnected longer than LOSS_MS': async (A) => A.live()[0]._conn.pc._state('disconnected'),
    'close and failed together': async (A) => { const l = A.live()[0]; l.close(); l._conn.pc._state('failed'); l._dc._fire('close', {}); },
    'send throws': async (A) => { const l = A.live()[0]; l._dc.failSend = new DOMException('queue full', 'OperationError'); assert.equal(l.send(Uint8Array.of(1)), false); },
  };
  for (const [name, act] of Object.entries(cases)) {
    const w = fakeRTC(), A = device(w, 'A'), B = device(w, 'B');
    await pair(w, A, B);
    const first = A.links[0];
    await act(A, B);
    await until(() => A.closes.get(first.id) >= 1, 1000, `${name}: onClose`);
    await sleep(120);
    assert.equal(A.closes.get(first.id), 1, `${name}: onClose once`);
    const before = A.frames.filter((f) => f.link === first.id).length;
    first._dc._fire('message', { data: Uint8Array.of(7).buffer });   // a late frame on the old channel
    await sleep(5);
    assert.equal(A.frames.filter((f) => f.link === first.id).length, before, `${name}: nothing delivered on a closed link`);
  }
});

test('a channel stuck in closing: the next send takes the link down; the new channel replaces the answerer\'s stale link', async () => {
  const w = fakeRTC(), A = device(w, 'A'), B = device(w, 'B');
  await pair(w, A, B);
  const a1 = A.links[0], b1 = B.links[0];
  a1._dc.readyState = 'closing';                                 // closed with data buffered; no close event ever comes
  assert.equal(a1.send(Uint8Array.of(1)), false);
  assert.equal(A.closes.get(a1.id), 1, 'link down at the first send that cannot go out');
  assert.equal(b1._dc.readyState, 'open', 'B never learns from the old channel');
  a1._dc.peer = null;                                           // the old channel's close does not reach B
  await until(() => A.live().length === 1 && B.live().length === 1, 2000, 'a new link');
  assert.equal(B.closes.get(b1.id), 1, 'B\'s stale link was replaced (closed once)');
  assert.equal(A.t.connections().length, 1);
});

test('connection failed while Chromium keeps the channel open: the link goes down and the connection is dropped', async () => {
  const w = fakeRTC(), A = device(w, 'A'), B = device(w, 'B');
  await pair(w, A, B);
  const bLink = B.links[0];
  A.live()[0]._conn.pc.vanish();                                 // A's browser killed
  await sleep(FAST.LOSS_MS / 2);
  assert.equal(bLink._dc.readyState, 'open', 'the channel still says open, as in Chromium');
  assert.equal(B.closes.get(bLink.id), 0, 'not yet: disconnected for less than LOSS_MS');
  await sleep(FAST.LOSS_MS);
  assert.equal(B.closes.get(bLink.id), 1, 'link down after LOSS_MS of disconnected');
  assert.equal(bLink._dc.readyState, 'closed', 'and the transport closed the dead channel itself');
  assert.equal(B.t.connections()[0].state, 'interrupted');
  w.later();                                                     // ... then failed
  await until(() => B.t.connections().length === 0, 500, 'connection dropped on failed');
  assert.equal(B.closes.get(bLink.id), 1);
});

test('a short disconnection keeps the link; a recovered connection gets a new link', async () => {
  const w = fakeRTC(), A = device(w, 'A'), B = device(w, 'B');
  await pair(w, A, B);
  const pc = A.live()[0]._conn.pc;
  pc._state('disconnected'); await sleep(FAST.LOSS_MS / 3); pc._state('connected');
  await sleep(FAST.LOSS_MS * 2);
  assert.equal(A.live().length, 1, 'short interruption: same link');
  pc._state('disconnected'); await sleep(FAST.LOSS_MS * 2);
  assert.equal(A.live().length, 0);
  pc._state('connected');
  await until(() => A.live().length === 1 && B.live().length === 1, 1000, 'new link after recovery');
  assert.notEqual(A.live()[0].id, A.links[0].id);
});

test('a closed link is replaced on the live connection with a growing back-off, reset after a long-lived link', async () => {
  const w = fakeRTC(), A = device(w, 'A'), B = device(w, 'B');
  await pair(w, A, B);
  const gaps = [];
  for (let i = 0; i < 4; i++) {
    const t0 = Date.now(); B.live()[0].close();                  // e.g. the answerer's engine restart
    await until(() => A.live().length === 1 && B.live().length === 1, 2000, `link ${i + 2}`);
    gaps.push(Date.now() - t0);
  }
  assert.ok(gaps[3] > gaps[0] * 2 && gaps[3] >= 140, `back-off grows: ${gaps}`);
  assert.ok(gaps[3] <= FAST.REOPEN_MAX + 100, `bounded: ${gaps}`);
  assert.equal(A.t.connections().length, 1, 'no re-pairing');
  await sleep(FAST.REOPEN_RESET_AFTER + 50);
  const t0 = Date.now(); A.live()[0].close();
  await until(() => A.live().length === 1 && B.live().length === 1, 2000);
  assert.ok(Date.now() - t0 < 120, 'back-off reset after a link lived a while');
});

test('offline closes links but keeps connections; neither side re-links until it is back online', async () => {
  const w = fakeRTC(), A = device(w, 'A'), B = device(w, 'B');
  await pair(w, A, B);
  const conn = A.t.connections()[0].id;
  B.t.setOnline(false);                                          // the answerer goes offline
  await until(() => A.live().length === 0 && B.live().length === 0);
  await sleep(300);
  assert.equal(A.live().length + B.live().length, 0, 'not re-linked while B is offline');
  assert.equal(A.t.connections().length, 1); assert.equal(B.t.connections().length, 1);
  B.t.setOnline(true);
  await until(() => A.live().length === 1 && B.live().length === 1, 1000, 're-linked');
  A.t.setOnline(false);                                          // the offerer goes offline
  await until(() => A.live().length === 0 && B.live().length === 0);
  await sleep(300);
  assert.equal(A.live().length + B.live().length, 0);
  A.t.setOnline(true);
  await until(() => A.live().length === 1 && B.live().length === 1, 1000);
  assert.equal(A.t.connections()[0].id, conn, 'same connection: no re-pairing');
});

test('the other device closing its connection drops ours; disconnect() and stop() close everything', async () => {
  const w = fakeRTC(), A = device(w, 'A'), B = device(w, 'B'), C = device(w, 'C');
  await pair(w, A, B);
  B.t.disconnect(B.t.connections()[0].id);
  await until(() => A.t.connections().length === 0 && A.closes.get(A.links[0].id) === 1, 1000, 'A sees B leave');
  await pair(w, A, C);
  A.t.stop();
  await until(() => C.t.connections().length === 0, 1000);
  await assert.rejects(A.t.invite(), /stopped/);
});

test('onDrain fires on bufferedamountlow, and at once if the buffer is already low', async () => {
  const w = fakeRTC(), A = device(w, 'A'), B = device(w, 'B');
  await pair(w, A, B);
  const l = A.live()[0]; let n = 0;
  l._dc.hold = true; l.send(new Uint8Array(1 << 20));
  assert.equal(l.bufferedAmount, 1 << 20);
  l.onDrain(() => n++);
  await sleep(10); assert.equal(n, 0, 'not while full');
  l._dc.drain(); await sleep(1); assert.equal(n, 1);
  l.onDrain(() => n++); await sleep(1); assert.equal(n, 2, 'already low: fired without an event');
});

test('candidates: an srflx candidate is used when STUN is configured; none, and a warning, otherwise', async () => {
  const w = fakeRTC(), A = device(w, 'A'), B = device(w, 'B');
  A.ice = [{ urls: 'stun:stun.example:3478' }];
  const inv = await A.t.invite();
  assert.deepEqual(parseCode(inv.code, 'offer').cands.map((c) => c.type), ['host', 'srflx']);
  assert.equal(inv.noSrflx, false);
  const plain = await B.t.invite();
  assert.deepEqual(parseCode(plain.code, 'offer').cands.map((c) => c.type), ['host']);
  inv.cancel(); plain.cancel();
});
