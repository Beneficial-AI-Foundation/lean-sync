// The host core (app/js/core.mjs) with the real wasm engine, fake storage and fake links.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createCore } from '../../app/js/core.mjs';
import { sha256, hex } from '../../app/js/hash.mjs';
import { memoryStorage, realEngine, trappable, sleep } from './fakes.mjs';

function fakeLinks() {
  const l = { calls: [], accepting: false, resets: 0,
    setAccepting(v) { l.accepting = v; l.calls.push(['accept', v]); }, resetAll() { l.resets++; },
    sendMessage(p, b) { l.calls.push(['send', p, b.length]); }, closePeer(p) { l.calls.push(['close', p]); },
    expect() {}, serve() {}, labelOf: () => 'R' };
  return l;
}
function setup(o = {}) {
  const storage = o.storage ?? memoryStorage(), links = fakeLinks(), trap = { next: 0, fired: 0, calls: 0 }, seen = [];
  links.acceptedAfter = [];
  const setAcc = links.setAccepting; links.setAccepting = (v) => { if (v) links.acceptedAfter.push(seen.length); setAcc(v); };
  const notices = []; const phases = [];
  const ctx = {};
  const core = createCore({
    storage, links, makeEngine: async () => { if (ctx.holdEngine) { const g = ctx.holdEngine; ctx.holdEngine = null; await g; } const e = trappable(await realEngine(), trap); return { ...e, process: (b) => { seen.push(b[2]); return e.process(b); } }; },
    ui: { onNotice: (n) => notices.push(n), onPhase: (p) => phases.push(p) }, ...o.core,
  });
  return Object.assign(ctx, { core, storage, links, trap, seen, notices, phases });
}

test('first start: initFresh, and the record is acknowledged only once the save completed', async () => {
  const t = setup(); t.storage.holdSaves = true;
  await t.core.start();
  assert.equal(t.core.st.phase, 'running');
  assert.equal(t.seen[0], 1, 'initFresh is the first event');
  await sleep(20);
  assert.ok(!t.seen.includes(6), 'no `persisted` while the save is pending');
  t.storage.held.shift()();
  await sleep(20);
  assert.ok(t.seen.includes(6), '`persisted` after the save completed');
  assert.ok(t.storage.record);
});

test('a failed save becomes persistFailed and saveFailed; no event storm from the host', async () => {
  const t = setup();
  await t.core.start(); await sleep(20);
  t.storage.failSaves = 100;
  const f = new Blob([new Uint8Array([1, 2, 3])]);
  await t.core.addFiles([{ name: 'a', blob: f }]);
  await sleep(300);
  assert.ok(t.seen.includes(7), 'persistFailed delivered');
  assert.ok(t.notices.some((n) => n.notice === 'saveFailed'));
  assert.equal(t.core.st.saveFailed, true);
  const n = t.seen.length;
  await sleep(500);
  assert.equal(t.seen.length, n, 'no events generated while waiting for the back-off');
  t.storage.failSaves = 0;
  await sleep(800);                                    // the 1 s nudge retries
  assert.equal(t.core.st.saveFailed, false);
});

test('the inventory is reported in chunks before peers are accepted', async () => {
  const storage = memoryStorage();
  for (let i = 0; i < 25000; i++) storage.blobs.set(i.toString(16).padStart(64, '0'), new Uint8Array(0));
  const t = setup({ storage });
  await t.core.start();
  assert.deepEqual(t.seen.slice(0, 3), [1, 12, 12], 'initFresh + 2 blobsStored chunks');
  assert.deepEqual(t.links.acceptedAfter, [3], 'peers accepted once, after the 3 start-up events');
});

test('a corrupt record: startupFailed, nothing written, reset needs an explicit call', async () => {
  const storage = memoryStorage();
  storage.record = { replica: { hi: 1n, lo: 1n }, state: Uint8Array.from([1, 1, 9, 9]) };
  const t = setup({ storage });
  await t.core.start(); await sleep(20);
  assert.equal(t.core.st.phase, 'startupFailed');
  assert.deepEqual(storage.saves, [], 'nothing saved');
  assert.ok(!t.links.calls.some((c) => c[0] === 'accept' && c[1]), 'no peers');
  await t.core.resetIndex(); await sleep(20);
  assert.equal(t.core.st.phase, 'running');
  assert.notEqual(storage.record.replica.hi, 1n);
});

test('a trap while running: discard, new instance from the stored record, stale completions dropped', async () => {
  const t = setup();
  await t.core.start(); await sleep(20);
  await t.core.addFiles([{ name: 'x', blob: new Blob([new Uint8Array([5])]) }]); await sleep(20);
  const replica = t.core.replica(), epoch = t.core.st.epoch;
  t.trap.next = 1;
  t.core.emit({ type: 'query', q: 'status' });
  await sleep(50);
  assert.equal(t.core.st.instances, 2); assert.equal(t.core.st.phase, 'running'); assert.equal(t.core.st.epoch, epoch + 1);
  assert.deepEqual(t.core.replica(), replica, 'same identity: the record is trusted');
  assert.equal(t.links.resets, 1, 'all links closed');
  const before = t.seen.length;
  t.core.emit({ type: 'persisted', tag: 0, digest: new Uint8Array(32) }, epoch);   // stale
  await sleep(10);
  assert.equal(t.seen.length, before, 'stale persisted never reaches the new machine');
  await sleep(150);
  assert.ok(t.core.st.lastSnapshot.some((f) => f.path === 'x'), 'state restored');
});

test('a trap during start-up stops, without a retry loop', async () => {
  const t = setup(); t.trap.always = true;
  await t.core.start(); await sleep(50);
  assert.equal(t.core.st.phase, 'failed'); assert.equal(t.core.st.instances, 1); assert.equal(t.trap.fired, 1);
});

test('repeated traps stop sync after the limit', async () => {
  const t = setup({ core: { maxTraps: 2 } });
  await t.core.start(); await sleep(20);
  t.trap.next = 1; t.core.emit({ type: 'query', q: 'status' }); await sleep(50);
  assert.equal(t.core.st.phase, 'running');
  t.trap.next = 1; t.core.emit({ type: 'query', q: 'status' }); await sleep(50);
  assert.equal(t.core.st.phase, 'failed'); assert.equal(t.core.st.instances, 2);
});

test('rollback restart: a new identity from the stored record, rotate flag cleared with the first save', async () => {
  const t = setup();
  await t.core.start(); await sleep(20);
  const old = t.core.replica();
  await t.core.newIdentity(); await sleep(30);
  assert.notDeepEqual(t.core.replica(), old);
  assert.equal(t.storage.rotate, false);
  assert.deepEqual(t.storage.record.replica, t.core.replica());
});

test('back-to-back persists: a restart waits for the write still in flight, and leaves `running` first', async () => {
  const t = setup(); t.storage.holdSaves = true;
  await t.core.start(); await sleep(20);
  t.storage.held.shift()();                                  // persist 0 (initFresh) completes
  await sleep(20);
  await t.core.addFiles([{ name: 'x', blob: new Blob([new Uint8Array([1])]) }]); await sleep(20);
  await t.core.addFiles([{ name: 'y', blob: new Blob([new Uint8Array([2])]) }]); await sleep(20);
  assert.equal(t.storage.held.length, 1, 'one write in flight (x); y waits');
  t.storage.held.shift()();                                  // x's write completes -> persisted -> y's persist starts
  await sleep(30);
  assert.equal(t.storage.held.length, 1, 'the next write (with y) is in flight');
  assert.ok(t.core.st.persist, 'the slot holds the new write, not cleared by the previous one');
  t.trap.next = 1; t.core.emit({ type: 'query', q: 'status' });
  await sleep(100);
  assert.equal(t.core.st.instances, 1, 'the restart waits for the outstanding write');
  assert.notEqual(t.core.st.phase, 'running', 'not running while restarting');
  assert.equal(t.core.canEdit(), false);
  await assert.rejects(t.core.addFiles([{ name: 'z', blob: new Blob([new Uint8Array([3])]) }]));
  t.storage.holdSaves = false;
  t.storage.held.shift()();
  await sleep(200);
  assert.equal(t.core.st.instances, 2); assert.equal(t.core.st.phase, 'running');
  assert.deepEqual(t.core.st.lastSnapshot.map((f) => f.path), ['x', 'y'], 'restarted from the latest record');
});

test('supersession uses the versions captured when the user acted, not those present after the upload', async () => {
  const t = setup();
  await t.core.start(); await sleep(150);
  await t.core.addFiles([{ name: 'p', blob: new Blob([new Uint8Array([7])]) }]); await sleep(150);   // p = {7}
  // The store of content 8 is slow; while it runs, another edit replaces p with 9.
  let release; const slow = new Promise((r) => { release = r; });
  const orig = t.storage.storeLocal;
  t.storage.storeLocal = async (b) => { const u = new Uint8Array(await b.arrayBuffer()); if (u[0] === 8) await slow; return orig(new Blob([u])); };
  const pending = t.core.addFiles([{ name: 'p', blob: new Blob([new Uint8Array([8])]) }]);   // user saw {7}
  await t.core.addFiles([{ name: 'p', blob: new Blob([new Uint8Array([9])]) }]); await sleep(150);   // p = {9}
  release(); await pending; await sleep(150);
  // 8 supersedes only 7 (what was shown when the user acted): 9 survives, as a conflict.
  assert.equal(t.core.st.lastSnapshot.find((f) => f.path === 'p').versions.length, 2);
});

test('an add that spans an engine restart is not applied to the new machine; its blobs are still reported', async () => {
  const t = setup();
  await t.core.start(); await sleep(150);
  let release; const slow = new Promise((r) => { release = r; });
  const orig = t.storage.storeLocal; t.storage.storeLocal = async (b) => { await slow; return orig(b); };
  const pending = t.core.addFiles([{ name: 'q', blob: new Blob([new Uint8Array([4])]) }]);
  t.trap.next = 1; t.core.emit({ type: 'query', q: 'status' });
  await sleep(150);
  assert.equal(t.core.st.instances, 2);
  const n = t.seen.length;
  release(); const r = await pending; await sleep(150);
  assert.equal(r.added, 0); assert.match(r.errors[0].error, /restarted/);
  assert.ok(!t.seen.slice(n).includes(5), 'no localOp reached the new machine');
  assert.ok(t.seen.slice(n).includes(12), 'the stored blob was reported (blobsStored)');
  assert.ok(!t.core.st.lastSnapshot.some((f) => f.path === 'q'));
});

test('an add finishing while the restarted engine loads: edit dropped, blob reported once running', async () => {
  const t = setup();
  await t.core.start(); await sleep(150);
  let release; const slow = new Promise((r) => { release = r; });
  const orig = t.storage.storeLocal; t.storage.storeLocal = async (b) => { await slow; return orig(b); };
  let open; const gate = new Promise((r) => { open = r; });
  const pending = t.core.addFiles([{ name: 'r', blob: new Blob([new Uint8Array([6])]) }]);
  t.holdEngine = gate;                                          // hold the next engine creation
  t.trap.next = 1; t.core.emit({ type: 'query', q: 'status' });
  await sleep(50);                                              // restart: inventory listed, engine loading
  assert.equal(t.core.st.phase, 'starting');
  release(); const r = await pending;                           // the add completes now
  assert.equal(r.added, 0);
  const n = t.seen.length;
  open(); await sleep(200);
  assert.equal(t.core.st.phase, 'running');
  const after = t.seen.slice(n);
  assert.equal(after[0], 0, 'init first');
  assert.ok(after.includes(12), 'the stored blob reaches the new machine as blobsStored');
  assert.ok(!after.includes(5), 'no edit');
});
