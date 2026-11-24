// Stage-1 smoke test of the wasm engine under Node: `initFresh`, then a local `putMany`, through
// the real envelope (JS encoder -> wasm LeanSync.Envelope -> JS decoder), with the host's side of
// the persist handshake. Also measures start-up time.
// usage: node test/wasm-smoke.mjs   (after scripts/wasm/build.sh)
import { createHash } from 'node:crypto';
import { join, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createEngine } from '../app/js/engine.mjs';
import { encodeEvent, decodeEffects, hex, bytesEqual } from '../app/js/codec.mjs';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const sha256 = (b) => new Uint8Array(createHash('sha256').update(b).digest());
let failures = 0;
const check = (name, cond, detail = '') => { console.log(`${cond ? 'PASS' : 'FAIL'} ${name}${cond ? '' : ' ' + detail}`); if (!cond) failures++; };
const show = (effs) => effs.map((e) => e.type === 'notify' ? `notify ${e.notice}` : e.type === 'reply' ? `reply ${e.reply}` :
  e.type === 'persist' ? `persist ${e.tag} (${e.state.length} B)` : e.type).join(', ');

const t0 = performance.now();
const { default: createLeanSync } = await import(pathToFileURL(join(root, 'build/sync/lean_sync.mjs')));
const tImport = performance.now();
const eng = await createEngine(createLeanSync);
const tReady = performance.now();
console.log(`startup: import ${(tImport - t0).toFixed(1)} ms, instantiate ${eng.timings.instantiateMs.toFixed(1)} ms, ` +
  `lean init ${eng.timings.leanInitMs.toFixed(1)} ms, total ${(tReady - t0).toFixed(1)} ms`);

const step = (ev) => { const out = eng.process(encodeEvent(ev)); return decodeEffects(out); };
const replica = { hi: 0x0123456789abcdefn, lo: 0xfedcba9876543210n };

// Before init: notInitialized.
let effs = step({ type: 'query', q: 'status' });
check('event before init -> notInitialized', effs.length === 1 && effs[0].notice === 'notInitialized', show(effs));

// initFresh: Lean asks to persist the empty state (tag 0).
effs = step({ type: 'initFresh', replica, blobs: [] });
console.log('  initFresh ->', show(effs));
const p0 = effs.find((e) => e.type === 'persist');
check('initFresh -> persist 0', p0 && p0.tag === 0);
// Empty state: 01 01 | r=0 | n=0
check('empty state encodes as 01 01 00 00', p0 && hex(p0.state) === '01010000', p0 && hex(p0.state));
effs = step({ type: 'persisted', tag: 0, digest: sha256(p0.state) });
console.log('  persisted 0 ->', show(effs));

// putMany one file.
const content = new TextEncoder().encode('hello, wasm\n');
const h = sha256(content);
effs = step({ type: 'putMany', items: [{ path: 'notes/hello.txt', hash: h, supersedes: [] }] });
console.log('  putMany ->', show(effs));
const p1 = effs.find((e) => e.type === 'persist');
check('putMany -> persist 1', p1 && p1.tag === 1);
check('putMany -> indexChanged', effs.some((e) => e.notice === 'indexChanged'));
// Expected record: 01 01 | r=1 {hi lo counter=1} | n=1 {path idx=0 counter=1 hash}
const enc = (n) => { const o = []; let v = BigInt(n); do { let b = Number(v & 0x7fn); v >>= 7n; if (v) b |= 0x80; o.push(b); } while (v); return o; };
const pathBytes = new TextEncoder().encode('notes/hello.txt');
const want = Uint8Array.from([1, 1, 1, ...enc(replica.hi), ...enc(replica.lo), 1, 1, pathBytes.length, ...pathBytes, 0, 1, ...h]);
check('persisted record is the expected canonical state', p1 && bytesEqual(p1.state, want), p1 && hex(p1.state));
effs = step({ type: 'persisted', tag: 1, digest: sha256(p1.state) });
console.log('  persisted 1 ->', show(effs));

effs = step({ type: 'query', q: 'snapshot' });
const snap = effs.find((e) => e.reply === 'snapshot');
check('snapshot lists the file, present', snap && snap.files.length === 1 && snap.files[0].path === 'notes/hello.txt' &&
  snap.files[0].versions.length === 1 && bytesEqual(snap.files[0].versions[0].hash, h) && snap.files[0].versions[0].present === true,
  JSON.stringify(snap, (k, v) => (v instanceof Uint8Array ? hex(v) : typeof v === 'bigint' ? v.toString() : v)));
effs = step({ type: 'query', q: 'status' });
const st = effs.find((e) => e.reply === 'status');
check('status: no persist in flight, not dirty, no rollback', st && !st.persistInFlight && !st.dirty && !st.rollback);

// Second init -> alreadyInitialized; malformed event -> badEvent, machine unchanged.
effs = step({ type: 'initFresh', replica, blobs: [] });
check('second init -> alreadyInitialized', effs.some((e) => e.notice === 'alreadyInitialized'), show(effs));
effs = decodeEffects(eng.process(Uint8Array.from([1, 3, 99])));
check('bad event -> badEvent badTag 99', effs.length === 1 && effs[0].notice === 'badEvent' && effs[0].error === 'badTag' && effs[0].value === 99);

if (failures) { console.log(`${failures} FAILED`); process.exit(1); }
console.log('all passed');
