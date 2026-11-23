// Scale/stack probe of the wasm engine under Node: device A adds N files in one putMany; device B
// (fresh) connects and syncs the index; B then stores every blob. A minimal in-memory host routes
// messages and acknowledges persists at once (real SHA-256). Reports timings; fails if anything
// traps or the devices do not converge.
// usage: node test/wasm-scale.mjs [N=20000]
import { createHash } from 'node:crypto';
import { join, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createEngine } from '../app/js/engine.mjs';
import { encodeEvent, decodeEffects, hex } from '../app/js/codec.mjs';

const N = Number(process.argv[2] ?? 20000);
const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const { default: createLeanSync } = await import(pathToFileURL(join(root, 'build/sync/lean_sync.mjs')));
const sha256 = (b) => new Uint8Array(createHash('sha256').update(b).digest());

function device(name, eng) {
  const d = { name, eng, queue: [], blobs: new Map(), record: null, peer: null, other: null, stepMs: 0, steps: 0, wants: [] };
  d.feed = (ev) => d.queue.push(ev);
  d.run = () => {
    while (d.queue.length) {
      const ev = d.queue.shift();
      const t = performance.now();
      const effs = decodeEffects(d.eng.process(encodeEvent(ev)));
      d.stepMs += performance.now() - t; d.steps++;
      for (const e of effs) {
        if (e.type === 'persist') { d.record = e.state.slice(); d.queue.push({ type: 'persisted', tag: e.tag, digest: sha256(e.state) }); }
        else if (e.type === 'send') d.other.feed({ type: 'received', peer: d.other.peer, bytes: e.bytes.slice() });
        else if (e.type === 'fetch') { d.other.feed({ type: 'received', peer: d.other.peer, bytes: e.bytes.slice() }); }
        else if (e.type === 'serveBlob') d.other.wants.push(e.hash.slice());
        else if (e.type === 'close') throw new Error(`${name}: close ${e.reason}`);
        else if (e.type === 'notify' && ['badEvent', 'opRejected', 'peerError', 'rollbackDetected', 'saveFailed'].includes(e.notice)) throw new Error(`${name}: ${e.notice} ${JSON.stringify(e, (k, v) => typeof v === 'bigint' ? String(v) : v)}`);
      }
    }
  };
  return d;
}

const A = device('A', await createEngine(createLeanSync));
const B = device('B', await createEngine(createLeanSync));
A.other = B; B.other = A; A.peer = 1; B.peer = 2;
A.feed({ type: 'initFresh', replica: { hi: 1n, lo: 1n }, blobs: [] }); A.run();
B.feed({ type: 'initFresh', replica: { hi: 2n, lo: 2n }, blobs: [] }); B.run();

const items = [];
for (let i = 0; i < N; i++) {
  const content = new TextEncoder().encode(`file ${i}`);
  const h = sha256(content);
  A.blobs.set(hex(h), content);
  items.push({ path: `dir${i % 100}/file${i}.txt`, hash: h, supersedes: [] });
}
let t = performance.now();
A.feed({ type: 'putMany', items }); A.run();
console.log(`putMany of ${N} items + persist: ${(performance.now() - t).toFixed(0)} ms, record ${A.record.length} B`);

t = performance.now();
A.feed({ type: 'connected', peer: A.peer }); B.feed({ type: 'connected', peer: B.peer });
const pump = () => { let moved = true; while (moved) { moved = A.queue.length + B.queue.length > 0; A.run(); B.run();
  // B's host stores what A serves (verify the hash first, as the real host must)
  while (B.wants.length) { const h = B.wants.shift(); const c = A.blobs.get(hex(h)); if (hex(sha256(c)) !== hex(h)) throw new Error('hash'); B.blobs.set(hex(h), c); B.feed({ type: 'blobStored', hash: h, peer: B.peer }); moved = true; }
} };
pump();
console.log(`full sync (index + ${N} blobs): ${(performance.now() - t).toFixed(0)} ms wall; inside wasm A ${A.stepMs.toFixed(0)} ms / ${A.steps} events, B ${B.stepMs.toFixed(0)} ms / ${B.steps} events`);
const snap = (d) => decodeEffects(d.eng.process(encodeEvent({ type: 'query', q: 'snapshot' }))).find((e) => e.reply === 'snapshot');
const sa = snap(A), sb = snap(B);
const ok = sa.files.length === N && sb.files.length === N && sb.files.every((f) => f.versions.every((v) => v.present)) && B.blobs.size === N;
console.log(`A files ${sa.files.length}, B files ${sb.files.length}, B blobs ${B.blobs.size}, heap A ${A.eng.heapBytes()} B ${B.eng.heapBytes()}`);
console.log(ok ? 'all passed' : 'FAILED');
process.exit(ok ? 0 : 1);
