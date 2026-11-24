// Replay a native simulator trace through the wasm engine and compare every output byte for byte.
//   .lake/build/bin/sync-tests trace <seed> <count> build/vectors/sim.bin
//   node test/wasm-replay.mjs build/vectors/sim.bin
// The trace (Tests/Sync.lean, `traceRec`) holds, per device, every event it processed (as encoded
// by Lean) and the native output of `process` on it; a crash resets that device's machine, which
// here means a fresh wasm instance. Every wasm output must equal the native one, and must decode
// with the JS effects decoder (app/js/codec.mjs).
//
// Then a steady-state loop checks for leaks: after a warm-up, 3000 calls carrying a 256 KiB message
// each (768 MiB in total) must not grow the wasm memory by more than BOUND bytes.
import { readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createEngine } from '../app/js/engine.mjs';
import { decodeEffects, encodeEvent, bytesEqual, hex } from '../app/js/codec.mjs';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
// usage: wasm-replay.mjs [--module <lean_sync.mjs>] [--leak-only] [<trace>]
const args = process.argv.slice(2);
const opt = (name) => { const i = args.indexOf(name); if (i < 0) return null; const v = args[i + 1]; args.splice(i, 2); return v; };
const flag = (name) => { const i = args.indexOf(name); if (i < 0) return false; args.splice(i, 1); return true; };
const modulePath = opt('--module') ?? join(root, 'build/sync/lean_sync.mjs');
const leakOnly = flag('--leak-only');
const file = args[0] ?? join(root, 'build/vectors/sim.bin');
const { default: createLeanSync } = await import(pathToFileURL(modulePath));

let mismatches = 0, decodeFailures = 0, events = 0;
if (!leakOnly) {
const buf = readFileSync(file);
const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
let pos = 0;
const u32 = () => { const v = dv.getUint32(pos, true); pos += 4; return v; };

const engines = new Map();
let instances = 0, worlds = 0, outBytes = 0;
let wasmMs = 0;
while (pos < buf.length) {
  const kind = buf[pos++]; const dev = u32();
  const ev = new Uint8Array(buf.buffer, buf.byteOffset + pos + 4, dv.getUint32(pos, true)); pos += 4 + ev.length;
  const want = new Uint8Array(buf.buffer, buf.byteOffset + pos + 4, dv.getUint32(pos, true)); pos += 4 + want.length;
  if (kind === 2) { engines.clear(); worlds++; continue; }
  if (kind === 1) { engines.delete(dev); continue; }
  let eng = engines.get(dev);
  if (!eng) { eng = await createEngine(createLeanSync); engines.set(dev, eng); instances++; }
  const t = performance.now();
  const got = eng.process(ev);
  wasmMs += performance.now() - t;
  events++; outBytes += got.length;
  if (!bytesEqual(got, want)) {
    mismatches++;
    if (mismatches <= 3) console.log(`MISMATCH world ${worlds} device ${dev} event ${hex(ev.subarray(0, 40))}...\n  wasm   ${hex(got.subarray(0, 80))}\n  native ${hex(want.subarray(0, 80))}`);
  }
  try { decodeEffects(got); } catch (e) { decodeFailures++; if (decodeFailures <= 3) console.log(`JS decode failure: ${e.message}`); }
}
console.log(`replay: ${worlds} worlds, ${events} events, ${instances} wasm instances, ${outBytes} output bytes, ` +
  `${wasmMs.toFixed(0)} ms inside wasm; byte mismatches ${mismatches}, JS decode failures ${decodeFailures}`);
}

// Leak check (carried-forward requirement 3).
const BOUND = 1 << 20;
const eng = await createEngine(createLeanSync);
const run = (ev) => decodeEffects(eng.process(encodeEvent(ev)));
const replica = { hi: 7n, lo: 9n };
for (const e of run({ type: 'initFresh', replica, blobs: [] })) if (e.type === 'persist') run({ type: 'persisted', tag: e.tag, digest: new Uint8Array(32).fill(1) });
run({ type: 'connected', peer: 1 });
const big = new Uint8Array(256 * 1024).map((_, i) => (i * 31) & 0xff);   // garbage: closes the session each time
let peer = 1;
const cycle = () => {
  run({ type: 'received', peer, bytes: big });       // protocol error -> bye + close
  run({ type: 'disconnected', peer });
  peer++; run({ type: 'connected', peer });
  run({ type: 'query', q: 'snapshot' });
};
for (let i = 0; i < 200; i++) cycle();
const before = eng.heapBytes();
for (let i = 0; i < 3000; i++) cycle();
const after = eng.heapBytes();
const growth = after - before;
console.log(`heap: ${before} -> ${after} bytes after 3000 steady-state cycles (bound ${BOUND})`);

const ok = mismatches === 0 && decodeFailures === 0 && (leakOnly || events > 0) && growth <= BOUND;
console.log(ok ? 'all passed' : 'FAILED');
process.exit(ok ? 0 : 1);
