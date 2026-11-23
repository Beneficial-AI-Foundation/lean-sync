// Automated check: run the wasm build under Node on several inputs and compare byte-for-byte
// with the native build of the same Lean code (.lake/build/bin/wasm-demo-native).
// usage: node wasm/check-node.mjs wasm32|wasm64 [--bench]
import { execFileSync } from 'node:child_process';
import { mkdtempSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { loadLean } from './host.mjs';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const arch = process.argv[2] ?? 'wasm32';
const native = join(root, '.lake/build/bin/wasm-demo-native');
// What the platform line must say for the requested arch (guards against a mislabelled artifact).
const EXPECTED_PLATFORM = {
  wasm32: 'numBits=32 usizeMax=4294967295 ',
  wasm64: 'numBits=64 usizeMax=18446744073709551615 ',
};
if (!EXPECTED_PLATFORM[arch]) { console.log(`unknown arch ${arch}`); process.exit(2); }

const t0 = performance.now();
const { default: createLeanDemo } = await import(pathToFileURL(join(root, 'build', arch, 'lean_demo.mjs')));
const tImport = performance.now();
const lean = await loadLean(createLeanDemo);
const tReady = performance.now();

const enc = new TextEncoder();
function dropPlatformLine(bytes) {
  const s = new TextDecoder('latin1').decode(bytes);
  const i = s.indexOf('\nnumBits=');
  if (i < 0) return bytes;
  const j = s.indexOf('\n', i + 1);
  return Uint8Array.from([...bytes.subarray(0, i), ...bytes.subarray(j)]);
}
const big = new Uint8Array(1 << 20).map((_, i) => (i * 7919) % 251);
const inputs = [
  ['empty', new Uint8Array()],
  ['ascii', enc.encode('hello, wasm')],
  ['utf8', enc.encode('héllo wörld — ∀ε>0 🙂')],
  ['binary', Uint8Array.from([0, 255, 1, 254, 128, 127])],
  ['1MiB', big],
];

const tmp = mkdtempSync(join(tmpdir(), 'lean-wasm-'));
let failures = 0;
for (const [name, input] of inputs) {
  const t = performance.now();
  const got = lean.process(input);
  const ms = performance.now() - t;
  const f = join(tmp, name);
  writeFileSync(f, input);
  const want = new Uint8Array(execFileSync(native, [f], { maxBuffer: 1 << 26 }));
  // The `numBits=… usizeMax=…` line legitimately differs on wasm32: first check it matches the
  // requested arch, then compare everything else with native.
  const platform = new TextDecoder('latin1').decode(got).split('\n').find((l) => l.startsWith('numBits=')) ?? '';
  const platformOk = platform.startsWith(EXPECTED_PLATFORM[arch]);
  if (!platformOk) console.log(`  platform line ${JSON.stringify(platform)} does not match ${arch}`);
  const a = dropPlatformLine(got), b = dropPlatformLine(want);
  const ok = platformOk && a.length === b.length && a.every((x, i) => x === b[i]);
  if (!ok) failures++;
  console.log(`${ok ? 'PASS' : 'FAIL'} ${name.padEnd(7)} in=${input.length} out=${got.length} ${ms.toFixed(1)}ms`);
  if (!ok) {
    console.log('  wasm  :', JSON.stringify(new TextDecoder().decode(got).slice(0, 600)));
    console.log('  native:', JSON.stringify(new TextDecoder().decode(want).slice(0, 600)));
  }
}

// Repeated calls: catches leaks / use-after-free that a single call would not show.
const heapBefore = lean.module.HEAPU8.length;
for (let i = 0; i < 2000; i++) lean.process(inputs[2][1]);
const heapAfter = lean.module.HEAPU8.length;

console.log(`platform line: ${new TextDecoder().decode(lean.process(new Uint8Array())).split('\n').find((l) => l.startsWith('numBits'))}`);
console.log(`startup: import ${(tImport - t0).toFixed(1)}ms, instantiate ${lean.timings.instantiateMs.toFixed(1)}ms, ` +
  `lean init ${lean.timings.leanInitMs.toFixed(1)}ms, total ${(tReady - t0).toFixed(1)}ms`);
console.log(`heap: ${heapBefore} -> ${heapAfter} bytes after 2000 extra calls`);
if (failures) { console.log(`${failures} FAILED`); process.exit(1); }
console.log('all passed');
