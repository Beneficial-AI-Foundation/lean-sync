// Minimal JS host for the Lean wasm module: bytes in, bytes out.
// On wasm64 pointers arrive as BigInts; toNum() converts them for HEAPU8 indexing.

const toNum = (p) => (typeof p === 'bigint' ? Number(p) : p);

/** Instantiate an Emscripten factory (createLeanDemo) and return a `process(Uint8Array)` API. */
export async function loadLean(factory, options = {}) {
  const t0 = performance.now();
  const mod = await factory(options);
  const tInst = performance.now();
  const rc = mod._lw_init();
  const tInit = performance.now();
  if (rc !== 0) throw new Error(`Lean initialization failed (${rc})`);

  function process(input) {
    const inPtr = toNum(mod._lw_input(input.length));
    mod.HEAPU8.set(input, inPtr);            // HEAPU8 re-read: memory may have grown
    const len = mod._lw_process();
    const outPtr = toNum(mod._lw_result());
    const out = mod.HEAPU8.slice(outPtr, outPtr + len);  // copy out before releasing
    mod._lw_release();
    return out;
  }

  return {
    process,
    module: mod,
    timings: { instantiateMs: tInst - t0, leanInitMs: tInit - tInst },
  };
}
