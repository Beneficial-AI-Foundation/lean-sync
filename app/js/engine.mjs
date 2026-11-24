// The Lean sync engine (LeanSync.Envelope built to wasm64, see wasm/sync_shim.c): bytes in, bytes out.
//
// One instance holds one protocol machine. Calls are synchronous, so two calls can never overlap
// inside one instance. After ANY exception out of the module (a trap: stack exhaustion, unreachable,
// out of memory) the instance is marked dead and every later call throws `EngineDead`; the host must
// discard it, create a new one and start again with `init` (docs/spike-lean-wasm.md, carried-forward
// requirement 1). Pointers are i64 on wasm64 and arrive as BigInts.

const toNum = (p) => (typeof p === 'bigint' ? Number(p) : p);

export class EngineTrap extends Error {
  constructor(cause) { super(`Lean engine trapped: ${cause?.message ?? cause}`); this.name = 'EngineTrap'; this.cause = cause; }
}
export class EngineDead extends Error {
  constructor() { super('Lean engine instance is dead (it trapped earlier); create a new one'); this.name = 'EngineDead'; }
}

/** Instantiate the Emscripten factory (`createLeanSync`) and initialize Lean. */
export async function createEngine(factory, options = {}) {
  const t0 = performance.now();
  const mod = await factory({ print: () => {}, printErr: (s) => console.warn('[lean]', s), ...options });
  const t1 = performance.now();
  const rc = mod._ls_init();
  const t2 = performance.now();
  if (rc !== 0) throw new Error(`Lean initialization failed (${rc})`);
  let dead = false;
  let busy = false;

  /** Feed one encoded event; return the encoded effects (a fresh copy). */
  function process(input) {
    if (dead) throw new EngineDead();
    if (busy) throw new Error('re-entrant call into the Lean engine');
    busy = true;
    try {
      const inPtr = toNum(mod._ls_input(input.length));
      mod.HEAPU8.set(input, inPtr);              // re-read HEAPU8: memory may have grown
      const len = mod._ls_process();
      if (len === 0xffffffff) throw new Error('lean_sync_process returned an IO error');
      const outPtr = toNum(mod._ls_result());
      const out = mod.HEAPU8.slice(outPtr, outPtr + len);
      mod._ls_release();
      return out;
    } catch (e) {
      dead = true;
      throw new EngineTrap(e);
    } finally {
      busy = false;
    }
  }

  return {
    process,
    get dead() { return dead; },
    heapBytes: () => mod.HEAPU8.length,
    timings: { instantiateMs: t1 - t0, leanInitMs: t2 - t1 },
  };
}
