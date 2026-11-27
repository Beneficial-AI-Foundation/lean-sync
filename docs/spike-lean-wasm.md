> **Note (branch `browser-app`):** the demo this note describes (`WasmDemo.lean`, its lakefile targets, `wasm/index.html`,
> `serve.mjs`, `check-node.mjs`, `host.mjs`, `shim.c`, `scripts/wasm/check-browsers.sh`) was removed. The build scripts now build
> the sync engine; the equivalent checks live in `scripts/wasm/check-engine.sh` (Node and browser checks of the engine) and
> `scripts/test-app.sh` (the app); see `docs/app-design.md`.

# Spike: running compiled Lean in the browser (WebAssembly)

Date: 2026-11-23 · Lean **4.36.0 (pinned for the demo)** · Emscripten 6.0.5 · branch `spike/lean-wasm`

## What this branch builds

**A wasm64 (Memory64) module built from Lean 4.36.0 code, loaded by a static page.** The page calls an
exported `ByteArray → ByteArray` function. The function exercises `String` (UTF-8 decode/encode, `toUpper`,
formatting), `Nat` bignums up to ~10^90, `Array`, `Std.HashMap`, closures, `panic!`, and the
initialization of 803 Init/Std modules. Its output is **byte-identical to the native build** of the same
code, platform line included (`numBits=64`), in:

- Node 25.2.1 (automated check: 5 inputs including 1 MiB, plus 2000 repeated calls with no heap growth)
- headless **Chromium 154**, **Firefox 146** and **Firefox ESR 140** (real browsers, page served over HTTP)

**Browser floor: Chrome 133+ (desktop and Android), Firefox 134+ (desktop and Android). No stable Safari,
so no iOS browser at all.** Memory64 is in Safari 27.3, which is still beta; stable Safari is 27.2. This is a
deliberate choice: losing Safari/iOS for now in exchange for not carrying the wasm32 Nat-literal post-pass
(see "Not pursued: wasm32" below). Sources: MDN browser-compat-data `webassembly/memory64.json` (updated
2026-11-11, "Updates for Safari 27.3 beta") and the webassembly.org feature table `features.json` (updated 2026-11-10,
which lists Safari as "flag / Technical Preview 251"). Node needs 24+.

**Not tested in Safari/WebKit** (it would fail today anyway), Chrome on Android, or on real phones.
Playwright's WebKit download needs system libraries that are not installed here.

### The pipeline
1. Compile the Lean C++ runtime (`src/runtime` from the v4.36.0 tag) with `em++ -m64`: single-threaded,
   no GMP (Lean's own bignums), no mimalloc, no mmap, plus `-DLEAN_EMSCRIPTEN`. It needs 2 small patches
   to upstream code and ENOSYS stubs for 8 libuv functions (see "Upstream status" below).
2. Generate C for the import closure: our modules via Lake, and Init/Std by re-running the stock native
   `lean -c` on the matching v4.36.0 sources. Then compile it with `emcc -m64`. The native compiler is 64-bit,
   so its C is correct for wasm64 as is.
3. Link with a ~60-line C shim (`wasm/shim.c`) exporting `lw_init / lw_input / lw_process / lw_result / lw_release`.
   The JS host is `wasm/host.mjs`: `loadLean(factory) → { process(Uint8Array): Uint8Array }`.

### Numbers (this machine, 20 cores, `-O2`, full demo)
| | |
|---|---|
| `.wasm` raw / gzip -9 | 1,660,784 B / **259 KB** |
| JS glue raw / gzip | 61 KB / 17 KB |
| Node startup: instantiate + Lean init | 12 + 30 ms = **43 ms** (earlier median of 7 runs: 47 ms) |
| Browser, page load to ready (cold profile, noisy) | Chromium 60–210 ms, Firefox 210–380 ms |
| 1 MiB call (Node) | 34–49 ms |
| Max non-tail recursion depth (Node default stack) | ~13,000 frames |
| Clean build (`build.sh`, vendor already fetched) | **4m12s** wall, of which ~3m45s is generating Init/Std C |

### Upstream status of what we carry
Each item is noted in its file, so whoever upgrades Lean can tell when it can be dropped:
- `scripts/wasm/patches/lean4-0002-…`, the `lean_io_create_tempfile/tempdir` argument-count mismatch:
  **leanprover/lean4#16089**, closed 2026-11-02 and fixed on master after 4.36.0. Drop it after upgrading past that.
- `scripts/wasm/patches/lean4-0002-…`, the unconditional `uv_strerror` in `io.cpp`: open **PR #13298**.
- `wasm/uv_stubs.c`: PR #13298 also guards the temp-file libuv calls (`uv_os_tmpdir`, `uv_fs_mkstemp/mkdtemp`,
  `uv_fs_req_cleanup`). As of 2026-11-23 it does **not** cover `uv_fs_stat/lstat/link/unlink`, which 4.36's
  `io.cpp` also calls, so the stubs stay until upstream covers them.
- `scripts/wasm/patches/lean4-0001-…`, the wrong signature of the Emscripten stub `lean_uv_os_get_group`:
  covered by neither #16089 nor #13298. Re-check on upgrade.

## How to build and run

Prerequisites: elan with `leanprover/lean4:v4.36.0` installed, `emcc` on PATH, Node ≥ 24, git, python3.

```sh
scripts/wasm/build.sh              # fetch + generate C + build runtime + link → build/site/
node wasm/check-node.mjs           # Node check vs native (asserts numBits=64, byte-for-byte equality)
scripts/wasm/check-browsers.sh     # headless Chromium/Firefox, needs a prior build
node wasm/serve.mjs 8000           # then open http://127.0.0.1:8000/
```
Any static host can serve `build/site/`. No COOP/COEP headers are needed because the build has no threads.
For checks, the page accepts `?input=…` (initial input) and `?report=1&run=<id>`.

What `build.sh` does and costs, from scratch:
- `fetch.sh`: shallow clone of lean4@v4.36.0 plus libuv headers (828 MB under gitignored `vendor/`), then apply patches.
- `gen-c.sh`: about **3m45s wall (~1 CPU-hour)** the first time. It re-elaborates the 802 Init/Std modules in
  the closure; `Std.Data.HashMap` drags in all its `Lemmas` files. Later runs only redo our own modules.
- runtime + C → wasm: about **35 s** wall. `build/` is 71 MB.

**What was run and observed (verified):**
- `rm -rf build .lake/build && scripts/wasm/build.sh` → built in 4m12s.
- `node wasm/check-node.mjs` → "all passed", exit 0: 5 inputs byte-identical to native including the
  `numBits=64` line, heap size unchanged after 2000 calls.
- `scripts/wasm/check-browsers.sh` → 9 of 9 OK, exit 0, in 13 s: Chromium 154, Firefox 146 and Firefox ESR 140,
  each with the default input, `!panic` and `!deep 1000`. Each invocation has its own run id and must produce exactly
  one PASS. The server checks:
  - the platform line is 64-bit,
  - the output is byte-identical to native,
  - **what the page displays** (this covers the probe display fix).

  A crash, timeout or missing report fails the run; a busy port fails fast; malformed reports are logged as
  FAIL without killing the server.
- Negative checks:
  - a page that strips the input-length suffix from probe output → 6 probe runs FAIL ("page displayed the result incorrectly");
  - a report with a `numBits=32` platform line → FAIL ("platform line is not 64-bit");
  - earlier, with the two-arch layout, a 32-bit artifact in the 64-bit slot failed both checks.
- Probes: `panic!` prints the message and returns the default value, as on native. Exceeding the stack
  throws a JS `RangeError` out of `lw_process`.

## Known gaps in the spike harness (not fixed)

A second review of `d2ab800` found these nine issues. All of them are in spike scaffolding (`wasm/index.html`,
`wasm/serve.mjs`, `wasm/check-node.mjs`) that the real build will replace, so they were recorded rather than fixed.
None of them affects the Lean/wasm build itself, but a harness pass is less strong evidence than it looks.

1. **[P2][carry] Trapped instance is reused** (`wasm/index.html`). After a trap, such as `!deep N` exhausting the
   stack, the Run button stays enabled and reuses the same, possibly corrupted, instance.
2. **[P2][carry] Oracle uses the input the page reports** (`wasm/serve.mjs`), not the input assigned to the run.
   If the page stopped honouring `?input=`, the probe runs would still pass on the default text.
3. **[P2] `display` is the pre-render string** (`wasm/index.html`). The check sends the `report` string rather
   than reading the output element, so a blank or wrong render would still pass.
4. **[P2] A JSON `null` body kills the server** (`wasm/serve.mjs`). The catch handler reads `r.run` on `null`,
   throws again, and the unhandled rejection ends the process.
5. **[P2] Malformed percent-escapes kill the server** (`wasm/serve.mjs`). URL parsing and decoding happen
   outside the `try`, so the server dies instead of returning 400.
6. **[P2] Request chunks are decoded independently** (`wasm/serve.mjs`). A multibyte character split across
   chunks becomes replacement characters and fails a correct run.
7. **[P2] Platform check takes the first `numBits=` match** (`wasm/index.html`), which can be inside quoted
   input text rather than the platform line. It should be anchored to line start, as the Node check does.
8. **[P2][carry] Heap growth is logged, never asserted** (`wasm/check-node.mjs`). Growth over the 2000 repeated
   calls is printed, but a leak would still end in "all passed".
9. **[P3] Oracle temp files are never removed** (`wasm/serve.mjs`). The temp directory and input file are left behind.

### Requirements carried forward to the real host and tests
- **Re-instantiate after any trap** (from 1). The host must discard the module and create a new instance; it must
  never call into an instance that has trapped.
- **Verify each run used its assigned input** (from 2). The oracle's input must come from the test, not from
  what the system under test reports.
- **Fail on heap growth** (from 8). Repeated-call tests must fail when growth exceeds a steady-state bound.

## What was hard or fragile and will bite later

- **Upstream's Emscripten path is unmaintained.** The CI job is commented out and the code has bit-rotted
  (see "Upstream status" above). Expect new breakage of this kind on every Lean upgrade.
  wasm-ld's signature-mismatch warnings are a useful ABI check and should probably be turned into errors.
- **Stack depth.** Non-tail recursion is limited by the *JS engine's* stack (~13k frames of a trivial
  function in Node; browsers differ), not by Emscripten's `STACK_SIZE` (set to 8 MB). Native handles 1M+.
  CRDT code over long histories must be tail-recursive or loop-based. After a trap, the module's state
  (Lean heap refcounts, Emscripten's stack pointer) should be considered corrupt: the host should re-instantiate it.
- **Initialization cost.** Linking `Std.Data.HashMap` pulls in 802 modules, all of whose initializers run at
  startup: 30–50 ms in Node and Chromium, single-digit ms in Firefox. It is also most of the 1.6 MB. Importing
  narrower modules is the lever for both. The shim must call `lean_initialize_runtime_module()` first and
  `lean_io_mark_end_initialization()` last.
- **Package name leaks into symbols.** The exported init function is `initialize_lean_x2dsync_WasmDemo` (`..._x2dcrdt_...` when the package was named lean-crdt), derived
  from the Lake package name. `@[export]` names (`lean_wasm_demo_process`) are stable.
- **Exceptions.** The runtime is C++ and uses exceptions internally, so the build uses `-fwasm-exceptions`
  (legacy EH by default in Emscripten 6.0.5).
- **Threads.** The build is single-threaded (`LEAN_MULTI_THREAD` off) and `Task`s run synchronously. That is
  fine for a bytes-in/bytes-out core.
- **Allocator / bignums.** Emscripten's dlmalloc instead of mimalloc (not benchmarked), and Lean's mpn instead
  of GMP: very large `Nat` arithmetic is slower than native.
- **No filesystem/IO.** File, process and network IO return errors.
- **Build cost and drift.** About 1 CPU-hour to generate Init/Std C once per Lean version, plus an 828 MB checkout.
  The output also depends on the system Emscripten (Debian's 6.0.5). Caching the generated C and pinning
  Emscripten (emsdk) would address both.

## Existing tools (evaluated, not adopted)
- **lean2wasm** (T-Brick): last commit March 2024, Lean v4.6.1. It downloads an official `linux_wasm32`
  release artifact that no longer exists (none for 4.36), and only builds `main` programs.
- **lasm** (`@lasm/cli` 0.10.0, Nov 2026): wasm64-only like us, but it accepts exactly Lean 4.35.0, ships its
  own patched Lean (12 patches), pthreads and mimalloc, and is a whole framework (JS binding layer, 2.5 GB tool
  cache, frequent breaking changes). I read the npm package only and did not run it. It is useful as a reference
  for patches.

---

## Not pursued: wasm32 (kept for the record, in case Safari/iOS becomes a requirement)

wasm32 was built and verified up to commit `f35de44` on this branch. It runs in every browser, including Safari
15.2+ and all iOS devices. It was dropped because it needs a post-pass over the generated C (below).
`git show f35de44:scripts/wasm/fix-nat-literals.py` recovers the fix; that commit also has the two-arch build scripts.

### Measured comparison (at `f35de44`, same machine)

| | wasm32 | wasm64 |
|---|---|---|
| Works (Node, Chromium 154, Firefox 146/140) | yes, **only with the big-Nat-literal fix** (without it: memory corruption, crash on the first call) | yes, no fix needed |
| `.wasm` raw / gzip -9 | 1,560,823 B / 248 KB | 1,661,413 B / 260 KB |
| Node startup median (instantiate + Lean init) | 10 + 30 = 41 ms | 11 + 34 = 47 ms |
| Max non-tail recursion depth (Node) | ~15,000 frames | ~13,000 frames |
| `numBits` / `USize.size` | 32 / 2^32 | 64 / 2^64 (same as native) |
| Browser support | universal | Chrome 133+, Firefox 134+, no stable Safari |

Also observed: `Std.HashMap` iteration order was identical on native, wasm32 and wasm64 in the demo. Bucket
indices only use the low bits of the hash, which survive 32-bit truncation. Anything that serialises a `USize`
or a hash would still differ.

### The big-Nat-literal bug (why wasm32 needs a post-pass)
- `ToImpure.lean` types every Nat literal `< 2^32` as `tagged` (unboxed, no refcount), **regardless of host**.
  `ExplicitBoxing.lean` additionally retypes literals `≤ maxSmallNat` as `tagged`, which is 2^63−1 on the 64-bit host.
- On wasm32, a Nat is a scalar only below 2^31, so any literal in [2^31, 2^63] is a heap bignum that the code
  never increments or decrements. It leaks in borrowed positions and is **double-freed** when used in two owned
  positions. The demo has such a case (`acc.push k |>.push k`, `k := 5000000000`). It crashed with "memory
  access out of bounds" in `lean_dec_ref_cold` on the first call. Adding the missing `lean_inc` by hand fixed it.
- The fix rewrote the 22 such literal sites in the closure (7 files, mostly Init: `UInt32/UInt64.size`, `2^53`
  in `OfScientific`, float-model constants) into per-call-site cached **persistent** objects, whose RC
  operations are no-ops. Being a regex over emitted C, it would need a CI guard against silently missing new
  patterns. The real fix is upstream (make the `tagged` decision target-aware), and it was not reported.

### No 32-bit native Lean is needed for wasm32
I checked this against the 4.36.0 compiler and the emitted C:
- Layouts and static objects are emitted symbolically (`sizeof(size_t)*k`, `sizeof(void*)`).
- `USize` constant folding only folds when the 32-bit and 64-bit results agree.
- Static ground `Nat`s are emitted only below 2^31.
- Constants like `closureMaxArgs` and `maxCtorScalarsSize` are the same on both platforms.
- `numBits` is a runtime call.
- No `USize` literals of 2^32 or more appear.

The only host-dependent decision is the literal boxing above. A 32-bit native compiler would fix only its
[2^32, 2^63] half, since the [2^31, 2^32) half is wrong on any host. The 32-bit stage0 in lean4's old CI existed
to produce 32-bit `.olean` files for a Lean *compiler* running inside wasm, and AOT programs don't load oleans.
(Building one would also need gcc-multilib, which is not installed.)

---

## Files

- `WasmDemo.lean`: the demo function (separate `WasmDemo` lib and `wasm-demo-native` exe in `lakefile.toml`)
- `wasm/shim.c`, `wasm/uv_stubs.c`: the C boundary and the libuv stubs
- `wasm/host.mjs`: the JS host
- `wasm/index.html`: the demo page
- `wasm/serve.mjs`: the dev server with the `/report` check endpoint
- `wasm/check-node.mjs`: the Node check
- `scripts/wasm/*.sh`, `scripts/wasm/ModClosure.lean`, `scripts/wasm/patches/`: the reproducible build
