# Spike: running compiled Lean in the browser (WebAssembly)

Date: 2026-11-23 · Lean 4.36.0 · Emscripten 6.0.5 · branch `spike/lean-wasm`

## (a) Verdict

**It works.** A static page loads a wasm module built from Lean 4.36.0 code and calls an
exported `ByteArray → ByteArray` function. The function exercises `String` (UTF-8
decode/encode, `toUpper`, formatting), `Nat` bignums up to ~10^90, `Array`, `Std.HashMap`,
closures, `panic!`, and module initialization of 803 Init/Std modules. Its output matches
the native build of the same code byte for byte, for wasm32 and for wasm64, in:

- Node 25.2.1 (automated check, 5 inputs including 1 MiB, plus 2000 repeated calls with no heap growth)
- headless **Chromium 154**, **Firefox 146** and **Firefox ESR 140** (real browsers, page served over HTTP)
- **Not tested in Safari/WebKit.** No WebKit engine is installed. Playwright's WebKit download
  needs ICU 76, libxml2, libwoff2dec and libmanette system libraries that are not installed here,
  and installing them is out of scope.

**Route: a hand-built toolchain, not an existing tool.** The pipeline:
1. Compile the Lean C++ runtime (`src/runtime` from the v4.36.0 tag) with `em++`: single-threaded,
   no GMP (Lean's own bignums), no mimalloc, no mmap, plus `-DLEAN_EMSCRIPTEN`. It needs 2 small patches
   to upstream code and 8 ENOSYS stubs for libuv fs calls.
2. Generate C for the import closure (our modules via Lake, Init/Std by re-running the stock native
   `lean -c` on the matching v4.36.0 sources), then compile it with `emcc`.
3. Post-process the generated C to fix big Nat literals. This is required for wasm32 (see (d)), and harmless on wasm64.
4. Link with a ~60-line C shim exporting `lw_init / lw_input / lw_process / lw_result / lw_release`.

Existing tools:
- **lean2wasm** (T-Brick): last commit March 2024, Lean v4.6.1. It downloads the official
  `lean-<ver>-linux_wasm32` release artifact, which has not been published for a long time (none for
  4.36). It only builds `main` programs. **Unsuitable.**
- **lasm** (`@lasm/cli` 0.10.0, Nov 2026, single author, MIT): serious and active, CI-tested in Chromium,
  Firefox and WebKit. However, it accepts **exactly Lean 4.35.0** and rejects other toolchains. It ships its
  own patched Lean build (12 patches), and its only memory layout is **wasm64** (`targets/lean-4.35.0-wasm64`, with
  pthreads and mimalloc). It is a whole framework: its own JS binding layer, a 2.5 GB tool cache, and breaking
  changes in most releases. Adopting it would mean pinning Lean to whatever lasm supports and requiring
  Memory64 in every browser. **Not adopted.** It is still useful corroboration that wasm64 + Lean works,
  and a reference for their patches. I evaluated it by reading the npm package only; I did not run it.

## (b) wasm32 vs wasm64

Measured on this machine (20 cores). The build uses `-O2`, and sizes are for the full demo (all 803 Init/Std modules linked).

| | **wasm32** | **wasm64** (Memory64, `-m64`) |
|---|---|---|
| Works (Node, Chromium 154, Firefox 146/140) | yes, **after the big-Nat-literal fix** (without it: memory corruption, crash on the first call) | yes, no fix needed |
| `.wasm` raw / gzip -9 | 1,560,823 B / **248 KB** | 1,661,413 B / **260 KB** |
| JS glue raw / gzip | 60 KB / 17 KB | 61 KB / 17 KB |
| Node startup (median of 7 cold processes): instantiate + Lean init | 10 + 30 = **41 ms** | 11 + 34 = **47 ms** |
| Browser, page load to ready (noisy, cold profile, busy machine) | Chromium 50–170 ms, Firefox 90–330 ms | Chromium 56–210 ms, Firefox 130–380 ms |
| 1 MiB call (Node) | 25–40 ms | 41–49 ms |
| Max non-tail recursion depth (Node default stack) | ~15,000 frames | ~13,000 frames |
| `System.Platform.numBits` / `USize.size` | 32 / 2^32 | 64 / 2^64 (same as native) |
| Browser support | universal | Chrome 133+, Firefox 134+, **Safari: not in a stable release** |

Linking with `-Oz` instead of `-O2` shrinks wasm32 to 1.28 MB raw, but only to 241 KB gzipped (−2%). Not worth it yet.

**Memory64 browser support** (sources: MDN browser-compat-data `webassembly/memory64.json`, last updated
2026-11-11 "Updates for Safari 27.3 beta"; webassembly.org feature table `features.json`, last updated 2026-11-10):
- Chrome 133+, **Chrome Android: same versions as desktop** (BCD "mirror")
- Firefox 134+, Firefox Android: same versions as desktop
- **Safari: 27.3, which is currently beta.** Stable Safari is 27.2 (released 2026-10-26) and does not support it.
  webassembly.org still lists it as "flag / Safari Technical Preview 251". **iOS Safari follows Safari, and every
  iOS browser is WebKit**, so no iPhone or iPad can run wasm64 today. Older iOS devices stuck on old versions never will.
- Node 24+, Deno 2.2+.
- For comparison, the Wasm exception handling we use (legacy EH, chosen by Emscripten 6.0.5 by default): Chrome 95,
  Firefox 100, Safari 15.2.

**Recommendation: wasm32**, with the literal fix built into the pipeline. Reasons:
- It runs on every current browser, including all iOS devices. For a file-sync app that must run on phones,
  that is decisive: wasm64 would exclude every iOS user until Safari 27.3 ships, and older iOS devices
  permanently.
- It is smaller (−6% gzipped), starts slightly faster, and uses less memory per object (4-byte pointers).

Trade-offs of wasm32:
- The C it runs was generated by a 64-bit compiler. The one miscompilation class I found (big Nat literals) is
  fixed by a regex post-pass. It is narrow and was analysed (below), but it is the kind of thing that can change
  with a Lean upgrade, so the post-pass and the Node check must run in CI.
- `USize` is 32 bits: `numBits`, `USize.size`, `Array` index limits and hash truncation differ from native.
  The demo's HashMap iteration order *happened* to be identical on native, wasm32 and wasm64. Bucket indices
  only use the low bits of the hash, and those survive the truncation. But anything that serialises a `USize` or
  `hash` value, or depends on it, must be checked. The CRDT's wire format should use fixed-width types only.
- 4 GiB address-space cap. That is irrelevant for a sync core that processes one file or batch at a time.

wasm64 would be the choice only if Safari/iOS were explicitly out of scope.

### Does wasm32 need a 32-bit native Lean to generate C?

**No.** I checked this concretely by reading the 4.36.0 compiler and the emitted C:
- Struct layout, scalar offsets and static objects are emitted symbolically (`sizeof(size_t)*k`, `sizeof(void*)`), so the C compiler resolves them per target.
- `USize` constant folding (`ConstantFold.lean`) only folds when the 32-bit and 64-bit results agree.
- Static ground `Nat` values are only emitted for literals below 2^31.
- Constants like `closureMaxArgs` (16) and `maxCtorScalarsSize` (1023) are the same on both platforms.
- `System.Platform.numBits` is a runtime call and correctly returns 32 under wasm32.
- No `USize` literals of 2^32 or more appear in the generated C.
- **The one host-dependent decision** is in `ExplicitBoxing.lean`: a Nat literal `n ≤ maxSmallNat` (2^63−1 on the
  64-bit host) gets the `tagged` (unboxed, no refcount) type. **Independently of the host**, `ToImpure.lean` types every
  literal `< 2^32` as `tagged`. So on wasm32, any literal in [2^31, 2^63] is a heap bignum that the code never
  increments or decrements. It leaks in borrowed positions and is **double-freed** when used in two owned positions.
  The demo has such a case: `acc.push k |>.push k` with `k := 5000000000`. It crashed with "memory access out of
  bounds" in `lean_dec_ref_cold` on the very first call. Adding the missing `lean_inc` by hand fixed it.
- A 32-bit native Lean would fix only the [2^32, 2^63] half of this; the [2^31, 2^32) half is wrong on any host.
  So it is not the right tool. The 32-bit stage0 in lean4's old CI existed to produce 32-bit **.olean** files for a
  Lean *compiler* running inside wasm. AOT-compiled programs don't load oleans. (Building one would also need
  gcc-multilib, which is not installed: `gcc -m32` fails for lack of `crti.o`.)
- The fix (`scripts/wasm/fix-nat-literals.py`) rewrites the 22 such literal sites in our closure (7 files,
  mostly Init: `UInt32/UInt64.size`, `2^53` in `OfScientific`, float-model constants, ...). Each one becomes
  a per-call-site cached **persistent** object, whose RC operations are no-ops. That removes both the leak
  and the double free with no semantic change, because Nats are immutable.

## (c) How to build and run

Prerequisites: elan with `leanprover/lean4:v4.36.0` installed, `emcc` on PATH, Node ≥ 24, git, python3.

```sh
scripts/wasm/build.sh                 # both archs; or: scripts/wasm/build.sh wasm32
node wasm/check-node.mjs wasm32       # Node check vs native (also: wasm64)
scripts/wasm/check-browsers.sh        # headless Chromium/Firefox, both archs, needs a prior build
node wasm/serve.mjs 8000              # then open http://127.0.0.1:8000/?arch=wasm32 (or wasm64)
```
`python3 -m http.server -d build/site 8000` also works for the demo page. Any static host does, too:
it needs no COOP/COEP headers because the build has no threads.

What `build.sh` does and costs, from scratch:
- `fetch.sh`: shallow clone of lean4@v4.36.0 (828 MB with libuv, under gitignored `vendor/`), then apply patches.
- `gen-c.sh`: about **3m45s wall (~1 CPU-hour)** the first time. It re-elaborates the 802 Init/Std modules in
  the closure; `Std.Data.HashMap` drags in all its `Lemmas` files. Later runs only redo our own modules.
- runtime + C → wasm: about **35 s wall per architecture** (20 cores). `build/` is 141 MB.

**What I actually ran and observed (verified):**
- `scripts/wasm/build.sh` from a clean `build/` → both archs built.
- `node wasm/check-node.mjs wasm32|wasm64` → "all passed" (5 inputs, byte-identical to native except the
  intentionally platform-specific `numBits` line; heap size unchanged after 2000 calls).
- `scripts/wasm/check-browsers.sh` → 6× `REPORT PASS` (Chromium 154, Firefox 146, Firefox ESR 140 × wasm32/wasm64).
  The page itself posts its output and the server compares it with the native binary.
  Each browser/arch invocation carries its own run id and must produce exactly one PASS. A browser that crashes
  or never reports counts as a failure. Both the Node and browser checks also assert that the platform line
  matches the requested arch (`numBits=32`/`64`) before comparing the rest. Negative tests: a wasm32 artifact
  copied into the wasm64 directory fails both checks; a page that never reports fails all 6 runs; a busy port
  fails fast; malformed reports are logged as FAIL without killing the server.
- wasm32 *without* the literal fix → reproducible crash (described above).
- Probes: `panic!` prints the message and returns the default value, as on native. Exceeding the stack
  throws a JS `RangeError` out of `lw_process`.

**Assumed / not verified:** Safari/iOS behaviour (not run at all; only compat tables), Chrome on Android,
behaviour on low-memory phones, and timings anywhere other than this desktop.

## (d) What was hard or fragile and will bite later

- **Upstream's Emscripten path is unmaintained.** The CI job is commented out and the code has bit-rotted. I needed:
  a wrong stub signature (`lean_uv_os_get_group`); an unconditional `uv_strerror` in `io.cpp`;
  `lean_io_create_tempfile/dir` still taking the IO world argument the 4.36 compiler no longer passes (harmless
  on x86-64, but wasm-ld turns the mismatch into a trapping stub); and 8 libuv fs functions referenced even
  with `LEAN_EMSCRIPTEN` (stubbed as ENOSYS in `wasm/uv_stubs.c`). Expect new breakage of this kind on
  **every Lean upgrade**. Mitigation: pin Lean, keep `scripts/wasm/patches/`, and run the Node check in CI.
  wasm-ld's signature-mismatch warnings are a useful ABI check and should probably be turned into errors.
- **Big Nat literal miscompilation on wasm32.** Fixed by a post-pass, but the fix is a regex over emitted C.
  If Lean changes how it prints literals, the regex silently stops matching. CI should therefore also grep for unfixed patterns.
  The real fix is upstream: type literals as `tagged` only below 2^31, or make the decision target-aware.
  Worth reporting upstream.
- **Stack depth.** Non-tail recursion is limited by the *JS engine's* stack (~13–15k frames of a trivial
  function in Node; browsers differ, and Safari is unknown), not by Emscripten's `STACK_SIZE` (set to 8 MB).
  Native handles 1M+. CRDT code over long histories must be tail-recursive or loop-based. After a trap, the module's
  state (Lean heap refcounts, Emscripten's stack pointer) should be considered corrupt: the host should
  re-instantiate it.
- **Initialization cost.** Linking `Std.Data.HashMap` pulls in 802 modules, all of whose initializers run at
  startup: 30–50 ms in Node and Chromium, single-digit ms in Firefox. It is also most of the 1.5 MB. Importing narrower
  modules, or trimming initializers, is the lever for both. Note that the Lean init order is fixed by the
  generated `initialize_*` chain, and the shim must call `lean_initialize_runtime_module()` first and
  `lean_io_mark_end_initialization()` last.
- **Package name leaks into symbols.** The exported init function is `initialize_lean_x2dcrdt_WasmDemo`, which
  comes from the Lake package name. Renaming the package breaks the shim. `@[export]` names (`lean_wasm_demo_process`) are stable.
- **Exceptions.** The runtime is C++ and uses exceptions internally, so the build uses `-fwasm-exceptions`
  (legacy EH by default in Emscripten 6.0.5, Safari 15.2+). Switching to exnref later would need Safari 18.4+.
- **Threads.** The build is single-threaded (`LEAN_MULTI_THREAD` off). `Task`s run synchronously and
  `IO.asTask` cannot run in parallel. That is fine for a "bytes in, bytes out" core. Using pthreads would need
  SharedArrayBuffer and COOP/COEP headers on the host.
- **Allocator.** Emscripten's dlmalloc instead of mimalloc. Not benchmarked; the 1 MiB call is fine.
  Bignums use Lean's own mpn instead of GMP, so very large `Nat` arithmetic is slower than native (my first
  test, a product over 1 MiB of bytes, was impractically slow and had to be capped).
- **No filesystem/IO.** File, process and network IO return errors (ENOSYS stubs). stdout/stderr go to the
  console.
- **Build cost.** About 1 CPU-hour to generate Init/Std C once per Lean version, plus an 828 MB vendor checkout.
  Both could be cached as CI artifacts. A sparse checkout of `src/` would cut the clone size.
- **Emscripten version drift.** Debian's emcc 6.0.5 printed a deprecation for `-sMEMORY64` (now `-m64`).
  The output depends on the system Emscripten. Pinning it via emsdk would make builds reproducible.

## (e) Open questions for the user

1. **wasm32 (all browsers, needs our literal post-pass) or wasm64 (no iOS until Safari 27.3 ships)?**
   I recommend wasm32. Is supporting iOS/Safari a hard requirement?
2. **Upstream:** should we report the Nat-literal boxing issue and the Emscripten bit-rot to lean4, or send patches?
   That would reduce what we carry with each Lean upgrade.
3. **lasm:** it is ahead of us on browser polish (JS bindings, Vite plugin, CI across engines) but is wasm64-only
   and pinned to Lean 4.35. Revisit it if it adds wasm32 or tracks Lean releases quickly?
4. **Lean version policy:** each upgrade means re-running ~1 CPU-hour of C generation and re-checking the patches.
   How often do we expect to upgrade?
5. **Real-device testing:** someone with a Mac/iPhone needs to run the demo (`?arch=wasm32`) in Safari. I could not.
   Is there a device or BrowserStack-type service available?
6. **Stack depth:** is ~10k frames of non-tail recursion an acceptable design constraint for the CRDT code?
   As far as I know, browsers offer no portable way to enlarge the JS/wasm stack.

## Files

- `WasmDemo.lean` — the demo function (separate `WasmDemo` lib + `wasm-demo-native` exe in `lakefile.toml`)
- `wasm/shim.c`, `wasm/uv_stubs.c` — C boundary and libuv stubs
- `wasm/host.mjs` — JS host (`loadLean(factory) → { process(Uint8Array): Uint8Array }`), the same for both archs
- `wasm/index.html`, `wasm/serve.mjs`, `wasm/check-node.mjs` — demo page, dev server with `/report`, Node check
- `scripts/wasm/*.sh`, `ModClosure.lean`, `fix-nat-literals.py`, `patches/` — the reproducible build
