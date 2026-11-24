# lean-crdt

A file-sync app for one user's devices: the sync logic is a CRDT and a pure step-function protocol
written and proved in Lean 4 (`LeanCrdt/`, `LeanSync/`), compiled to WebAssembly (wasm64) and run
in the browser behind a thin JavaScript host (`app/`).

Design notes: `docs/crdt-design.md` (the CRDT), `docs/sync-design.md` (the protocol and the host
obligations), `docs/spike-lean-wasm.md` (Lean → wasm), `docs/app-design.md` (the browser app).

## How to run

Prerequisites (as on the development machine): elan with `leanprover/lean4:v4.36.0`, Debian's
`emcc` 6.0.5 on `PATH`, Node ≥ 24 (tested with 25), git, python3; for the tests, `chromium` and
`firefox` (optionally `firefox-esr`). Browsers supported by the app: Chrome 133+, Firefox 134+ (no
Safari: it needs WebAssembly Memory64).

**Build** (the first build fetches lean4 v4.36.0 and libuv headers into `vendor/`, ~830 MB):

```sh
scripts/wasm/build.sh        # LeanSync -> build/sync/lean_sync.{mjs,wasm}  (a few minutes the first time)
scripts/build-site.sh        # app/ + engine -> build/site/
```

**Start** the development server. It serves `build/site/` and runs the test transport (a
WebSocket relay); it listens on 127.0.0.1 only and is not part of the app:

```sh
node dev/serve.mjs --port 8000        # add --admin only for the tests' fault-injection API
```

**Open two devices.** Each device is a browser profile with its own storage, e.g.:

```sh
chromium --user-data-dir=/tmp/dev-a 'http://127.0.0.1:8000/?device=laptop'
firefox --no-remote --profile "$(mktemp -d)" 'http://127.0.0.1:8000/?device=phone'
```

Devices in the same room connect to each other through the relay: without `?room=`, all devices of this server share a random room chosen when it starts. The relay accepts only pages served by itself (it checks `Origin`); `--admin` enables the fault-injection API the tests use.
Add files with the button or by dropping them; untick "online" to edit offline. A second tab of the
same profile shows "open in another tab" and does nothing.

**Tests:**

```sh
scripts/check-proofs.sh      # no sorry/axiom/..., axioms of the headline theorems
scripts/test-crdt.sh         # CRDT tests (native)
scripts/test-sync.sh         # protocol tests (native)
scripts/wasm/check-engine.sh # wasm engine: Node smoke, native-vs-wasm replay, leak check and its
                             # negative control, 20k-file scale, browser smoke
scripts/test-app.sh          # the app: codec vs Lean vectors, unit tests, engine checks,
                             # end-to-end scenarios in headless Chromium and Firefox
node test/e2e/run.mjs --only storage-failure --browsers chromium   # one scenario, one browser
node test/mutations.mjs      # breaks each host obligation in turn; its test must fail (~10 min)
```
