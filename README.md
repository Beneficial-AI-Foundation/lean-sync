# lean-sync

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

**Serve** `build/site/` with any static web server, over HTTPS in real use (the app needs a secure
context: OPFS, Web Locks, clipboard). It works from any path; `.mjs` must be served as JavaScript.
For development, `dev/serve.mjs` is a minimal static server on 127.0.0.1 (`http://127.0.0.1` is a
secure context):

```sh
node dev/serve.mjs --port 8000            # optionally --base /some/path/
```

**Open two devices.** Each device is a browser profile with its own storage, e.g.:

```sh
chromium --user-data-dir=/tmp/dev-a 'http://127.0.0.1:8000/?device=laptop'
firefox --no-remote --profile "$(mktemp -d)" 'http://127.0.0.1:8000/?device=phone'
```

**Pair them** (docs/net-design.md): on one device choose *Invite a device*; on the other *Join a
device* and paste the invitation's text (copy it with *Copy*, send it any way you like); the
second device then shows a reply: press *Copy* (the reply stops changing) and paste it on the
first device within a few seconds. Devices connect directly over WebRTC; nothing goes through a
server except the STUN query (default `stun:stun.l.google.com:19302`, editable under *Connection
settings*, may be empty). Pairing lasts while both pages stay open: after a reload, pair again.
Add files with the button or by dropping them; untick "online" to edit offline (the pairing is
kept). A second tab of the same profile shows "open in another tab" and does nothing.

**Tests:**

```sh
scripts/check-proofs.sh      # no sorry/axiom/..., axioms of the headline theorems
scripts/test-crdt.sh         # CRDT tests (native)
scripts/test-sync.sh         # protocol tests (native)
scripts/wasm/check-engine.sh # wasm engine: Node smoke, native-vs-wasm replay, leak check and its
                             # negative control, 20k-file scale, browser smoke
scripts/test-app.sh          # the app: codec vs Lean vectors, unit tests, engine checks,
                             # end-to-end scenarios in headless Chromium and Firefox (run in a
                             # private network namespace: needs unprivileged user namespaces, or a
                             # network interface; see test/e2e/run.mjs)
node test/e2e/run.mjs --only storage-failure --browsers chromium   # one scenario, one browser
node test/mutations.mjs      # breaks each host obligation in turn; its test must fail
```
