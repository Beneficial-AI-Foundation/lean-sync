# Browser app (single machine): design note

Branch `browser-app` · Lean 4.36.0 · Emscripten 6.0.5 (Debian) · wasm64 only. **Built and tested**
(stage 2); §0 is the engine work of stage 1, §1–§12 describe the app as built, §13 lists what the
browser forced and what is not done. How to run: `README.md`. Specs:
`docs/sync-design.md` (protocol, §8 host obligations), `docs/crdt-design.md` (host rule),
`docs/spike-lean-wasm.md` (build, constraints).

## 0. Stage 1: the engine under wasm (done, measured)

`scripts/wasm/build.sh` now builds `LeanSync.Envelope` (shim `wasm/sync_shim.c`, exactly the
C-shim change of sync-design §1) into `build/sync/lean_sync.{mjs,wasm}`. The scripts were
generalised: `gen-c.sh <Module> <dir>` writes the closure list, `build-wasm.sh` links only that
closure (build/c and build/obj are shared caches). `scripts/wasm/check-engine.sh` runs all checks.

| Measured (this machine, 20 cores) | |
|---|---|
| Closure | 679 modules: 668 `Init`, 4 `LeanCrdt`, 7 `LeanSync` (no `Std`, no proof modules) |
| `.wasm` raw / gzip -9 | 1,537,700 B / **248 KB** (glue `.mjs` 60,806 B / 17 KB) |
| Clean build (`rm -rf build`, vendor and `.lake` present) | **97 s** wall, 27 CPU-min: C generation 50 s, runtime 6 s, C→wasm + link 41 s |
| Node start-up (import + instantiate + Lean init), 7 runs | 38–42 ms, median 39 ms (init ≈ 27 ms) |
| Browser start-up incl. fetch, headless, cold profile, 1 run each | Chromium 154: 62 ms · Firefox 146: 116 ms · Firefox ESR 140: 131 ms |
| 20k files: `putMany` + persist / full sync of a fresh device (index + 20k blobs) | 54 ms / 11.8 s wall, of which ~10 s inside the receiving engine (~0.5 ms per `blobStored`, about 2× the native figure) |

**Same behaviour as native: yes, as far as tested.** `sync-tests trace 1 200` (new test subcommand
in `Tests/Sync.lean`; libraries untouched) records 200 simulator worlds — 83,729 events with every
injected fault (crashes, drops, garbage, truncation, persist and blob failures) — with the native
output of `process` on each Lean-encoded event. `test/wasm-replay.mjs` feeds each device's events
to its own wasm instance (a fresh instance after each simulated crash: 1,601 instances) and
compares: **0 byte mismatches**, and all 83,729 outputs decode with the JS decoder. The Node smoke
test (`test/wasm-smoke.mjs`) runs `initFresh` → `persisted` → `putMany` → `persisted` → `snapshot`
through the JS encoder, wasm and the JS decoder and checks the exact record bytes; the browser smoke
(`test/browser-smoke.mjs`) does the same in Chromium 154, Firefox 146 and Firefox ESR 140, each run
checked against a path the server assigned to it. A steady-state loop (3,000 cycles, each a
256 KiB message) grew the wasm heap by 0 bytes (bound 1 MiB). Not yet probed under wasm: the frame
budget with states much larger than 20k entries. Replies, which the simulator never produces, are
covered by the golden vectors (§2). **The leak check can fail:** against a test-only build whose
shim leaks every input (`scripts/wasm/build-leak-variant.sh`), the same loop grows the heap from
63.5 MB to 870 MB and the check fails; `check-engine.sh` requires that failure.

**Trap probe.** An allocation of 4 GiB (`_ls_input(0xffffffff)`) makes Lean print `INTERNAL PANIC:
out of memory` and Emscripten throw `ExitStatus`; afterwards the instance still *accepts* calls, so
the wrapper (`app/js/engine.mjs`) marks an instance dead on any exception and refuses further calls.
In the browser e2e test the trap is triggered for real inside the module (§8).

## 1. Module layout (as built)

```
app/                         the shipped static site (scripts/build-site.sh copies it with the engine into build/site/)
  index.html, app.css
  js/main.mjs                boot: Web Lock, storage, engine, core, links, transport, UI; window.leansync diagnostics (read-only)
  js/engine.mjs              wasm instance wrapper: synchronous bytes→bytes, dead after any exception
  js/codec.mjs               event encoder; effects/notice/reply decoder; the tables the tests check against Lean
  js/core.mjs                event queue and pump, effect execution, epochs, start-up, trap recovery, user operations
  js/storage.mjs             IndexedDB record, OPFS blobs (incoming/ → verify → move to blobs/), 256 MiB file limit
  js/links.mjs               host framing, PeerIds, HELLO / own-id refusal, fragmentation, blob streams with credit
  js/view.mjs                snapshot + pending → rows (pure)
  js/ui.mjs                  DOM rendering, dialogs, drag-and-drop
  js/hash.mjs                WebCrypto SHA-256
  js/transport/relay.mjs     the transport of this version: client of the dev relay (interface in its header)
  lean/lean_sync.{mjs,wasm}  (in build/site only) the engine
dev/serve.mjs                dev/test only: static server + WebSocket relay + admin API; 127.0.0.1 only
test/unit/                   node --test: codec vs Lean vectors, links, core (real engine), view
test/e2e/                    driver (CDP / WebDriver BiDi on Node built-ins), lib, scenarios, runner, feature probe
test/wasm-*.mjs, test/browser-smoke.*   engine checks (§0)
scripts/build-site.sh, scripts/test-app.sh, scripts/wasm/*   build and checks
```
The spike demo was removed. The shipped app contains no test-only code path: all fault injection
(traps, IndexedDB failure in Chromium, download capture) is done by the test driver from outside,
through init scripts (`test/e2e/lib.mjs`), so the app under test is byte-identical to what ships.
`window.leansync` exposes read-only diagnostics (phase, epoch, engine instances, traps, heap size,
log), which the tests read.

## 2. Codec: hand-written, differentially tested against Lean

`codec.mjs` is hand-written (the format is small and version-tagged; a generator would be more,
unverified, code). It is kept in step by tests that regenerate their inputs from the current Lean
build on every run (`scripts/test-app.sh`):
- `sync-tests vectors` writes 636 cases: one sample of **every** event, local op, query, effect,
  notice (all 14), reply (all 3), pending status, peer status, close reason and decode error, with
  edge values (u64-max replica halves, 2^40 tags, peer 2^32−1, empty lists, Unicode and quotes in
  paths, `sendAgain`), plus 600 random ones. JS must encode each event to identical bytes and
  decode each envelope to the same values; every proper prefix must be rejected, and a trailing
  byte too. The Lean renderers are exhaustive matches, so a new constructor breaks their build.
- `scripts/wasm/Ctors.lean` prints the constructor lists of the ten boundary types from the Lean
  environment; the JS test fails unless the codec's tables cover exactly those constructors, and
  unless the vectors exercise every one of them.
- The 83,729 real envelopes of the trace replay (§0) all decode.

## 3. Event loop (as built)

One `Core` (`core.mjs`) owns the engine, a FIFO and an epoch. Every event — UI operation, link
change, message, storage completion, blob completion, timer — goes through `emit(ev, epoch)`. The
pump dequeues one event, calls `engine.process` (synchronous; the wrapper also rejects re-entry),
decodes, and executes every effect in order without awaiting: sends are queued on links, `persist`
and blob work start async jobs whose completion is a later `emit`. So events reach Lean one at a
time and all effects of an event are dispatched before the next one. Start-up events (`init`, then
inventory chunks) are processed directly, in order, before peers are accepted.

Two rules found necessary while building:
- **No host-generated events while saves fail.** Every event makes Lean retry the write, and the
  UI's refresh queries are events; the first version therefore spun at 16 failed writes per second.
  While `saveFailed` holds, UI queries are deferred to the back-off nudge (1, 2, 4 … 60 s, growing
  only with the nudges). Real events (peer messages, blob completions) still cause retries — 138
  failed writes in the Firefox quota test, during a burst of 150 incoming files — which is the
  protocol's design (any event retries), bounded by the event rate.
- **A restart cancels pending refreshes** (found by a unit test: a stale debounced query of the old
  epoch was dropped and the new machine's file list was never requested).

Epochs: a restart increments the epoch; completions of an older epoch are dropped, except that a
blob that became durable is re-reported as `blobsStored [h]`. Stale `persisted`/`persistFailed`
never reach the new machine (its tags restart at 0).

## 4. Host obligations

| Obligation (sync-design §8, decision 7) | Mechanism | Test |
|---|---|---|
| Persist the record atomically, then `persisted tag SHA-256(bytes)` | `storage.saveRecord`: one `readwrite` transaction with `durability:'strict'` putting `{v,hi,lo,state}`; the promise resolves **only** from the transaction's `complete` event; digest of exactly those bytes | unit `core`: no `persisted` while the save is held; e2e `reload-and-kill-mid-session` |
| Never acknowledge a failed write | `error`, `abort` or any exception (including Firefox's `InvalidStateError`, Chromium's OPFS `AbortError`) rejects → `persistFailed` | unit `core`; e2e `storage-failure` |
| Retry after back-off; surface `saveFailed` until resolved | nudge timer; "Retry now"; banner and "not saved" header stay until a later save completes | e2e `storage-failure` (banner still there after 4 s and ≥2 failed retries; peer did not get the unsaved delete) |
| One persist in flight | Lean; host logs a violation | unit `core` |
| Blob verified and durable before `blobStored`; local blob before `localOp` | write to `incoming/`, close, hash the **stored** bytes, `move()` to `blobs/<hex>`, then emit; local add the same, then `putMany` | unit `links`; e2e `corrupted-blob…`, `reload-and-kill…` |
| Nothing else persisted | IDB holds the record, `rotateId` and the device label | review |
| One owner (Web Lock) | `navigator.locks.request('leansync-owner', {ifAvailable:true})`, held for the tab's life | e2e `second-tab-lock` |
| Start-up: `init` / `initFresh` / `init newId` | `rotateId` set on `rollbackDetected` and before a user-confirmed new identity; cleared in the same transaction as the first record under the new id | unit `core`; e2e `rollback…`, `startup-failure…` |
| Inventory before any peer | 10k hashes in `init`, rest in `blobsStored` chunks; `links.setAccepting(true)` only afterwards; links that greet earlier are closed (the remote retries) | unit `core` (25,000 blobs), unit `links` |
| `startupFailed` → error; reset only after confirmation | start-up failure screen: Try again / Reset… (dialog says what is lost and kept) → `initFresh newId` | unit `core`; e2e `startup-failure-and-reset` |
| `sendAgain` | decoder, within one envelope | codec vectors |
| `send` to a closed peer dropped; `close` after queued bytes | per-link queue with a CLOSE marker | unit `links` |
| `fetch`: accept only those hashes, verify, size limit, `blobFailed`; drop mid-stream discards | per-peer expected set; START over 256 MiB refused before any byte; mismatch/abort/over-credit → `blobFailed`; link loss → partial deleted, nothing reported | unit `links`; e2e `corrupted-blob…`, `disconnect-mid-transfer…` |
| `serveBlob`: unreadable → abort + `blobLost` | read, verify hash (bit rot: delete), stream; else ABORT + `blobLost` | unit `links` |
| `connected`/`disconnected` once; PeerIds never reused | page-lifetime counter; `connected` after the host HELLO | unit `links` |
| `received`: one complete message ≤ limit | reassembly; over the limit closes the link | unit `links` |
| Persist answers only for persists given | epochs | unit `core` |
| Rollback mode surfaced; restart only on click + confirm | banner, edit controls disabled, dialog (keeps / loses), then `init newId bytes` | e2e `rollback-detected-then-new-identity` |
| Re-instantiate after a trap; no loop | §8 | e2e `trap-mid-sync…`, `trap-at-startup…`; unit `core` |
| Refuse a peer with our own replica id | host HELLO carries the replica id; equal → link closed before Lean sees it (Lean's own `sameReplicaId` check stays behind it) | unit `links`; e2e `same-replica-id-refused` |

## 5. Storage schema and crash consistency

IndexedDB `leansync`/`kv`: `record` `{v:1, hi, lo (BigInt), state}`, `rotateId`, `label`. OPFS
`blobs/<64 hex>` (verified), `incoming/<rand>` (partial, emptied at start-up). Crash cases are as in
the plan: the record transaction is atomic and unacknowledged states were never sent; a blob is in
`blobs/` only after verification; an add interrupted before its `putMany` leaves an orphan blob.
`e2e reload-and-kill-mid-session` kills the browser (SIGKILL) right after an add and checks that
after restart every listed file is complete and sync resumes (in the runs so far the add had been
saved each time; the "lost" branch is accepted by the test but was not observed).

Browser behaviour found by the feature probe (`test/e2e/probe-features.mjs`) and the tests:
- OPFS `move()` and IDB `durability:'strict'` work in Chromium 154, Firefox 146 and ESR 140.
- **Firefox:** after a transaction aborts for quota, the next `db.transaction()` on that connection
  throws `InvalidStateError` ("did not allow mutations"), and kept doing so after space was freed.
  `storage.mjs` then reopens the connection and tries the same write once more (nothing was
  written by the failed call). A record rewritten in place does not grow and fits in pages IDB
  already owns, so a full disk only fails saves whose record grows.
- `navigator.storage.persist()` shows a permission prompt in Firefox (never answered in headless
  mode); it is requested without blocking start-up.

## 6. Transport interface and the test transport (as built)

Interface: in the header of `app/js/transport/relay.mjs` (`start({onLink, onStatus})`,
`setOnline`, `stop`; link: `send`, `close`, `bufferedAmount`, `onFrame`, `onClose`, `onDrain`).
Host framing (`links.mjs`): MSG (fragment), START, DATA, END, ABORT, CREDIT, HELLO; payload ≤ 16 KiB.
The relay (`dev/serve.mjs`, hand-written RFC 6455, 127.0.0.1 only) links devices of a room; the
device with the smaller relay id asks for each link, with a per-remote back-off (0.5 s doubling to
30 s, reset after a link lived 20 s) so a session closed for an error cannot spin. Admin API:
topology, cut at a byte offset, corrupt the next blob frame, inject a garbage message, state. The
relay client is in `app/` because it is this version's only transport; the server is not.

## 7. Blob streaming and backpressure (as built)

One outgoing blob at a time per device: read whole (≤ 256 MiB), verify, START, then DATA frames
interleaved behind Lean messages while the link buffer is under 1 MiB and the receiver's credit
allows; END. The receiver grants credit up to 4 MiB beyond what it has written; bytes beyond the
credit, or beyond the announced size, fail the stream; a START above 256 MiB is refused before any
byte is accepted. So a peer can make this device buffer at most 4 MiB per stream in memory, and the
receiving side's hashing buffer is bounded by the same 256 MiB limit as local adds. The limit exists
because WebCrypto hashes one in-memory buffer (decision 6); adds above it are refused with a message.

## 8. Traps and re-instantiation (as built)

On a trap while running: bump the epoch, drop the queue, close all links, wait for the in-flight
save, create a new instance and start again from the stored record with the same identity; the
user sees a "restarted" banner. A trap during start-up stops at once with an error screen (no
automatic retry: a trap on the stored state would loop); the user can retry. Three traps in five
minutes stop sync. **E2E:** the driver wraps the instance's exports so that `ls_process` first calls
`ls_input(0xffffffff)` inside the module — a real trap (Lean's out-of-memory abort) — then
`trap-mid-sync-reinstantiates` checks one trap, two instances, the dead one never called again
(a call would count as a second trap), and that sync completes; `trap-at-startup-does-not-loop`
makes every call trap from page load on and checks one instance, one trap, an error screen, and a
working manual retry.

## 9. UI (as built)

As in the wireframe of the plan, plus a "saving… / saved / not saved" indicator. Rules: a file is
"complete" only when Lean reports every version present, i.e. verified and stored; a missing version
shows fetching (from whom), queued, waiting ("nobody reachable has it") or "not yet available";
conflicts list their versions with Keep / Download, and Keep both for two versions (the other one
becomes `name (2).ext`). Adding under an existing name supersedes the versions shown; Delete
supersedes the versions shown. Flat names only: folder drops are refused with a message; a name
containing `/` that arrives from another device is shown in full with the part up to the last `/`
dimmed, and downloads under its last component (nothing below the UI restricts paths). Files over
256 MiB are refused with a message giving the reason.

## 10. Tests and results

Unit (`node --test test/unit/*.test.mjs`): 28 tests — codec vs Lean (5), links (12), core with the
real engine (8), view (3). Engine checks: §0. End-to-end (`node test/e2e/run.mjs`): 17 scenarios,
44 runs; browsers per run in the table below (Chromium 154.0.8037.92, Firefox 146.0, Firefox ESR
140.16.0esr, all headless, each device its own browser process and profile).

| Scenario | Configurations (device A + B [+ C]) |
|---|---|
| `add-replace-delete-download` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146; Firefox ESR 140 + Firefox 146; Chromium 154 + Firefox 146 |
| `offline-edits-both-sides` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146; Firefox 146 + Chromium 154 |
| `conflict-keep-one-and-keep-both` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146; Chromium 154 + Firefox 146 |
| `edit-vs-delete` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146; Firefox 146 + Chromium 154 |
| `three-device-chain` | Chromium 154 + Chromium 154 + Chromium 154; Firefox 146 + Firefox 146 + Firefox 146; Chromium 154 + Firefox 146 + Chromium 154 |
| `disconnect-mid-transfer-and-resume` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146; Chromium 154 + Firefox 146 |
| `corrupted-blob-and-garbage-message` | Chromium 154 + Chromium 154; Firefox 146 + Chromium 154 |
| `storage-failure` | Chromium 154 + Chromium 154; Firefox 146 + Chromium 154; Firefox ESR 140 + Firefox 146 |
| `reload-and-kill-mid-session` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146; Chromium 154 + Firefox 146 |
| `second-tab-lock` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146 |
| `startup-failure-and-reset` | Chromium 154 + Chromium 154; Firefox 146 + Chromium 154 |
| `rollback-detected-then-new-identity` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146; Firefox 146 + Chromium 154 |
| `same-replica-id-refused` | Chromium 154; Firefox 146 |
| `trap-mid-sync-reinstantiates` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146 |
| `trap-at-startup-does-not-loop` | Chromium 154; Firefox 146 |
| `repeated-edits-heap-bound` | Chromium 154; Firefox 146 |
| `file-size-limit-and-folder-drop` | Chromium 154; Firefox 146 |

`same-replica-id-refused` runs two profiles of one browser, the second a copy of the first.
App bugs found by these tests and fixed: start-up hung in Firefox on `storage.persist()` (permission
prompt); a host-driven write-retry loop while saves failed (§3); a restart lost the pending file-list
refresh (§3); on `rollbackDetected` the Add button stayed enabled until the next status reply (a
false state; seen once in 44 runs, Firefox + Chromium).

Storage failures, per browser: Firefox 146 and ESR 140 — real (quota pref `dom.quotaManager.
temporaryStorage.fixedLimit` = 20 MiB, storage filled with random data) for both OPFS and the
IndexedDB record; Chromium — OPFS real (CDP `Storage.overrideQuotaForOrigin`), IndexedDB record
**injected** by the driver (an init script aborts the transaction writing `record`), because
Chromium 154 does not apply the override to IndexedDB.

## 11. Deviations forced by the browser, and what is not done

Deviations from sync-design §8 / the plan:
1. **Retries are event-driven** (a protocol property made visible by the browser): any event retries
   a failed save, so incoming traffic causes failed writes in bursts (138 in one test). The host adds
   no events of its own while saves fail.
2. **Firefox `InvalidStateError` after a quota abort**: the host reopens the IDB connection and
   repeats that one write (§5). Not a retry of Lean's persist in Lean's sense: the failed call wrote
   nothing.
3. **Durability**: IDB `strict` and OPFS `close()` are the strongest available, not a documented
   fsync everywhere (unchanged risk).
4. **`storage.persist()`** is requested without waiting (Firefox prompts the user).
5. **Chromium storage-failure test** injects the IndexedDB failure (above).
6. **A blob that fails to store locally** (disk full) must be reported as `blobFailed`, which Lean
   records as "this peer lacks it" for the session; after space is freed it is fetched again only in
   a later session (reconnect, or toggling online). No event says "my storage failed".

Planned in the stage-1 note and not done:
- Relay faults are injected at the relay, not by a "corrupting relay mode" per link direction for
  every frame type; a garbage-message test covers protocol errors.
- No e2e test restores a *whole* backup (record plus blobs); the rollback test restores the record.
- The "kill mid-persist → add lost" branch is accepted but was not observed (timing).
- Firefox ESR 140 runs only in some scenarios (basic, storage failure); Chromium and Firefox 146 run
  all of them.
- Downloads are verified from the Blob the app hands to the browser (captured by an init script),
  not from a file written to disk.

## 12. Risks and open questions

1. Browser durability is best-effort (§5); eviction is mitigated by `storage.persist()`, and an
   evicted device restarts as a new replica (its unsynced changes are lost).
2. The engine runs on the main thread: large merges and snapshots may cause 10–100 ms jank; moving
   it to a Worker changes only `engine.mjs` and the call sites become async (the one-at-a-time
   guarantee would then rest on the pump alone).
3. A peer-triggered deterministic trap is contained by the restart limit, not prevented.
4. Files are limited to 256 MiB (WebCrypto hashes whole buffers); serving and downloading also read a
   whole file into memory, one at a time.
5. One outgoing blob at a time per device: a slow peer delays others.
6. Accepted limits carried over: whole-state send per edit and peer, no blob GC, no file sizes in the
   index.
7. The relay client and the dev server are unauthenticated; the next task (WebRTC) replaces both.
