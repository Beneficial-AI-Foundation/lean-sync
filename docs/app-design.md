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
test/proc.mjs                process groups and the per-run temporary directory for every browser test
test/mutations.mjs           mutation audit of the host-obligations table (§4)
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

Rules found necessary while building or in review:
- **The save is acknowledged only from the transaction's `complete` event.** A failed request
  aborts its transaction (the default action, never prevented); `persisted` follows only from
  `complete`, so a state is never advertised unless every request of its write succeeded.
  *(Review P1: a first version called `preventDefault()` on the bubbled request error, which keeps
  the transaction alive: it could reach `complete` without the record, and `persisted` was then
  sent for a state that was never stored. The storage-failure tests missed it because both the
  real quota failure and the injected one abort the whole transaction; a request-level fault test
  now exists.)*
- **The persist slot is cleared before the acknowledgement is emitted, and only if it still holds
  the completing write.** Processing `persisted` can start the next persist; a restart waits for
  whatever write the slot holds. *(Review P1: the slot used to be cleared in a `finally` after the
  emit, which could clear the next write's entry, so a restart read storage without waiting.)*
- **A restart leaves `running` before anything else** (no edits, no pump, no queries while it
  waits for the in-flight write). *(Review P2.)*
- **Supersession is what the user was shown.** Add, replace, delete, keep and keep-both supersede
  exactly the versions displayed when the user acted, captured synchronously in the UI and passed
  to the core before any await. A version that arrives later — e.g. a peer's edit during an upload —
  is not superseded and becomes a conflict. *(Review P1: the add read the versions after storing
  and hashing, so a peer's edit arriving meanwhile was silently removed.)*
- **No host-generated events while saves fail.** Every event makes Lean retry the write, and the
  UI's refresh queries are events; the first version therefore spun at 16 failed writes per second.
  While `saveFailed` holds, UI queries are deferred to the back-off nudge (1, 2, 4 … 60 s, growing
  only with the nudges). Real events still cause retries (§11, protocol consequence A).
- **A restart cancels pending refreshes** (a stale debounced query of the old epoch was dropped
  and the new machine's file list was never requested).

Epochs: a restart increments the epoch; completions of an older epoch are dropped, except that a
blob that became durable is re-reported as `blobsStored [h]`. Stale `persisted`/`persistFailed`
never reach the new machine (its tags restart at 0).

## 4. Host obligations

Audited by mutation (`node test/mutations.mjs`): for each row the mechanism was removed or broken
in the app's source and the named test was run (e2e in Chromium); **36 of 36 mutants were caught**.
"Mutant" names the break that was tried.

| Obligation (sync-design §8, decision 7) | Mechanism | Test (fails when the mechanism is broken) | Mutant |
|---|---|---|---|
| Persist atomically, then `persisted tag SHA-256(bytes)` | one strict `readwrite` transaction; resolved only from `complete`; digest of exactly those bytes | unit `core` (no `persisted` while the save is held) | ack without awaiting the save |
| Never acknowledge a failed write | request errors abort the transaction (not prevented); `abort`/exception → reject → `persistFailed` | e2e `record-request-error-not-acknowledged` (request-level fault: no ack, record unchanged, peer unaffected); unit `core`; e2e `storage-failure` | `preventDefault` on request errors; `persistFailed` dropped |
| Retry after back-off; surface `saveFailed` until resolved | nudge timer; no host events while failing; banner + "not saved" until a later save completes | unit `core` (no event storm); e2e `storage-failure` | host refresh while failing; banner removed |
| One persist in flight; a restart waits for it | Lean issues one; the host slot is cleared only by its own write | unit `core` (back-to-back persists, then a trap) | slot cleared after the emit |
| Blob verified and durable before `blobStored`; local blob before `localOp` | `incoming/` → hash of the stored bytes → `move()` (replacing a damaged copy) → emit | unit `links`; e2e `damaged-or-missing-blob-recovers`, `corrupted-blob…` | finish without hash; keep the damaged copy |
| Supersede only what the user was shown | versions captured by the UI at the click, before any await | unit `core`; e2e `peer-edit-during-upload-becomes-conflict` | versions read after the upload |
| One owner (Web Lock) | `navigator.locks.request(…, {ifAvailable:true})`, held for the tab's life | e2e `second-tab-lock` | lock ignored |
| Start-up: `init` / `initFresh` / `init newId` | `rotateId` honoured; cleared with the first record under the new id | unit `core` (rollback restart) | `rotateId` ignored |
| Inventory before any peer | `setAccepting(true)` after `init` + all `blobsStored` chunks | unit `core` (accepted after 3 start-up events) | accept before the inventory |
| `startupFailed` → error; reset only after confirmation | failure screen; reset only through the confirmed dialog | unit `core`; e2e `startup-failure-and-reset` | silent reset on a bad record |
| `sendAgain` | decoder, within one envelope | unit `codec` (vectors) | wrong bytes for `sendAgain` |
| `send` to a closed peer dropped; `close` after queued bytes | per-link queue with a CLOSE marker | unit `links` | close at once |
| `fetch`: only those hashes, verify, size limit, bounded buffering | expected set; START > 256 MiB refused; credit; mismatch → `blobFailed`; link loss discards | unit `links`; e2e `disconnect-mid-transfer…` | no size limit; no credit check |
| `serveBlob`: unreadable → abort + `blobLost` | read, verify, stream; else ABORT + `blobLost` | unit `links` | `blobLost` not emitted |
| `blobLost` when a present blob is found gone | serving, and downloading (missing file or digest mismatch; other read errors are transient) | e2e `damaged-or-missing-blob-recovers` | missing file not reported |
| `connected`/`disconnected` once; PeerIds never reused | page-lifetime counter | unit `links` | ids reused |
| `received`: one complete message ≤ limit | reassembly; over the limit closes | unit `links` | no limit |
| Persist answers only for persists given | epochs | unit `core` | stale epochs delivered |
| Rollback mode; restart only on click + confirm | banner, edits disabled, dialog, `init newId bytes` | e2e `rollback-detected-then-new-identity` | edits allowed in rollback |
| The single serving slot is always released | END right after START for an empty blob; ABORT from the receiver when it cannot create the file; release on END, receiver ABORT, link close, unreadable blob; abort after 60 s without credit | e2e `empty-file-then-normal-file`, `incoming-file-creation-fails-then-next-file`; unit `links` (all six paths) | no END for an empty blob; sink failure ignored; no stall timeout |
| A blob is replaced only by a verified copy, never deleted first | an intact existing copy is kept; a damaged one is overwritten by one `move()` | e2e `existing-blob-kept-when-replacement-fails` | delete, then move |
| Row statuses follow request planning | `pending` re-queried on peer changes and on `pendingSummary` | e2e `peer-leaves-mid-fetch-row-updates` | refresh removed |
| Transport only to the serving origin | no URL parameter selects the relay | e2e `relay-parameter-ignored` (a second relay that accepts any origin sees no connection) | `?relay=` honoured |
| Re-instantiate after a trap; no loop | §8 | e2e `trap-mid-sync…`, `trap-at-startup…`; unit `core` | no restart; start-up trap retried; restart stays `running` |
| Refuse a peer with our own replica id | host HELLO check before Lean | unit `links`; e2e `same-replica-id-refused` | check removed |
| Nothing else persisted | IDB holds the record, `rotateId`, the label | review only (not mutation-tested) | — |

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
- **Replacing a blob.** `move()` onto an existing name overwrites it in Chromium 154, Firefox 146
  and ESR 140 (probed). `publish` keeps an intact existing copy (the new one is dropped) and
  overwrites a damaged or unreadable one with a single `move()`; it never deletes first. What we get:
  a failed `move()` leaves the old file in place; a tab closed during the move leaves the old or the
  new file under that name (the browsers do not document crash atomicity for `move()`); the temp
  copy left in `incoming/` is deleted at start-up, and an old damaged copy is detected again when it
  is served or downloaded (`blobLost`, then fetched again). *(Review: the first fix for the damaged
  copy deleted it before the move, so a failed move or a closed tab left the index with no copy.)*
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

Access (review P1: loopback is not access control — any page open in the same browser can reach
127.0.0.1): the relay accepts a WebSocket upgrade only if its `Origin` is the server's own origin
(`http://127.0.0.1:<port>` or `http://localhost:<port>`; no `Origin`, no upgrade); devices that name
no room join a random 128-bit room chosen when the server starts; the admin API is off unless the
server is started with `--admin` (the tests do) and refuses requests carrying a foreign `Origin`.
Unit `relay` checks all four. There is no URL parameter to choose the relay: the app always uses
`/relay` on the origin that served it. *(Review P1: a `?relay=` parameter let a crafted link
connect the profile's files to someone else's endpoint.)*

## 7. Blob streaming and backpressure (as built)

One outgoing blob at a time per device: read whole (≤ 256 MiB), verify, START, then DATA frames
interleaved behind Lean messages while the link buffer is under 1 MiB and the receiver's credit
allows; END. The receiver grants credit up to 4 MiB beyond what it has written; bytes beyond the
credit, or beyond the announced size, fail the stream; a START above 256 MiB is refused before any
byte is accepted. So a peer can make this device buffer at most 4 MiB per stream in memory, and the
receiving side's hashing buffer is bounded by the same 256 MiB limit as local adds. The limit exists
because WebCrypto hashes one in-memory buffer (decision 6); adds above it are refused with a message.

**The single serving slot.** Because outgoing blobs are served one at a time per device, any
transfer that never ends blocks every later file for every peer. Every way out, and its test:

| How a transfer ends | Mechanism | Test |
|---|---|---|
| normal | END after the last DATA | e2e (every sync) |
| empty blob (no credit will ever come) | END right after START | unit `links`; e2e `empty-file-then-normal-file` *(review P1)* |
| receiver cannot create the file | receiver: `blobFailed` + ABORT; sender: releases on ABORT | unit `links`; e2e `incoming-file-creation-fails-then-next-file` *(review P1)* |
| receiver aborts for another reason (bad size, over credit, unexpected) | sender releases on ABORT | unit `links` |
| receiving link closes mid-transfer (or ABORT lost with it) | link close releases the slot | unit `links` |
| blob gone or unreadable on the sender | ABORT + `blobLost`, release | unit `links`; e2e `damaged-or-missing-blob-recovers` |
| receiver stops granting credit without saying why | sender aborts after 60 s without credit | unit `links` (short timeout) |

A lost ABORT on a live link cannot happen (links are reliable and ordered); if a link breaks, its
close releases the slot.

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

Unit (`node --test test/unit/*.test.mjs`): 39 tests — codec vs Lean (5), links (19), core with the
real engine (10), relay access (2), view (3), plus the mutation audit of §4. Engine checks: §0.
End-to-end (`node test/e2e/run.mjs`): 25 scenarios, 62 runs; browsers per run in the table below (Chromium 154.0.8037.92, Firefox 146.0, Firefox ESR
140.16.0esr, all headless, each device its own browser process and profile).

| Scenario | Configurations (device A + B [+ C]) |
|---|---|
| `empty-file-then-normal-file` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146; Chromium 154 + Firefox 146 |
| `incoming-file-creation-fails-then-next-file` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146 |
| `peer-leaves-mid-fetch-row-updates` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146 |
| `existing-blob-kept-when-replacement-fails` | Chromium 154; Firefox 146 |
| `relay-parameter-ignored` | Chromium 154; Firefox 146 |
| `record-request-error-not-acknowledged` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146 |
| `peer-edit-during-upload-becomes-conflict` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146; Chromium 154 + Firefox 146 |
| `damaged-or-missing-blob-recovers` | Chromium 154 + Chromium 154; Firefox 146 + Firefox 146 |
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

**Test hygiene.** Every browser is started in its own process group and killed as a group on every
exit path (normal, failure, scenario timeout, SIGINT/SIGTERM, uncaught error); all temporary
profiles live under one run directory (`$LEANSYNC_TEST_DIR`, else a `leansync-test-*` directory
under `$TMPDIR`), removed at the end with retries. Each runner then reports `hygiene:` (no process
left, directory removed) or `CLEANUP FAILED`, separately from the test results (exit 1 = test
failure, 2 = cleanup failure only); `scripts/test-app.sh` additionally checks that no process
mentioning its run directory is alive and that the directory is gone. *(Review: a Chromium helper
process still writing into the profile made the profile removal fail with `ENOTEMPTY` in about one
run in three, and a Firefox from a timed-out scenario was left running.)*

Storage failures, per browser: Firefox 146 and ESR 140 — real (quota pref `dom.quotaManager.
temporaryStorage.fixedLimit` = 20 MiB, storage filled with random data) for both OPFS and the
IndexedDB record; Chromium — OPFS real (CDP `Storage.overrideQuotaForOrigin`), IndexedDB record
**injected** by the driver (an init script aborts the transaction writing `record`), because
Chromium 154 does not apply the override to IndexedDB. The request-level fault of
`record-request-error-not-acknowledged` is injected the same way in both browsers (the write of
`record` becomes an `add()` on an existing key, which fails with `ConstraintError`).

## 11. Deviations forced by the browser, and what is not done

Deviations from sync-design §8 / the plan forced by the browser:
1. **Firefox `InvalidStateError` after a quota abort**: the host reopens the IDB connection and
   repeats that one write (§5). The failed call wrote nothing, so this is not a second write.
2. **Durability**: IDB `strict` and OPFS `close()` are the strongest available, not a documented
   fsync everywhere (unchanged risk).
3. **`storage.persist()`** is requested without waiting (Firefox prompts the user).
4. **Chromium storage-failure test** injects the IndexedDB failure (above).

Consequences of the protocol design, not host bugs (left as they are in the host; proposals for the
user):

**A. A failed save is retried on every event.** `step` sets `holdPersist` on `persistFailed` and
clears it at the end of the same step (sync-design §3, `persistFailed_no_retry_in_step`), so the
*next* event of any kind issues a new `persist` with the latest state. The host can delay only its
own events; peer messages and blob completions keep arriving. Observed: in the Firefox quota test,
while 150 files arrived from a peer, 131–139 writes were attempted and failed within about a
second. Each is cheap (the write is refused), but the host cannot apply a back-off.
*Possible `LeanSync` change:* keep `holdPersist` set across events until the host sends a new event
`retrySave` (event tag 13). `persistFailed` would then mean "stop saving until told", and the host
would own the back-off (it already has the timer and the "Retry now" button). Effects on the
proofs: `persistFailed_no_retry_in_step` generalises to "no `persist` between `persistFailed` and the
next `retrySave`"; `save_before_send`, `persist_one_in_flight` and executability are unaffected,
because nothing new is published while held; the local-settling statements need the hypothesis that
the host eventually sends `retrySave`. The event envelope changes, which is host↔Lean only (no peer
compatibility issue).

**B. A local storage failure looks like a peer failure.** The only event for a transfer that did
not end in a stored blob is `blobFailed p h`, which records `h` as lacking at `p` for the rest of
the session (sync-design §5). When the bytes arrived intact but *this* device could not store them
(quota, I/O error), the host must still send `blobFailed`; after space is freed the blob is fetched
again only in a later session (reconnect, or toggling "online"). The file shows "waiting: nobody
reachable has it", which is not true.
*Possible `LeanSync` change:* a distinct event `blobStoreFailed h` (tag 14) that removes `h` from
the session's `inflight` without adding it to `lacks`, and parks it in a node-level `localFailed`
set that the planner skips until `retrySave` (A) or a new event `storageAvailable`; a pending
status `localFailure` (and a fourth `pendingSummary` count) would let the UI say "could not be
stored on this device". Effects: `step_plans_blobs` gains a disjunct for parked hashes; the
effects envelope (pending reply, summary notice) changes, again host↔Lean only.

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
5. One outgoing blob at a time per device: a slow peer delays others (a stalled one by at most 60 s).
6. Accepted limits carried over: whole-state send per edit and peer, no blob GC, no file sizes in the
   index.
7. The dev relay accepts only its own origin and uses a random room, but is otherwise unauthenticated;
   the next task (WebRTC) replaces it.
