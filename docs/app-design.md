# Browser app (single machine): design note

Branch `browser-app` · Lean 4.36.0 · Emscripten 6.0.5 (Debian) · wasm64 only. Stage 1: the engine
is built and checked; this note is the plan for stage 2 and is **not built yet**. Specs:
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
budget with states much larger than 20k entries; replies (`snapshot`, `pending`) are covered by the
smoke test but not by the replay (the simulator issues no queries).

**Trap probe.** An allocation of 4 GiB (`_ls_input(0xffffffff)`) makes Lean print `INTERNAL PANIC:
out of memory` and Emscripten throw `ExitStatus`; afterwards the instance still *accepts* calls, so
the wrapper (`app/js/engine.mjs`) marks an instance dead on any exception and refuses further calls.
Under Node, Emscripten's exit also sets the process exit status; tests will pass a `quit` override.

## 1. Module layout

```
app/                         the shipped static site (copied with the wasm into build/site/)
  index.html, app.css
  js/main.mjs                boot: lock, storage, engine, core, transport, UI
  js/engine.mjs              wasm instance wrapper: sync bytes→bytes, dead after any trap   [exists]
  js/codec.mjs               event encoder, effects/notice/reply decoder                    [exists]
  js/core.mjs                event queue, pump, effect executor, epochs, start-up, trap recovery
  js/storage.mjs             IndexedDB record + OPFS blob store, inventory, fault hooks (test mode)
  js/links.mjs               link ↔ PeerId, host framing, message fragmentation, reconnect policy
  js/blobs.mjs               blob streams: sender scheduler, receiver with credits, verification
  js/view.mjs                snapshot + pending → file rows (pure; unit-tested)
  js/ui.mjs                  DOM: file list, banners, dialogs, drag-and-drop
  js/transport/relay.mjs     dev transport: WebSocket relay client (implements the interface, §6)
dev/serve.mjs                dev/test only: static server + WebSocket relay + admin API, 127.0.0.1
test/                        Node unit tests, engine checks [exist], e2e driver and scenarios
```
No framework, bundler or npm package; the relay's WebSocket server and the CDP/BiDi clients are
hand-written on Node's built-ins. The spike demo (`WasmDemo.lean`, its two lakefile targets,
`wasm/index.html`, `serve.mjs`, `check-node.mjs`, `host.mjs`, `shim.c`, `check-browsers.sh`) is
removed in stage 2 unless you want it kept.

## 2. Codec: hand-written, differentially tested against Lean

The format is small (15 event forms, 8 effect forms, 14 notices, 3 replies), version-tagged, and
its Lean side is proved; a generator (Lean metaprogram emitting JS) would be more code than the
codec and itself unverified. So `codec.mjs` is hand-written, and kept in step by tests that use
**bytes produced by the current Lean build on every run**: (a) the trace replay above (every real
envelope must decode); (b) a new `sync-tests vectors` subcommand writes the codec tests' random
events and effect lists (all constructors, `sendAgain` included) as JSON plus Lean's bytes — JS must
encode each event to identical bytes and decode each envelope to the JSON; (c) JS must reject every
proper prefix of each envelope. A format change in Lean breaks (b) at once. The decoder resolves
`sendAgain p` to the last state message written in full *in the same envelope* (Lean's `effsGo`
starts each envelope with no state), sharing the same `Uint8Array`.

## 3. Event loop

One `Core` owns the engine, a FIFO of events, and an `epoch` number. Everything that is an event —
UI operations, transport messages and link changes, storage and hash completions, back-off timers,
UI queries — calls `core.enqueue(ev)`. A single pump drains the FIFO: **dequeue one event, encode,
call `engine.process` (synchronous), decode, then execute every effect in order, synchronously**.
Executing an effect never awaits: it queues bytes on a link, closes a link, or *starts* an async
job (IndexedDB write, OPFS write, file read) whose completion later enqueues an event tagged with
the epoch that started it. Because `process` is synchronous, JS is single-threaded and the pump is
the only caller (the wrapper also throws on re-entry), events reach Lean strictly one at a time,
and all effects of event *i* are dispatched before event *i+1* is processed — per-link order is the
effect order. The engine runs on the main thread: a 20k-file `putMany` + persist took 54 ms under wasm,
a 20k-entry merge ~10 ms natively (not yet isolated under wasm); moving it to a Worker later
changes only `engine.mjs`.

Epochs: a restart (trap recovery, rollback restart, reset) increments the epoch. Completions of
an older epoch are dropped, except that a blob that became durable is re-reported as
`blobsStored [h]`; `persisted`/`persistFailed` of an older epoch are never delivered (the new
instance's tags restart at 0, so a stale tag would be misattributed).

## 4. Host obligations

| Obligation (sync-design §8, user decision 7) | Mechanism | Test |
|---|---|---|
| Persist the record atomically, then answer `persisted tag SHA-256(bytes)` | one IDB `readwrite` transaction, `durability:'strict'`, puts `{replica, state}`; digest of exactly the bytes put; event enqueued on `complete` | core unit test with a fake store whose commits are held (no `persisted` before commit); e2e kill-during-persist |
| Never acknowledge a failed write | `error`/`abort`/exception → `persistFailed tag` | fault hook + real quota (Chromium CDP `Storage.overrideQuotaForOrigin`, Firefox `dom.quotaManager…fixedLimit` pref) |
| Retry after back-off; surface `saveFailed` | timer 1, 2, 4 … 60 s enqueues `query status`; "Retry now" button; banner until a later `persisted` | e2e storage failure: banner shown, peers receive nothing new, recovery after quota lifted |
| One persist in flight, no reordering | guaranteed by Lean; host asserts and logs if violated | core unit test |
| Blobs verified and durable before `blobStored`; local blob before `localOp` | stream → `incoming/<rand>`, close, hash, `move()` to `blobs/<hex>`; only then enqueue; local add = same path, then `putMany` | unit (fake OPFS); e2e add then kill before op: orphan blob, no entry |
| Nothing else persisted | IDB holds only the record, a `rotateId` flag and the device label (host-level, §5) | review |
| One owner of the storage | Web Lock `leansync-owner`, `ifAvailable`; a second tab shows "Open in another tab" and starts nothing | e2e second tab in the same profile |
| Start-up: record → `init id bytes`, none → `initFresh newId`, cannot vouch → `init newId bytes` | `rotateId` flag set on `rollbackDetected` (and by reset); cleared in the same transaction that writes a record under the new id | e2e reload; rollback scenario (restore an older IDB copy) |
| Inventory before any peer | first ≤10k hashes in `init`, rest as `blobsStored` chunks; transport started only after the last chunk is processed | core unit test (no `connected` before last chunk); e2e reload with many blobs |
| `startupFailed` → error, reset only on confirmation | error screen: Retry, or Reset (dialog states that unsynced changes are lost) → `initFresh newId`, blobs kept | e2e: corrupt the record bytes in IDB, reload |
| `sendAgain` | decoder (§2) | codec vectors |
| `send` to a closed link dropped silently | link lookup by PeerId; missing → drop | core unit test |
| `close` after queued bytes | CLOSE frame queued behind data; `disconnected` enqueued when the link is gone | e2e protocol error (garbage injected by the relay admin API) |
| `fetch`: send `want`, accept only those hashes, verify hash and size, report | per-link expected set; unexpected stream → abort; mismatch, abort or > size cap → `blobFailed p h`; link drop mid-stream → delete partial, report nothing | unit; e2e corrupting relay mode; e2e disconnect mid-transfer |
| `serveBlob`: unreadable → abort frame + `blobLost` | read, hash (also catches bit rot: delete file), stream; failure → ABORT + `blobLost h` | e2e: delete/corrupt a blob file in OPFS, peer asks |
| `connected`/`disconnected` once each; PeerIds never reused | page-lifetime counter, never reset (not even across engine restarts) | core unit test |
| `received`: one complete message ≤ `maxMessageBytes` | reassembly of MSG fragments; overflow → close link | unit |
| `persisted`/`persistFailed` only for persists given | epochs (§3) | core unit test with a trap mid-persist |
| Rollback mode surfaced | banner; edits disabled in UI; `rotateId` written at once; "Restart with a new identity" re-instantiates with `init newId bytes` | e2e rollback scenario |
| Discard and re-instantiate after a trap (carried 1) | §8 | e2e with a real trap; Node wrapper test |

## 5. Storage schema and crash consistency

IndexedDB `leansync`, store `kv`: `record` = `{v:1, replicaHi, replicaLo (BigInt), state:Uint8Array}`;
`rotateId` = true when the next start must use a fresh id; `label` = device name. OPFS:
`blobs/<64 hex>` (complete, verified), `incoming/<random>` (partial; emptied at start-up).
`navigator.storage.persist()` is requested at first start (result shown under "Storage").

- *Tab dies mid-persist:* the transaction is atomic: the old or the new record survives. Neither
  was sent unacknowledged (save-before-send), so restarting from either is safe under the host rule.
- *Tab dies after a blob was moved into `blobs/` but before `blobStored`:* the start-up inventory
  reports it. *Before the move:* the partial file in `incoming/` is deleted at start-up and the blob
  is fetched again. *During a local add, before `putMany`:* an orphan blob, no entry; the user re-adds.
- *Storage partly evicted:* record without blobs → blobs show as missing and are re-fetched; blobs
  without a record → `initFresh` with a new id, blobs reported (no GC, as decided).
- *Durability limits:* `strict` IDB durability and OPFS `close()` are the strongest the platform
  offers but are not a documented fsync guarantee everywhere (risk 2).

## 6. Transport interface and the test transport

```js
transport.start({ onLink(link) }) / stop()
link = { label, send(frame: Uint8Array), close(), bufferedAmount, onFrame(cb), onDrain(cb), onClose(cb) }
```
Ordered, reliable byte frames per link, plus a buffered-amount signal for backpressure — the
`RTCDataChannel` model, so WebRTC replaces only `transport/relay.mjs`. Frames are ≤ 16 KiB (safe
for data channels). The host framing on a link (`links.mjs`): `MSG more:bool bytes` fragments of
Lean messages; `BLOB_START hash size`, `BLOB_DATA hash bytes`, `BLOB_END hash`, `BLOB_ABORT hash`;
`CREDIT hash n`; `CLOSE`. Lean never sees frames.

**Test transport: a WebSocket relay** in `dev/serve.mjs` (127.0.0.1 only, never shipped). Each page
opens one WebSocket to it; the relay announces devices present in a room, the host asks to link to
a device (the lower label initiates; backoff on failure; no automatic re-link after `sameReplicaId`
or `incompatible`), and the relay multiplexes `[linkId][frame]` and reports link closure to both
ends. It genuinely crosses browser profiles and browsers (each device has its own profile directory
and storage; a Chromium device can sync with a Firefox one). The relay pauses reading a sender's
socket while the receiver's is congested, so TCP pushes back to the sender's `bufferedAmount`
(polled, since WebSocket has no drain event). An admin HTTP API lets tests set the allowed topology
(chain A–B–C), cut links at a byte offset, and inject garbage or corrupted blob bytes. BroadcastChannel
was rejected: same-origin tabs share storage.

## 7. Blob streaming and backpressure

Files go whole, in 16 KiB `BLOB_DATA` frames. **Sender:** one blob at a time per link, chunks
interleaved with Lean messages (messages first), produced only while `bufferedAmount` < 1 MiB
**and** the receiver's credit allows. **Receiver:** grants 4 MiB of credit per stream, extending it
as chunks are written to `incoming/`, so receiver memory is bounded even on a transport that cannot
pause reads (data channels). At `BLOB_END`: close the file, check the size, read it and hash it with
WebCrypto, `move()` it, enqueue `blobStored h (some p)`. Since WebCrypto has no incremental digest,
hashing needs the whole file in memory once (risk 1); a per-file cap (proposed 256 MiB, rejected at
add with a message, `blobFailed` on receive) bounds that. Resume after a disconnect means re-fetching
the whole blob (Lean re-plans on `disconnected`).

## 8. Traps and re-instantiation

On `EngineTrap`: stop the pump; bump the epoch; drop the queue; close every link; wait for the
in-flight persist (at most one) to settle; create a new instance; run start-up as at page load
(record, inventory, `init`), then restart the transport (new links, new PeerIds). The dead instance
is never called again (the wrapper throws `EngineDead`). More than 3 traps in 5 minutes → stop and
show an error with the diagnostic log (a trap triggered by a peer's message would otherwise loop).
Test hook (test mode only): force a real trap via the out-of-memory path of §0.

## 9. UI

```
┌ LeanSync ───────────────────────────── this device: laptop (3fa2c1d0) ┐
│ [ Add files… ]  drop files anywhere           Storage: persistent ✓   │
│ ⚠ Changes could not be saved (quota). Retrying in 8 s.  [Retry now]   │  banners: saveFailed,
│ Peers: phone (91be…) in sync · tablet (07c4…) syncing                 │  rollback, trap restart
│ Pending: 3 fetching · 1 queued · 2 waiting                            │
├───────────────────────────────────────────────────────────────────────┤
│ notes.txt          12 KB   complete            [Download] [Delete]    │
│ photo.jpg           —      fetching from tablet                       │
│ report.pdf          —      waiting (nobody reachable has it)          │
│ plan.md                    CONFLICT  ▸ version a1b2 (12 KB) [Keep][↓] │
│                                      ▸ version 9c0d (14 KB) [Keep][↓] │
│                                      [Keep both]                      │
└───────────────────────────────────────────────────────────────────────┘
```
Add (picker or drop; names NFC-normalised) = `putMany` superseding the versions shown for that
name, i.e. adding under an existing name replaces it. Delete = `deleteMany` with the versions
shown (not `none`, so a version that arrived unseen survives). Keep = `putMany` of that hash
superseding all shown versions; Keep both = one `putMany` that also writes the other version under
`name (2).ext`. Download reads, verifies and saves via an object URL. Status comes from `snapshot`
(re-queried, debounced, on `indexChanged`) and `pending` (on `blobsChanged`); sizes come from OPFS
(the index has none). Rollback disables the edit controls; `startupFailed` and the lock replace the
whole page.

## 10. Test plan

**Node unit** (`node --test`, real wasm where Lean is involved): codec vectors and truncation (§2);
framing and reassembly; view model; core with fake storage/transport and the real engine — event
ordering, epochs, inventory before connect, persist hold/fail, trap recovery; engine replay, heap
bound and scale (existing). **E2E** in headless Chromium 154 and Firefox 146 (ESR 140 where cheap),
driven over CDP (Chromium) and WebDriver BiDi (Firefox, probed: works from Node's built-in
`WebSocket`); each device is a separate browser process with its own profile directory; one mixed
Chromium↔Firefox pair. Scenarios:
1. add / replace / delete / download (bytes compared with what the test generated);
2. both offline, edits on both, reconnect, converge; 3. concurrent edit → conflict → Keep, and Keep
both; 4. edit vs delete (edit survives); 5. three-device chain A–B–C (relay topology), C gets A's
blobs through B; 6. disconnect mid-transfer (relay cut at a byte offset), reconnect, complete;
7. storage failure (quota) → banner, nothing new sent, recovery; 8. reload mid-session and kill
mid-persist → state intact, sync resumes; 9. second tab in the same profile → lock message, first
tab unaffected; 10. corrupted record → `startupFailed` → confirmed reset; 11. rollback (restore an
older record copy) → banner, restart with new id, no data lost on the peer.
Carried-forward: (1) a forced trap mid-sync → new instance (counter checked), no call to the dead
one, sync completes; (2) every run gets random file names and contents from the test, and every
check compares against those, never against what the page reports; (3) repeated add/delete of one
file 300× in the browser → wasm heap growth between cycle 50 and 300 ≤ 1 MiB (plus the Node loop).

## 11. Risks and open questions for the user

1. **Hashing large files** (decision 6). WebCrypto cannot hash incrementally, so a file is hashed
   from one in-memory buffer: memory peak ≈ file size at add, receive, serve and download. Proposal:
   a 256 MiB per-file cap for this version. Alternative: a JS incremental SHA-256 (tested against
   WebCrypto), which lifts the cap but departs from "SHA-256 via WebCrypto". **Which?**
2. Browser durability is best-effort (see §5); eviction is mitigated by `storage.persist()`, and an
   evicted device restarts as a new replica (unsynced changes on it are lost).
3. Rollback: restart with a new id automatically, or only when the user clicks? I propose the
   button (edits are already blocked, nothing is lost by waiting).
4. Flat file list: names only, folders not supported in this version (folder drops rejected). OK?
5. Not yet verified in these browsers, to be probed first in stage 2: OPFS `FileSystemFileHandle.move()`
   and IDB `durability:'strict'` in Firefox 146/140, Chromium's CDP quota override. If `move()` is
   missing I will report before choosing a fallback.
6. The engine runs on the main thread; large merges and snapshots may cause 10–100 ms jank.
7. Peer-triggered deterministic traps are contained by the restart limit, not prevented.
8. Removal of the spike demo (§1), and `Tests/Sync.lean` gained `trace` (and will gain `vectors`)
   subcommands — test code only; `LeanCrdt/` and `LeanSync/` are untouched.
9. Accepted limits carried over: whole-state send per edit and peer, no blob GC, no file sizes in
   the index.
