# Sync protocol and wire format: design and status

Branch `sync-protocol` · Lean 4.36.0 · `Init` only · library `LeanSync` (`LeanSync/`), built by
default next to `LeanCrdt`. The CRDT's definitions and theorem statements are unchanged.

**Status.** Everything is implemented and every theorem is proved: there is no `sorry`, `axiom`,
`native_decide`, `unsafe`/`implemented_by` or `partial` in `LeanCrdt/` or `LeanSync/`. The
headline theorems depend only on `propext`, `Classical.choice` and `Quot.sound`
(`scripts/check-proofs.sh` re-checks both claims). The protocol is tested natively by
`scripts/test-sync.sh` (§10). It has not been built for wasm; the C-shim change is in §1.

| File | Contents | Runtime? |
|---|---|---|
| `LeanSync/Types.lean` | messages, events, effects, session, node, machine | yes |
| `LeanSync/Bytes.lean` | byte-level parsers and writers (varints, fixed bytes, strings, lists) and their correctness | yes |
| `LeanSync/Wire.lean` | limits, `WireOk`, state and message codecs, round trip and canonicity | yes |
| `LeanSync/Sets.lean` | sorted hash sets: sort+dedup, one-pass difference | yes |
| `LeanSync/Step.lean` | the step function | yes |
| `LeanSync/EffectsWire.lean` | the effects envelope (Lean → host), with state payloads de-duplicated, and its proved round trip | yes |
| `LeanSync/Envelope.lean` | the event envelope (host → Lean), `process`, exported `processIO` | yes |
| `LeanSync/HostModel.lean` | what a host can carry out (`HostView`, `Executable`) | used by tests and a theorem |
| `LeanSync/StepProofs.lean`, `LeanSync/Laws.lean` | proofs; `Laws.lean` states the stage-1 theorems | proofs only |
| `Tests/Sync.lean`, `scripts/test-sync.sh` | unit, codec and fuzz, simulator, mutation check, scale, stack | tests |
| `scripts/check-proofs.sh`, `scripts/check-forbidden.sh`, `scripts/Axioms.lean` | forbidden-construct check (comment-aware) and `#print axioms` allowlist | check |

## 1. Shape and the wasm boundary

`step : Machine → Event → Machine × List Effect` is pure, total and deterministic. A `Machine` is
`uninit` or `running (n : Node)`. One exported function carries everything:

```lean
def process (m : Machine) (input : ByteArray) : Machine × ByteArray   -- encoded event in, encoded effects out
initialize machineRef : IO.Ref Machine ← IO.mkRef .uninit
@[export lean_sync_process] def processIO (input : ByteArray) : IO ByteArray  -- get, process, set
```

The machine lives in an `IO.Ref` between calls. `IO.Ref` is part of `Init`, and the code does no
other IO. A malformed input yields the effect list `[notify (badEvent e)]` and leaves the machine
unchanged.

**Every output decodes (proved, `process_output_decodes`).** For a machine satisfying the
invariant, whatever `process` returns is an effects envelope that `decodeEffects` decodes back to
exactly the effects the step emitted. So the host can always decode and carry out every effect,
and a session's `lastSent` is never advanced for a send the host could not receive. The size of
one envelope is bounded by design, not by a cap: all state messages sent in one step carry the
same published state, and the envelope writes it once (§6). A step's envelope therefore holds at
most two copies of a state (the persist and the shared state message), plus small messages and
any query reply.

**C-shim change, for the host task.** Do not apply it here, since `wasm/` is not touched.
Checked against the C that Lean 4.36 generates (`.lake/build/ir/LeanSync/Envelope.c`):
- **Declarations.** Declare `lean_object *initialize_lean_x2dcrdt_LeanSync_Envelope(uint8_t builtin);`
  and `lean_object *lean_sync_process(lean_object *input);`. The second takes **one** argument (no
  world token) and returns an **IO result**.
- **`lw_init`.** Call `initialize_lean_x2dcrdt_LeanSync_Envelope(1)` instead of the demo's
  initializer.
  - Its import closure is `Init`, `LeanCrdt.{Types,SortedList,VersionVector,State}` and
    `LeanSync.{Types,Bytes,Wire,Sets,Step,Envelope}`. It imports no `Std`, and none of the
    proof modules.
  - It also creates `machineRef`, unconditionally.
- **`lw_process`.** In place of `g_result = lean_wasm_demo_process(in)`:
  ```c
  lean_object *res = lean_sync_process(in);            /* consumes `in` */
  if (!lean_io_result_is_ok(res)) { lean_io_result_show_error(res); lean_dec(res); return 0; }
  g_result = lean_io_result_get_value(res); lean_inc(g_result); lean_dec(res);
  ```
  It cannot fail in practice, because `processIO` only reads and writes the ref.
- **JS host.** Unchanged: bytes in, bytes out, one call at a time.
  - After a trap, re-instantiate the module and start again with `init`, as the spike requires.
  - Edits that were never acknowledged as persisted are lost. They were never sent either, so
    reusing their dots is safe.

## 2. Types (`LeanSync/Types.lean`, abridged)

```lean
structure Digest where bytes : ByteArray; size_eq : bytes.size = 32   -- host SHA-256 of a stored record
structure PeerId where val : UInt32                                     -- one connection; never reused in a run

inductive Message where
  | hello (maxVersion : UInt8) (replica : ReplicaId) (digest : Digest)
  | digest (d : Digest) | state (d : Digest) (s : State)
  | want (hs : List Hash) | noBlob (hs : List Hash) | have (hs : List Hash)   -- sorted batches, 1..1024
  | bye (reason : CloseReason)

inductive Event where
  | init (self : ReplicaId) (stored : ByteArray) (blobs : List Hash)    -- restore from the stored record
  | initFresh (self : ReplicaId) (blobs : List Hash)                    -- empty index, fresh replica id
  | connected (p : PeerId) | disconnected (p : PeerId)
  | received (p : PeerId) (bytes : ByteArray)                           -- one complete Lean message
  | localOp (op : LocalOp)                                              -- putMany | deleteMany | resolve
  | persisted (tag : Nat) (digest : Digest) | persistFailed (tag : Nat)
  | blobStored (h : Hash) (src : Option PeerId) | blobFailed (p : PeerId) (h : Hash) | blobLost (h : Hash)
  | blobsStored (hs : List Hash)                                        -- a batch, e.g. the start-up inventory in chunks
  | query (q : Query)                                                   -- snapshot | pending | status

inductive Effect where
  | send (p : PeerId) (msg : Message) | close (p : PeerId) (reason : CloseReason)
  | persist (tag : Nat) (s : State)          -- store atomically, hash the stored bytes, answer persisted/persistFailed
  | fetch (p : PeerId) (hs : List Hash)      -- send `want hs` (bytes in the envelope), accept those streams
  | serveBlob (p : PeerId) (h : Hash)
  | notify (n : Notice) | reply (r : Reply)
```

The `Node` holds:
- `self` and `current`, the latest state, which may carry dots not yet persisted;
- `published`, the last acknowledged state together with its digest, and `inflight`, the one
  persist in flight;
- `nextTag` and `dirty`;
- `blobs`, the sorted set of present blobs, and `missing`, a sorted cache of the hashes referenced
  by `current` that are not present;
- `sessions`, sorted by peer;
- `rollback` and the last pending summary.

A `Session` holds:
- `helloSent`, and `peerReplica`, which is `some` once the peer's hello arrived ("ready");
- `peerDigest`, `announced` and `lastSent`;
- `inflight`, `lacks` and `toldNo` (blob bookkeeping, §5), and `reported`.

Notices for the UI:
- `indexChanged` and `blobsChanged`: re-query;
- `peerStatus p (handshaking|syncing|inSync) replica`, `peerClosed`, `peerLeft`, `peerError`;
- `pendingSummary fetching queued waiting`, which separates "being fetched", "queued behind a
  peer whose request slots are full", and "nobody reachable has it" (§5);
- `rollbackDetected`, `opRejected`, `badEvent`, `startupFailed`, `notInitialized`,
  `alreadyInitialized`.

Replies:
- `snapshot`: each path with its versions, each marked present or not;
- `pending`: each missing hash, `requested p`, `queued` or `waiting`;
- `status`.

Changes since stage 1:
- `init` takes the stored bytes (no longer optional), and `initFresh` is new (user decision, §7);
- `persistFailed` and the `fetch` effect were already introduced at the end of stage 1;
- `startupFailed` replaces `corruptStore`, and `peerLeft` and `pendingSummary` are new.

Changes made after the review of the stage-2 branch:
- `blobsStored` is new: the start-up inventory can be reported in chunks (§7);
- `PendingStatus.queued` is new, and `pendingSummary` has three counts instead of two (§5);
- `Node.summary` is a triple.

## 3. Save-before-send, made structural

The only state ever put on the wire is `published`: the state of the last persist the host
acknowledged.
- Any change to `current` sets `dirty`.
- When no persist is in flight, the end-of-step pass emits `persist nextTag current`.
- On `persisted tag d` with the in-flight tag, `published := ⟨that state, d⟩`. Other tags, stale
  or duplicate, are ignored.
- `persistFailed tag` clears the in-flight persist and sets `dirty`. The next event retries; the
  host decides when to call again.

**At most one persist is ever in flight.** Later changes are folded into the next persist. The
host therefore never has two writes racing, and an earlier write can never overtake a later one.

**The digest comes with `persisted`** (accepted by the user). The host hashes exactly the bytes it
stored, so every digest Lean holds belongs to a durable state, and nothing waits on a separate
digest round trip.

**Merged states are persisted before they are forwarded** (accepted). This is stricter than the
host rule.

Proved for **every** event sequence from the uninitialised machine, with no hypothesis (§9):
- `sent_state_acked`: every `send p (.state d s)` at step `i` carries a state `s` for which
  `persist t s` was emitted at some step `j < k`, and `evs[k] = persisted t _` with `k ≤ i`.
- `save_before_send`: the host-rule form, over every effect that puts a message on the wire.
- `persist_tag_unique` and `persist_one_in_flight`.
- Remaining assumption: the host answers `persisted` only after the write is durable.

## 4. Session flow

After every event, `step` runs the same end-of-step pass:
1. **persist**, if one is needed;
2. **reconcile** each session:
   - send `hello 1 self digest` once `published` exists;
   - then, on a ready session: if the peer announced a different digest and we have not yet sent
     this state in this session, send `state digest published`; otherwise, if we have not
     announced this digest, send `digest d`;
3. **plan** blob requests (§5);
4. **report** status changes and the pending summary.

On receipt of a message:
- `hello`: record the peer's replica and digest. Our own id closes the session with
  `sameReplicaId`, and `maxVersion = 0` closes it with `incompatible`.
- `digest d`: record `d`.
- `state d s`: `current := merge current s`, record `d`, and run the rollback check. If the merge
  would exceed the size limit, close with `stateTooLarge` and keep `current`.
- `want`: serve the present blobs; answer the rest with `noBlob` and remember them in `toldNo`.
- `noBlob`: move the hashes from `inflight` to `lacks`.
- `have`: remove the hashes from `lacks`.
- `bye`: drop the session.
- Anything before `hello`, a second `hello`, an undecodable message, or a wrong version:
  `send bye`, `close`, notify.

**Disconnect at any point.** The session, with its requests, is dropped in that step and its
requests are re-planned to other peers. A reconnect is a new `PeerId` and a fresh session.
Messages for an unknown peer are ignored. Duplicate or stale states are harmless, because merge
is idempotent and only grows the state.

**Local edit mid-session.** The edit is persisted; once acknowledged, the peer gets `digest`, and
gets `state` unless it already announced that digest.

**Cost (accepted for the demo).** One edit costs one whole-state send per connected peer. Each
entry encodes to about 37 bytes plus its path, so 20k files with short paths come to about 1 MB
per peer. Bursts are folded by the single in-flight persist.
- A state sent to k peers in one step appears **once** in the envelope; later sends of it are
  encoded as `sendAgain` (§6). Spotting the repeat costs a `State.beq` comparison, not an
  encoding. The host still transmits the bytes k times, once per connection.
- Each received state is also encoded once, to check its size.

**Rollback mode** (user decision). A received state with `s.context.get self >
current.context.get self` proves that our storage was rolled back or our id is shared. Lean then
sets `rollback`, notifies `rollbackDetected`, and from then on:
- **refuses every local edit** (`opRejected`; proved: `rollback_rejects_local`);
- **never sends its state** (proved: `rollback_no_state`).

It still:
- accepts and merges incoming states;
- persists;
- sends `hello`/`digest`;
- fetches and serves blobs, and answers `noBlob`/`have`.

Why this is the most conservative option that cannot make things worse for other devices:
- The only thing that can spread damage is a `state` message, whose possibly colliding dots other
  devices would merge, and those are stopped.
- Digests and hellos reveal no dots.
- Blob bytes are checked against their SHA-256 by the receiving host, so serving cannot spread
  wrong content.
- Merging incoming states changes only this device, and only adds what peers already hold. It
  keeps the user's view current, and keeps the persisted state complete for the restart under a
  fresh id.

Honest limit: dots issued before detection may already have reached peers. Detection only stops
further damage. The host must restart with a fresh replica id.

**Why it converges.** The local half is proved; the global half is a paper argument, checked by
simulation.
- **Proved,** `step_settles`: after every step, for every ready session of a node not in rollback
  mode, we announced our published digest, and either the peer announced the same digest or we
  sent it our published state in this session.
- **Paper argument for two connected nodes A, B at quiescence.**
  - At quiescence every persist is acknowledged (`published = current`), every message is
    delivered (the channel is reliable and ordered), and neither node is in rollback mode.
  - B's last announced digest is B's current one. So either `dA = dB` (equal states, by
    `encodeState_inj` and SHA-256 collision resistance), or A sent `sA` in this session and B
    merged it, so `sA ≤ sB`.
  - Symmetrically `sB ≤ sA`, hence `sA = sB`.
  - Transitivity over a connected topology follows.
- The simulator checks the whole claim, end to end (§10).

## 5. Blobs: presence, pending, who to ask

- **Present blobs.** `blobs` is rebuilt at start-up from the host's listing (in `init`, and/or in
  `blobsStored` chunks, §7), and updated by `blobStored`/`blobsStored`, by local puts (the host
  stores the blob before reporting the op), and by `blobLost`. A batch is recorded in one sorted
  pass.
- **Missing blobs.** `missing` is the set of hashes referenced by `current` that are not present,
  every sibling version included. A file is complete when all its versions are present.
- **Planning,** after every event. Each ready session **to which we have sent our hello**, in
  `PeerId` order, with fewer than 32 requests in flight, receives one `fetch` for the first
  missing hashes that are neither in flight anywhere nor listed as lacking at that peer.
  - The simulator found that requesting before our own hello makes the peer reject the session.
    This was a real bug, now fixed; `step_plans_blobs` changed with it (§9).
  - Proved, `step_plans_blobs`: after every step, each missing hash is in flight somewhere, or
    every greeted ready session either lacks it or is full.
- **Chains** (A has a blob, B is fetching it, C asks B). B answers `noBlob` and records the hash
  in `toldNo`. When B stores the blob it sends `have` to C, and C asks again.
  - Proved, `step_no_owed_have`: no `have` is owed after any step.
  - `toldNo` is capped at 4096 per session; past that, C retries on its next session with B.
- `blobFailed p h` marks `h` as lacked at `p` for that session, so a peer serving corrupt data
  cannot cause a retry loop.
- **Three kinds of pending blob** (user decision: no clock, wait indefinitely; the review asked
  that a blob queued behind a busy peer not be reported as unreachable):
  - **fetching**: requested from a peer now;
  - **queued**: not requested yet, but some greeted ready peer has not said it lacks it, so it
    will be requested as soon as that peer's 32 request slots free up (by `step_plans_blobs`, such
    a peer is full);
  - **waiting**: every greeted ready peer said it lacks it, or no peer is connected: nobody
    reachable has it.
  - `pendingSummary fetching queued waiting` is emitted whenever the triple changes, and the
    `pending` query lists each hash with `requested p`, `queued` or `waiting`. A unit test checks
    exactly the review's case: 33 missing blobs and one peer give (32, 1, 0).
  - A waiting hash is asked for again when a new session is greeted or a `have` arrives.
  - If the device that wrote it later superseded it, the next index sync removes the reference.
  - If that device is gone for good, the file stays pending until the user deletes or overwrites
    it.

## 6. Wire format, version 1

The format is defined in `Wire.lean` (states, messages), `Envelope.lean` (events) and
`EffectsWire.lean` (effects).
- **Integers** are canonical unsigned LEB128: no overlong forms, at most 10 bytes, value below
  2^64.
- **Replica ids** are two such varints, `hi` then `lo`. Stage 1 planned 16 fixed bytes; the
  varints let the encoding reuse one proved primitive.
- **Hashes and digests** are exactly 32 bytes in states and messages.
- **Strings** are a varint length followed by validated UTF-8.
- **Every top-level value** starts with `[version = 1][kind]`, where kind is 1 = state,
  2 = message, 3 = event, 4 = effect list.

```
state   := 01 01 r {hi lo counter≥1}^r  n {path:str idx<r counter∈[1,ctx[idx]] hash:32}^n
           (replica ids strictly increasing; entries strictly increasing by (path, dot, hash))
message := 01 02 tag ...  0 hello maxVersion:u8 hi lo digest:32 | 1 digest digest:32
                          2 state digest:32 <state without its 2-byte header>
                          3 want | 4 noBlob | 5 have   k∈[1,1024] {hash:32}^k (strictly increasing)
                          6 bye reason:u8
event   := 01 03 tag ...  (layout in the header of LeanSync/Envelope.lean; 12 = blobsStored)
effects := 01 04 k:nat {effect}^k                    (layout in the header of LeanSync/EffectsWire.lean)
           0 send peer msg:bytes | 1 close peer reason | 2 persist tag:nat state:bytes
           3 fetch peer {hash} want:bytes | 4 serveBlob peer hash | 5 notify | 6 reply
           7 sendAgain peer      -- the same state message as the last `send` of a state written in full
```

- **The effects envelope** is Lean's own output and is decoded by the trusted host, so it has no
  total size cap, and its integers and byte strings may be any length. The limits belong to the
  untrusted inputs: events and peer messages. Every embedded peer message and persisted state is
  `WireOk`, which includes its own size limit (`step_effects_ok`).
- **One payload per state per step.** A `send` of a state message equal to the last one written in
  full (same digest, `State.beq`) is encoded as `sendAgain peer`. A state sent to 32 peers in one
  step is written once, not 32 times: in the regression test, a 1.01 MB state sent to 32 peers
  plus its persist gives a 2.02 MB envelope. The equality check costs a comparison pass, not an
  encoding, so the k-fold re-encoding is gone too.

- **Digest preimage.** The persisted record and the digest preimage are both `encodeState`, header
  included.
- **Canonicity.** Two equal states always encode to the same bytes, and the decoder accepts
  nothing else: `encodeState_of_decodeState` says any accepted input is exactly the encoding of
  what was decoded.
- **Versioning.** `hello` stays decodable in v1 and advertises `maxVersion`.
- **Limits.**
  - State ≤ 64 MiB (about 500k entries); message ≤ state + 64 B; event ≤ 128 MiB. The effects
    envelope has no cap (see above).
  - Path ≤ 4096 bytes; batch ≤ 1024 hashes; ≤ 32 sessions; ≤ 32 requests in flight per peer;
    `toldNo` ≤ 4096.
  - A local op that would break a limit is rejected with `opRejected`, including a hash that is
    not 32 bytes.
  - A merge that would exceed the state limit closes that session with `stateTooLarge`.
- **Decoders** are total and make one tail-recursive pass over their input.
  - Order is checked only between neighbours.
  - A dot's coverage is checked in O(1), through an `Array` of the context.
  - Nothing is preallocated from a claimed count.
  - The size is checked before parsing.

## 7. Start-up, reset, and what the host persists

**Restore.** `init self storedBytes blobs`. If the bytes decode, the node starts from them and
immediately emits `persist 0 state`; the host may skip the identical write but must answer with the
digest. Until that acknowledgement, no hello is sent.

**Blob inventory in chunks.** `init` and `initFresh` may carry the whole list of stored blob
hashes, part of it, or none. The rest is reported with `blobsStored` batches (chunks of, say, 10k
hashes), each its own event of at most 128 MiB. The host must send all of them **before**
connecting any peer.

If a peer connects before the inventory is complete, the protocol stays correct but does
unnecessary work. Lean believes the unreported blobs are missing, so:
- it may request them from the peer; the host stores the incoming copy again, which is
  idempotent;
- it answers `noBlob` to a peer's request for them.

When the batch that reports a blob arrives, Lean sends `have` to every peer it told `noBlob`, and
those peers ask again. A unit test covers this case.

**Start-up error** (user decision: never reset silently). If the stored bytes do not decode, Lean
emits `startupFailed e` and stays uninitialised. The host may retry `init`, for example after
re-reading storage.

**Reset** is a separate, explicit, host-initiated event: `initFresh newId blobs`, which starts an
empty index. The UI puts it behind a user confirmation, because it loses changes that were never
synced; blobs on disk are kept. The same event is used for a first start on empty storage.

**Other cases.**
- Any event before an initialisation yields `notInitialized`.
- A second `init` yields `alreadyInitialized`.

## 8. Host obligations (for the JS implementer)

**What to persist, and when.**
1. **The record.** Store `{replicaId, stateBytes}` in **one** atomic IndexedDB transaction for each
   `persist tag stateBytes`, replacing the previous record.
   - Only after the transaction commits, send `persisted tag SHA-256(stateBytes)`.
   - If it fails, send `persistFailed tag`; back-off is the host's job.
   - Lean never has two persists outstanding. Do not reorder writes.
2. **Blobs.** Store a blob durably, after verifying its SHA-256, *before* sending `blobStored`.
   For a local edit, store the blob *before* sending the `localOp` that refers to it.
3. **Nothing else** is persisted: no sessions, tags, pending sets or blob lists.

**Start-up.**
- Hold a Web Lock, so that one tab owns the storage.
- Load the record and list the stored blob hashes.
  - If there is no record: `initFresh newId hashes`.
  - If the record is trustworthy: `init id bytes hashes`.
  - If you cannot vouch that the record is the latest one written (backup restore, lost
    storage, previous `rollbackDetected`): `init newId bytes hashes`, with a fresh id.
- `hashes` may be a prefix of the inventory, or empty. Report the rest with `blobsStored`
  batches, keeping each event under 128 MiB (10k hashes per batch is plenty), and **before
  connecting any peer** (§7 says what happens otherwise).
- On `startupFailed`: show the error, and offer a reset, which is `initFresh newId hashes` after
  the user confirms.

**Decoding the effects envelope.**
- Read it with no total size cap.
- Integers are LEB128 of any length.
- Keep the bytes of the last `send` whose message is a state. A `sendAgain p` means: send those
  same bytes to `p`.
- `process_output_decodes` guarantees that every envelope decodes.

**What each effect requires** (Lean guarantees the preconditions; `effects_executable`):
- `send p bytes` (or `sendAgain p`): queue `bytes` on connection `p`, in order. If `p` is already
  closed, drop it silently: Lean will receive `disconnected p`.
- `close p reason`: close `p` after the bytes already queued for it.
- `persist tag bytes`: as in 1 above.
- `fetch p hashes bytes`: send `bytes` to `p`, then accept blob streams from `p` for exactly those
  hashes.
  - Verify each blob's SHA-256 and its size against the host's own limit, store it, and report
    `blobStored h (some p)`.
  - Report `blobFailed p h` on a mismatch, an abort, or the size limit.
  - If the connection drops mid-stream, discard the partial blob and report nothing more for it.
- `serveBlob p h`: stream blob `h` to `p`. If it cannot be read, send an abort frame for `h` and
  report `blobLost h`.
- `notify` and `reply`: for the UI.

**What each event promises.**
- `connected p` and `disconnected p`: once each per connection, and `p` is never reused.
- `received p bytes`: one complete Lean message, in order, of at most `maxMessageBytes`. The
  host reassembles its own fragments, and closes a connection that exceeds the limit.
- `persisted` and `persistFailed`: only for a `persist` the host was given.
- `blobStored` and `blobsStored`: the blobs are durably stored and verified.
- `blobLost`: a blob previously reported present is gone.

**Framing.** On a data channel the host multiplexes fragments of Lean messages and blob-stream
frames. That framing belongs to the host and is invisible to Lean.

## 9. Theorems

All of these are proved in `LeanSync/Laws.lean`, with lemmas in `StepProofs.lean`, `Wire.lean` and
`EffectsWire.lean`.

| Group | Theorem | Statement |
|---|---|---|
| Wire | `decodeState_encodeState` | `s.WireOk → decodeState (encodeState s) = .ok s` |
| Wire | `encodeState_of_decodeState` | canonicity: whatever decodes is exactly the encoding of the result |
| Wire | `wireOk_of_decodeState` | decoded states are `WireOk`, and carry the CRDT invariants by construction |
| Wire | `encodeState_inj` | equal encodings ⇒ equal states |
| Wire | four message counterparts | `decodeMessage_encodeMessage`, `encodeMessage_of_decodeMessage`, `wireOk_of_decodeMessage`, `decodeMessage_tooLarge` |
| Trace | `sent_state_acked`, `save_before_send` | §3 |
| Trace | `persist_tag_unique`, `persist_one_in_flight` | §3 |
| Host | `effects_executable` | every effect of every step of every event sequence is executable by `HostView`, which models the host from the events and effects so far; this includes that every sent message, fetch batch and persisted state is `WireOk` |
| Envelope | `decodeEffects_encodeEffects` | every effect list whose sends, fetches and persists are well formed decodes back to itself, with state payloads de-duplicated |
| Envelope | `step_effects_ok`, `process_output_decodes` | every effect a step emits is well formed, so whatever `process` outputs decodes back to exactly the emitted effects |
| Step | `step_inv` | the node invariant holds after every step: sortedness, caps, `missing` = refs(current) \ blobs, published/in-flight ≤ current, owed-`have` bookkeeping, `WireOk` states |
| Step | `step_current_grows` | the state only grows and the replica id never changes |
| Step | `step_received_state`, `step_putMany` | exact merge and `putMany` semantics |
| Step | `step_settles`, `step_plans_blobs`, `step_no_owed_have` | §4 and §5 |
| Step | `step_detects_rollback`, `rollback_no_state`, `rollback_rejects_local` | rollback mode (§4) |

**Statements changed since stage 1**, each marked in `Laws.lean`:
1. **`step_putMany`** gains `n.rollback = false`. Local edits are refused after a rollback. The
   stage-1 statement was already false under the stage-1 design, which refused them too; I missed
   that at stage 1.
2. **`step_settles`** gains `n'.rollback = false`. In rollback mode no state is sent (your
   decision), so sessions cannot settle.
3. **`step_plans_blobs`** restricts the "no peer can take it" disjunct to sessions with
   `helloSent`. This follows the hello-first bug fix (§5): a ready session we have not greeted yet
   cannot be asked.

**Definitions refined.**
- `Node.Inv` gained fields (the `missing` cache, per-session facts), which makes `step_inv`
  stronger.
- `State.WireOk` keeps its stage-1 shape, with the path size written as `toByteArray.size`, which
  equals `utf8ByteSize`. The count bounds that the varint encoding needs are *derived* from the
  size bound (`fieldsOk_of_wireOk`), not added as assumptions.
- `rollback_no_state` and `rollback_rejects_local` are new.

**After the review (no theorem statement changed):**
- `HostView.exec` now requires every sent message, every fetch batch and every persisted state
  to be `WireOk` (decided by `checkMessage`, `checkBatch` and `checkWire`). Before, it required
  only that they fit the size limits. This makes `effects_executable` stronger.
- `decodeEffects_encodeEffects`, `step_effects_ok` and `process_output_decodes` are new.

**Re-run the no-placeholder claim:** `scripts/check-proofs.sh`.
- **Forbidden constructs.** `scripts/check-forbidden.sh` looks for `sorry`, `axiom`,
  `native_decide`, `implemented_by`, `unsafe` and `partial` as whole words anywhere outside
  comments and string literals. It therefore catches `private partial def`, `@[inline] unsafe def`
  and `protected axiom`. The script first self-tests on four planted constructs.
- **Axioms.** It runs `#print axioms` on every theorem listed in `scripts/Axioms.lean` (26). Each
  must report, and the only axioms allowed are `propext`, `Classical.choice` and `Quot.sound`.
  Fewer, or none, is accepted.

**What is proved, argued, and only simulated:**
- **Proved:** everything in the table above.
- **Argued on paper, checked by simulation, not proved:**
  - global convergence of several nodes (§4);
  - blob liveness: once connected enough and quiescent, every referenced blob that some
    connected device holds reaches every device. This follows from `step_plans_blobs`, the
    `have` mechanism and transitivity.
- **Tested only:**
  - the event envelope round trip (the effects envelope round trip is now proved);
  - linear decoding time;
  - stack depth.

## 10. Tests (`scripts/test-sync.sh`; `sync-tests <subcommand>`)

All of these passed in the final run, both with the default stack and with
`LEAN_STACK_SIZE_KB=256`.

**`unit`** (53 checks) covers every flow of §4 to §7:
- the persist-before-send ordering;
- stale and duplicate acknowledgements;
- protocol errors: before hello, bad version, own id;
- the session cap;
- re-planning on disconnect, and the `noBlob` → `have` chain;
- `blobFailed`;
- rollback mode;
- `startupFailed`, then `initFresh`;
- the pending summary and the queries;
- **queued versus waiting:** 33 missing blobs and one peer give summary (32, 1, 0), and the
  `pending` reply lists 32 requested, 1 queued, 0 waiting;
- **late inventory:** a restart with an empty `init` inventory and a peer connecting early. The
  blob shows as waiting, then a `blobsStored` batch makes Lean send `have`, and the devices
  converge.

**`codec`**:
- **Round trips:** 200 random `WireOk` states, and 300 each of random messages, events and effect
  lists, compared at byte level. The effect lists include repeated state sends, encoded as
  `sendAgain`.
- **P1 regression:** a 20,000-entry state (1,010,391 bytes) sent to 32 peers, plus its persist,
  gives a 2,020,890-byte envelope that decodes back to the 33 effects.
- **Truncation:** every proper prefix of six encodings (6,937 prefixes) must be rejected. The six
  are a state with 28 entries and 3 replicas, a state message, a 20-hash `want`, a `hello`, an
  `init` event and an effect list.
- **Mutation fuzz:** 24,000 mutants of states, messages and events, made by bit flips, overwrites,
  inserts, deletes, duplicated spans and huge varint counts. Each must fail to decode or re-encode
  to exactly the mutated bytes; there were no crashes.
  - States: 7,331 rejected, 669 accepted.
  - Messages: 7,244 rejected, 756 accepted.
  - Events: 6,729 rejected, 1,271 accepted.
- **Random bytes:** 18,000 random inputs, all rejected.

**`sim 1 200`**: 200 seeds × 4 devices × 400 random steps, then quiescence.
- **Faults injected over the 200 seeds:**
  - 2,116 connection drops at arbitrary points and 798 crash/restarts from the persisted record;
    half of all start-ups report the blob inventory in `blobsStored` chunks;
  - 589 persist failures and delayed acknowledgements;
  - 99 blob-transfer failures and 443 blob losses (only when another copy exists);
  - 365 garbage, 187 truncated and 189 duplicated messages.
- **Volume:** 84,427 events, of which 21,092 went through `process` and the byte envelopes, and
  15,708 state sends.
- **Checked after every event:**
  - save-before-send, through a global **dot registry**: no dot is ever seen on the wire with two
    different contents;
  - every sent state equals a state its host acknowledged;
  - every effect is executable in `HostView`;
  - the node invariants;
  - hello-first order on every connection.
- **At quiescence:** all connections are rebuilt as a full mesh, a chain, or sequential pairs
  (by seed). The run then requires equal states, `published = current`, no persist in flight, and
  every referenced blob present on every device.
- **Result:** 0 failing seeds.
- **Not injected:** bit corruption that still decodes. The transport has integrity, and the trust
  model excludes it.

**`mutation`** runs broken step functions, 30 seeds each. Each seed runs the strict simulator
plus a **directed chain scenario**:
- A holds the blobs. B learns the index from A, but A's blob streams are held back.
- C connects to B only, learns the index from B, and asks B, which answers `noBlob`.
- Everything is then delivered **without reconnecting**, so C can obtain the blobs only through
  B's `have`.

| Mutant | Caught on |
|---|---|
| state sends carry `current` instead of `published` | 30/30 |
| no `have` sent | 30/30 (was 8/30 with the random simulator alone, whose quiescence phase reconnects and so retries) |
| received states ignored | 30/30 |
| a send after disconnect | 30/30 |

The real step function is clean on 30/30 seeds. Earlier, the simulator caught the real
want-before-hello bug on 83 of 200 seeds.

**`scale 20000`**: 20,000 files on one device, then a full sync of two fresh devices: the index
plus 40,000 blobs, 79,962 events.
- `putMany` of the 20k files plus their persist: 0.5 s.
- The whole sync: about 19.5 s native, of which 10.8 s is inside `step`.
- It passes under the 256 KB stack.

**`stepbench n`** gives compiled per-event costs. At 20k entries:
- merging the 20k-entry state and persisting it: about 10 ms;
- `blobStored`: about 56 µs;
- an event that changes nothing: about 43 µs;
- a 32-hash `want`: about 66 µs.

These timings are noisy between runs on this machine, by up to 2×.

## 11. Costs and limits (accepted), with the fix I would make

| Limit | Fix |
|---|---|
| One edit during a session costs a whole-state send per peer (§4) | a `sendPublished` effect that rebuilds the message from the stored record, or index deltas: both declined for the demo |
| O(n) blob bookkeeping per event: sorted-list membership, the `missing` cache, the summary length; at 20k files about 0.05–0.1 ms per event native, so a full initial sync of 20k blobs costs about 10–19 s of `step` time over the transfer | balanced-tree or array-indexed sets; a cached missing count |
| Index ≤ 64 MiB, about 500k entries; a merge past the limit closes the session | raise the limit (a version bump), or chunked state messages |
| One envelope holds the persisted state, the shared state message, small messages and any query reply. A `snapshot` reply is about the size of the index | page the snapshot reply if a UI needs less |
| A state that grows by merging can reach the 64 MiB limit | the merge closes the session with `stateTooLarge` (§6) |
| Merge is O((n+m)·r) (CRDT note, risk 5) | as in the CRDT note |

## 12. Future work and open points

- **Blob GC** is not done (user decision), so storage grows with superseded versions. A safe rule
  for later:
  - a host may delete a blob only when the **published** state does not reference it, and only
    after that state is acknowledged;
  - a peer that still references it then gets `noBlob`, and drops the reference at its next index
    sync with a device that superseded it.
- **File sizes or other metadata** in the index are not in v1 (user decision). Adding them is a
  CRDT `Entry` change *and* a wire-format version bump (`wireVersion` 2, negotiated through
  `hello.maxVersion`).
- **Deltas or `sendPublished`**: see §11.
- **Not yet run under wasm.** The import closure is `Init` only, but startup time, size and stack
  depth have not been measured there.
