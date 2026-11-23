# Sync protocol and wire format: design note (stage 1)

Branch `sync-protocol` · Lean 4.36.0 · `Init` only · new library `LeanSync` (`LeanSync/`), built by
default next to `LeanCrdt`, which is unchanged.

| File | Contents | Status at stage 1 |
|---|---|---|
| `LeanSync/Types.lean` | messages, events, effects, session, node, machine | real |
| `LeanSync/Wire.lean` | limits, `WireOk` predicates, encoders/decoders | limits and predicates real; codec bodies are placeholders |
| `LeanSync/Step.lean` | `step`, `run`, `process`, exported `processIO` | `step` is a placeholder |
| `LeanSync/HostModel.lean` | what the host can carry out (`HostView`, `Executable`) | real |
| `LeanSync/Laws.lean` | theorem statements (proof-only) | statements real, proofs are placeholders |

Every placeholder is a `sorry` tagged `STAGE-1 PLACEHOLDER` (`grep -rn STAGE-1 LeanSync`).
Placeholders exist only in `LeanSync/`. `scripts/test-crdt.sh` greps only `LeanCrdt/`, so it still passes.
The Lean code below is copied from those files, which compile; where the two differ, the files are right.

## 1. Shape

`step : Machine → Event → Machine × List Effect` is pure, total and deterministic. A `Machine`
is either `uninit` or `running (n : Node)`. The wasm boundary is one function:

```lean
def process (m : Machine) (input : ByteArray) : Machine × ByteArray   -- event in, effects out
initialize machineRef : IO.Ref Machine ← IO.mkRef .uninit
@[export lean_sync_process] def processIO (input : ByteArray) : IO ByteArray   -- get, process, set
```

The machine lives in an `IO.Ref` between calls. `IO.Ref` comes from `Init`, and the code does no
other IO. The C shim calls `lean_sync_process` and unwraps the `IO` result. This is a one-time change
from the spike's pure `ByteArray → ByteArray` shim; after it, the C shim and the JS host stay fixed.
An input that does not decode yields `[notify (badEvent e)]` and leaves the machine unchanged.
The output is always a well-formed effect list.

## 2. Types (`LeanSync/Types.lean`, abridged: doc comments dropped)

```lean
structure Digest where bytes : ByteArray; size_eq : bytes.size = 32   -- host SHA-256
structure PeerId where val : UInt32      -- host handle of ONE connection; never reused in a run

inductive Message where
  | hello (maxVersion : UInt8) (replica : ReplicaId) (digest : Digest)
  | digest (d : Digest)                  -- my published state now has digest d
  | state (d : Digest) (s : State)       -- my whole published state, with its digest
  | want (hs : List Hash)                -- serve these blobs (only via Effect.fetch)
  | noBlob (hs : List Hash)              -- I lack these
  | have (hs : List Hash)                -- I now have these, which I said I lacked
  | bye (reason : CloseReason)

inductive Event where
  | init (self : ReplicaId) (stored : Option ByteArray) (blobs : List Hash)
  | connected (p : PeerId) | disconnected (p : PeerId)
  | received (p : PeerId) (bytes : ByteArray)       -- one complete Lean message
  | localOp (op : LocalOp)                          -- putMany | deleteMany | resolve
  | persisted (tag : Nat) (digest : Digest) | persistFailed (tag : Nat)
  | blobStored (h : Hash) (src : Option PeerId) | blobFailed (p : PeerId) (h : Hash)
  | blobLost (h : Hash)
  | query (q : Query)                               -- snapshot | pending | status

inductive Effect where
  | send (p : PeerId) (msg : Message)
  | close (p : PeerId) (reason : CloseReason)
  | persist (tag : Nat) (s : State)                 -- store atomically, hash, answer persisted
  | fetch (p : PeerId) (hs : List Hash)             -- send `want hs`, accept those streams
  | serveBlob (p : PeerId) (h : Hash)
  | notify (n : Notice) | reply (r : Reply)

structure Session where
  peer : PeerId
  helloSent : Bool;  peerReplica : Option ReplicaId     -- `some _` = hello received = ready
  peerDigest : Option Digest   -- last digest the peer announced
  announced : Option Digest    -- last digest we announced
  lastSent : Option Digest     -- digest of the last state we sent in this session
  inflight lacks toldNo : List Hash;  reported : PeerStatus

structure Published where state : State; digest : Digest
structure Node where
  self : ReplicaId
  current : State                     -- may hold unpersisted local dots
  published : Option Published        -- last state the host confirmed persisted
  inflight : Option (Nat × State)     -- the one persist in flight
  nextTag : Nat;  dirty : Bool        -- current changed since the last persist was issued
  blobs : List Hash                   -- present locally, strictly sorted
  sessions : List Session             -- strictly sorted by peer
  rollback : Bool                     -- host-rule violation detected
```

`Notice` covers these cases:
- `indexChanged` and `blobsChanged`: the UI should re-query;
- `peerStatus p (handshaking|syncing|inSync) replica`, `peerClosed`, `peerError`;
- `rollbackDetected`, `opRejected`, `badEvent`, `corruptStore`, `notInitialized`, `alreadyInitialized`.

`Reply` answers a `query`:
- `snapshot`: each path with its versions, each marked present or not;
- `pending`: each missing hash, with `requested p` or `waiting`;
- `status`: persistence state and peer statuses.

## 3. Save-before-send, made structural

**Only one state is ever put on the wire: `published`, the state of the last `persist` the host
acknowledged.**
- Every change to `current` (local op or merge) sets `dirty`.
- When no persist is in flight and `dirty` is set, Lean emits `persist tag current`.
- On `persisted tag d` with the matching tag, `published := ⟨that state, d⟩`. On a non-matching or
  duplicate tag, nothing happens.
- `hello`, `digest` and `state` messages carry only `published` and its digest.
- At most one persist is in flight. Later changes coalesce into the next persist, so the host never
  has two writes racing, and a later write can never be overtaken by an earlier one.

This rule is stricter than the host rule: merged states, which carry other replicas' dots, are also
persisted before they are forwarded. The cost is a few ms of latency, and the benefit is that a
reload never has to re-download the index. If the user keeps editing, the peer gets the last
acknowledged state, so sync is never starved.

**The digest comes back with `persisted`.** The host hashes exactly the bytes it stored. So there
is no separate digest effect/event round trip, and no state that is "changed but digest not yet
known". Every digest Lean holds is the digest of a durable state, and `published` is one atomic
`(state, digest)` pair. This bundles two of decision 2's examples into one effect/event pair; I
think it is strictly simpler. The alternative is a separate `computeDigest`/`digest` pair tagged
with a state epoch, which drops stale answers.

Statement, for **every** event sequence, with no hypothesis (`Laws.lean`, §3):
`sent_state_acked`: if `send p (.state d s)` is among the effects of step `i`, then `persist t s` was
emitted at some step `j` and `evs[k] = persisted t _` for some `j < k ≤ i`.
`save_before_send` is the host-rule form: for every effect that puts a message `m` on the wire
(`Effect.sentMessage?`) and every replica `r`, the dots of `r` that `m` reveals are bounded by some
acknowledged state. `persist_tag_unique` and `persist_one_in_flight` make "acknowledged" unambiguous.
What remains an assumption: the host sends `persisted` only after the write is durable.

**Rollback detection (new, cheap).** A legitimate peer can never know more of our own dots than
`current`. So if a received state has `s.context.get self > current.context.get self`, our storage
was rolled back or our id is shared. In that case Lean sets `rollback`, emits
`notify rollbackDetected`, and **rejects further local ops**. Continuing under the same id is
unsafe, because another peer may know even higher counters. The host must restart with a fresh
replica id. A hello carrying our own replica id closes the session with `sameReplicaId`.

## 4. Session flow

A session is per connection: `connected p` creates it, and `disconnected p` or our `close p`
removes it. After **every** event, `step` runs one reconciliation pass over all sessions, in
`PeerId` order. For a session `x`, with published state `P` (if any), the pass does this:

1. If `P` exists and the hello has not been sent, send `hello 1 self P.digest`.
2. If `x` is ready (its hello was received):
   - if `x.peerDigest ≠ P.digest` and `x.lastSent ≠ P.digest`, send `state P.digest P.state`;
   - else if `x.announced ≠ P.digest`, send `digest P.digest`.
3. Plan blob requests (§5).
4. Then, once per step and not per session, issue a persist if one is needed, and emit UI notices
   for changed statuses.

On receipt of a message:
- `hello`: record the peer's replica id and digest; the session becomes ready.
- `digest d`: set `peerDigest := d`.
- `state d s`: set `current := merge current s` and `peerDigest := d`, and run the rollback check.
- `want`: emit `serveBlob` for present blobs. Answer the rest with `noBlob`, remembered in `toldNo`.
- `noBlob`: move the hashes from `inflight` to `lacks`.
- `have`: remove the hashes from `lacks`.
- `bye`: remove the session.
- Any message before `hello`, a second `hello`, an undecodable message, or a bad version:
  `send bye`, `close`, `notify`.

A typical session, where A and B differ:

```
A → B  hello(dA)           B → A  hello(dB)          (both, as soon as each has a published state)
A → B  state(dA, sA)       B → A  state(dB, sB)      (each sees a different digest and has not sent this state)
A: merge, persist, ack → published = sA⊔sB → A → B  digest(d')   (B does the same; d' equal on both sides)
both: peerDigest = own digest → nothing more to send; blob requests start as soon as states merge
```

If the digests are equal at hello, nothing is sent. The protocol is symmetric, so both sides send
their state on a mismatch, even the side that is behind. That is inherent in decision 1: a digest
says nothing about direction. Comparing version vectors does not help either, because deletes issue
no dot.

**Local edit mid-session.** `current` changes, then persist, then ack, then `published` changes.
Every ready session then gets `digest`, and also `state` unless the peer already announced that
digest. One edit therefore costs one whole-state send per peer. Bursts of edits coalesce through
the single in-flight persist.

**Disconnect at any point.** The session is dropped with its blob requests, which are re-planned to
other peers in the same step. Nothing about the session is persisted. A partially received message
is never delivered, because the host delivers only complete messages. A reconnect is a fresh session
and starts again with `hello`. Late events for an unknown `PeerId` are ignored. Duplicate or stale
states are harmless, since merge is idempotent and inflationary.

**Why it converges (paper argument; the local half is proved).**
- `step_settles` holds after every step: each ready session has been told our published digest, and
  either the peer announced the same digest or we sent it our published state in this session.
- Take two connected nodes A, B at quiescence: every persist is acknowledged, so `published = current`,
  and every message is delivered.
- B's announced digest is B's current one. So either `dA = dB`, or A sent `sA` and B merged it, so
  `sA ≤ sB`. Symmetrically, `sB ≤ sA`. Hence `sA = sB`, by `encodeState_inj` and SHA-256 collision
  resistance for the digest case, and by `Le` antisymmetry otherwise.
- Transitivity over the topology follows. The simulator checks the whole claim (§8).

## 5. Blobs: presence, pending, and who to ask

- `blobs` holds the hashes present locally. It is rebuilt at `init` from the host's listing. It is
  updated by `blobStored`, by local puts (the host stores a blob before reporting the op), and by
  `blobLost`.
- The **missing** set is the hashes referenced by `current` and absent from `blobs`. This includes
  every sibling of a conflict, because every device stores every file. A file is complete iff all
  its versions are present.
- **Planning**, after every event: for each missing hash, in hash order, that is not in flight
  anywhere, pick the ready session that does not list it in `lacks` and has the fewest requests in
  flight, with ties going to the smaller `PeerId`. Each session is capped at `maxInflightPerPeer`.
  The requests to one peer become a single `fetch p hs`.
  - Lean does not know which peer has which blob. It asks, and a peer without the blob answers
    `noBlob`. That costs one round trip, and avoids advertising whole blob sets.
- **Transitive case** (A has the blob, B is fetching it from A, and C asks B): B answers `noBlob`
  and records the hash in `toldNo`. When B stores the blob, it sends `have` to C, and C asks again.
  `step_no_owed_have` proves B owes no `have` after any step. `toldNo` is capped at `maxToldNo`;
  past the cap, C retries only on its next session with B.
- `blobFailed p h` marks `h` as lacked from `p` for the rest of that session, so that a peer serving
  corrupt data cannot cause a retry loop.
- **A hash no connected peer has** stays `waiting`. That is not an error: there is no clock, so
  there is no timeout. It is asked for again when a new session becomes ready or a `have` arrives.
  - If the device that wrote it later superseded it, the next index sync removes the reference.
  - If that device is gone forever, the file stays pending until the user deletes or overwrites it.
  - The UI should show "waiting for a device that has this file".
- Serving: the serving host streams the blob. If it cannot read the blob, it aborts the stream,
  which the requester's host reports as `blobFailed`, and it reports `blobLost` to its own Lean.

## 6. Wire format, version 1

Integers are canonical unsigned LEB128 (no overlong forms, at most 10 bytes, value < 2^64).
`ReplicaId` is 16 bytes big-endian `(hi, lo)`. Hashes and digests are exactly 32 bytes. A string is
a varint byte length followed by valid UTF-8. Every top-level value starts with
`[version = 1][kind]`, where kind is 1 = state, 2 = message, 3 = event, 4 = effect list.

```
state    := 01 01 ctx:varint r { replica:16 counter:varint≥1 }^r        (replica strictly increasing)
                  n:varint     { path:str idx:varint<r counter:varint hash:32 }^n
            -- entry dot = (ctx[idx].replica, counter), 1 ≤ counter ≤ ctx[idx].counter: coverage is
            --   structural, and the check is O(1) through an Array of the context
            -- entries strictly increasing by (path, dot, hash); this is exactly the CRDT's canonical form
message  := 01 02 tag:u8 body
            0 hello  maxVersion:u8 replica:16 digest:32     3 want/4 noBlob/5 have  k:varint∈[1,1024] {hash:32}^k (strictly increasing)
            1 digest digest:32                              6 bye reason:u8
            2 state  digest:32 <state without its 2-byte header>
```

- **The digest preimage is the persisted record**, the `state` encoding including its header. The
  host stores the replica id beside it, in the same IndexedDB record.
- **Version scheme.** The first byte of every value is the format version, and a decoder rejects any
  other value with `badVersion`. `hello` stays decodable in v1 forever and advertises `maxVersion`;
  peers use the minimum. v1 nodes close with `incompatible`.
- **Limits** (`Wire.lean`): state ≤ 64 MiB (about 500k entries); message ≤ state + 64 B; envelope ≤
  128 MiB; path ≤ 4096 bytes; batch ≤ 1024 hashes; ≤ 32 sessions; ≤ 32 blob requests in flight per
  peer. Local ops that would break a limit are rejected with `opRejected`, and so are hashes that
  are not 32 bytes. A merge whose result would exceed the state limit closes that session with
  `stateTooLarge`.
- **Decoders** are total and make one tail-recursive pass, so they run in linear time. Each item is
  compared with the previous one only, which proves strict sortedness by transitivity, as
  `strictPaths` does. The output list is built reversed, then reversed once. Nothing is
  preallocated from a claimed count: each item consumes at least one byte, so a lying count fails
  as `truncated`. Before parsing, the decoder checks that the input is at most the limit.
- Event and effect envelopes use the same primitives. In the effect list:
  - `send` carries the encoded message as a length-prefixed blob, which the host forwards verbatim;
  - `fetch p hs` carries `hs` and the encoded `want` message;
  - `persist` carries the encoded state record.

## 7. Startup, and what the host persists

**The host persists exactly two kinds of data.**
1. One record `{replicaId, stateBytes}`, written atomically for each `persist` effect, replacing the
   previous record. Only after the write is durable does the host send
   `persisted tag (SHA-256 stateBytes)`; if the write fails, it sends `persistFailed tag`.
2. Blobs, stored by hash after SHA-256 verification, before `blobStored` is sent. A local edit's
   blob is stored before the `localOp` event.

Nothing else is persisted: no sessions, tags, pending sets or blob lists.

**At startup** the host loads the record and lists the hashes of its stored blobs. If the record is
missing, or the host cannot guarantee it is the latest one it ever wrote (backup restore, two tabs
without a Web Lock, a `rollbackDetected` on the previous run), it uses a fresh replica id.
It then sends `init self stored blobs`. Lean decodes and validates `stored`:
- on failure it emits `notify (corruptStore e)` and stays `uninit`;
- otherwise it sets `current := stored` (or `empty`) and immediately emits `persist 0 current`. The
  host may skip the write if the bytes are identical, but it must answer with the digest.

Until that acknowledgement arrives, `published = none` and no hello is sent. Connections and local
ops may arrive in the meantime. Any non-`init` event before `init` yields `notInitialized`, and a
second `init` yields `alreadyInitialized`. A host that traps must re-instantiate the module and
start again with `init`. Edits that were never acknowledged are lost, and so is nothing else. Those
edits were never sent, so reusing their dots is safe. The UI should call an edit "saved" only once
the `persisted` that covers it has arrived.

## 8. Proved versus tested

**To be proved** (statements in `LeanSync/Laws.lean`, all placeholders now):
- **Wire:**
  - `decodeState_encodeState`: round trip, under `WireOk`;
  - `encodeState_of_decodeState`: canonicity. Whatever decodes is exactly the encoding of the
    result, which rules out every non-canonical spelling, including trailing bytes;
  - `wireOk_of_decodeState`, `encodeState_inj`;
  - the same four for messages, and `decodeMessage_tooLarge`.
- **Protocol:**
  - `sent_state_acked`, `save_before_send`, `persist_tag_unique`, `persist_one_in_flight`;
  - `effects_executable`: every effect of every step of every event sequence can be carried out by
    `HostView`. That means: sends, fetches and closes only to open connections; no persist while
    one is unanswered; serving only blobs reported present; every message within limits;
  - `step_inv`, the node invariant;
  - `step_current_grows`: the state only grows and the id never changes;
  - `step_received_state` and `step_putMany`: exact semantics;
  - `step_settles`, `step_plans_blobs`, `step_no_owed_have`, `step_detects_rollback`.
- **Stretch:** round trip for the event and effect envelopes. I commit only to testing these.

**To be tested** (natively; `crdt-tests sync ...` or a sibling `sync-tests` exe, wired into
`scripts/test-crdt.sh` including the small-stack run):
- unit flows for each message and event, including out-of-order, duplicate and stale cases;
- codec round trips, and a fuzz of mutated valid encodings: bit flips, truncation, insertion,
  deletion, duplicated spans, lying counts. Each mutant must either fail to decode or re-encode to
  exactly the input, and must never crash;
- a seeded, deterministic simulator:
  - N devices, each with a model host: a storage record, a blob store, delayed persists and
    failures, and blob streams that are delayed, dropped or corrupted;
  - per-connection FIFO queues; random local ops, connects and disconnects, drops at any point,
    crash and restart from the persisted record, and injected corrupt or duplicate messages;
  - after every step it checks `HostView` executability and a boolean version of `Node.Inv`. It
    also keeps a global **dot registry**: every dot ever revealed on the wire, with its
    `(path, hash)`. Seeing the same dot with different content is a host-rule violation;
  - at the end it connects a spanning set and drains, then requires equal states everywhere, all
    blobs present, `published = current`, and settled sessions. The seed is printed on failure;
- mutation checks: deliberately broken steps must be caught. Examples: send `current` instead of
  `published`, ignore `lastSent`, forget `have`, accept a mismatched persist tag;
- scale: 20k paths, full initial sync of 3 devices, timed. Stack: the scale sync and the decoders
  must pass under `LEAN_STACK_SIZE_KB=256`.

**Not proved:** convergence and blob liveness across nodes and the network (simulated only), linear
decoding time, and stack depth (tested).

## 9. Risks, tensions and open questions for the user

1. **Digest bundled into `persisted`** (§3), so there is no separate digest effect. Please confirm.
2. **Every state is persisted before it is sent, merged states included.** This is stricter than the
   host rule. The extra writes are bounded by the single in-flight persist.
3. **Whole-state cost** (decision 1). Both sides send on a mismatch, and every local edit during a
   session costs one full state per connected peer. With 20k files that is about 2 MB per edit per
   peer. A state sent to k peers appears k times in one effect list, and is re-encoded each time.
   - Option: a `sendPublished p` effect, where the host builds the message from the record it
     stored. That keeps save-before-send structural on the host side too.
   - I propose plain `send` for v1, and to measure first.
4. **Blob GC is out of scope**, so superseded blobs accumulate. A safe rule for later: a host may
   delete a blob only if the *published* state does not reference it. A peer that still references
   it then gets `noBlob`, and drops the reference at its next index sync with a device that
   superseded it. Decide when, and whether, GC is wanted.
5. **Hashes with no source**, and files pending forever (§5). There is no timeout without a clock;
   the user resolves it by deleting or overwriting the file. Should Lean accept `tick` events to
   report "stuck for a long time"?
6. **Rollback response**: reject local ops until a restart with a fresh id. Syncing continues, so our
   possibly colliding dots keep spreading. The alternative is to quarantine: stop sending our state.
   Which do you prefer?
7. **Corrupt stored state** at startup: Lean refuses to start. The host's only recovery is a fresh id
   and an empty state. Paths edited only on this device and never synced are then lost, although
   their blobs remain on disk and could be offered as "recovered files". This is a product
   decision.
8. **Limits**: a 64 MiB index caps the index at about 500k entries. A merge exceeding the limit closes
   the session rather than producing an unsendable state.
9. **Unsolicited blob streams.** The host accepts streams only for `fetch`ed hashes and enforces its
   own maximum blob size. Lean never learns blob sizes, because the index has no size field, so the
   UI cannot show the size of a pending file. Should a size go into the index? That would be a
   CRDT change, so I have not made it.
10. **Boundary signature** changes to `ByteArray → IO ByteArray` (§1), a one-time shim edit. The
    alternative is to keep the state as an opaque handle in the C shim.
11. **Cost.** Each event does O(n) bookkeeping: missing-set computation, sorted-list membership, and
    the O((n+m)·r) merge. A full initial sync of 20k blobs therefore costs about 20k × O(20k) hash
    comparisons, spread over the transfer time. That is acceptable but quadratic in total.
    Batching `blobStored` events or adding an indexed set is the fix if measurements demand it.
12. **Proof risk.** The codec proofs are the largest item. Core 4.36 has the needed `ByteArray`
    lemmas (`size_append`, `getElem_append_*`, `extract_*`), and `String` is `ByteArray` plus
    validity with decidable `IsValidUTF8`, so string round trips are direct. The trace theorems
    need an invariant that relates `Node.inflight` to the trace; I expect them to be routine but
    long. If a statement turns out false, I will stop and report rather than weaken it.
