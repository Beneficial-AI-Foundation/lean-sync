import LeanCrdt.State

/-!
# Sync protocol: types

Executable module: imports only `Init` (through `LeanCrdt.State`).

See `docs/sync-design.md` for the protocol, the wire format and the host obligations.

Naming: a *node* is the protocol state of one device (one replica id); a *session* is one live
connection to one peer, identified by a host-assigned `PeerId` that is never reused within one
run of the module (a reconnect is a new `PeerId`).
-/

namespace LeanSync

open LeanCrdt

/-! ## Basic identifiers -/

/-- SHA-256 of the canonical encoding of a state, computed by the host. Always 32 bytes. -/
structure Digest where
  bytes : ByteArray
  size_eq : bytes.size = 32

instance : DecidableEq Digest := fun a b =>
  if h : a.bytes = b.bytes then isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro e; cases e; exact h rfl)

/-- Host-assigned handle of one connection (one session). Fresh for every connection. -/
structure PeerId where
  val : UInt32
  deriving DecidableEq, Repr, Inhabited

instance : Ord PeerId := ⟨compareOn PeerId.val⟩
instance : Std.TransOrd PeerId := inferInstanceAs (Std.TransCmp (compareOn _))
instance : Std.LawfulEqOrd PeerId where
  eq_of_compare {a b} h := by
    cases a; cases b; simp only [PeerId.mk.injEq]; exact Std.LawfulEqOrd.eq_of_compare h

/-! ## Peer-to-peer messages (Lean-encoded, carried opaquely by the host) -/

/-- Why a node ends a session. Sent in `bye` and reported to the local UI. -/
inductive CloseReason where
  | protocolError      -- undecodable or out-of-order message
  | incompatible       -- no common wire version
  | sameReplicaId      -- the peer uses our replica id: a host-rule violation on one side
  | tooManyPeers       -- session table full
  | stateTooLarge      -- our state or theirs exceeds the wire limit
  deriving DecidableEq, Repr, Inhabited

inductive Message where
  /-- First message on every session, from both sides. `maxVersion` is the highest wire version
  the sender speaks (the hello itself is always encoded in version 1). -/
  | hello (maxVersion : UInt8) (replica : ReplicaId) (digest : Digest)
  /-- "My published state now has this digest." -/
  | digest (d : Digest)
  /-- My whole published state and its digest. -/
  | state (d : Digest) (s : State)
  /-- Please serve these blobs (strictly sorted, 1..maxBatch hashes of 32 bytes). Only ever
  emitted through `Effect.fetch`, so that the host knows which streams to accept. -/
  | want (hs : List Hash)
  /-- I do not have these blobs (answer to `want`). -/
  | noBlob (hs : List Hash)
  /-- I now have these blobs, which I earlier answered `noBlob` for. -/
  | have (hs : List Hash)
  /-- I am closing this session, and why. -/
  | bye (reason : CloseReason)

/-! ## Host → Lean: events -/

/-- A local user operation. The host has already stored every blob a `put` refers to. -/
inductive LocalOp where
  | putMany (items : List PutItem)
  | deleteMany (items : List DeleteItem)
  | resolve (path : String) (h : Hash)

inductive Query where
  | snapshot   -- every path with its versions and whether each blob is present
  | pending    -- every missing blob and where it is being requested from
  | status     -- sessions, persistence, flags
  deriving DecidableEq, Repr, Inhabited

inductive Event where
  /-- Start by restoring the state record exactly as last persisted. `blobs` lists the blob
  hashes present in local storage. If `stored` does not decode, Lean answers
  `startupFailed` and stays uninitialised: it never resets on its own. -/
  | init (self : ReplicaId) (stored : ByteArray) (blobs : List Hash)
  /-- Start with an empty index: first run on this storage, or a reset the user confirmed after
  `startupFailed` (it loses changes never synced). `self` must be a fresh replica id. -/
  | initFresh (self : ReplicaId) (blobs : List Hash)
  | connected (p : PeerId)
  | disconnected (p : PeerId)
  /-- One complete Lean message from `p` (the host reassembles its own fragments). -/
  | received (p : PeerId) (bytes : ByteArray)
  | localOp (op : LocalOp)
  /-- The state of `persist tag` is durably stored; `digest` is SHA-256 of the stored bytes. -/
  | persisted (tag : Nat) (digest : Digest)
  /-- The host could not store the state of `persist tag` (e.g. quota). Lean will issue a new
  persist on a later event; the host decides when to call again (back-off is the host's job). -/
  | persistFailed (tag : Nat)
  /-- Blob `h` was verified and durably stored (`src` = the peer it came from, if any). -/
  | blobStored (h : Hash) (src : Option PeerId)
  /-- These blobs are durably stored: a batch of `blobStored`, used to report the start-up
  inventory in chunks after `init` (send them all before connecting peers). -/
  | blobsStored (hs : List Hash)
  /-- A transfer of `h` from `p` failed (hash mismatch, abort by the sender, size limit). -/
  | blobFailed (p : PeerId) (h : Hash)
  /-- The host found that a blob it had reported present is gone or unreadable. -/
  | blobLost (h : Hash)
  | query (q : Query)

/-! ## Lean → host: effects -/

inductive PeerStatus where
  | handshaking     -- hello not yet exchanged
  | syncing         -- index differs or blobs in flight from this peer
  | inSync          -- same digest, nothing in flight
  deriving DecidableEq, Repr, Inhabited

/-- Where a missing blob is. -/
inductive PendingStatus where
  | requested (p : PeerId)   -- a `want` is outstanding at `p`
  | queued                   -- a greeted ready peer may have it, but its request slots are full
  | waiting                  -- every greeted ready peer said it lacks it (or there is none)
  deriving DecidableEq, Repr, Inhabited

/-- Why a host input was rejected. -/
inductive DecodeError where
  | truncated
  | trailing             -- bytes left over after a complete value
  | tooLarge             -- input, string or batch over its limit
  | badVersion (v : Nat) -- unknown wire version byte
  | badKind (k : Nat)    -- wrong kind byte for this decoder
  | badTag (t : Nat)     -- unknown constructor tag
  | nonCanonical         -- unsorted/duplicate entries, zero counter, overlong varint, dangling dot
  | badUtf8
  deriving DecidableEq, Repr, Inhabited

inductive Notice where
  | indexChanged                          -- the file list or versions changed: re-query
  | blobsChanged                          -- presence or pending status changed: re-query
  | peerStatus (p : PeerId) (s : PeerStatus) (replica : Option ReplicaId)
  | peerClosed (p : PeerId) (reason : CloseReason) (byPeer : Bool)
  | peerLeft (p : PeerId)                -- the host reported the connection gone
  | peerError (p : PeerId) (e : DecodeError)
  /-- A peer knows dots of our replica id that we do not: our storage was rolled back or the id
  is shared. From now on this node refuses local edits and never sends its state; the host
  must restart with a fresh replica id (see the host rule). -/
  | rollbackDetected
  | opRejected (why : String)             -- invalid local op (bad hash size, too long path, too large)
  | badEvent (e : DecodeError)            -- the event envelope did not decode
  /-- The host could not store the state (`persistFailed`): recent changes are not durable, and
  nothing new is sent to peers until a later persist succeeds. Lean retries on the next event. -/
  | saveFailed
  /-- `init` with a stored state that does not decode. Lean stays uninitialised; the host may
  retry, or (after user confirmation) start with `initFresh` and a fresh replica id. -/
  | startupFailed (e : DecodeError)
  /-- Missing blobs: `fetching` are requested from a peer now; `queued` are not requested yet
  but some greeted ready peer may have them (its request slots are full); `waiting` have no
  reachable source (every greeted ready peer lacks them, or none is connected). Emitted
  whenever the triple changes. -/
  | pendingSummary (fetching : Nat) (queued : Nat) (waiting : Nat)
  | notInitialized                        -- an event other than `init` before `init`
  | alreadyInitialized                    -- a second `init`

/-- One version of a file as the UI sees it. -/
structure VersionInfo where
  hash : Hash
  present : Bool

inductive Reply where
  | snapshot (files : List (String × List VersionInfo))
  | pending (items : List (Hash × PendingStatus))
  | status (persistInFlight : Bool) (dirty : Bool) (rollback : Bool)
      (peers : List (PeerId × PeerStatus))

inductive Effect where
  /-- Send one Lean message to `p` (the host fragments it and keeps message boundaries). -/
  | send (p : PeerId) (msg : Message)
  /-- Close the connection to `p` (after sending what precedes this effect). -/
  | close (p : PeerId) (reason : CloseReason)
  /-- Durably store this state (atomically replacing the previous record, together with the
  replica id), then hash the stored bytes and answer `persisted tag digest`. -/
  | persist (tag : Nat) (s : State)
  /-- Send `want hs` to `p` (the envelope carries the encoded message) and accept, verify and
  store the blob streams for `hs` that `p` sends back on this connection. -/
  | fetch (p : PeerId) (hs : List Hash)
  /-- Stream blob `h` from local storage to `p`. -/
  | serveBlob (p : PeerId) (h : Hash)
  | notify (n : Notice)
  | reply (r : Reply)

/-- The peer message an effect puts on the wire, if any. -/
def Effect.sentMessage? : Effect → Option (PeerId × Message)
  | .send p m => some (p, m)
  | .fetch p hs => some (p, .want hs)
  | _ => none

/-! ## Protocol state -/

/-- One live connection. -/
structure Session where
  peer : PeerId
  helloSent : Bool := false
  /-- `some r` once the peer's hello has been received: the session is *ready*. -/
  peerReplica : Option ReplicaId := none
  /-- The last digest the peer announced (in `hello`, `digest` or `state`). -/
  peerDigest : Option Digest := none
  /-- The last digest we announced to the peer. -/
  announced : Option Digest := none
  /-- Digest of the last state we sent to the peer in this session. -/
  lastSent : Option Digest := none
  /-- Blobs requested from this peer and not yet stored, failed or refused. -/
  inflight : List Hash := []
  /-- Blobs this peer said it lacks (or whose transfer from it failed) in this session. -/
  lacks : List Hash := []
  /-- Blobs we told this peer we lack; we send `have` when we obtain them (capped). -/
  toldNo : List Hash := []
  /-- Last status reported to the UI, to notify only on change. -/
  reported : PeerStatus := .handshaking

/-- The last state the host confirmed persisted, with its digest. Only this state is ever sent. -/
structure Published where
  state : State
  digest : Digest

structure Node where
  self : ReplicaId
  /-- Latest state: may contain local dots not yet persisted. -/
  current : State
  /-- Last state confirmed persisted in this run (`none` until the first `persisted`). -/
  published : Option Published := none
  /-- The persist in flight, if any (at most one): its tag and the state it carries. -/
  inflight : Option (Nat × State) := none
  nextTag : Nat := 0
  /-- `current` changed since the last `persist` was issued. -/
  dirty : Bool := false
  /-- The host just reported a failed persist: do not issue the retry in the same step, but on
  the next event (so failures alone cannot drive a write loop). -/
  holdPersist : Bool := false
  /-- Blob hashes present in local storage, strictly sorted. -/
  blobs : List Hash := []
  /-- Hashes referenced by `current` and not in `blobs`, strictly sorted (a cache). -/
  missing : List Hash := []
  /-- Last `pendingSummary` reported. -/
  summary : Nat × Nat × Nat := (0, 0, 0)
  /-- Sessions, strictly sorted by `peer`. -/
  sessions : List Session := []
  /-- A peer revealed dots of `self` beyond `current`: host-rule violation detected. -/
  rollback : Bool := false

/-- What lives in Lean between two calls of the boundary function. -/
inductive Machine where
  | uninit
  | running (n : Node)

instance : Inhabited Machine := ⟨.uninit⟩

end LeanSync
