import LeanSync.Sets

/-!
# The step function

Executable module (imports `Init` only).

`step : Machine → Event → Machine × List Effect` is pure, total and deterministic. A running
node handles the event (`handle`), then always runs the same end-of-step pass (`finish`):

1. **persist**: if no persist is in flight and `current` changed, emit `persist nextTag current`;
2. **reconcile** every session: hello (once `published` exists), then on a ready session either
   the published state (if the peer announced another digest and this state was not yet sent in
   this session, and no rollback was detected) or our digest (if not yet announced);
3. **plan** blob requests (`fetch`), per session up to `maxInflightPerPeer`;
4. **report** peer status changes and the pending summary to the UI.

Save-before-send is structural: the only state ever put in a message is `published`, which is
set only from the persist the host acknowledged (`persisted` with the in-flight tag).
-/

set_option linter.unusedSectionVars false

namespace LeanSync

open LeanCrdt

/-! ## Sessions -/

def Session.ready (s : Session) : Bool := s.peerReplica.isSome

/-- Insert a session keeping the list sorted by peer (the list has at most `maxSessions`). -/
def insertSession (s : Session) : List Session → List Session
  | [] => [s]
  | x :: xs => if compare s.peer x.peer = .lt then s :: x :: xs else x :: insertSession s xs

namespace Node

def findSession? (n : Node) (p : PeerId) : Option Session := n.sessions.find? (·.peer == p)

/-- Replace the session with the same peer. -/
def setSession (n : Node) (s : Session) : Node :=
  { n with sessions := n.sessions.map (fun x => if x.peer == s.peer then s else x) }

def dropSession (n : Node) (p : PeerId) : Node :=
  { n with sessions := n.sessions.filter (fun x => x.peer != p) }

/-- `current` changed: mark dirty and recompute the missing set. -/
def withCurrent (n : Node) (s : State) : Node :=
  { n with current := s, dirty := true, missing := computeMissing s n.blobs }

end Node

/-! ## Blob arrival: presence, inflight, and owed `have` messages -/

/-- Record a batch of stored blobs in one pass: present, no longer missing or in flight anywhere,
and tell every peer we had answered `noBlob` for one of them. Cost: O(b log b + n) for b hashes
and n known blobs, plus O(i·b) per session for its i ≤ `maxInflightPerPeer` requests. -/
def gotBlobs (n : Node) (hs : List Hash) : Node × List Effect :=
  let new := sdiff (sortDedup hs) n.blobs
  if new.isEmpty then (n, [])
  else
    let sessions := n.sessions.map (fun s =>
      { s with inflight := s.inflight.filter (fun h => h ∉ new),
               toldNo := sdiff (sortDedup s.toldNo) new })
    let effs := n.sessions.flatMap (fun s =>
      (sdiff (sortDedup s.toldNo) (sdiff (sortDedup s.toldNo) new)).map (fun h => Effect.send s.peer (.have [h])))
    ({ n with blobs := union new n.blobs, missing := sdiff n.missing new, sessions := sessions }, effs)

/-! ## Local operations -/

def applyOp (s : State) (self : ReplicaId) : LocalOp → State
  | .putMany items => s.putMany self items
  | .deleteMany items => s.deleteMany items
  | .resolve p h => s.resolve self p h

def opHashes : LocalOp → List Hash
  | .putMany items => items.map (·.hash)
  | .deleteMany _ => []
  | .resolve _ h => [h]

/-! ## Messages -/

/-- End a session from our side: say why, close, tell the UI. -/
def closeWith (n : Node) (p : PeerId) (r : CloseReason) (extra : List Effect) : Node × List Effect :=
  (n.dropSession p, [.send p (.bye r), .close p r] ++ extra ++ [.notify (.peerClosed p r false)])

def reasonOfError : DecodeError → CloseReason
  | .badVersion _ => .incompatible
  | _ => .protocolError

/-- Add hashes to `toldNo` (an unordered list), up to `maxToldNo` entries. -/
def addToldNo (told : List Hash) (hs : List Hash) : List Hash :=
  hs.foldl (fun acc h => if h ∉ acc ∧ acc.length < maxToldNo then h :: acc else acc) told

def onMessage (n : Node) (s : Session) (msg : Message) : Node × List Effect :=
  let p := s.peer
  if !s.ready then
    match msg with
    | .hello v r d =>
      if r = n.self then closeWith n p .sameReplicaId []
      else if v = 0 then closeWith n p .incompatible []
      else (n.setSession { s with peerReplica := some r, peerDigest := some d }, [])
    | _ => closeWith n p .protocolError []
  else
    match msg with
    | .hello _ _ _ => closeWith n p .protocolError []
    | .digest d => (n.setSession { s with peerDigest := some d }, [])
    | .state d st =>
      let n1 := n.setSession { s with peerDigest := some d }
      let rb := decide (n.current.context.get n.self < st.context.get n.self)
      let n2 := if rb then { n1 with rollback := true } else n1
      let eRb : List Effect := if rb && !n.rollback then [.notify .rollbackDetected] else []
      let merged := n.current.merge st
      if checkWire merged then
        if State.beq merged n.current then ({ n2 with current := merged }, eRb)
        else (n2.withCurrent merged, eRb ++ [.notify .indexChanged])
      else closeWith n2 p .stateTooLarge eRb
    | .want hs =>
      -- `hs` and `blobs` are sorted: one pass each
      let lack := sdiff hs n.blobs
      let present := sdiff hs lack
      let serve := present.map (fun h => Effect.serveBlob p h)
      if lack.isEmpty then (n, serve)
      else (n.setSession { s with toldNo := addToldNo s.toldNo lack }, serve ++ [.send p (.noBlob lack)])
    | .noBlob hs =>
      let back := s.inflight.filter (fun h => h ∈ hs)
      let keep := s.inflight.filter (fun h => h ∉ hs)
      (n.setSession { s with inflight := keep, lacks := back.foldl (fun acc h => insertH h acc) s.lacks },
        [.notify .blobsChanged])
    | .have hs => (n.setSession { s with lacks := sdiff s.lacks hs }, [.notify .blobsChanged])
    | .bye r => (n.dropSession p, [.close p r, .notify (.peerClosed p r true)])

/-! ## Queries -/

/-- Hashes no greeted ready session can serve: the intersection of their `lacks` (sorted). The
flag says whether there is any greeted ready session at all (if not, nothing has a source). -/
def sourceless (sessions : List Session) : Bool × List Hash :=
  let greeted := sessions.filter (fun s => s.ready && s.helloSent)
  match greeted with
  | [] => (false, [])
  | g :: gs => (true, gs.foldl (fun acc s => sdiff acc (sdiff acc s.lacks)) g.lacks)

def sessionStatus (n : Node) (s : Session) : PeerStatus :=
  if !s.ready then .handshaking
  else match n.published with
    | some P => if s.peerDigest == some P.digest && s.inflight.isEmpty then .inSync else .syncing
    | none => .syncing

def answer (n : Node) : Query → Reply
  | .snapshot =>
    let arr := n.missing.toArray
    .snapshot (n.current.snapshot.map (fun (p, hs) => (p, hs.map (fun h => ⟨h, !binSearch arr h⟩))))
  | .pending =>
    let src := sourceless n.sessions
    let arr := src.2.toArray
    .pending (n.missing.map (fun h =>
      match n.sessions.find? (fun s => h ∈ s.inflight) with
      | some s => (h, .requested s.peer)
      | none => if src.1 && !binSearch arr h then (h, .queued) else (h, .waiting)))
  | .status =>
    .status n.inflight.isSome n.dirty n.rollback (n.sessions.map (fun s => (s.peer, sessionStatus n s)))

/-! ## Handling one event (running node) -/

def handle (n : Node) : Event → Node × List Effect
  | .init _ _ _ => (n, [.notify .alreadyInitialized])
  | .initFresh _ _ => (n, [.notify .alreadyInitialized])
  | .connected p =>
    if (n.findSession? p).isSome then (n, [])
    else if n.sessions.length < maxSessions then
      ({ n with sessions := insertSession { peer := p } n.sessions }, [])
    else (n, [.close p .tooManyPeers, .notify (.peerClosed p .tooManyPeers false)])
  | .disconnected p =>
    if (n.findSession? p).isSome then (n.dropSession p, [.notify (.peerLeft p)]) else (n, [])
  | .received p bytes =>
    match n.findSession? p with
    | none => (n, [])
    | some s =>
      match decodeMessage bytes with
      | .error e => closeWith n p (reasonOfError e) [.notify (.peerError p e)]
      | .ok msg => onMessage n s msg
  | .localOp op =>
    if n.rollback then
      (n, [.notify (.opRejected "rollback detected: restart with a fresh replica id")])
    else
      let s' := applyOp n.current n.self op
      -- an operation that changes nothing (empty batch, deleting an absent path) schedules no
      -- write and no notice; its blobs are still recorded
      if State.beq s' n.current then gotBlobs n (opHashes op)
      else if checkWire s' then
        let r := gotBlobs (n.withCurrent s') (opHashes op)
        (r.1, .notify .indexChanged :: r.2)
      else (n, [.notify (.opRejected "operation exceeds the wire limits (hash size, path length or state size)")])
  | .persisted t d =>
    match n.inflight with
    | some (t', s) => if t' = t then ({ n with published := some ⟨s, d⟩, inflight := none }, []) else (n, [])
    | none => (n, [])
  | .persistFailed t =>
    -- never answer a failure with a new write in the same step: the retry waits for the next
    -- event, so a host whose storage keeps failing cannot be driven into a write loop
    match n.inflight with
    | some (t', _) =>
      if t' = t then ({ n with inflight := none, dirty := true, holdPersist := true }, [.notify .saveFailed])
      else ({ n with holdPersist := true }, [])
    | none => ({ n with holdPersist := true }, [])
  | .blobStored h _ =>
    let r := gotBlobs n [h]
    (r.1, if (sdiff [h] n.blobs).isEmpty then [] else .notify .blobsChanged :: r.2)
  | .blobsStored hs =>
    let r := gotBlobs n hs
    (r.1, if (sdiff (sortDedup hs) n.blobs).isEmpty then [] else .notify .blobsChanged :: r.2)
  | .blobFailed p h =>
    match n.findSession? p with
    | some s =>
      if h ∈ s.inflight then
        (n.setSession { s with inflight := eraseH h s.inflight, lacks := insertH h s.lacks },
          [.notify .blobsChanged])
      else (n, [])
    | none => (n, [])
  | .blobLost h =>
    if h ∈ n.blobs then
      let bl := eraseH h n.blobs
      ({ n with blobs := bl, missing := computeMissing n.current bl }, [.notify .blobsChanged])
    else (n, [])
  | .query q => (n, [.reply (answer n q)])

/-! ## The end-of-step pass -/

def persistPass (n : Node) : Node × List Effect :=
  if n.holdPersist then ({ n with holdPersist := false }, [])
  else if n.inflight.isNone && n.dirty then
    ({ n with inflight := some (n.nextTag, n.current), nextTag := n.nextTag + 1, dirty := false },
      [.persist n.nextTag n.current])
  else (n, [])

/-- What one session needs sent, given the published state. -/
def helloPart (self : ReplicaId) (P : Published) (s : Session) : Session × List Effect :=
  if !s.helloSent then
    ({ s with helloSent := true, announced := some P.digest }, [.send s.peer (.hello 1 self P.digest)])
  else (s, [])

def reconcileSession (self : ReplicaId) (rollback : Bool) (P : Published) (s0 : Session) :
    Session × List Effect :=
  let s := (helloPart self P s0).1
  let e := (helloPart self P s0).2
  if s.ready then
    if !rollback && s.peerDigest != some P.digest && s.lastSent != some P.digest then
      ({ s with lastSent := some P.digest, announced := some P.digest },
        e ++ [.send s.peer (.state P.digest P.state)])
    else if s.announced != some P.digest then
      ({ s with announced := some P.digest }, e ++ [.send s.peer (.digest P.digest)])
    else (s, e)
  else (s, e)

def reconcilePass (n : Node) : Node × List Effect :=
  match n.published with
  | none => (n, [])
  | some P =>
    ({ n with sessions := n.sessions.map (fun s => (reconcileSession n.self n.rollback P s).1) },
      n.sessions.flatMap (fun s => (reconcileSession n.self n.rollback P s).2))

/-- Give each ready session that we have sent our hello to, and that has room, the first missing
hashes that are in flight nowhere and that it has not said it lacks. (No request may precede our
hello: the peer would reject it.) -/
def planGo (missing : List Hash) : List Hash → List Session → List Session → List Effect →
    List Session × List Effect
  | _, [], acc, effs => (acc.reverse, effs)
  | busy, s :: rest, acc, effs =>
    if s.ready && s.helloSent && s.inflight.length < maxInflightPerPeer then
      let cands := (sdiff (sdiff missing busy) s.lacks).take (maxInflightPerPeer - s.inflight.length)
      if cands.isEmpty then planGo missing busy rest (s :: acc) effs
      else planGo missing (union cands busy) rest ({ s with inflight := s.inflight ++ cands } :: acc)
        (effs ++ [.fetch s.peer cands])
    else planGo missing busy rest (s :: acc) effs

def busyOf (sessions : List Session) : List Hash := sortDedup (sessions.flatMap (·.inflight))

def planPass (n : Node) : Node × List Effect :=
  let r := planGo n.missing (busyOf n.sessions) n.sessions [] []
  ({ n with sessions := r.1 }, r.2)

/-- `(fetching, queued, waiting)` for the UI. Fetching: missing and requested from some peer
(walks `missing` only as far as the small set in flight). Waiting: missing, not requested, and
lacked by every greeted ready peer (or there is none). Queued: the rest, i.e. some greeted ready
peer may have it but its request slots are full. -/
def pendingCounts (n : Node) : Nat × Nat × Nat :=
  let busy := busyOf n.sessions
  let fetching := (sdiff busy (sdiff busy n.missing)).length
  let notInFlight := n.missing.length - fetching
  let src := sourceless n.sessions
  let waiting := if src.1 then (sdiff src.2 (sdiff src.2 (sdiff n.missing busy))).length else notInFlight
  (fetching, notInFlight - waiting, waiting)

def reportPass (n : Node) : Node × List Effect :=
  let sessions := n.sessions.map (fun s => { s with reported := sessionStatus n s })
  let effs : List Effect := n.sessions.filterMap (fun s =>
    let st := sessionStatus n s
    if st == s.reported then none else some (.notify (.peerStatus s.peer st s.peerReplica)))
  let sum := pendingCounts n
  let n1 := { n with sessions := sessions }
  if sum == n.summary then (n1, effs)
  else ({ n1 with summary := sum }, effs ++ [.notify (.pendingSummary sum.1 sum.2.1 sum.2.2)])

def finish (n : Node) : Node × List Effect :=
  let r1 := persistPass n
  let r2 := reconcilePass r1.1
  let r3 := planPass r2.1
  let r4 := reportPass r3.1
  (r4.1, r1.2 ++ r2.2 ++ r3.2 ++ r4.2)

/-! ## Start-up and the step function -/

def startNode (self : ReplicaId) (s : State) (blobs : List Hash) : Node × List Effect :=
  let bl := sortDedup blobs
  let n : Node := { self, current := s, blobs := bl, missing := computeMissing s bl, dirty := true }
  let r := finish n
  (r.1, .notify .indexChanged :: r.2)

/-- The protocol: one event in, the new machine and the effects out, in the order the host must
carry them out. Pure, total, deterministic. -/
def step (m : Machine) (ev : Event) : Machine × List Effect :=
  match m with
  | .uninit =>
    match ev with
    | .init self stored blobs =>
      match decodeState stored with
      | .ok s => let r := startNode self s blobs; (.running r.1, r.2)
      | .error err => (.uninit, [.notify (.startupFailed err)])
    | .initFresh self blobs => let r := startNode self State.empty blobs; (.running r.1, r.2)
    | _ => (.uninit, [.notify .notInitialized])
  | .running n =>
    let r1 := handle n ev
    let r2 := finish r1.1
    (.running r2.1, r1.2 ++ r2.2)

/-- Run a sequence of events; returns the final machine and the effects of each step. -/
def run (m : Machine) (evs : List Event) : Machine × List (List Effect) :=
  let r := evs.foldl (fun (acc : Machine × List (List Effect)) ev =>
    ((step acc.1 ev).1, (step acc.1 ev).2 :: acc.2)) (m, [])
  (r.1, r.2.reverse)

end LeanSync
