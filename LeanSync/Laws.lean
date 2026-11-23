import LeanSync.Envelope
import LeanSync.HostModel
import LeanCrdt.Laws

/-!
# Theorems about the wire format and the sync protocol

Proof-only module.

STAGE 1: statements only. Every `sorry` below is marked `STAGE-1 PLACEHOLDER` and is to be
replaced by a proof in stage 2; none may remain at the end of stage 2. The auxiliary
definitions (`effectsAt`, `AckedBy`, `Node.Inv`, ...) are real.
-/

namespace LeanSync

open LeanCrdt

/-! ## 1. Wire format -/

/-- Round trip for states (decision 5). -/
theorem decodeState_encodeState (s : State) (h : s.WireOk) :
    decodeState (encodeState s) = .ok s := decodeState_encodeState' s h

/-- Canonicity: the decoder accepts only the encoding of what it returns. This is the precise form
of "rejects non-canonical input": unsorted or duplicate entries, zero counters, overlong
varints, trailing bytes, and any other second spelling of a state all fail to decode. -/
theorem encodeState_of_decodeState {b : ByteArray} {s : State} (h : decodeState b = .ok s) :
    encodeState s = b := encodeState_of_decodeState' h

/-- Decoded states respect the limits (and, being `State`s, carry the CRDT invariants). -/
theorem wireOk_of_decodeState {b : ByteArray} {s : State} (h : decodeState b = .ok s) :
    s.WireOk := wireOk_of_decodeState' h

/-- Equal digests mean equal states, given a collision-free hash (decision 1). -/
theorem encodeState_inj {a b : State} (ha : a.WireOk) (hb : b.WireOk)
    (h : encodeState a = encodeState b) : a = b := by
  have h1 := decodeState_encodeState' a ha
  rw [h, decodeState_encodeState' b hb] at h1
  exact (Except.ok.inj h1).symm

theorem decodeMessage_encodeMessage (m : Message) (h : m.WireOk) :
    decodeMessage (encodeMessage m) = .ok m :=
  decodeMessage_encodeMessage' m h (size_encodeMessage_le m h)

theorem encodeMessage_of_decodeMessage {b : ByteArray} {m : Message}
    (h : decodeMessage b = .ok m) : encodeMessage m = b := encodeMessage_of_decodeMessage' h

theorem wireOk_of_decodeMessage {b : ByteArray} {m : Message} (h : decodeMessage b = .ok m) :
    m.WireOk := wireOk_of_decodeMessage' h

/-- Oversized input is rejected before it is parsed. -/
theorem decodeMessage_tooLarge {b : ByteArray} (h : maxMessageBytes < b.size) :
    decodeMessage b = .error .tooLarge := decodeMessage_tooLarge' h

/-! ## 2. Trace vocabulary -/

/-- Effects of step `i` (0-based) of a run from the uninitialised machine. -/
def effectsAt (evs : List Event) (i : Nat) : List Effect :=
  ((run .uninit evs).2)[i]?.getD []

/-- `s` was handed to the host by `persist t s` at step `j`, and the host acknowledged tag `t`
at a step `k` with `j < k ≤ i`. -/
def AckedBy (evs : List Event) (i : Nat) (s : State) : Prop :=
  ∃ j k t d, j < k ∧ k ≤ i ∧ Effect.persist t s ∈ effectsAt evs j ∧
    evs[k]? = some (.persisted t d)

/-- How far into replica `r`'s own dots a message reveals. -/
def Message.revealed (r : ReplicaId) : Message → Nat
  | .state _ s => s.context.get r
  | _ => 0

/-! ## 3. Save before send (decision 4), for every event sequence, with no hypothesis -/

/-- Every state that is sent was persisted and acknowledged earlier in the same run. -/
theorem sent_state_acked (evs : List Event) (i : Nat) (p : PeerId) (d : Digest) (s : State)
    (h : Effect.send p (.state d s) ∈ effectsAt evs i) : AckedBy evs i s :=
  sorry -- STAGE-1 PLACEHOLDER

/-- The host rule as an invariant: no message put on the wire by any effect reveals a dot of any
replica `r` beyond what an acknowledged state contains. (Covers every effect and message
constructor, present and future.) -/
theorem save_before_send (evs : List Event) (i : Nat) (e : Effect) (p : PeerId) (m : Message)
    (r : ReplicaId) (h : e ∈ effectsAt evs i) (hm : e.sentMessage? = some (p, m)) :
    m.revealed r = 0 ∨ ∃ s, AckedBy evs i s ∧ m.revealed r ≤ s.context.get r :=
  sorry -- STAGE-1 PLACEHOLDER

/-- Tags are never reused, so an acknowledgement names exactly one persisted state. -/
theorem persist_tag_unique (evs : List Event) {j j' t : Nat} {s s' : State}
    (h : Effect.persist t s ∈ effectsAt evs j) (h' : Effect.persist t s' ∈ effectsAt evs j') :
    j = j' ∧ s = s' := sorry -- STAGE-1 PLACEHOLDER

/-- At most one persist is outstanding: a later persist comes only after the host answered the
earlier one (stored or failed), so the host never has two writes racing. -/
theorem persist_one_in_flight (evs : List Event) {j j' t t' : Nat} {s s' : State}
    (h : Effect.persist t s ∈ effectsAt evs j) (h' : Effect.persist t' s' ∈ effectsAt evs j')
    (hlt : j < j') : ∃ k, j < k ∧ k ≤ j' ∧
      ((∃ d, evs[k]? = some (.persisted t d)) ∨ evs[k]? = some (.persistFailed t)) :=
  sorry -- STAGE-1 PLACEHOLDER

/-! ## 4. Every effect can be carried out -/

theorem effects_executable (evs : List Event) : Executable step {} .uninit evs :=
  sorry -- STAGE-1 PLACEHOLDER

/-! ## 5. Node invariant and the per-step guarantees -/

def Session.Ready (s : Session) : Prop := s.peerReplica.isSome

/-- Missing blob: referenced by the current state, not present locally. -/
def Node.Missing (n : Node) (h : Hash) : Prop := (∃ e ∈ n.current.entries, e.hash = h) ∧ h ∉ n.blobs

structure Node.Inv (n : Node) : Prop where
  currentOk : n.current.WireOk
  publishedOk : ∀ P, n.published = some P → P.state.WireOk
  publishedLe : ∀ P, n.published = some P → State.Le P.state n.current
  inflightLe : ∀ t s, n.inflight = some (t, s) → State.Le s n.current
  tagFresh : ∀ t s, n.inflight = some (t, s) → t < n.nextTag
  blobsSorted : StrictlySorted n.blobs
  sessionsSorted : n.sessions.Pairwise (fun a b => compare a.peer b.peer = .lt)
  sessionCap : n.sessions.length ≤ maxSessions
  inflightCap : ∀ s ∈ n.sessions, s.inflight.length ≤ maxInflightPerPeer
  toldNoCap : ∀ s ∈ n.sessions, s.toldNo.length ≤ maxToldNo

def Machine.Inv : Machine → Prop
  | .uninit => True
  | .running n => n.Inv

theorem step_inv (m : Machine) (ev : Event) (h : m.Inv) : (step m ev).1.Inv :=
  sorry -- STAGE-1 PLACEHOLDER

/-- Once running, a node stays running with the same replica id, and its state only grows:
no step ever loses information (in particular no update is lost across sessions). -/
theorem step_current_grows (n : Node) (ev : Event) (h : n.Inv) :
    ∃ n', (step (.running n) ev).1 = .running n' ∧ n'.self = n.self ∧
      State.Le n.current n'.current := sorry -- STAGE-1 PLACEHOLDER

/-- Receiving a state on a ready session merges it, exactly (unless the result would exceed the
wire limit, in which case the session is closed with `stateTooLarge` and nothing changes). -/
theorem step_received_state (n : Node) (p : PeerId) (b : ByteArray) (d : Digest) (s : State)
    (h : n.Inv) (hs : ∃ x ∈ n.sessions, x.peer = p ∧ x.Ready)
    (hdec : decodeMessage b = .ok (.state d s)) (hfit : (n.current.merge s).WireOk) :
    ∃ n', (step (.running n) (.received p b)).1 = .running n' ∧
      n'.current = n.current.merge s := sorry -- STAGE-1 PLACEHOLDER

/-- A valid local batch put is applied exactly as the CRDT's `putMany` with this node's id. -/
theorem step_putMany (n : Node) (items : List PutItem) (h : n.Inv)
    (hfit : (n.current.putMany n.self items).WireOk) :
    ∃ n', (step (.running n) (.localOp (.putMany items))).1 = .running n' ∧
      n'.current = n.current.putMany n.self items := sorry -- STAGE-1 PLACEHOLDER

/-- After every step, each ready session is *settled*: we have announced our published digest
to the peer, and either the peer announced the same digest or we have sent it our published
state in this session. (This is the local half of the convergence argument.) -/
theorem step_settles (n : Node) (ev : Event) (h : n.Inv) (n' : Node)
    (hstep : (step (.running n) ev).1 = .running n') (P : Published)
    (hP : n'.published = some P) (hrb : n'.rollback = false) :
    ∀ x ∈ n'.sessions, x.Ready → x.announced = some P.digest ∧
      (x.peerDigest = some P.digest ∨ x.lastSent = some P.digest) :=
  sorry -- STAGE-1 PLACEHOLDER

/-- After every step, every missing blob is requested from some peer, or no ready peer can take
the request (it said it lacks the blob, or its request window is full). -/
theorem step_plans_blobs (n : Node) (ev : Event) (h : n.Inv) (n' : Node)
    (hstep : (step (.running n) ev).1 = .running n') (hb : Hash) (hm : n'.Missing hb) :
    (∃ x ∈ n'.sessions, hb ∈ x.inflight) ∨
    (∀ x ∈ n'.sessions, x.Ready → hb ∈ x.lacks ∨ x.inflight.length = maxInflightPerPeer) :=
  sorry -- STAGE-1 PLACEHOLDER

/-- After every step, we owe no `have`: every blob we told a peer we lack is still absent. -/
theorem step_no_owed_have (n : Node) (ev : Event) (h : n.Inv) (n' : Node)
    (hstep : (step (.running n) ev).1 = .running n') :
    ∀ x ∈ n'.sessions, ∀ hb ∈ x.toldNo, hb ∉ n'.blobs := sorry -- STAGE-1 PLACEHOLDER

/-- A received state that knows more of our own dots than we do sets the rollback flag. -/
theorem step_detects_rollback (n : Node) (p : PeerId) (b : ByteArray) (d : Digest) (s : State)
    (h : n.Inv) (hs : ∃ x ∈ n.sessions, x.peer = p ∧ x.Ready)
    (hdec : decodeMessage b = .ok (.state d s))
    (hgt : n.current.context.get n.self < s.context.get n.self) :
    ∃ n', (step (.running n) (.received p b)).1 = .running n' ∧ n'.rollback = true :=
  sorry -- STAGE-1 PLACEHOLDER

end LeanSync
