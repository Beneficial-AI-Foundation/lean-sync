import LeanSync.StepProofs

/-!
# Theorems about the wire format and the sync protocol

Proof-only module. These are the statements fixed in stage 1 (`docs/sync-design.md`), each
proved here from the lemmas in `LeanSync.Wire` and `LeanSync.StepProofs`. Three statements differ
from stage 1; each is marked **CHANGED** with the reason:

* `step_putMany` and `step_settles` gain the hypothesis "no rollback detected": after a rollback
  is detected the node refuses local edits and never sends its state (user decision; the
  stage-1 `step_putMany` was already false under the stage-1 design, which refused local edits).
* `step_plans_blobs` quantifies over ready sessions *to which we have sent our hello*: the
  simulator found that requesting blobs before our own hello makes the peer close the session
  (a real bug, fixed), so no blob is requested on a session before that.

`rollback_no_state` is new. Definitions used below (`Node.Inv`, `Node.Missing`, `effectsAt`,
`AckedBy`, `Message.revealed`, `HostView`, `Executable`) are in `LeanSync.StepProofs` and
`LeanSync.HostModel`.
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

/-! ## 2. Save before send (decision 4), for every event sequence, with no hypothesis -/

/-- Every state that is sent was persisted and acknowledged earlier in the same run. -/
theorem sent_state_acked (evs : List Event) (i : Nat) (p : PeerId) (d : Digest) (s : State)
    (h : Effect.send p (.state d s) ∈ effectsAt evs i) : AckedBy evs i s :=
  sent_state_acked' evs i p d s h

/-- The host rule as an invariant: no message put on the wire by any effect reveals a dot of any
replica `r` beyond what an acknowledged state contains. (Covers every effect and message
constructor, present and future.) -/
theorem save_before_send (evs : List Event) (i : Nat) (e : Effect) (p : PeerId) (m : Message)
    (r : ReplicaId) (h : e ∈ effectsAt evs i) (hm : e.sentMessage? = some (p, m)) :
    m.revealed r = 0 ∨ ∃ s, AckedBy evs i s ∧ m.revealed r ≤ s.context.get r :=
  save_before_send' evs i e p m r h hm

/-- Tags are never reused, so an acknowledgement names exactly one persisted state. -/
theorem persist_tag_unique (evs : List Event) {j j' t : Nat} {s s' : State}
    (h : Effect.persist t s ∈ effectsAt evs j) (h' : Effect.persist t s' ∈ effectsAt evs j') :
    j = j' ∧ s = s' := persist_tag_unique' evs h h'

/-- At most one persist is outstanding: a later persist comes only after the host answered the
earlier one (stored or failed), so the host never has two writes racing. -/
theorem persist_one_in_flight (evs : List Event) {j j' t t' : Nat} {s s' : State}
    (h : Effect.persist t s ∈ effectsAt evs j) (h' : Effect.persist t' s' ∈ effectsAt evs j')
    (hlt : j < j') : ∃ k, j < k ∧ k ≤ j' ∧
      ((∃ d, evs[k]? = some (.persisted t d)) ∨ evs[k]? = some (.persistFailed t)) :=
  persist_one_in_flight' evs h h' hlt

/-! ## 3. Every effect can be carried out -/

theorem effects_executable (evs : List Event) : Executable step {} .uninit evs :=
  effects_executable' evs {} .uninit trivial rfl

/-! ## 4. Node invariant and the per-step guarantees -/

def Session.Ready (s : Session) : Prop := s.peerReplica.isSome = true

theorem step_inv (m : Machine) (ev : Event) (h : m.Inv) : (step m ev).1.Inv := step_inv' m ev h

/-- Once running, a node stays running with the same replica id, and its state only grows:
no step ever loses information (in particular no update is lost across sessions). -/
theorem step_current_grows (n : Node) (ev : Event) (_h : n.Inv) :
    ∃ n', (step (.running n) ev).1 = .running n' ∧ n'.self = n.self ∧
      State.Le n.current n'.current := step_current_grows' n ev

/-- Receiving a state on a ready session merges it, exactly (unless the result would exceed the
wire limit, in which case the session is closed with `stateTooLarge` and nothing changes). -/
theorem step_received_state (n : Node) (p : PeerId) (b : ByteArray) (d : Digest) (s : State)
    (h : n.Inv) (hs : ∃ x ∈ n.sessions, x.peer = p ∧ x.Ready)
    (hdec : decodeMessage b = .ok (.state d s)) (hfit : (n.current.merge s).WireOk) :
    ∃ n', (step (.running n) (.received p b)).1 = .running n' ∧
      n'.current = n.current.merge s := step_received_state' n p b d s h hs hdec hfit

/-- A valid local batch put is applied exactly as the CRDT's `putMany` with this node's id.
**CHANGED**: requires that no rollback was detected (local edits are refused after one). -/
theorem step_putMany (n : Node) (items : List PutItem) (_h : n.Inv) (hrb : n.rollback = false)
    (hfit : (n.current.putMany n.self items).WireOk) :
    ∃ n', (step (.running n) (.localOp (.putMany items))).1 = .running n' ∧
      n'.current = n.current.putMany n.self items := step_putMany' n items hrb hfit

/-- After every step, each ready session is *settled*: we have announced our published digest
to the peer, and either the peer announced the same digest or we have sent it our published
state in this session. (This is the local half of the convergence argument.)
**CHANGED**: requires that no rollback was detected (a node in rollback mode never sends its
state, so its sessions do not settle). -/
theorem step_settles (n : Node) (ev : Event) (h : n.Inv) (n' : Node)
    (hstep : (step (.running n) ev).1 = .running n') (P : Published)
    (hP : n'.published = some P) (hrb : n'.rollback = false) :
    ∀ x ∈ n'.sessions, x.Ready → x.announced = some P.digest ∧
      (x.peerDigest = some P.digest ∨ x.lastSent = some P.digest) :=
  step_settles' n ev h n' hstep P hP hrb

/-- After every step, every missing blob is requested from some peer, or no ready peer we have
greeted can take the request (it said it lacks the blob, or its request window is full).
**CHANGED**: only sessions to which we have sent our hello (`x.helloSent`): a request before our
hello would be rejected by the peer (bug found by the simulator, fixed). -/
theorem step_plans_blobs (n : Node) (ev : Event) (h : n.Inv) (n' : Node)
    (hstep : (step (.running n) ev).1 = .running n') (hb : Hash) (hm : n'.Missing hb) :
    (∃ x ∈ n'.sessions, hb ∈ x.inflight) ∨
    (∀ x ∈ n'.sessions, x.Ready → x.helloSent = true →
      hb ∈ x.lacks ∨ x.inflight.length = maxInflightPerPeer) :=
  step_plans_blobs' n ev h n' hstep hb hm

/-- After every step, we owe no `have`: every blob we told a peer we lack is still absent. -/
theorem step_no_owed_have (n : Node) (ev : Event) (h : n.Inv) (n' : Node)
    (hstep : (step (.running n) ev).1 = .running n') :
    ∀ x ∈ n'.sessions, ∀ hb ∈ x.toldNo, hb ∉ n'.blobs := by
  have hi := step_inv' (.running n) ev h
  rw [hstep] at hi
  exact fun x hx hb hh => ((hi.sessOk x hx).toldNoOk hb hh).2

/-- A received state that knows more of our own dots than we do sets the rollback flag. -/
theorem step_detects_rollback (n : Node) (p : PeerId) (b : ByteArray) (d : Digest) (s : State)
    (h : n.Inv) (hs : ∃ x ∈ n.sessions, x.peer = p ∧ x.Ready)
    (hdec : decodeMessage b = .ok (.state d s))
    (hgt : n.current.context.get n.self < s.context.get n.self) :
    ∃ n', (step (.running n) (.received p b)).1 = .running n' ∧ n'.rollback = true :=
  step_detects_rollback' n p b d s h hs hdec hgt

/-- New: once a rollback was detected, no step sends this node's state. -/
theorem rollback_no_state (n : Node) (ev : Event) (h : n.Inv) (hrb : n.rollback = true)
    (p : PeerId) (d : Digest) (s : State) :
    Effect.send p (.state d s) ∉ (step (.running n) ev).2 := by
  intro he
  rw [step_running] at he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact handle_no_state _ _ p d s he
  · exact rollback_mode_no_state h hrb ev he

/-- New: once a rollback was detected, local operations are rejected: the state is unchanged. -/
theorem rollback_rejects_local (n : Node) (op : LocalOp) (hrb : n.rollback = true) :
    ∃ n', (step (.running n) (.localOp op)).1 = .running n' ∧ n'.current = n.current := by
  refine ⟨_, rfl, ?_⟩
  rw [(finish_core _).current]
  simp only [handle, hrb, ite_true]

/-! ## 5. The effects envelope -/

/-- New: everything `process` outputs is an effects envelope that decodes back to exactly the
effects the step function emitted (or to `[notify (badEvent e)]` for a malformed input). So the
host can decode and carry out every effect, and no session's `lastSent` is ever advanced for a
send the host cannot have received. -/
theorem process_output_decodes (m : Machine) (hm : m.Inv) (input : ByteArray) :
    ∃ effs, decodeEffects (process m input).2 = .ok effs ∧
      ∀ ev, decodeEvent input = .ok ev → effs = (step m ev).2 := by
  unfold process
  split
  · next ev hev =>
    refine ⟨(step m ev).2, decodeEffects_encodeEffects _ (step_effects_ok m hm ev), fun ev' hev' => ?_⟩
    rw [hev] at hev'; cases hev'; rfl
  · next e hev =>
    refine ⟨_, decodeEffects_encodeEffects [.notify (.badEvent e)] (by simp [EffOk]), fun ev' hev' => ?_⟩
    rw [hev] at hev'; cases hev'

end LeanSync
