import LeanSync.Envelope
import LeanSync.HostModel
import LeanCrdt.Laws

/-!
# Lemmas about the step function

Proof-only module: the node invariant and its preservation by every event and pass, and the
facts about effects used by the theorems in `LeanSync.Laws`.
-/

set_option linter.unusedSectionVars false

namespace LeanSync

open LeanCrdt

/-! ## The CRDT order -/

theorem State.le_refl' (a : State) : State.Le a a := State.merge_idem a

theorem State.le_trans' {a b c : State} (h1 : State.Le a b) (h2 : State.Le b c) : State.Le a c := by
  unfold State.Le at *
  rw [← h2, ← State.merge_assoc, h1]

theorem State.le_merge (a b : State) : State.Le a (a.merge b) := by
  unfold State.Le
  rw [← State.merge_assoc, State.merge_idem]

theorem State.le_putSeq (r : ReplicaId) : ∀ (items : List PutItem) (s : State), State.Le s (s.putSeq r items)
  | [], s => State.le_refl' s
  | it :: items, s => by
    simp only [State.putSeq, List.foldl_cons]
    exact State.le_trans' (State.le_put s r it.path it.hash it.supersedes) (State.le_putSeq r items _)

theorem State.le_applyOp (s : State) (r : ReplicaId) (op : LocalOp) : State.Le s (applyOp s r op) := by
  cases op with
  | putMany items => simp only [applyOp]; rw [State.putMany_eq_putSeq]; exact State.le_putSeq r items s
  | deleteMany items => exact State.le_deleteMany s items
  | resolve p h => exact State.le_put s r p h _

theorem State.eq_of_beq {a b : State} (h : State.beq a b = true) : a = b := by
  unfold State.beq at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨he, hc⟩ := h
  have he' : a.entries = b.entries := LawfulBEq.eq_of_beq he
  have hc' : a.context.entries = b.context.entries := LawfulBEq.eq_of_beq hc
  apply State.ext he'
  have : ∀ (u v : VersionVector), u.entries = v.entries → u = v := by
    intro u v huv; cases u; cases v; simp only at huv; subst huv; rfl
  exact this _ _ hc'

/-! ## Wire facts -/

theorem wireOk_empty : State.empty.WireOk := by
  refine ⟨⟨by simp [State.empty], by simp [State.empty, VersionVector.empty],
    by simp [State.empty, VersionVector.empty, varBound], by simp [State.empty, varBound]⟩, ?_⟩
  rw [size_encodeState]
  simp [encState, encStateBody, State.empty, VersionVector.empty, maxStateBytes, encVar]

theorem checkWire_true {s : State} (h : checkWire s = true) : s.WireOk := (checkWire_iff s).1 h

/-! ## Sessions -/

def SessSorted (l : List Session) : Prop := l.Pairwise (fun a b => compare a.peer b.peer = .lt)

/-- Per-session facts kept by the invariant (they depend on the node only through `blobs`). -/
structure SessOk (blobs : List Hash) (s : Session) : Prop where
  inflightCap : s.inflight.length ≤ maxInflightPerPeer
  lacksSorted : StrictlySorted s.lacks
  toldNoCap : s.toldNo.length ≤ maxToldNo
  toldNoOk : ∀ h ∈ s.toldNo, h.bytes.size = hashLen ∧ h ∉ blobs

/-- Missing blob: referenced by the current state, not present locally. -/
def Node.Missing (n : Node) (h : Hash) : Prop := (∃ e ∈ n.current.entries, e.hash = h) ∧ h ∉ n.blobs

structure Node.Inv (n : Node) : Prop where
  currentOk : n.current.WireOk
  publishedOk : ∀ P, n.published = some P → P.state.WireOk
  publishedLe : ∀ P, n.published = some P → State.Le P.state n.current
  inflightOk : ∀ t s, n.inflight = some (t, s) → s.WireOk
  inflightLe : ∀ t s, n.inflight = some (t, s) → State.Le s n.current
  tagFresh : ∀ t s, n.inflight = some (t, s) → t < n.nextTag
  blobsSorted : StrictlySorted n.blobs
  missingSorted : StrictlySorted n.missing
  missingSpec : ∀ h, h ∈ n.missing ↔ n.Missing h
  sessionsSorted : SessSorted n.sessions
  sessionCap : n.sessions.length ≤ maxSessions
  sessOk : ∀ s ∈ n.sessions, SessOk n.blobs s

def Machine.Inv : Machine → Prop
  | .uninit => True
  | .running n => n.Inv

theorem sessSorted_map {l : List Session} (f : Session → Session) (hf : ∀ s, (f s).peer = s.peer)
    (h : SessSorted l) : SessSorted (l.map f) := by
  unfold SessSorted at *
  rw [List.pairwise_map]
  exact h.imp (fun {a b} hab => by rw [hf, hf]; exact hab)

theorem sessSorted_filter {l : List Session} (p : Session → Bool) (h : SessSorted l) :
    SessSorted (l.filter p) := List.Pairwise.filter _ h

theorem peer_ne_of_sorted {l : List Session} (h : SessSorted (x :: l)) : ∀ y ∈ l, y.peer ≠ x.peer := by
  intro y hy e
  have := (List.pairwise_cons.1 h).1 y hy
  rw [e] at this; exact cmp_lt_irrefl _ this

theorem mem_insertSession (s : Session) : ∀ (l : List Session) (x : Session),
    x ∈ insertSession s l ↔ x = s ∨ x ∈ l
  | [], x => by simp [insertSession]
  | y :: ys, x => by
    unfold insertSession
    split
    · simp
    · simp only [List.mem_cons]; rw [mem_insertSession s ys x]; grind

theorem length_insertSession (s : Session) : ∀ (l : List Session), (insertSession s l).length = l.length + 1
  | [] => rfl
  | y :: ys => by unfold insertSession; split <;> simp [length_insertSession s ys]

theorem sorted_insertSession (s : Session) : ∀ (l : List Session), SessSorted l →
    (∀ y ∈ l, y.peer ≠ s.peer) → SessSorted (insertSession s l)
  | [], _, _ => List.pairwise_singleton _ _
  | y :: ys, hl, hne => by
    unfold insertSession
    split
    · next hlt =>
      refine List.pairwise_cons.2 ⟨?_, hl⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hlt
      · exact cmp_lt_trans hlt ((List.pairwise_cons.1 hl).1 z hz)
    · next hge =>
      have hyl : compare y.peer s.peer = .lt := by
        have hne' : y.peer ≠ s.peer := hne y (.head _)
        cases h : compare s.peer y.peer
        · exact absurd h hge
        · exact absurd (cmp_eq_iff.1 h).symm hne'
        · exact cmp_gt_iff.1 h
      refine List.pairwise_cons.2 ⟨?_, sorted_insertSession s ys (List.pairwise_cons.1 hl).2
        (fun z hz => hne z (.tail _ hz))⟩
      intro z hz
      rw [mem_insertSession] at hz
      rcases hz with rfl | hz
      · exact hyl
      · exact (List.pairwise_cons.1 hl).1 z hz

theorem findSession_some {n : Node} {p : PeerId} {s : Session} (h : n.findSession? p = some s) :
    s ∈ n.sessions ∧ s.peer = p := by
  unfold Node.findSession? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem findSession_none {n : Node} {p : PeerId} (h : n.findSession? p = none) :
    ∀ s ∈ n.sessions, s.peer ≠ p := by
  unfold Node.findSession? at h
  intro s hs e
  have := List.find?_eq_none.1 h s hs
  simp [e] at this

theorem find_peer_of_mem : ∀ {l : List Session}, SessSorted l → ∀ {x : Session}, x ∈ l →
    l.find? (·.peer == x.peer) = some x
  | [], _, _, hx => by cases hx
  | y :: ys, hs, x, hx => by
    rw [List.find?_cons]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · have hne := peer_ne_of_sorted hs x hx
      have : (y.peer == x.peer) = false := by simp; exact fun e => hne e.symm
      rw [this]; exact find_peer_of_mem (List.pairwise_cons.1 hs).2 hx

/-- With sorted sessions, a session with peer `p` is the one `findSession?` returns. -/
theorem findSession_of_mem {n : Node} (hs : SessSorted n.sessions) {x : Session} (hx : x ∈ n.sessions) :
    n.findSession? x.peer = some x := find_peer_of_mem hs hx

theorem mem_setSession {n : Node} {s x : Session} (hx : x ∈ (n.setSession s).sessions) :
    x = s ∨ x ∈ n.sessions := by
  simp only [Node.setSession, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  split <;> simp_all

theorem setSession_sorted {n : Node} (s : Session) (h : SessSorted n.sessions) :
    SessSorted (n.setSession s).sessions :=
  sessSorted_map _ (fun x => by split <;> simp_all) h

theorem length_setSession (n : Node) (s : Session) : (n.setSession s).sessions.length = n.sessions.length := by
  simp [Node.setSession]

theorem mem_dropSession {n : Node} {p : PeerId} {x : Session} (hx : x ∈ (n.dropSession p).sessions) :
    x ∈ n.sessions ∧ x.peer ≠ p := by
  simp only [Node.dropSession, List.mem_filter, bne_iff_ne, ne_eq] at hx
  exact hx

/-! ### Invariant under session updates -/

theorem Inv.setSession {n : Node} (h : n.Inv) {s : Session} (hs : SessOk n.blobs s) :
    (n.setSession s).Inv where
  currentOk := h.currentOk
  publishedOk := h.publishedOk
  publishedLe := h.publishedLe
  inflightOk := h.inflightOk
  inflightLe := h.inflightLe
  tagFresh := h.tagFresh
  blobsSorted := h.blobsSorted
  missingSorted := h.missingSorted
  missingSpec := h.missingSpec
  sessionsSorted := setSession_sorted s h.sessionsSorted
  sessionCap := by rw [length_setSession]; exact h.sessionCap
  sessOk := fun x hx => by
    rcases mem_setSession hx with rfl | hx
    · exact hs
    · exact h.sessOk x hx

theorem Inv.dropSession {n : Node} (h : n.Inv) (p : PeerId) : (n.dropSession p).Inv where
  currentOk := h.currentOk
  publishedOk := h.publishedOk
  publishedLe := h.publishedLe
  inflightOk := h.inflightOk
  inflightLe := h.inflightLe
  tagFresh := h.tagFresh
  blobsSorted := h.blobsSorted
  missingSorted := h.missingSorted
  missingSpec := h.missingSpec
  sessionsSorted := sessSorted_filter _ h.sessionsSorted
  sessionCap := Nat.le_trans (List.length_filter_le _ _) h.sessionCap
  sessOk := fun x hx => h.sessOk x (mem_dropSession hx).1

/-! ### Invariant under the other node updates -/

theorem Inv.withCurrent {n : Node} (h : n.Inv) {s : State} (hs : s.WireOk) (hle : State.Le n.current s) :
    (n.withCurrent s).Inv where
  currentOk := hs
  publishedOk := h.publishedOk
  publishedLe := fun P hP => State.le_trans' (h.publishedLe P hP) hle
  inflightOk := h.inflightOk
  inflightLe := fun t s' hi => State.le_trans' (h.inflightLe t s' hi) hle
  tagFresh := h.tagFresh
  blobsSorted := h.blobsSorted
  missingSorted := sorted_computeMissing s h.blobsSorted
  missingSpec := fun z => by
    simp only [Node.withCurrent]; rw [mem_computeMissing s h.blobsSorted]; rfl
  sessionsSorted := h.sessionsSorted
  sessionCap := h.sessionCap
  sessOk := h.sessOk

theorem length_eraseH_le (h : Hash) (l : List Hash) : (eraseH h l).length ≤ l.length :=
  List.length_filter_le _ _

theorem inv_gotBlob {n : Node} (h : n.Inv) (hb : Hash) : (gotBlob n hb).1.Inv := by
  unfold gotBlob
  split
  · exact h
  · next hnot =>
    exact {
      currentOk := h.currentOk
      publishedOk := h.publishedOk
      publishedLe := h.publishedLe
      inflightOk := h.inflightOk
      inflightLe := h.inflightLe
      tagFresh := h.tagFresh
      blobsSorted := sorted_insertH h.blobsSorted
      missingSorted := sorted_eraseH h.missingSorted
      missingSpec := fun z => by
        simp only [Node.Missing]
        rw [mem_eraseH, h.missingSpec z, mem_insertH h.blobsSorted]
        simp only [Node.Missing]; grind
      sessionsSorted := sessSorted_map _ (fun _ => rfl) h.sessionsSorted
      sessionCap := by simpa using h.sessionCap
      sessOk := fun x hx => by
        simp only [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have ho := h.sessOk y hy
        exact {
          inflightCap := Nat.le_trans (length_eraseH_le _ _) ho.inflightCap
          lacksSorted := ho.lacksSorted
          toldNoCap := Nat.le_trans (length_eraseH_le _ _) ho.toldNoCap
          toldNoOk := fun z hz => by
            rw [mem_eraseH] at hz
            obtain ⟨hs, hn⟩ := ho.toldNoOk z hz.1
            refine ⟨hs, ?_⟩
            rw [mem_insertH h.blobsSorted]; simp [hz.2, hn] } }

/-- Facts that `gotBlob` leaves alone. -/
theorem gotBlob_frame (n : Node) (hb : Hash) :
    let n' := (gotBlob n hb).1
    n'.self = n.self ∧ n'.current = n.current ∧ n'.published = n.published ∧ n'.inflight = n.inflight ∧
      n'.nextTag = n.nextTag ∧ n'.rollback = n.rollback ∧ n'.dirty = n.dirty := by
  unfold gotBlob; split <;> simp

theorem inv_gotBlobs {n : Node} (h : n.Inv) (hs : List Hash) : (gotBlobs n hs).1.Inv := by
  unfold gotBlobs
  suffices ∀ (l : List Hash) (acc : Node × List Effect), acc.1.Inv →
      (l.foldl (fun (acc : Node × List Effect) h => ((gotBlob acc.1 h).1, acc.2 ++ (gotBlob acc.1 h).2)) acc).1.Inv by
    exact this hs (n, []) h
  intro l
  induction l with
  | nil => intro acc ha; exact ha
  | cons x xs ih => intro acc ha; exact ih _ (inv_gotBlob ha x)

theorem gotBlobs_frame (n : Node) (hs : List Hash) :
    let n' := (gotBlobs n hs).1
    n'.self = n.self ∧ n'.current = n.current ∧ n'.published = n.published ∧ n'.inflight = n.inflight ∧
      n'.nextTag = n.nextTag ∧ n'.rollback = n.rollback ∧ n'.dirty = n.dirty := by
  unfold gotBlobs
  suffices ∀ (l : List Hash) (acc : Node × List Effect),
      let n' := (l.foldl (fun (acc : Node × List Effect) h => ((gotBlob acc.1 h).1, acc.2 ++ (gotBlob acc.1 h).2)) acc).1
      n'.self = acc.1.self ∧ n'.current = acc.1.current ∧ n'.published = acc.1.published ∧
        n'.inflight = acc.1.inflight ∧ n'.nextTag = acc.1.nextTag ∧ n'.rollback = acc.1.rollback ∧
        n'.dirty = acc.1.dirty by
    exact this hs (n, [])
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ih ((gotBlob acc.1 x).1, acc.2 ++ (gotBlob acc.1 x).2)
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := gotBlob_frame acc.1 x
    simp only [List.foldl_cons]
    exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6, a7.trans b7⟩

theorem closeWith_fst (n : Node) (p : PeerId) (r : CloseReason) (extra : List Effect) :
    (closeWith n p r extra).1 = n.dropSession p := rfl

theorem length_addToldNo (told hs : List Hash) (h : told.length ≤ maxToldNo) :
    (addToldNo told hs).length ≤ maxToldNo := by
  unfold addToldNo
  induction hs generalizing told with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · next hc => simp; omega
    · exact h

theorem mem_addToldNo (told hs : List Hash) (z : Hash) (hz : z ∈ addToldNo told hs) : z ∈ told ∨ z ∈ hs := by
  unfold addToldNo at hz
  induction hs generalizing told with
  | nil => exact .inl hz
  | cons x xs ih =>
    simp only [List.foldl_cons] at hz
    rcases ih _ hz with h | h
    · split at h
      · simp only [List.mem_cons] at h; rcases h with rfl | h; exact .inr (.head _); exact .inl h
      · exact .inl h
    · exact .inr (.tail _ h)

theorem sorted_foldl_insertH (l acc : List Hash) (h : StrictlySorted acc) :
    StrictlySorted (l.foldl (fun acc h => insertH h acc) acc) := by
  induction l generalizing acc with
  | nil => exact h
  | cons x xs ih => exact ih _ (sorted_insertH h)

theorem onMessage_inv {n : Node} (h : n.Inv) {s : Session} (hs : s ∈ n.sessions) {msg : Message}
    (hm : msg.WireOk) : (onMessage n s msg).1.Inv := by
  have ho := h.sessOk s hs
  unfold onMessage
  split
  · split
    · split
      · exact Inv.dropSession h _
      · split
        · exact Inv.dropSession h _
        · exact Inv.setSession h { ho with }
    · exact Inv.dropSession h _
  · cases msg with
    | hello => exact Inv.dropSession h _
    | digest d => exact Inv.setSession h { ho with }
    | state d st =>
      simp only
      have h1 : (n.setSession { s with peerDigest := some d }).Inv := Inv.setSession h { ho with }
      have h2 : (if decide (n.current.context.get n.self < st.context.get n.self) = true then
          { n.setSession { s with peerDigest := some d } with rollback := true }
          else n.setSession { s with peerDigest := some d }).Inv := by
        split
        · exact { h1 with }
        · exact h1
      split
      · next hw =>
        split
        · next hbeq =>
          have he := State.eq_of_beq hbeq
          rw [he]
          split <;> exact { h1 with }
        · apply Inv.withCurrent h2 (checkWire_true hw)
          split <;> exact State.le_merge _ _
      · exact Inv.dropSession h2 _
    | want hs' =>
      simp only
      split
      · exact h
      · apply Inv.setSession h
        exact {
          inflightCap := ho.inflightCap
          lacksSorted := ho.lacksSorted
          toldNoCap := length_addToldNo _ _ ho.toldNoCap
          toldNoOk := fun z hz => by
            rcases mem_addToldNo _ _ z hz with hz | hz
            · exact ho.toldNoOk z hz
            · simp only [List.mem_filter, decide_eq_true_eq] at hz
              exact ⟨hm.2.2.2 z hz.1, hz.2⟩ }
    | noBlob hs' =>
      apply Inv.setSession h
      exact {
        inflightCap := Nat.le_trans (List.length_filter_le _ _) ho.inflightCap
        lacksSorted := sorted_foldl_insertH _ _ ho.lacksSorted
        toldNoCap := ho.toldNoCap
        toldNoOk := ho.toldNoOk }
    | «have» hs' =>
      apply Inv.setSession h
      exact { ho with lacksSorted := ho.lacksSorted.filter _ }
    | bye r => exact Inv.dropSession h _

theorem sessOk_mono {b b' : List Hash} {s : Session} (h : SessOk b s) (hb : ∀ z ∈ b', z ∈ b) :
    SessOk b' s where
  inflightCap := h.inflightCap
  lacksSorted := h.lacksSorted
  toldNoCap := h.toldNoCap
  toldNoOk := fun z hz => ⟨(h.toldNoOk z hz).1, fun hm => (h.toldNoOk z hz).2 (hb z hm)⟩

theorem handle_inv {n : Node} (h : n.Inv) (ev : Event) : (handle n ev).1.Inv := by
  cases ev with
  | init => exact h
  | initFresh => exact h
  | connected p =>
    simp only [handle]
    split
    · exact h
    · split
      · next hnone hlt =>
        have hn : n.findSession? p = none := by
          cases hf : n.findSession? p
          · rfl
          · simp [hf] at hnone
        exact { h with
          sessionsSorted := sorted_insertSession _ _ h.sessionsSorted (findSession_none hn)
          sessionCap := by rw [length_insertSession]; omega
          sessOk := fun x hx => by
            rw [mem_insertSession] at hx
            rcases hx with rfl | hx
            · exact { inflightCap := by simp [maxInflightPerPeer], lacksSorted := List.Pairwise.nil,
                      toldNoCap := by simp [maxToldNo], toldNoOk := by simp }
            · exact h.sessOk x hx }
      · exact h
  | disconnected p =>
    simp only [handle]
    split
    · exact Inv.dropSession h p
    · exact h
  | received p b =>
    simp only [handle]
    split
    · exact h
    · next s hs =>
      split
      · exact Inv.dropSession h p
      · next msg hdec => exact onMessage_inv h (findSession_some hs).1 (wireOk_of_decodeMessage' hdec)
  | localOp op =>
    simp only [handle]
    split
    · exact h
    · split
      · next hw =>
        exact inv_gotBlobs (Inv.withCurrent h (checkWire_true hw) (State.le_applyOp _ _ _)) _
      · exact h
  | persisted t d =>
    simp only [handle]
    split
    · next t' s hi =>
      split
      · next ht =>
        exact { h with
          publishedOk := fun P hP => by
            simp only [Option.some.injEq] at hP; subst hP; exact h.inflightOk t' s hi
          publishedLe := fun P hP => by
            simp only [Option.some.injEq] at hP; subst hP; exact h.inflightLe t' s hi
          inflightOk := fun _ _ hx => by simp at hx
          inflightLe := fun _ _ hx => by simp at hx
          tagFresh := fun _ _ hx => by simp at hx }
      · exact h
    · exact h
  | persistFailed t =>
    simp only [handle]
    split
    · split
      · exact { h with
          inflightOk := fun _ _ hx => by simp at hx
          inflightLe := fun _ _ hx => by simp at hx
          tagFresh := fun _ _ hx => by simp at hx }
      · exact h
    · exact h
  | blobStored hb src => exact inv_gotBlobs h [hb]
  | blobFailed p hb =>
    simp only [handle]
    split
    · next s hs =>
      split
      · have ho := h.sessOk s (findSession_some hs).1
        exact Inv.setSession h { ho with
          inflightCap := Nat.le_trans (length_eraseH_le _ _) ho.inflightCap
          lacksSorted := sorted_insertH ho.lacksSorted }
      · exact h
    · exact h
  | blobLost hb =>
    simp only [handle]
    split
    · exact { h with
        blobsSorted := sorted_eraseH h.blobsSorted
        missingSorted := sorted_computeMissing _ (sorted_eraseH h.blobsSorted)
        missingSpec := fun z => by
          rw [mem_computeMissing _ (sorted_eraseH h.blobsSorted)]; rfl
        sessOk := fun x hx => sessOk_mono (h.sessOk x hx) (fun z hz => ((mem_eraseH z).1 hz).1) }
    · exact h
  | query q => exact h

/-! ### The end-of-step passes -/

theorem persistPass_inv {n : Node} (h : n.Inv) : (persistPass n).1.Inv := by
  unfold persistPass
  split
  · exact { h with
      inflightOk := fun t s hx => by simp only [Option.some.injEq, Prod.mk.injEq] at hx; rw [← hx.2]; exact h.currentOk
      inflightLe := fun t s hx => by
        simp only [Option.some.injEq, Prod.mk.injEq] at hx; rw [← hx.2]; exact State.le_refl' _
      tagFresh := fun t s hx => by simp only [Option.some.injEq, Prod.mk.injEq] at hx; simp only; omega }
  · exact h

theorem reconcileSession_fields (self : ReplicaId) (rb : Bool) (P : Published) (s : Session) :
    let s' := (reconcileSession self rb P s).1
    s'.peer = s.peer ∧ s'.peerReplica = s.peerReplica ∧ s'.peerDigest = s.peerDigest ∧
      s'.inflight = s.inflight ∧ s'.lacks = s.lacks ∧ s'.toldNo = s.toldNo := by
  have hp : let s1 := (helloPart self P s).1
      s1.peer = s.peer ∧ s1.peerReplica = s.peerReplica ∧ s1.peerDigest = s.peerDigest ∧
      s1.inflight = s.inflight ∧ s1.lacks = s.lacks ∧ s1.toldNo = s.toldNo := by
    unfold helloPart; split <;> simp
  unfold reconcileSession
  simp only
  split
  · split
    · simpa using hp
    · split
      · simpa using hp
      · exact hp
  · exact hp

theorem reconcilePass_inv {n : Node} (h : n.Inv) : (reconcilePass n).1.Inv := by
  unfold reconcilePass
  split
  · exact h
  · next P hP =>
    exact { h with
      sessionsSorted := sessSorted_map _ (fun s => (reconcileSession_fields _ _ _ s).1) h.sessionsSorted
      sessionCap := by simpa using h.sessionCap
      sessOk := fun x hx => by
        simp only [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        obtain ⟨-, -, -, h4, h5, h6⟩ := reconcileSession_fields n.self n.rollback P y
        have ho := h.sessOk y hy
        exact { inflightCap := by rw [h4]; exact ho.inflightCap
                lacksSorted := by rw [h5]; exact ho.lacksSorted
                toldNoCap := by rw [h6]; exact ho.toldNoCap
                toldNoOk := by rw [h6]; exact ho.toldNoOk } }

theorem reportPass_inv {n : Node} (h : n.Inv) : (reportPass n).1.Inv := by
  unfold reportPass
  simp only
  have h1 : ({ n with sessions := n.sessions.map (fun s => { s with reported := sessionStatus n s }) } : Node).Inv :=
    { h with
      sessionsSorted := sessSorted_map _ (fun _ => rfl) h.sessionsSorted
      sessionCap := by simpa using h.sessionCap
      sessOk := fun x hx => by
        simp only [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact { h.sessOk y hy with } }
  split
  · exact h1
  · exact { h1 with }

/-! ### Blob planning -/

/-- Two lists related pointwise. -/
inductive Forall2 {α β} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons {a b as bs} : R a b → Forall2 R as bs → Forall2 R (a :: as) (b :: bs)

/-- How `planGo` changes one session: it appends a sorted batch of missing hashes, within the cap,
and only on a ready session. -/
def PlanRel (missing : List Hash) (s s' : Session) : Prop :=
  ∃ c, s' = { s with inflight := s.inflight ++ c } ∧ (∀ h ∈ c, h ∈ missing) ∧
    (c = [] ∨ (s.ready = true ∧ s.inflight.length + c.length ≤ maxInflightPerPeer))

/-- A `fetch` effect produced by planning. -/
def FetchOk (missing : List Hash) (l : List Session) (e : Effect) : Prop :=
  ∃ s ∈ l, ∃ c, e = .fetch s.peer c ∧ s.ready = true ∧ StrictlySorted c ∧ 0 < c.length ∧
    c.length ≤ maxInflightPerPeer ∧ ∀ h ∈ c, h ∈ missing

theorem forall2_inflight {missing : List Hash} : ∀ {l l' : List Session}, Forall2 (PlanRel missing) l l' →
    ∀ x ∈ l, ∀ h ∈ x.inflight, ∃ x' ∈ l', h ∈ x'.inflight
  | [], [], _, x, hx => by cases hx
  | a :: as, b :: bs, .cons hab hr, x, hx => by
    intro h hh
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · obtain ⟨c, rfl, -, -⟩ := hab
      exact ⟨_, .head _, by simp [hh]⟩
    · obtain ⟨x', hx', hh'⟩ := forall2_inflight hr x hx h hh
      exact ⟨x', .tail _ hx', hh'⟩

theorem sorted_take {l : List Hash} (h : StrictlySorted l) (k : Nat) : StrictlySorted (l.take k) :=
  h.sublist (List.take_sublist _ _)

theorem planGo_spec (missing : List Hash) (hm : StrictlySorted missing) :
    ∀ (l : List Session) (busy : List Hash) (acc : List Session) (effs : List Effect),
      StrictlySorted busy → (∀ s ∈ l, StrictlySorted s.lacks) →
      (∀ h ∈ busy, ∃ x ∈ acc ++ l, h ∈ x.inflight) →
      ∃ l' es, planGo missing busy l acc effs = (acc.reverse ++ l', effs ++ es) ∧
        Forall2 (PlanRel missing) l l' ∧ (∀ e ∈ es, FetchOk missing l e) ∧
        ∀ h ∈ missing, (∃ x ∈ acc ++ l', h ∈ x.inflight) ∨
          ∀ s' ∈ l', s'.ready = true → h ∈ s'.lacks ∨ maxInflightPerPeer ≤ s'.inflight.length
  | [], busy, acc, effs, _, _, _ => by
    refine ⟨[], [], by simp [planGo], .nil, by simp, fun h _ => .inr (by simp)⟩
  | s :: rest, busy, acc, effs, hb, hl, hbusy => by
    have hls := hl s (.head _)
    have hrest : ∀ x ∈ rest, StrictlySorted x.lacks := fun x hx => hl x (.tail _ hx)
    have hL := sorted_sdiff (sorted_sdiff hm hb) hls
    have memL : ∀ z, z ∈ sdiff (sdiff missing busy) s.lacks ↔ z ∈ missing ∧ z ∉ busy ∧ z ∉ s.lacks := by
      intro z; rw [mem_sdiff (sorted_sdiff hm hb) hls, mem_sdiff hm hb]; simp [and_assoc]
    unfold planGo
    split
    · next hroom =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hroom
      obtain ⟨hready, hlt⟩ := hroom
      dsimp only
      split
      · next hempty =>
        -- nothing to ask this peer
        have hbusy' : ∀ h ∈ busy, ∃ x ∈ (s :: acc) ++ rest, h ∈ x.inflight := by
          intro h hh
          obtain ⟨x, hx, hxi⟩ := hbusy h hh
          exact ⟨x, by simp at hx ⊢; grind, hxi⟩
        obtain ⟨l', es, heq, hrel, hes, hcov⟩ := planGo_spec missing hm rest busy (s :: acc) effs hb hrest hbusy'
        refine ⟨s :: l', es, by rw [heq]; simp, .cons ⟨[], by simp, by simp, .inl rfl⟩ hrel,
          fun e he => by obtain ⟨x, hx, rest'⟩ := hes e he; exact ⟨x, .tail _ hx, rest'⟩, ?_⟩
        intro h hh
        rcases hcov h hh with ⟨x, hx, hxi⟩ | hall
        · exact .inl ⟨x, by simp at hx ⊢; grind, hxi⟩
        · -- the candidate list was empty, so `h` is busy or lacked
          have hL0 : sdiff (sdiff missing busy) s.lacks = [] := by
            simp only [List.isEmpty_iff, List.take_eq_nil_iff] at hempty
            rcases hempty with h0 | h0
            · omega
            · exact h0
          by_cases hbz : h ∈ busy
          · obtain ⟨x, hx, hxi⟩ := hbusy h hbz
            simp only [List.mem_append, List.mem_cons] at hx
            rcases hx with hx | rfl | hx
            · exact .inl ⟨x, by simp [hx], hxi⟩
            · exact .inl ⟨x, by simp, hxi⟩
            · obtain ⟨x', hx', hxi'⟩ := forall2_inflight hrel x hx h hxi
              exact .inl ⟨x', by simp [hx'], hxi'⟩
          · by_cases hlz : h ∈ s.lacks
            · refine .inr ?_
              intro s' hs'
              simp only [List.mem_cons] at hs'
              rcases hs' with rfl | hs'
              · exact fun _ => .inl hlz
              · exact hall s' hs'
            · have : h ∈ sdiff (sdiff missing busy) s.lacks := (memL h).2 ⟨hh, hbz, hlz⟩
              rw [hL0] at this; cases this
      · next hne =>
        let k := maxInflightPerPeer - s.inflight.length
        let cands := (sdiff (sdiff missing busy) s.lacks).take k
        have hcs : StrictlySorted cands := sorted_take hL k
        have hcm : ∀ z ∈ cands, z ∈ missing := fun z hz => ((memL z).1 (List.mem_of_mem_take hz)).1
        have hclen : cands.length ≤ k := List.length_take_le _ _
        let s' : Session := { s with inflight := s.inflight ++ cands }
        have hbusy' : ∀ h ∈ union cands busy, ∃ x ∈ (s' :: acc) ++ rest, h ∈ x.inflight := by
          intro h hh
          rw [mem_union h hcs hb] at hh
          rcases hh with hh | hh
          · exact ⟨s', by simp, by simp [s', hh]⟩
          · obtain ⟨x, hx, hxi⟩ := hbusy h hh
            simp only [List.mem_append, List.mem_cons] at hx
            rcases hx with hx | rfl | hx
            · exact ⟨x, by simp [hx], hxi⟩
            · exact ⟨s', by simp, by simp [s', hxi]⟩
            · exact ⟨x, by simp [hx], hxi⟩
        obtain ⟨l', es, heq, hrel, hes, hcov⟩ :=
          planGo_spec missing hm rest (union cands busy) (s' :: acc) (effs ++ [.fetch s.peer cands])
            (sorted_union hcs hb) hrest hbusy'
        refine ⟨s' :: l', .fetch s.peer cands :: es, by rw [heq]; simp [s', cands, k],
          .cons ⟨cands, rfl, hcm, .inr ⟨hready, by omega⟩⟩ hrel, ?_, ?_⟩
        · intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · refine ⟨s, .head _, cands, rfl, hready, hcs, ?_, by omega, hcm⟩
            cases hc : cands with
            | nil => simp [cands, k, hc] at hne
            | cons _ _ => simp
          · obtain ⟨x, hx, rest'⟩ := hes e he; exact ⟨x, .tail _ hx, rest'⟩
        · intro h hh
          rcases hcov h hh with ⟨x, hx, hxi⟩ | hall
          · exact .inl ⟨x, by simp at hx ⊢; grind, hxi⟩
          · by_cases hfull : maxInflightPerPeer ≤ s'.inflight.length
            · exact .inr (fun x hx => by
                simp only [List.mem_cons] at hx
                rcases hx with rfl | hx
                · exact fun _ => .inr hfull
                · exact hall x hx)
            · -- not full: the whole candidate list was taken
              have hall' : cands = sdiff (sdiff missing busy) s.lacks := by
                apply List.take_of_length_le
                have : s'.inflight.length = s.inflight.length + cands.length := by simp [s']
                have hk : cands.length = min k (sdiff (sdiff missing busy) s.lacks).length := List.length_take
                omega
              by_cases hbz : h ∈ busy
              · exact .inl (by
                  obtain ⟨x, hx, hxi⟩ := hbusy h hbz
                  simp only [List.mem_append, List.mem_cons] at hx
                  rcases hx with hx | rfl | hx
                  · exact ⟨x, by simp [hx], hxi⟩
                  · exact ⟨s', by simp, by simp [s', hxi]⟩
                  · obtain ⟨x', hx', hxi'⟩ := forall2_inflight hrel x hx h hxi
                    exact ⟨x', by simp [hx'], hxi'⟩)
              · by_cases hlz : h ∈ s.lacks
                · exact .inr (fun x hx => by
                    simp only [List.mem_cons] at hx
                    rcases hx with rfl | hx
                    · exact fun _ => .inl hlz
                    · exact hall x hx)
                · have hin : h ∈ cands := by rw [hall']; exact (memL h).2 ⟨hh, hbz, hlz⟩
                  exact .inl ⟨s', by simp, by simp [s', hin]⟩
    · next hnoroom =>
      have hbusy' : ∀ h ∈ busy, ∃ x ∈ (s :: acc) ++ rest, h ∈ x.inflight := by
        intro h hh
        obtain ⟨x, hx, hxi⟩ := hbusy h hh
        exact ⟨x, by simp at hx ⊢; grind, hxi⟩
      obtain ⟨l', es, heq, hrel, hes, hcov⟩ := planGo_spec missing hm rest busy (s :: acc) effs hb hrest hbusy'
      refine ⟨s :: l', es, by rw [heq]; simp, .cons ⟨[], by simp, by simp, .inl rfl⟩ hrel,
        fun e he => by obtain ⟨x, hx, rest'⟩ := hes e he; exact ⟨x, .tail _ hx, rest'⟩, ?_⟩
      intro h hh
      rcases hcov h hh with ⟨x, hx, hxi⟩ | hall
      · exact .inl ⟨x, by simp at hx ⊢; grind, hxi⟩
      · refine .inr (fun x hx => ?_)
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · intro hr
          simp only [hr, Bool.true_and, decide_eq_true_eq, Nat.not_lt] at hnoroom
          exact .inr hnoroom
        · exact hall x hx

theorem forall2_mem {α β} {R : α → β → Prop} : ∀ {l : List α} {l' : List β}, Forall2 R l l' →
    ∀ y' ∈ l', ∃ y ∈ l, R y y'
  | [], [], .nil, y', hy => by cases hy
  | a :: as, b :: bs, .cons hab hr, y', hy => by
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨a, .head _, hab⟩
    · obtain ⟨y, hy, hr'⟩ := forall2_mem hr y' hy; exact ⟨y, .tail _ hy, hr'⟩

theorem forall2_length {α β} {R : α → β → Prop} : ∀ {l : List α} {l' : List β}, Forall2 R l l' →
    l'.length = l.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ hr => by simp [forall2_length hr]

theorem planRel_peer {missing : List Hash} {s s' : Session} (h : PlanRel missing s s') : s'.peer = s.peer := by
  obtain ⟨c, rfl, -, -⟩ := h; rfl

theorem sessSorted_of_forall2 {missing : List Hash} : ∀ {l l' : List Session},
    Forall2 (PlanRel missing) l l' → SessSorted l → SessSorted l'
  | [], [], .nil, _ => List.Pairwise.nil
  | a :: as, b :: bs, .cons hab hr, hs => by
    refine List.pairwise_cons.2 ⟨?_, sessSorted_of_forall2 hr (List.pairwise_cons.1 hs).2⟩
    intro y' hy'
    obtain ⟨y, hy, hyy⟩ := forall2_mem hr y' hy'
    rw [planRel_peer hab, planRel_peer hyy]
    exact (List.pairwise_cons.1 hs).1 y hy

theorem mem_busyOf {l : List Session} {h : Hash} (hh : h ∈ busyOf l) : ∃ x ∈ l, h ∈ x.inflight := by
  unfold busyOf at hh
  rw [mem_sortDedup, List.mem_flatMap] at hh
  exact hh

/-- The spec of the planning pass, instantiated. -/
theorem planPass_spec {n : Node} (h : n.Inv) :
    ∃ l', (planPass n).1 = { n with sessions := l' } ∧ Forall2 (PlanRel n.missing) n.sessions l' ∧
      (∀ e ∈ (planPass n).2, FetchOk n.missing n.sessions e) ∧
      ∀ hb ∈ n.missing, (∃ x ∈ l', hb ∈ x.inflight) ∨
        ∀ s' ∈ l', s'.ready = true → hb ∈ s'.lacks ∨ maxInflightPerPeer ≤ s'.inflight.length := by
  obtain ⟨l', es, heq, hrel, hes, hcov⟩ := planGo_spec n.missing h.missingSorted n.sessions (busyOf n.sessions)
    [] [] (sorted_sortDedup _) (fun x hx => (h.sessOk x hx).lacksSorted)
    (fun hb hh => by simpa using mem_busyOf hh)
  refine ⟨l', by simp [planPass, heq], hrel, by simpa [planPass, heq] using hes, fun hb hh => ?_⟩
  rcases hcov hb hh with ⟨x, hx, hxi⟩ | hall
  · exact .inl ⟨x, by simpa using hx, hxi⟩
  · exact .inr hall

theorem planPass_inv {n : Node} (h : n.Inv) : (planPass n).1.Inv := by
  obtain ⟨l', heq, hrel, -, -⟩ := planPass_spec h
  rw [heq]
  exact { h with
    sessionsSorted := sessSorted_of_forall2 hrel h.sessionsSorted
    sessionCap := by rw [forall2_length hrel]; exact h.sessionCap
    sessOk := fun x' hx' => by
      obtain ⟨x, hx, c, rfl, -, hc⟩ := forall2_mem hrel x' hx'
      have ho := h.sessOk x hx
      exact { ho with
        inflightCap := by
          rcases hc with rfl | ⟨-, hc⟩
          · simpa using ho.inflightCap
          · simpa using hc } }

theorem finish_inv {n : Node} (h : n.Inv) : (finish n).1.Inv := by
  unfold finish
  exact reportPass_inv (planPass_inv (reconcilePass_inv (persistPass_inv h)))

theorem startNode_inv (self : ReplicaId) {s : State} (hs : s.WireOk) (blobs : List Hash) :
    (startNode self s blobs).1.Inv := by
  unfold startNode
  apply finish_inv
  exact {
    currentOk := hs
    publishedOk := fun _ hP => by simp at hP
    publishedLe := fun _ hP => by simp at hP
    inflightOk := fun _ _ hx => by simp at hx
    inflightLe := fun _ _ hx => by simp at hx
    tagFresh := fun _ _ hx => by simp at hx
    blobsSorted := sorted_sortDedup _
    missingSorted := sorted_computeMissing _ (sorted_sortDedup _)
    missingSpec := fun z => by rw [mem_computeMissing _ (sorted_sortDedup _)]; rfl
    sessionsSorted := List.Pairwise.nil
    sessionCap := by simp [maxSessions]
    sessOk := fun _ hx => by simp at hx }

theorem step_inv' (m : Machine) (ev : Event) (h : m.Inv) : (step m ev).1.Inv := by
  cases m with
  | uninit =>
    cases ev with
    | init self stored blobs =>
      simp only [step]
      split
      · next s hdec => exact startNode_inv self (wireOk_of_decodeState' hdec) blobs
      · trivial
    | initFresh self blobs => exact startNode_inv self wireOk_empty blobs
    | _ => trivial
  | running n => exact finish_inv (handle_inv h ev)

/-! ## What each part of a step changes -/

/-- The fields the end-of-step passes never change. -/
structure Core (n n' : Node) : Prop where
  self : n'.self = n.self
  current : n'.current = n.current
  published : n'.published = n.published
  rollback : n'.rollback = n.rollback
  blobs : n'.blobs = n.blobs
  missing : n'.missing = n.missing

theorem Core.trans {a b c : Node} (h1 : Core a b) (h2 : Core b c) : Core a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3, h2.4.trans h1.4, h2.5.trans h1.5, h2.6.trans h1.6⟩

theorem persistPass_core (n : Node) : Core n (persistPass n).1 := by
  unfold persistPass; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem reconcilePass_core (n : Node) : Core n (reconcilePass n).1 := by
  unfold reconcilePass; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem planPass_core (n : Node) : Core n (planPass n).1 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem reportPass_core (n : Node) : Core n (reportPass n).1 := by
  unfold reportPass; simp only; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem finish_core (n : Node) : Core n (finish n).1 :=
  (persistPass_core n).trans ((reconcilePass_core _).trans ((planPass_core _).trans (reportPass_core _)))

theorem onMessage_grows (n : Node) (s : Session) (msg : Message) :
    (onMessage n s msg).1.self = n.self ∧ State.Le n.current (onMessage n s msg).1.current := by
  unfold onMessage
  split
  · split
    · split
      · exact ⟨rfl, State.le_refl' _⟩
      · split <;> exact ⟨rfl, State.le_refl' _⟩
    · exact ⟨rfl, State.le_refl' _⟩
  · cases msg with
    | state d st =>
      simp only
      split
      · split
        · split <;> exact ⟨rfl, State.le_merge _ _⟩
        · split <;> exact ⟨rfl, State.le_merge _ _⟩
      · split <;> exact ⟨rfl, State.le_refl' _⟩
    | want hs => simp only; split <;> exact ⟨rfl, State.le_refl' _⟩
    | _ => exact ⟨rfl, State.le_refl' _⟩

theorem handle_grows (n : Node) (ev : Event) :
    (handle n ev).1.self = n.self ∧ State.Le n.current (handle n ev).1.current := by
  cases ev with
  | received p b =>
    simp only [handle]
    split
    · exact ⟨rfl, State.le_refl' _⟩
    · split
      · exact ⟨rfl, State.le_refl' _⟩
      · exact onMessage_grows _ _ _
  | localOp op =>
    simp only [handle]
    split
    · exact ⟨rfl, State.le_refl' _⟩
    · split
      · obtain ⟨h1, h2, -⟩ := gotBlobs_frame (n.withCurrent (applyOp n.current n.self op)) (opHashes op)
        exact ⟨h1, by rw [h2]; exact State.le_applyOp _ _ _⟩
      · exact ⟨rfl, State.le_refl' _⟩
  | blobStored hb src =>
    obtain ⟨h1, h2, -⟩ := gotBlobs_frame n [hb]
    exact ⟨h1, by simp only [handle]; rw [h2]; exact State.le_refl' _⟩
  | connected p => simp only [handle]; split; exact ⟨rfl, State.le_refl' _⟩; split <;> exact ⟨rfl, State.le_refl' _⟩
  | disconnected p => simp only [handle]; split <;> exact ⟨rfl, State.le_refl' _⟩
  | persisted t d => simp only [handle]; split; split <;> exact ⟨rfl, State.le_refl' _⟩; exact ⟨rfl, State.le_refl' _⟩
  | persistFailed t => simp only [handle]; split; split <;> exact ⟨rfl, State.le_refl' _⟩; exact ⟨rfl, State.le_refl' _⟩
  | blobFailed p hb =>
    simp only [handle]; split; split <;> exact ⟨rfl, State.le_refl' _⟩; exact ⟨rfl, State.le_refl' _⟩
  | blobLost hb => simp only [handle]; split <;> exact ⟨rfl, State.le_refl' _⟩
  | init => exact ⟨rfl, State.le_refl' _⟩
  | initFresh => exact ⟨rfl, State.le_refl' _⟩
  | query q => exact ⟨rfl, State.le_refl' _⟩

theorem step_current_grows' (n : Node) (ev : Event) :
    ∃ n', (step (.running n) ev).1 = .running n' ∧ n'.self = n.self ∧ State.Le n.current n'.current := by
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [(finish_core _).self]; exact (handle_grows n ev).1
  · rw [(finish_core _).current]; exact (handle_grows n ev).2

/-- A ready session's message reaches `onMessage` with that session. -/
theorem handle_received {n : Node} (h : n.Inv) {x : Session} (hx : x ∈ n.sessions) {b : ByteArray}
    {msg : Message} (hdec : decodeMessage b = .ok msg) :
    handle n (.received x.peer b) = onMessage n x msg := by
  simp only [handle, findSession_of_mem h.sessionsSorted hx, hdec]

theorem onMessage_state {n : Node} {x : Session} (hr : x.ready = true) (d : Digest) (s : State)
    (hfit : (n.current.merge s).WireOk) :
    (onMessage n x (.state d s)).1.current = n.current.merge s ∧
    (n.current.context.get n.self < s.context.get n.self → (onMessage n x (.state d s)).1.rollback = true) := by
  have hw : checkWire (n.current.merge s) = true := (checkWire_iff _).2 hfit
  unfold onMessage
  simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false, hw, ite_true]
  split
  · refine ⟨by split <;> rfl, fun hlt => ?_⟩
    have : decide (n.current.context.get n.self < s.context.get n.self) = true := decide_eq_true hlt
    simp only [this, ite_true]
  · refine ⟨by split <;> rfl, fun hlt => ?_⟩
    have : decide (n.current.context.get n.self < s.context.get n.self) = true := decide_eq_true hlt
    simp only [Node.withCurrent, this, ite_true]

theorem step_received_state' (n : Node) (p : PeerId) (b : ByteArray) (d : Digest) (s : State)
    (h : n.Inv) (hs : ∃ x ∈ n.sessions, x.peer = p ∧ x.ready = true)
    (hdec : decodeMessage b = .ok (.state d s)) (hfit : (n.current.merge s).WireOk) :
    ∃ n', (step (.running n) (.received p b)).1 = .running n' ∧ n'.current = n.current.merge s := by
  obtain ⟨x, hx, rfl, hr⟩ := hs
  refine ⟨_, rfl, ?_⟩
  try simp only [step]
  rw [(finish_core _).current, handle_received h hx hdec]
  exact (onMessage_state hr d s hfit).1

theorem step_detects_rollback' (n : Node) (p : PeerId) (b : ByteArray) (d : Digest) (s : State)
    (h : n.Inv) (hs : ∃ x ∈ n.sessions, x.peer = p ∧ x.ready = true)
    (hdec : decodeMessage b = .ok (.state d s))
    (hgt : n.current.context.get n.self < s.context.get n.self) :
    ∃ n', (step (.running n) (.received p b)).1 = .running n' ∧ n'.rollback = true := by
  obtain ⟨x, hx, rfl, hr⟩ := hs
  refine ⟨_, rfl, ?_⟩
  try simp only [step]
  rw [(finish_core _).rollback, handle_received h hx hdec]
  unfold onMessage
  simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false, hgt, decide_true, ite_true]
  split
  · split <;> rfl
  · rfl

theorem step_putMany' (n : Node) (items : List PutItem) (hrb : n.rollback = false)
    (hfit : (n.current.putMany n.self items).WireOk) :
    ∃ n', (step (.running n) (.localOp (.putMany items))).1 = .running n' ∧
      n'.current = n.current.putMany n.self items := by
  refine ⟨_, rfl, ?_⟩
  try simp only [step]
  rw [(finish_core _).current]
  have hw : checkWire (applyOp n.current n.self (.putMany items)) = true := (checkWire_iff _).2 hfit
  simp only [handle, hrb, Bool.false_eq_true, ite_false, hw, ite_true]
  rw [(gotBlobs_frame _ _).2.1]
  rfl

/-! ## Settled sessions and planned blobs -/

/-- The session fields that only reconciliation and message handling touch. -/
def SyncFields (s : Session) : Option ReplicaId × Option Digest × Option Digest × Option Digest :=
  (s.peerReplica, s.peerDigest, s.announced, s.lastSent)

theorem reconcileSession_settles (self : ReplicaId) (P : Published) (s : Session)
    (hr : s.peerReplica.isSome = true) :
    let s' := (reconcileSession self false P s).1
    s'.peerReplica = s.peerReplica ∧ s'.announced = some P.digest ∧
      (s'.peerDigest = some P.digest ∨ s'.lastSent = some P.digest) := by
  have hp : let s1 := (helloPart self P s).1
      s1.peerReplica = s.peerReplica ∧ s1.peerDigest = s.peerDigest ∧ s1.lastSent = s.lastSent := by
    unfold helloPart; split <;> simp
  obtain ⟨h1, h2, h3⟩ := hp
  have hready : (helloPart self P s).1.ready = true := by simp [Session.ready, h1, hr]
  unfold reconcileSession
  simp only [hready, ite_true, Bool.not_false, Bool.true_and]
  split
  · next hc => exact ⟨h1, rfl, .inr rfl⟩
  · next hc =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at hc
    split
    · refine ⟨h1, rfl, ?_⟩
      by_cases hd : (helloPart self P s).1.peerDigest = some P.digest
      · exact .inl hd
      · exact .inr (hc hd)
    · next ha =>
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at ha
      refine ⟨h1, ha, ?_⟩
      by_cases hd : (helloPart self P s).1.peerDigest = some P.digest
      · exact .inl hd
      · exact .inr (hc hd)

theorem step_settles' (n : Node) (ev : Event) (h : n.Inv) (n' : Node)
    (hstep : (step (.running n) ev).1 = .running n') (P : Published)
    (hP : n'.published = some P) (hrb : n'.rollback = false) :
    ∀ x ∈ n'.sessions, x.peerReplica.isSome = true → x.announced = some P.digest ∧
      (x.peerDigest = some P.digest ∨ x.lastSent = some P.digest) := by
  simp only [step, Machine.running.injEq] at hstep
  subst hstep
  let n1 := (handle n ev).1
  let r1 := persistPass n1
  have hcore1 := persistPass_core n1
  have hinv2 : (reconcilePass r1.1).1.Inv := reconcilePass_inv (persistPass_inv (handle_inv h ev))
  have hfin := finish_core n1
  have hpub : r1.1.published = some P := by
    rw [hcore1.published]; rw [← hfin.published]; exact hP
  have hrb1 : r1.1.rollback = false := by
    rw [hcore1.rollback]; rw [← hfin.rollback]; exact hrb
  -- sessions after reconciliation
  have hrec : (reconcilePass r1.1).1.sessions =
      r1.1.sessions.map (fun s => (reconcileSession r1.1.self false P s).1) := by
    unfold reconcilePass; rw [hpub]; simp [hrb1]
  obtain ⟨l', heq, hrel, -, -⟩ := planPass_spec hinv2
  intro x hx hready
  -- `x` comes from `l'` through the report pass, which only sets `reported`
  have hx' : ∃ y ∈ l', SyncFields y = SyncFields x := by
    change x ∈ (reportPass (planPass (reconcilePass r1.1).1).1).1.sessions at hx
    unfold reportPass at hx
    rw [heq] at hx
    simp only at hx
    split at hx <;> (simp only [List.mem_map] at hx; obtain ⟨y, hy, rfl⟩ := hx; exact ⟨y, hy, rfl⟩)
  obtain ⟨y, hy, hyx⟩ := hx'
  obtain ⟨z, hz, c, rfl, -, -⟩ := forall2_mem hrel y hy
  rw [hrec] at hz
  simp only [List.mem_map] at hz
  obtain ⟨w, -, rfl⟩ := hz
  simp only [SyncFields, Prod.mk.injEq] at hyx
  obtain ⟨e1, e2, e3, e4⟩ := hyx
  have hw : w.peerReplica.isSome = true := by
    have := (reconcileSession_fields r1.1.self false P w).2.1
    rw [← this]; rw [e1]; exact hready
  obtain ⟨-, ha, hd⟩ := reconcileSession_settles r1.1.self P w hw
  rw [← e3, ← e2, ← e4]
  exact ⟨ha, hd⟩

theorem step_plans_blobs' (n : Node) (ev : Event) (h : n.Inv) (n' : Node)
    (hstep : (step (.running n) ev).1 = .running n') (hb : Hash) (hm : n'.Missing hb) :
    (∃ x ∈ n'.sessions, hb ∈ x.inflight) ∨
    (∀ x ∈ n'.sessions, x.peerReplica.isSome = true → hb ∈ x.lacks ∨ x.inflight.length = maxInflightPerPeer) := by
  have hinv' : n'.Inv := by
    have := step_inv' (.running n) ev h; rw [hstep] at this; exact this
  have hmiss : hb ∈ n'.missing := (hinv'.missingSpec hb).2 hm
  simp only [step, Machine.running.injEq] at hstep
  subst hstep
  let n2 := (reconcilePass (persistPass (handle n ev).1).1).1
  have hinv2 : n2.Inv := reconcilePass_inv (persistPass_inv (handle_inv h ev))
  obtain ⟨l', heq, hrel, -, hcov⟩ := planPass_spec hinv2
  have hm2 : hb ∈ n2.missing := by
    have hc := (planPass_core n2).trans (reportPass_core (planPass n2).1)
    rw [← hc.missing]; exact hmiss
  -- the report pass keeps inflight, lacks and peerReplica
  have hsess : (reportPass (planPass n2).1).1.sessions =
      l'.map (fun s => { s with reported := sessionStatus (planPass n2).1 s }) := by
    unfold reportPass; rw [heq]; simp only; split <;> rfl
  change (∃ x ∈ (reportPass (planPass n2).1).1.sessions, hb ∈ x.inflight) ∨
    ∀ x ∈ (reportPass (planPass n2).1).1.sessions, x.peerReplica.isSome = true →
      hb ∈ x.lacks ∨ x.inflight.length = maxInflightPerPeer
  have hcap : ∀ x ∈ (reportPass (planPass n2).1).1.sessions, x.inflight.length ≤ maxInflightPerPeer :=
    fun x hx => (hinv'.sessOk x hx).inflightCap
  rw [hsess] at hcap ⊢
  rcases hcov hb hm2 with ⟨x, hx, hxi⟩ | hall
  · exact .inl ⟨_, List.mem_map_of_mem hx, hxi⟩
  · refine .inr (fun x hx hr => ?_)
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rcases hall y hy (by simpa [Session.ready] using hr) with h1 | h2
    · exact .inl h1
    · exact .inr (Nat.le_antisymm (hcap _ (List.mem_map_of_mem hy)) h2)

/-! ## What a step emits -/

/-- The effects `handle` may emit: no persist, no state, no hello/digest, no fetch. -/
def HandleEff : Effect → Prop
  | .send _ (.bye _) => True
  | .send _ (.have _) => True
  | .send _ (.noBlob _) => True
  | .close _ _ => True
  | .serveBlob _ _ => True
  | .notify _ => True
  | .reply _ => True
  | _ => False

theorem gotBlob_effs (n : Node) (hb : Hash) : ∀ e ∈ (gotBlob n hb).2,
    ∃ s ∈ n.sessions, hb ∈ s.toldNo ∧ e = .send s.peer (.have [hb]) := by
  unfold gotBlob
  split
  · simp
  · intro e he
    simp only [List.mem_filterMap] at he
    obtain ⟨s, hs, hse⟩ := he
    split at hse
    · next hm => simp only [Option.some.injEq] at hse; exact ⟨s, hs, hm, hse.symm⟩
    · cases hse

theorem gotBlobs_effs_handle (n : Node) (hs : List Hash) : ∀ e ∈ (gotBlobs n hs).2, HandleEff e := by
  unfold gotBlobs
  suffices ∀ (l : List Hash) (acc : Node × List Effect), (∀ e ∈ acc.2, HandleEff e) →
      ∀ e ∈ (l.foldl (fun (acc : Node × List Effect) h => ((gotBlob acc.1 h).1, acc.2 ++ (gotBlob acc.1 h).2)) acc).2,
        HandleEff e by
    exact this hs (n, []) (by simp)
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons x xs ih =>
    intro acc h
    apply ih
    intro e he
    simp only [List.mem_append] at he
    rcases he with he | he
    · exact h e he
    · obtain ⟨s, -, -, rfl⟩ := gotBlob_effs acc.1 x e he; trivial

theorem heff_ite_notify (c : Bool) (x : Notice) :
    ∀ e ∈ (if c = true then [Effect.notify x] else []), HandleEff e := by
  intro e he; split at he <;> simp at he; subst he; trivial

theorem onMessage_effs (n : Node) (s : Session) (msg : Message) :
    ∀ e ∈ (onMessage n s msg).2, HandleEff e := by
  unfold onMessage closeWith
  split
  · split
    · split
      · simp [HandleEff]
      · split
        · simp [HandleEff]
        · simp
    · simp [HandleEff]
  · cases msg with
    | hello => simp [HandleEff]
    | digest d => simp
    | state d st =>
      simp only
      intro e he
      split at he
      · split at he
        · split at he <;> exact heff_ite_notify _ _ e he
        · split at he <;>
          · simp only [List.mem_append, List.mem_singleton] at he
            rcases he with he | rfl
            · exact heff_ite_notify _ _ e he
            · trivial
      · split at he <;>
        · simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
          rcases he with ((rfl | rfl) | he) | rfl
          · trivial
          · trivial
          · exact heff_ite_notify _ _ e he
          · trivial
    | want hs =>
      simp only
      split
      · intro e he; simp only [List.mem_map] at he; obtain ⟨_, _, rfl⟩ := he; trivial
      · intro e he
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at he
        rcases he with ⟨_, _, rfl⟩ | rfl <;> trivial
    | noBlob hs => simp [HandleEff]
    | «have» hs => simp [HandleEff]
    | bye r => simp [HandleEff]

theorem handle_effs (n : Node) (ev : Event) : ∀ e ∈ (handle n ev).2, HandleEff e := by
  cases ev with
  | received p b =>
    simp only [handle]
    split
    · simp
    · split
      · simp [closeWith, HandleEff]
      · exact onMessage_effs _ _ _
  | localOp op =>
    simp only [handle]
    split
    · simp [HandleEff]
    · split
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · trivial
        · exact gotBlobs_effs_handle _ _ e he
      · simp [HandleEff]
  | blobStored hb src =>
    simp only [handle]
    split
    · simp
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · trivial
      · exact gotBlobs_effs_handle _ _ e he
  | connected p => simp only [handle]; split; simp; split <;> simp [HandleEff]
  | disconnected p => simp only [handle]; split <;> simp [HandleEff]
  | persisted t d => simp only [handle]; split; split <;> simp; simp
  | persistFailed t => simp only [handle]; split; split <;> simp; simp
  | blobFailed p hb => simp only [handle]; split; split <;> simp [HandleEff]; simp
  | blobLost hb => simp only [handle]; split <;> simp [HandleEff]
  | init => simp [handle, HandleEff]
  | initFresh => simp [handle, HandleEff]
  | query q => simp [handle, HandleEff]

/-- `handle` leaves the persistence bookkeeping alone, except when the host answers the persist in
flight. -/
def Answers (t : Nat) (ev : Event) : Prop := (∃ d, ev = .persisted t d) ∨ ev = .persistFailed t

theorem onMessage_pframe (n : Node) (s : Session) (msg : Message) :
    let n' := (onMessage n s msg).1
    n'.inflight = n.inflight ∧ n'.published = n.published ∧ n'.nextTag = n.nextTag := by
  unfold onMessage closeWith
  split
  · split
    · split
      · exact ⟨rfl, rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  · cases msg with
    | state d st =>
      simp only
      split
      · split
        · split <;> exact ⟨rfl, rfl, rfl⟩
        · split <;> exact ⟨rfl, rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl, rfl⟩
    | want hs => simp only; split <;> exact ⟨rfl, rfl, rfl⟩
    | _ => exact ⟨rfl, rfl, rfl⟩

theorem handle_persistence (n : Node) (ev : Event) :
    let n' := (handle n ev).1
    n'.nextTag = n.nextTag ∧
    ((n'.inflight = n.inflight ∧ n'.published = n.published) ∨
     (∃ t s, n.inflight = some (t, s) ∧ Answers t ev ∧ n'.inflight = none ∧
       (n'.published = n.published ∨ ∃ d, ev = .persisted t d ∧ n'.published = some ⟨s, d⟩))) := by
  cases ev with
  | received p b =>
    simp only [handle]
    split
    · exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
    · split
      · exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
      · obtain ⟨h1, h2, h3⟩ := onMessage_pframe n _ _
        exact ⟨h3, .inl ⟨h1, h2⟩⟩
  | localOp op =>
    simp only [handle]
    split
    · exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
    · split
      · obtain ⟨-, -, h3, h4, h5, -, -⟩ := gotBlobs_frame (n.withCurrent (applyOp n.current n.self op)) (opHashes op)
        exact ⟨h5, .inl ⟨h4, h3⟩⟩
      · exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | blobStored hb src =>
    obtain ⟨-, -, h3, h4, h5, -, -⟩ := gotBlobs_frame n [hb]
    exact ⟨h5, .inl ⟨h4, h3⟩⟩
  | persisted t d =>
    simp only [handle]
    split
    · next t' s hi =>
      split
      · next ht => subst ht; exact ⟨rfl, .inr ⟨t', s, hi, .inl ⟨d, rfl⟩, rfl, .inr ⟨d, rfl, rfl⟩⟩⟩
      · exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | persistFailed t =>
    simp only [handle]
    split
    · next t' s hi =>
      split
      · next ht => subst ht; exact ⟨rfl, .inr ⟨t', s, hi, .inr rfl, rfl, .inl rfl⟩⟩
      · exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | connected p => simp only [handle]; split; exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩; split <;> exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | disconnected p => simp only [handle]; split <;> exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | blobFailed p hb =>
    simp only [handle]; split; split <;> exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩; exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | blobLost hb => simp only [handle]; split <;> exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | init => exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | initFresh => exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | query q => exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩

/-- An unanswered persist stays in flight through `handle`. -/
theorem handle_keeps_inflight {n : Node} {ev : Event} {t : Nat} {s : State}
    (hi : n.inflight = some (t, s)) (hna : ¬ Answers t ev) : (handle n ev).1.inflight = some (t, s) := by
  rcases (handle_persistence n ev).2 with ⟨h1, -⟩ | ⟨t', s', hi', ha, -, -⟩
  · rw [h1, hi]
  · rw [hi] at hi'; simp only [Option.some.injEq, Prod.mk.injEq] at hi'; obtain ⟨rfl, rfl⟩ := hi'
    exact absurd ha hna

/-! ### The passes after `persistPass` -/

def LateEff (n : Node) : Effect → Prop
  | .send p (.hello _ _ _) => ∃ x ∈ n.sessions, x.peer = p
  | .send p (.digest _) => ∃ x ∈ n.sessions, x.peer = p
  | .send p (.state d s) => (∃ x ∈ n.sessions, x.peer = p) ∧ ∃ P, n.published = some P ∧ d = P.digest ∧ s = P.state
  | .fetch p c => FetchOk n.missing n.sessions (.fetch p c)
  | .notify _ => True
  | _ => False

theorem reconcileSession_effs (self : ReplicaId) (rb : Bool) (P : Published) (s : Session) :
    ∀ e ∈ (reconcileSession self rb P s).2,
      e = .send s.peer (.hello 1 self P.digest) ∨ e = .send s.peer (.state P.digest P.state) ∨
      e = .send s.peer (.digest P.digest) := by
  have hp : ∀ e ∈ (helloPart self P s).2, e = .send s.peer (.hello 1 self P.digest) := by
    unfold helloPart; split <;> simp
  have hpeer : (helloPart self P s).1.peer = s.peer := by unfold helloPart; split <;> rfl
  unfold reconcileSession
  simp only
  split
  · split
    · intro e he; simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact .inl (hp e he)
      · exact .inr (.inl (by rw [hpeer]))
    · split
      · intro e he; simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact .inl (hp e he)
        · exact .inr (.inr (by rw [hpeer]))
      · intro e he; exact .inl (hp e he)
  · intro e he; exact .inl (hp e he)

theorem reconcilePass_effs (n : Node) : ∀ e ∈ (reconcilePass n).2, LateEff n e := by
  unfold reconcilePass
  split
  · simp
  · next P hP =>
    intro e he
    simp only [List.mem_flatMap] at he
    obtain ⟨s, hs, he⟩ := he
    rcases reconcileSession_effs n.self n.rollback P s e he with rfl | rfl | rfl
    · exact ⟨s, hs, rfl⟩
    · exact ⟨⟨s, hs, rfl⟩, P, hP, rfl, rfl⟩
    · exact ⟨s, hs, rfl⟩

theorem planPass_effs {n : Node} (h : n.Inv) : ∀ e ∈ (planPass n).2, LateEff n e := by
  obtain ⟨l', -, -, hes, -⟩ := planPass_spec h
  intro e he
  obtain ⟨x, hx, c, rfl, rest⟩ := hes e he
  exact ⟨x, hx, c, rfl, rest⟩

theorem reportPass_effs (n : Node) : ∀ e ∈ (reportPass n).2, LateEff n e := by
  unfold reportPass
  simp only
  have : ∀ e ∈ n.sessions.filterMap (fun s =>
      if (sessionStatus n s == s.reported) = true then none
      else some (Effect.notify (.peerStatus s.peer (sessionStatus n s) s.peerReplica))), LateEff n e := by
    intro e he
    simp only [List.mem_filterMap] at he
    obtain ⟨s, -, hse⟩ := he
    split at hse
    · cases hse
    · simp only [Option.some.injEq] at hse; subst hse; trivial
  split
  · exact this
  · intro e he; simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact this e he
    · trivial

theorem late_frame_reconcile (n : Node) :
    (reconcilePass n).1.inflight = n.inflight ∧ (reconcilePass n).1.nextTag = n.nextTag := by
  unfold reconcilePass; split <;> exact ⟨rfl, rfl⟩

theorem late_frame_plan (n : Node) :
    (planPass n).1.inflight = n.inflight ∧ (planPass n).1.nextTag = n.nextTag := ⟨rfl, rfl⟩

theorem late_frame_report (n : Node) :
    (reportPass n).1.inflight = n.inflight ∧ (reportPass n).1.nextTag = n.nextTag := by
  unfold reportPass; simp only; split <;> exact ⟨rfl, rfl⟩

/-! ### `finish` and persistence -/

theorem lateEff_not_persist {n : Node} {e : Effect} (h : LateEff n e) : ∀ t s, e ≠ .persist t s := by
  intro t s he; subst he; exact h

theorem lateEff_state {n : Node} {p : PeerId} {d : Digest} {s : State} (h : LateEff n (.send p (.state d s))) :
    ∃ P, n.published = some P ∧ d = P.digest ∧ s = P.state := h.2

/-- The effects of `finish` after the persist pass, as `LateEff` of the node they were computed on. -/
theorem finish_mem {n : Node} (h : n.Inv) {e : Effect} (he : e ∈ (finish n).2) :
    e ∈ (persistPass n).2 ∨ ∃ m : Node, Core (persistPass n).1 m ∧ LateEff m e := by
  unfold finish at he
  simp only [List.mem_append] at he
  have hi1 := persistPass_inv h
  have hi2 := reconcilePass_inv hi1
  have hi3 := planPass_inv hi2
  rcases he with ((he | he) | he) | he
  · exact .inl he
  · exact .inr ⟨_, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, reconcilePass_effs _ e he⟩
  · exact .inr ⟨_, reconcilePass_core _, planPass_effs hi2 e he⟩
  · exact .inr ⟨_, (reconcilePass_core _).trans (planPass_core _), reportPass_effs _ e he⟩

theorem finish_frame (n : Node) :
    (finish n).1.inflight = (persistPass n).1.inflight ∧ (finish n).1.nextTag = (persistPass n).1.nextTag := by
  unfold finish
  simp only
  rw [(late_frame_report _).1, (late_frame_report _).2, (late_frame_plan _).1, (late_frame_plan _).2,
    (late_frame_reconcile _).1, (late_frame_reconcile _).2]
  exact ⟨rfl, rfl⟩

theorem finish_persist {n : Node} (h : n.Inv) {t : Nat} {s : State} (he : .persist t s ∈ (finish n).2) :
    n.inflight = none ∧ t = n.nextTag ∧ s = n.current ∧ (finish n).1.inflight = some (t, s) ∧
      (finish n).1.nextTag = t + 1 := by
  rcases finish_mem h he with he | ⟨m, -, hl⟩
  · unfold persistPass at he
    split at he
    · next hc =>
      simp only [List.mem_singleton, Effect.persist.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
      obtain ⟨hf1, hf2⟩ := finish_frame n
      unfold persistPass at hf1 hf2
      simp only [hc.1, hc.2, Option.isNone_none, Bool.and_self, ite_true] at hf1 hf2
      exact ⟨hc.1, rfl, rfl, hf1, hf2⟩
    · simp at he
  · exact absurd rfl (lateEff_not_persist hl t s)

theorem finish_keeps {n : Node} (h : n.Inv) {x : Nat × State} (hi : n.inflight = some x) :
    (finish n).1.inflight = some x ∧ (finish n).1.nextTag = n.nextTag ∧
      ∀ t s, .persist t s ∉ (finish n).2 := by
  refine ⟨?_, ?_, fun t s he => ?_⟩
  · rw [(finish_frame n).1]; unfold persistPass; simp [hi]
  · rw [(finish_frame n).2]; unfold persistPass; simp [hi]
  · have := (finish_persist h he).1; rw [hi] at this; cases this

theorem finish_inflight_cases {n : Node} (h : n.Inv) {t : Nat} {s : State}
    (hi : (finish n).1.inflight = some (t, s)) : .persist t s ∈ (finish n).2 ∨ n.inflight = some (t, s) := by
  rw [(finish_frame n).1] at hi
  unfold persistPass at hi
  split at hi
  · next hc =>
    left
    simp only [Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    unfold finish
    simp only [List.mem_append]
    left; left; left
    unfold persistPass; simp [hc]
  · exact .inr hi

theorem finish_nextTag_le (n : Node) : n.nextTag ≤ (finish n).1.nextTag := by
  rw [(finish_frame n).2]; unfold persistPass; split <;> simp

theorem finish_state {n : Node} (h : n.Inv) {p : PeerId} {d : Digest} {s : State}
    (he : .send p (.state d s) ∈ (finish n).2) : ∃ P, n.published = some P ∧ d = P.digest ∧ s = P.state := by
  rcases finish_mem h he with he | ⟨m, hc, hl⟩
  · unfold persistPass at he; split at he <;> simp at he
  · obtain ⟨P, hP, rfl, rfl⟩ := lateEff_state hl
    exact ⟨P, by rw [← (persistPass_core n).published, ← hc.published]; exact hP, rfl, rfl⟩

/-! ### `step` and persistence -/

theorem step_running (n : Node) (ev : Event) :
    step (.running n) ev = (.running (finish (handle n ev).1).1, (handle n ev).2 ++ (finish (handle n ev).1).2) := rfl

theorem handle_no_persist (n : Node) (ev : Event) (t : Nat) (s : State) : .persist t s ∉ (handle n ev).2 :=
  fun he => handle_effs n ev _ he

theorem handle_no_state (n : Node) (ev : Event) (p : PeerId) (d : Digest) (s : State) :
    .send p (.state d s) ∉ (handle n ev).2 :=
  fun he => handle_effs n ev _ he

/-! ### Start-up -/

theorem startNode_facts (self : ReplicaId) {s : State} (hs : s.WireOk) (blobs : List Hash) :
    let r := startNode self s blobs
    r.1.published = none ∧ r.1.nextTag = 1 ∧ r.1.inflight = some (0, s) ∧
      (∀ t s', .persist t s' ∈ r.2 → t = 0 ∧ s' = s) ∧ .persist 0 s ∈ r.2 ∧
      (∀ p d s', .send p (.state d s') ∉ r.2) := by
  let n0 : Node := { self, current := s, blobs := sortDedup blobs, missing := computeMissing s (sortDedup blobs), dirty := true }
  have h0 : n0.Inv := {
    currentOk := hs
    publishedOk := fun _ hP => by simp [n0] at hP
    publishedLe := fun _ hP => by simp [n0] at hP
    inflightOk := fun _ _ hx => by simp [n0] at hx
    inflightLe := fun _ _ hx => by simp [n0] at hx
    tagFresh := fun _ _ hx => by simp [n0] at hx
    blobsSorted := sorted_sortDedup _
    missingSorted := sorted_computeMissing _ (sorted_sortDedup _)
    missingSpec := fun z => by rw [mem_computeMissing _ (sorted_sortDedup _)]; rfl
    sessionsSorted := List.Pairwise.nil
    sessionCap := by simp [n0, maxSessions]
    sessOk := fun _ hx => by simp [n0] at hx }
  have hpers : .persist 0 s ∈ (finish n0).2 := by
    unfold finish; simp only [List.mem_append]; left; left; left
    unfold persistPass; simp [n0]
  obtain ⟨-, -, -, hi, hn⟩ := finish_persist h0 hpers
  refine ⟨?_, hn, hi, ?_, ?_, ?_⟩
  · show (finish n0).1.published = none
    rw [(finish_core n0).published]
  · intro t s' he
    simp only [startNode, List.mem_cons, reduceCtorEq, false_or] at he
    obtain ⟨-, ht, hs', -⟩ := finish_persist h0 he
    exact ⟨ht, hs'⟩
  · simp only [startNode, List.mem_cons, reduceCtorEq, false_or]; exact hpers
  · intro p d s' he
    simp only [startNode, List.mem_cons, reduceCtorEq, false_or] at he
    obtain ⟨P, hP, -⟩ := finish_state h0 he
    simp [n0] at hP

/-- What a step from the uninitialised machine can do. -/
theorem step_uninit (ev : Event) :
    ((step .uninit ev).1 = .uninit ∧ ∀ e ∈ (step .uninit ev).2, ∃ x, e = .notify x) ∨
    ∃ self s blobs, s.WireOk ∧ step .uninit ev = (.running (startNode self s blobs).1, (startNode self s blobs).2) := by
  cases ev with
  | init self stored blobs =>
    simp only [step]
    split
    · next s hdec => exact .inr ⟨self, s, blobs, wireOk_of_decodeState' hdec, rfl⟩
    · exact .inl ⟨rfl, by simp⟩
  | initFresh self blobs => exact .inr ⟨self, _, blobs, wireOk_empty, rfl⟩
  | _ => exact .inl ⟨rfl, by simp [step]⟩

/-! ## Traces -/

def runF (acc : Machine × List (List Effect)) (ev : Event) : Machine × List (List Effect) :=
  ((step acc.1 ev).1, (step acc.1 ev).2 :: acc.2)

theorem run_eq (m : Machine) (evs : List Event) :
    run m evs = ((evs.foldl runF (m, [])).1, (evs.foldl runF (m, [])).2.reverse) := rfl

theorem foldl_runF_acc : ∀ (evs : List Event) (m : Machine) (acc : List (List Effect)),
    evs.foldl runF (m, acc) = ((evs.foldl runF (m, [])).1, (evs.foldl runF (m, [])).2 ++ acc)
  | [], m, acc => by simp
  | e :: es, m, acc => by
    simp only [List.foldl_cons, runF]
    rw [foldl_runF_acc es _ ((step m e).2 :: acc), foldl_runF_acc es _ [(step m e).2]]
    simp

theorem run_append (m : Machine) (l1 l2 : List Event) :
    run m (l1 ++ l2) = ((run (run m l1).1 l2).1, (run m l1).2 ++ (run (run m l1).1 l2).2) := by
  simp only [run_eq, List.foldl_append]
  rw [show l1.foldl runF (m, []) = ((l1.foldl runF (m, [])).1, (l1.foldl runF (m, [])).2) from rfl,
    foldl_runF_acc l2]
  simp

theorem run_single (m : Machine) (e : Event) : run m [e] = ((step m e).1, [(step m e).2]) := by
  simp [run_eq, runF]

theorem run_length : ∀ (m : Machine) (evs : List Event), (run m evs).2.length = evs.length
  | m, [] => by simp [run_eq]
  | m, e :: es => by
    rw [show e :: es = [e] ++ es from rfl, run_append, run_single]
    simp [run_length _ es]

/-- The machine before step `k`. -/
def machineAt (evs : List Event) (k : Nat) : Machine := (run .uninit (evs.take k)).1

/-- Effects of step `i` (0-based) of a run from the uninitialised machine. -/
def effectsAt (evs : List Event) (i : Nat) : List Effect :=
  ((run .uninit evs).2)[i]?.getD []

theorem machineAt_zero (evs : List Event) : machineAt evs 0 = .uninit := by
  simp [machineAt, run_eq]

theorem take_succ_eq {evs : List Event} {k : Nat} (hk : k < evs.length) :
    evs.take (k + 1) = evs.take k ++ [evs[k]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl

theorem machineAt_succ {evs : List Event} {k : Nat} (hk : k < evs.length) :
    machineAt evs (k + 1) = (step (machineAt evs k) evs[k]).1 := by
  unfold machineAt
  rw [take_succ_eq hk, run_append, run_single]

theorem effectsAt_eq {evs : List Event} {k : Nat} (hk : k < evs.length) :
    effectsAt evs k = (step (machineAt evs k) evs[k]).2 := by
  unfold effectsAt machineAt
  have hsplit : evs = evs.take (k + 1) ++ evs.drop (k + 1) := (List.take_append_drop _ _).symm
  conv => lhs; rw [hsplit]
  rw [run_append, take_succ_eq hk, run_append, run_single]
  have hl : (run .uninit (evs.take k)).2.length = k := by
    rw [run_length, List.length_take]; omega
  rw [List.append_assoc, List.getElem?_append_right (by omega), hl]
  simp

theorem effectsAt_ge {evs : List Event} {k : Nat} (hk : evs.length ≤ k) : effectsAt evs k = [] := by
  unfold effectsAt
  rw [List.getElem?_eq_none (by rw [run_length]; exact hk)]
  rfl

theorem machineAt_inv (evs : List Event) : ∀ k, (machineAt evs k).Inv
  | 0 => by rw [machineAt_zero]; trivial
  | k + 1 => by
    by_cases hk : k < evs.length
    · rw [machineAt_succ hk]; exact step_inv' _ _ (machineAt_inv evs k)
    · unfold machineAt
      rw [List.take_of_length_le (by omega)]
      have := machineAt_inv evs evs.length
      unfold machineAt at this
      rwa [List.take_of_length_le (Nat.le_refl _)] at this

/-- The host's answer to the persist with tag `t`. -/
def AnswersAt (evs : List Event) (t k : Nat) : Prop :=
  (∃ d, evs[k]? = some (.persisted t d)) ∨ evs[k]? = some (.persistFailed t)

/-- What has happened to persists up to (not including) step `k`. -/
structure TraceInv (evs : List Event) (k : Nat) : Prop where
  uninitClean : machineAt evs k = .uninit → ∀ j < k, ∀ t s, .persist t s ∉ effectsAt evs j
  published : ∀ n, machineAt evs k = .running n → ∀ P, n.published = some P →
    ∃ j k' t d, j < k' ∧ k' < k ∧ .persist t P.state ∈ effectsAt evs j ∧ evs[k']? = some (.persisted t d)
  inflight : ∀ n, machineAt evs k = .running n → ∀ t s, n.inflight = some (t, s) →
    ∃ j < k, .persist t s ∈ effectsAt evs j
  tagsBelow : ∀ n, machineAt evs k = .running n → ∀ j < k, ∀ t s, .persist t s ∈ effectsAt evs j →
    t < n.nextTag
  answered : ∀ n, machineAt evs k = .running n → ∀ j < k, ∀ t s, .persist t s ∈ effectsAt evs j →
    (∃ k', j < k' ∧ k' < k ∧ AnswersAt evs t k') ∨ n.inflight = some (t, s)

theorem answers_of {evs : List Event} {k t : Nat} (hk : k < evs.length) (h : Answers t evs[k]) :
    AnswersAt evs t k := by
  unfold AnswersAt
  rw [List.getElem?_eq_getElem hk]
  rcases h with ⟨d, hd⟩ | hd
  · exact .inl ⟨d, by rw [hd]⟩
  · exact .inr (by rw [hd])

theorem traceInv (evs : List Event) : ∀ k, k ≤ evs.length → TraceInv evs k
  | 0, _ => {
      uninitClean := fun _ j hj => absurd hj (Nat.not_lt_zero _)
      published := fun n hm => by rw [machineAt_zero] at hm; cases hm
      inflight := fun n hm => by rw [machineAt_zero] at hm; cases hm
      tagsBelow := fun n hm => by rw [machineAt_zero] at hm; cases hm
      answered := fun n hm => by rw [machineAt_zero] at hm; cases hm }
  | k + 1, hk1 => by
    have hk : k < evs.length := by omega
    have ih := traceInv evs k (by omega)
    have hinv := machineAt_inv evs k
    have hm' := machineAt_succ hk
    have he := effectsAt_eq hk
    -- persists emitted before step `k`, or at it
    have hj : ∀ j, j < k + 1 → j < k ∨ j = k := fun j hj => by omega
    cases hmk : machineAt evs k with
    | uninit =>
      rw [hmk] at hm' he
      have hclean := ih.uninitClean hmk
      rcases step_uninit evs[k] with ⟨hst, hnot⟩ | ⟨self, s, blobs, hs, hst⟩
      · -- still uninitialised: no persist at step k either
        rw [hst] at hm'
        have hk0 : ∀ t s, .persist t s ∉ effectsAt evs k := by
          intro t s hp; rw [he] at hp; obtain ⟨x, hx⟩ := hnot _ hp; cases hx
        exact {
          uninitClean := fun _ j hj' t s => by
            rcases hj j hj' with hj' | rfl
            · exact hclean j hj' t s
            · exact hk0 t s
          published := fun n hm => by rw [hm'] at hm; cases hm
          inflight := fun n hm => by rw [hm'] at hm; cases hm
          tagsBelow := fun n hm => by rw [hm'] at hm; cases hm
          answered := fun n hm => by rw [hm'] at hm; cases hm }
      · rw [hst] at hm' he
        obtain ⟨hpub, hnext, hinfl, hpers, hpers0, -⟩ := startNode_facts self hs blobs
        exact {
          uninitClean := fun hm => by rw [hm'] at hm; cases hm
          published := fun n hm P hP => by
            rw [hm'] at hm; cases hm; rw [hpub] at hP; cases hP
          inflight := fun n hm t s' hi => by
            rw [hm'] at hm; cases hm; rw [hinfl] at hi
            simp only [Option.some.injEq, Prod.mk.injEq] at hi; obtain ⟨rfl, rfl⟩ := hi
            exact ⟨k, Nat.lt_succ_self _, by rw [he]; exact hpers0⟩
          tagsBelow := fun n hm j hj' t s' hp => by
            rw [hm'] at hm; cases hm
            rcases hj j hj' with hj' | rfl
            · exact absurd hp (hclean j hj' t s')
            · rw [he] at hp; rw [(hpers t s' hp).1, hnext]; omega
          answered := fun n hm j hj' t s' hp => by
            rw [hm'] at hm; cases hm
            rcases hj j hj' with hj' | rfl
            · exact absurd hp (hclean j hj' t s')
            · rw [he] at hp; obtain ⟨rfl, rfl⟩ := hpers t s' hp; exact .inr hinfl }
    | running n =>
      rw [hmk] at hm' he hinv
      rw [step_running] at hm' he
      simp only at hm' he
      have hn : n.Inv := hinv
      have hi1 : (handle n evs[k]).1.Inv := handle_inv hn _
      obtain ⟨htag1, hpc⟩ := handle_persistence n evs[k]
      exact {
        uninitClean := fun hm => by rw [hm'] at hm; cases hm
        published := fun n' hm P hP => by
          rw [hm'] at hm; cases hm
          rw [(finish_core _).published] at hP
          rcases hpc with ⟨-, hp1⟩ | ⟨t, s, hi, -, -, hp1 | ⟨d, hev, hp1⟩⟩
          · rw [hp1] at hP
            obtain ⟨j, k', t, d, h1, h2, h3, h4⟩ := ih.published n hmk P hP
            exact ⟨j, k', t, d, h1, by omega, h3, h4⟩
          · rw [hp1] at hP
            obtain ⟨j, k', t, d, h1, h2, h3, h4⟩ := ih.published n hmk P hP
            exact ⟨j, k', t, d, h1, by omega, h3, h4⟩
          · rw [hp1] at hP; simp only [Option.some.injEq] at hP; subst hP
            obtain ⟨j, hj', hpj⟩ := ih.inflight n hmk t s hi
            exact ⟨j, k, t, d, hj', Nat.lt_succ_self _, hpj, by rw [List.getElem?_eq_getElem hk, hev]⟩
        inflight := fun n' hm t s hi => by
          rw [hm'] at hm; cases hm
          rcases finish_inflight_cases hi1 hi with hp | hp
          · exact ⟨k, Nat.lt_succ_self _, by rw [he]; exact List.mem_append_right _ hp⟩
          · rcases hpc with ⟨hf, -⟩ | ⟨t', s', -, -, hnone, -⟩
            · rw [hf] at hp
              obtain ⟨j, hj', hpj⟩ := ih.inflight n hmk t s hp
              exact ⟨j, by omega, hpj⟩
            · rw [hnone] at hp; cases hp
        tagsBelow := fun n' hm j hj' t s hp => by
          rw [hm'] at hm; cases hm
          have hmono : n.nextTag ≤ (finish (handle n evs[k]).1).1.nextTag := by
            have := finish_nextTag_le (handle n evs[k]).1; rw [htag1] at this; exact this
          rcases hj j hj' with hj' | rfl
          · exact Nat.lt_of_lt_of_le (ih.tagsBelow n hmk j hj' t s hp) hmono
          · rw [he] at hp
            simp only [List.mem_append] at hp
            rcases hp with hp | hp
            · exact absurd hp (handle_no_persist _ _ t s)
            · obtain ⟨-, -, -, -, hnt⟩ := finish_persist hi1 hp; rw [hnt]; exact Nat.lt_succ_self t
        answered := fun n' hm j hj' t s hp => by
          rw [hm'] at hm; cases hm
          rcases hj j hj' with hj' | rfl
          · rcases ih.answered n hmk j hj' t s hp with ⟨k', h1, h2, h3⟩ | hfl
            · exact .inl ⟨k', h1, by omega, h3⟩
            · by_cases hans : Answers t evs[k]
              · exact .inl ⟨k, hj', Nat.lt_succ_self _, answers_of hk hans⟩
              · exact .inr (finish_keeps hi1 (handle_keeps_inflight hfl hans)).1
          · rw [he] at hp
            simp only [List.mem_append] at hp
            rcases hp with hp | hp
            · exact absurd hp (handle_no_persist _ _ t s)
            · exact .inr (finish_persist hi1 hp).2.2.2.1 }

end LeanSync
