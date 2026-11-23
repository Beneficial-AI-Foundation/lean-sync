import LeanCrdt.State

/-!
# Theorems about the CRDT

All equalities are literal `=` on `State`: the representation is canonical, so no quotient
or observational equivalence is involved. This is a proof-only module; nothing here is
needed at runtime.
-/

set_option linter.unusedSectionVars false

namespace LeanCrdt.State

open Std

/-- Semilattice order: `a ≤ b` iff `b` already contains everything `a` knows. -/
def Le (a b : State) : Prop := merge a b = b

/-! ## Auxiliary lemmas -/

theorem covers_of_mem {s : State} {e : Entry} (h : e ∈ s.entries) :
    s.context.covers e.dot = true := by
  rw [VersionVector.covers_iff]; exact (s.covered e h).2

theorem covers_merge' (a b : State) (d : Dot) :
    (merge a b).context.covers d = (a.context.covers d || b.context.covers d) := by
  rw [context_merge_eq, VersionVector.covers_merge]

theorem entries_ext {a b : State} (h : ∀ e, e ∈ a.entries ↔ e ∈ b.entries) :
    a.entries = b.entries := eq_of_sorted_of_mem_iff a.sorted b.sorted h

theorem context_ext {a b : State} (h : ∀ r, a.context.get r = b.context.get r) :
    a.context = b.context := VersionVector.ext h

theorem get_merge' (a b : State) (r : ReplicaId) :
    (merge a b).context.get r = max (a.context.get r) (b.context.get r) := by
  rw [context_merge_eq, VersionVector.get_merge]

/-- Sufficient condition for `Le a b`: `b`'s context dominates `a`'s, and every entry of `b`
that `a` lacks is one `a` has not seen. -/
theorem le_of (a b : State) (hctx : ∀ r, a.context.get r ≤ b.context.get r)
    (hnew : ∀ e ∈ b.entries, e ∉ a.entries → a.context.covers e.dot = false) : Le a b := by
  apply ext
  · apply entries_ext
    intro e
    rw [mem_merge_entries]
    constructor
    · rintro (⟨_, h⟩ | ⟨ha, _, hc⟩ | ⟨h, _⟩)
      · exact h
      · have h1 := (a.covered e ha).2
        have h2 := hctx e.dot.replica
        simp [VersionVector.covers] at hc; omega
      · exact h
    · intro hb
      by_cases ha : e ∈ a.entries
      · exact .inl ⟨ha, hb⟩
      · exact .inr (.inr ⟨hb, ha, hnew e hb ha⟩)
  · apply context_ext
    intro r
    rw [get_merge']
    have := hctx r
    omega

theorem le_context {a b : State} (h : Le a b) (r : ReplicaId) :
    a.context.get r ≤ b.context.get r := by
  have := get_merge' a b r
  rw [h] at this
  omega

/-! ## 1. Join-semilattice laws (state-based CRDT) -/

theorem merge_comm (a b : State) : merge a b = merge b a := by
  apply ext
  · apply entries_ext; intro e; rw [mem_merge_entries, mem_merge_entries]; grind
  · apply context_ext; intro r; rw [get_merge', get_merge']; omega

theorem merge_assoc (a b c : State) : merge (merge a b) c = merge a (merge b c) := by
  apply ext
  · apply entries_ext
    intro e
    have fa : e ∈ a.entries → a.context.covers e.dot = true := covers_of_mem
    have fb : e ∈ b.entries → b.context.covers e.dot = true := covers_of_mem
    have fc : e ∈ c.entries → c.context.covers e.dot = true := covers_of_mem
    simp only [mem_merge_entries, covers_merge', Bool.or_eq_false_iff]
    grind
  · apply context_ext; intro r; simp only [get_merge']; omega

theorem merge_idem (a : State) : merge a a = a := by
  apply ext
  · apply entries_ext; intro e; rw [mem_merge_entries]; grind
  · apply context_ext; intro r; rw [get_merge']; omega

theorem merge_empty (a : State) : merge a empty = a := by
  apply ext
  · apply entries_ext
    intro e
    rw [mem_merge_entries]
    have he : e ∈ a.entries → empty.context.covers e.dot = false := fun h => by
      have := (a.covered e h).1
      simp [VersionVector.covers, empty, VersionVector.get_empty]; omega
    have hn : e ∉ empty.entries := by simp [empty]
    grind
  · apply context_ext; intro r; rw [get_merge']; simp [empty, VersionVector.get_empty]

/-- Convergence: any two replicas that have merged the same collection of states, in any order
and grouping, are equal. (Grouping is covered by `merge_assoc`; this covers order.) -/
theorem mergeAll_perm {l l' : List State} (h : l.Perm l') : mergeAll l = mergeAll l' := by
  unfold mergeAll
  apply List.Perm.foldl_eq' h
  intro x _ y _ z
  rw [merge_assoc, merge_comm x y, ← merge_assoc]

theorem mem_put_entries (s : State) (r : ReplicaId) (p : String) (h : Hash) (S : List Hash)
    (e : Entry) :
    e ∈ (s.put r p h S).entries ↔
      e = ⟨p, ⟨r, s.context.get r + 1⟩, h⟩ ∨ (e ∈ s.entries ∧ superseded p S e = false) := by
  simp only [put]
  rw [mem_union e (sorted_single _) (s.sorted.filter _)]
  simp

theorem context_put (s : State) (r p h S r') :
    (s.put r p h S).context.get r' =
      if r' = r then s.context.get r + 1 else s.context.get r' := by
  simp only [put, VersionVector.get_merge, VersionVector.get_single]
  by_cases hr : r' = r
  · subst hr; simp only [ite_true]; omega
  · simp only [hr, ite_false]; omega

theorem new_not_covered (s : State) (r : ReplicaId) :
    s.context.covers ⟨r, s.context.get r + 1⟩ = false := by
  simp [VersionVector.covers]

/-- Local operations are inflations, so merging a state with its own past never undoes them
(no resurrection of deleted or superseded versions). -/
theorem le_put (s : State) (r p h S) : Le s (s.put r p h S) := by
  apply le_of
  · intro r'; rw [context_put]
    by_cases hr : r' = r
    · subst hr; simp
    · simp [hr]
  · intro e he hns
    rw [mem_put_entries] at he
    rcases he with rfl | he
    · exact new_not_covered s r
    · exact absurd he.1 hns

theorem le_delete (s : State) (p S) : Le s (s.delete p S) := by
  apply le_of
  · intro r; exact Nat.le_refl _
  · intro e he hns
    exact absurd (List.mem_filter.1 he).1 hns

/-! ## 2. Exact meaning of merge -/

theorem context_merge (a b : State) (r : ReplicaId) :
    (merge a b).context.get r = max (a.context.get r) (b.context.get r) := get_merge' a b r

theorem mem_merge (a b : State) (e : Entry) :
    e ∈ (merge a b).entries ↔
      (e ∈ a.entries ∧ ¬ b.Supersedes e) ∨ (e ∈ b.entries ∧ ¬ a.Supersedes e) := by
  have fa : e ∈ a.entries → a.context.covers e.dot = true := covers_of_mem
  have fb : e ∈ b.entries → b.context.covers e.dot = true := covers_of_mem
  rw [mem_merge_entries]
  simp only [Supersedes]
  cases ha : a.context.covers e.dot <;> cases hb : b.context.covers e.dot <;> grind

/-! ## 4. Queries -/

theorem mem_versionsOf (l : List Entry) (p : String) (h : Hash) :
    h ∈ versionsOf l p ↔ ∃ e ∈ l, e.path = p ∧ e.hash = h := by
  simp only [versionsOf, mem_sortedSetOf, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨e, ⟨he, hp⟩, rfl⟩; exact ⟨e, he, hp, rfl⟩
  · rintro ⟨e, he, hp, rfl⟩; exact ⟨e, ⟨he, hp⟩, rfl⟩

theorem versionsOf_eq {l : List Entry} {p : String} {hs : List Hash} (hsorted : StrictlySorted hs)
    (h : ∀ x, x ∈ hs ↔ ∃ e ∈ l, e.path = p ∧ e.hash = x) : versionsOf l p = hs :=
  eq_of_sorted_of_mem_iff (sorted_sortedSetOf _) hsorted
    (fun x => by rw [mem_versionsOf, h])

theorem mem_versions (s : State) (p : String) (h : Hash) :
    h ∈ s.versions p ↔ ∃ e ∈ s.entries, e.path = p ∧ e.hash = h := mem_versionsOf _ _ _

theorem versions_sorted (s : State) (p : String) : StrictlySorted (s.versions p) :=
  sorted_sortedSetOf _

theorem versionsOf_cons_ne {e : Entry} {l : List Entry} {q : String} (h : e.path ≠ q) :
    versionsOf (e :: l) q = versionsOf l q := by
  simp [versionsOf, h]

theorem versionsOf_eq_single {l : List Entry} {p : String} {h : Hash}
    (hall : ∀ y ∈ l, y.path = p → y.hash = h) (hex : ∃ y ∈ l, y.path = p ∧ y.hash = h) :
    versionsOf l p = [h] := by
  apply versionsOf_eq (List.pairwise_singleton _ _)
  intro x
  rw [List.mem_singleton]
  constructor
  · rintro rfl; exact hex
  · rintro ⟨y, hy, hp, rfl⟩; exact hall y hy hp

/-- Right-fold form of `paths`. -/
def pathsR (l : List Entry) : List String := l.foldr (fun e acc => pathsStep acc e) []

theorem paths_eq (s : State) : s.paths = pathsR s.entries := by
  simp [paths, pathsR, List.foldl_reverse]

theorem pathsR_cons_head (e : Entry) (l : List Entry) : ∃ t, pathsR (e :: l) = e.path :: t := by
  simp only [pathsR, List.foldr_cons]
  generalize List.foldr (fun e acc => pathsStep acc e) [] l = acc
  cases acc with
  | nil => exact ⟨[], rfl⟩
  | cons q t =>
    simp only [pathsStep]
    split
    · next h => exact ⟨t, by rw [h]⟩
    · exact ⟨q :: t, rfl⟩

theorem cmp_eq_of_le_le {a b : String} (h₁ : compare a b ≠ .gt) (h₂ : compare b a ≠ .gt) :
    a = b := by
  apply cmp_eq_iff.1
  cases h : compare a b
  · exact absurd (cmp_gt_iff.2 h) h₂
  · rfl
  · exact absurd h h₁

theorem pathSorted_cons {e : Entry} {l : List Entry} :
    PathSorted (e :: l) ↔ (∀ x ∈ l, compare e.path x.path ≠ .gt) ∧ PathSorted l :=
  List.pairwise_cons

/-- In a path-sorted `e :: f :: l` with `e.path ≠ f.path`, no later entry has `e`'s path. -/
theorem no_later_same_path {e f : Entry} {l : List Entry} (hs : PathSorted (e :: f :: l))
    (hne : e.path ≠ f.path) : ∀ x ∈ f :: l, x.path ≠ e.path := by
  intro x hx hxe
  have h1 := (pathSorted_cons.1 hs).1 f (.head _)
  have hf : compare f.path x.path ≠ .gt := by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [ReflOrd.compare_self]; decide
    · exact (pathSorted_cons.1 (pathSorted_cons.1 hs).2).1 x hx
  rw [hxe] at hf
  exact hne (cmp_eq_of_le_le h1 hf)

theorem pathsR_spec : ∀ (l : List Entry), PathSorted l →
    StrictlySorted (pathsR l) ∧ ∀ p, p ∈ pathsR l ↔ ∃ e ∈ l, e.path = p
  | [], _ => ⟨.nil, by simp [pathsR]⟩
  | [e], _ => ⟨List.pairwise_singleton _ _, by simp [pathsR, pathsStep, eq_comm]⟩
  | e :: f :: l, hs => by
    obtain ⟨ih1, ih2⟩ := pathsR_spec (f :: l) (pathSorted_cons.1 hs).2
    obtain ⟨t, ht⟩ := pathsR_cons_head f l
    have hstep : pathsR (e :: f :: l) = pathsStep (pathsR (f :: l)) e := rfl
    rw [hstep, ht]
    rw [ht] at ih1 ih2
    simp only [pathsStep]
    split
    · next heq =>
      refine ⟨ih1, fun p => ?_⟩
      rw [ih2]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x, .tail _ hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨f, .head _, heq⟩
        · exact ⟨x, by simp [hx], rfl⟩
    · next hne =>
      have hlt : compare e.path f.path = .lt := by
        have h1 := (pathSorted_cons.1 hs).1 f (.head _)
        cases h : compare e.path f.path
        · rfl
        · exact absurd (cmp_eq_iff.1 h).symm hne
        · exact absurd h h1
      refine ⟨List.pairwise_cons.2 ⟨fun q hq => ?_, ih1⟩, fun p => ?_⟩
      · simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hlt
        · exact cmp_lt_trans hlt ((List.pairwise_cons.1 ih1).1 q hq)
      · rw [List.mem_cons, ih2]
        constructor
        · rintro (rfl | ⟨x, hx, rfl⟩)
          · exact ⟨e, .head _, rfl⟩
          · exact ⟨x, .tail _ hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact .inl rfl
          · exact .inr ⟨x, hx, rfl⟩

theorem mem_paths (s : State) (p : String) :
    p ∈ s.paths ↔ ∃ e ∈ s.entries, e.path = p := by
  rw [paths_eq]; exact (pathsR_spec _ (pathSorted_of_sorted s.sorted)).2 p

theorem paths_sorted (s : State) : StrictlySorted s.paths := by
  rw [paths_eq]; exact (pathsR_spec _ (pathSorted_of_sorted s.sorted)).1

theorem mem_paths_iff (s : State) (p : String) : p ∈ s.paths ↔ s.versions p ≠ [] := by
  rw [mem_paths]
  constructor
  · rintro ⟨e, he, hp⟩ hnil
    have : e.hash ∈ s.versions p := (mem_versions _ _ _).2 ⟨e, he, hp, rfl⟩
    rw [hnil] at this; simp at this
  · intro hne
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨e, he, hp, _⟩ := (mem_versions _ _ _).1 hx
    exact ⟨e, he, hp⟩

/-- Right-fold form of `snapshot`. -/
def snapR (l : List Entry) : List (String × List Hash) := l.foldr (fun e acc => snapStep acc e) []

theorem snapR_spec : ∀ (l : List Entry), PathSorted l →
    snapR l = (pathsR l).map (fun p => (p, versionsOf l p))
  | [], _ => rfl
  | [e], _ => by
    simp only [snapR, pathsR, List.foldr, snapStep, pathsStep, List.map]
    congr
    refine (versionsOf_eq_single (fun y hy _ => ?_) ⟨e, .head _, rfl, rfl⟩).symm
    rw [List.mem_singleton] at hy; rw [hy]
  | e :: f :: l, hs => by
    have ih := snapR_spec (f :: l) (pathSorted_cons.1 hs).2
    obtain ⟨t, ht⟩ := pathsR_cons_head f l
    have hsorted := (pathsR_spec (f :: l) (pathSorted_cons.1 hs).2)
    rw [ht] at hsorted
    have hstep : snapR (e :: f :: l) = snapStep (snapR (f :: l)) e := rfl
    have hpstep : pathsR (e :: f :: l) = pathsStep (pathsR (f :: l)) e := rfl
    rw [hstep, hpstep, ih, ht]
    simp only [List.map_cons, snapStep, pathsStep]
    split
    · next heq =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq, true_and]
      constructor
      · apply (versionsOf_eq (sorted_union (List.pairwise_singleton _ _) (sorted_sortedSetOf _)) _).symm
        intro x
        have hv := mem_versionsOf (f :: l) f.path x
        simp only [versionsOf] at hv
        rw [mem_union x (List.pairwise_singleton _ _) (sorted_sortedSetOf _), hv]
        simp only [List.mem_cons, List.mem_nil_iff, or_false]
        constructor
        · rintro (rfl | ⟨y, hy, hp, rfl⟩)
          · exact ⟨e, .inl rfl, heq.symm, rfl⟩
          · exact ⟨y, .inr hy, hp, rfl⟩
        · rintro ⟨y, (rfl | hy), hp, rfl⟩
          · exact .inl rfl
          · exact .inr ⟨y, hy, hp, rfl⟩
      · apply List.map_congr_left
        intro q hq
        have hlt := (List.pairwise_cons.1 hsorted.1).1 q hq
        have hne : e.path ≠ q := by
          intro h; rw [heq, h] at hlt; exact cmp_lt_irrefl _ hlt
        rw [versionsOf_cons_ne hne]
    · next hne =>
      have hnone := no_later_same_path hs (Ne.symm hne)
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq, true_and]
      refine ⟨?_, ?_, ?_⟩
      · refine (versionsOf_eq_single (fun y hy hp => ?_) ⟨e, .head _, rfl, rfl⟩).symm
        rw [List.mem_cons] at hy
        rcases hy with rfl | hy
        · rfl
        · exact absurd hp (hnone y hy)
      · rw [versionsOf_cons_ne (Ne.symm hne)]
      · apply List.map_congr_left
        intro q hq
        have : q ∈ f.path :: t := .tail _ hq
        rw [hsorted.2] at this
        obtain ⟨x, hx, rfl⟩ := this
        rw [versionsOf_cons_ne (Ne.symm (hnone x hx))]

theorem snapshot_eq (s : State) : s.snapshot = s.paths.map (fun p => (p, s.versions p)) := by
  have : s.snapshot = snapR s.entries := by simp [snapshot, snapR, List.foldl_reverse]
  rw [this, snapR_spec _ (pathSorted_of_sorted s.sorted), paths_eq]
  rfl

theorem length_ge_two_iff {l : List Hash} (hs : StrictlySorted l) :
    l.length ≥ 2 ↔ ∃ h₁ h₂, h₁ ≠ h₂ ∧ h₁ ∈ l ∧ h₂ ∈ l := by
  match l, hs with
  | [], _ => simp
  | [x], _ => simp
  | x :: y :: rest, hs =>
    simp only [List.length_cons, ge_iff_le]
    refine ⟨fun _ => ⟨x, y, cmp_lt_ne ((List.pairwise_cons.1 hs).1 y (.head _)), .head _,
      .tail _ (.head _)⟩, fun _ => by omega⟩

theorem isConflicted_iff (s : State) (p : String) :
    s.isConflicted p = true ↔ ∃ h₁ h₂, h₁ ≠ h₂ ∧ h₁ ∈ s.versions p ∧ h₂ ∈ s.versions p := by
  rw [← length_ge_two_iff (versions_sorted s p)]
  simp [isConflicted]

/-! ## 3. No lost update -/

/-- A version present in `a` is still a current version of its path after merging with any `b`,
unless `b` has seen the event that wrote it and no longer holds it (superseded or deleted it). -/
theorem no_lost_update (a b : State) (e : Entry) (he : e ∈ a.entries) :
    e.hash ∈ (merge a b).versions e.path ∨ b.Supersedes e := by
  by_cases hs : b.Supersedes e
  · exact .inr hs
  · left
    rw [mem_versions]
    exact ⟨e, (mem_merge a b e).2 (.inl ⟨he, hs⟩), rfl, rfl⟩

/-! ## 5. Local operations -/

theorem mem_versions_put (s : State) (r p h S q x) :
    x ∈ (s.put r p h S).versions q ↔
      (q = p ∧ x = h) ∨ (x ∈ s.versions q ∧ ¬ (q = p ∧ x ∈ S)) := by
  simp only [mem_versions, mem_put_entries, superseded, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  constructor
  · rintro ⟨e, (rfl | ⟨he, hsup⟩), hp, rfl⟩
    · exact .inl ⟨hp.symm, rfl⟩
    · refine .inr ⟨⟨e, he, hp, rfl⟩, ?_⟩
      rintro ⟨rfl, hS⟩
      rcases hsup with hsup | hsup
      · exact hsup hp
      · simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨⟨e, he, hp, rfl⟩, hn⟩)
    · exact ⟨_, .inl rfl, rfl, rfl⟩
    · refine ⟨e, .inr ⟨he, ?_⟩, hp, rfl⟩
      by_cases hep : e.path = p
      · right
        cases hc : S.contains e.hash
        · rfl
        · exact absurd ⟨hp.symm.trans hep, List.contains_iff_mem.1 hc⟩ hn
      · exact .inl hep

theorem mem_versions_delete (s : State) (p S q x) :
    x ∈ (s.delete p S).versions q ↔ x ∈ s.versions q ∧ ¬ (q = p ∧ x ∈ S) := by
  simp only [mem_versions, delete, List.mem_filter, superseded, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  constructor
  · rintro ⟨e, ⟨he, hsup⟩, hp, rfl⟩
    refine ⟨⟨e, he, hp, rfl⟩, ?_⟩
    rintro ⟨rfl, hS⟩
    rcases hsup with hsup | hsup
    · exact hsup hp
    · simp_all
  · rintro ⟨⟨e, he, hp, rfl⟩, hn⟩
    refine ⟨e, ⟨he, ?_⟩, hp, rfl⟩
    by_cases hep : e.path = p
    · right
      cases hc : S.contains e.hash
      · rfl
      · exact absurd ⟨hp.symm.trans hep, List.contains_iff_mem.1 hc⟩ hn
    · exact .inl hep

theorem context_delete (s : State) (p S) : (s.delete p S).context = s.context := rfl

theorem versions_resolve (s : State) (r p h) : (s.resolve r p h).versions p = [h] := by
  apply versionsOf_eq (List.pairwise_singleton _ _)
  intro x
  rw [← mem_versions, resolve, mem_versions_put]
  simp only [List.mem_singleton, true_and]
  constructor
  · rintro rfl; exact .inl rfl
  · rintro (h | ⟨h1, h2⟩)
    · exact h
    · exact absurd h1 h2

/-! ## 6. Concurrency semantics (decisions 2 and 3)

The hypothesis `b.context.get r ≤ a.context.get r` says "`b` has not seen the edit about to be
made by `r` on `a`". It always holds when `a` is replica `r`'s own state and `b` is any other
state, given the system assumption that `r` is the only issuer of `r`-dots and its state is
never rolled back (the host rule in `docs/crdt-design.md`). -/

/-- An edit survives a merge with any state that has not seen it, whatever that state did. -/
theorem put_survives_merge (a b : State) (r p h S) (hb : b.context.get r ≤ a.context.get r) :
    h ∈ (merge (a.put r p h S) b).versions p := by
  rw [mem_versions]
  refine ⟨⟨p, ⟨r, a.context.get r + 1⟩, h⟩, (mem_merge _ _ _).2 (.inl ⟨?_, ?_⟩), rfl, rfl⟩
  · rw [mem_put_entries]; exact .inl rfl
  · rintro ⟨hc, _⟩
    rw [VersionVector.covers_iff] at hc
    simp at hc; omega

/-- Decision 3: concurrent edit and delete of the same path: the edit wins. -/
theorem edit_wins_over_concurrent_delete (a b : State) (r p h S T)
    (hb : b.context.get r ≤ a.context.get r) :
    h ∈ (merge (a.put r p h S) (b.delete p T)).versions p :=
  put_survives_merge a _ r p h S (by rw [context_delete]; exact hb)

/-- Decision 2: concurrent edits of the same path are all kept, and differing ones are
reported as a conflict. -/
theorem concurrent_puts_kept (a b : State) (r₁ r₂ p h₁ h₂ S₁ S₂) (hr : r₁ ≠ r₂)
    (h1 : b.context.get r₁ ≤ a.context.get r₁) (h2 : a.context.get r₂ ≤ b.context.get r₂) :
    let m := merge (a.put r₁ p h₁ S₁) (b.put r₂ p h₂ S₂)
    h₁ ∈ m.versions p ∧ h₂ ∈ m.versions p ∧ (h₁ ≠ h₂ → m.isConflicted p = true) := by
  intro m
  have k1 : h₁ ∈ m.versions p :=
    put_survives_merge a _ r₁ p h₁ S₁ (by rw [context_put]; simp only [hr, ite_false]; exact h1)
  have k2 : h₂ ∈ m.versions p := by
    show h₂ ∈ (merge (a.put r₁ p h₁ S₁) (b.put r₂ p h₂ S₂)).versions p
    rw [merge_comm]
    exact put_survives_merge b _ r₂ p h₂ S₂ (by rw [context_put]; simp only [Ne.symm hr, ite_false]; exact h2)
  exact ⟨k1, k2, fun hne => (isConflicted_iff _ _).2 ⟨h₁, h₂, hne, k1, k2⟩⟩

theorem resolve_entry_at {a : State} {r p h} {e : Entry} (he : e ∈ (a.resolve r p h).entries)
    (hp : e.path = p) : e = ⟨p, ⟨r, a.context.get r + 1⟩, h⟩ := by
  rw [resolve, mem_put_entries] at he
  rcases he with he | ⟨he, hsup⟩
  · exact he
  · exfalso
    have : e.hash ∈ a.versions p := (mem_versions _ _ _).2 ⟨e, he, hp, rfl⟩
    simp [superseded, hp, this] at hsup

/-- Decision 2: resolving supersedes every sibling it saw: merged with anything in the
resolver's causal past, only the resolution remains. -/
theorem resolve_supersedes (a b : State) (r p h) (hb : Le b a) :
    (merge (a.resolve r p h) b).versions p = [h] := by
  apply versionsOf_eq (List.pairwise_singleton _ _)
  intro x
  rw [← mem_versions, List.mem_singleton]
  constructor
  · rintro rfl
    exact put_survives_merge a b r p x _ (le_context hb r)
  · intro hx
    rw [mem_versions] at hx
    obtain ⟨e, he, hp, rfl⟩ := hx
    rw [mem_merge] at he
    rcases he with ⟨he, _⟩ | ⟨heb, hns⟩
    · rw [resolve_entry_at he hp]
    · -- `e` comes from `b`, which `a` has absorbed: `a` covers `e`, hence so does the resolution.
      have hca : a.context.covers e.dot = true := by
        by_cases hea : e ∈ a.entries
        · exact covers_of_mem hea
        · apply Classical.byContradiction
          intro hc
          have hin : e ∈ (merge b a).entries :=
            (mem_merge b a e).2 (.inl ⟨heb, fun hs => hc hs.1⟩)
          rw [hb] at hin
          exact hea hin
      by_cases her : e ∈ (a.resolve r p h).entries
      · rw [resolve_entry_at her hp]
      · exfalso
        apply hns
        refine ⟨?_, her⟩
        rw [VersionVector.covers_iff] at hca ⊢
        show e.dot.counter ≤ (a.put r p h (a.versions p)).context.get e.dot.replica
        rw [context_put]
        by_cases hr : e.dot.replica = r
        · simp only [hr, ite_true]; rw [hr] at hca; omega
        · simp only [hr, ite_false]; exact hca

/-! ## 7. Batch put -/

theorem putSeq_spec (r : ReplicaId) : ∀ (items : List PutItem) (s : State),
    (items.map (·.path)).Nodup →
    (∀ z, z ∈ (s.putSeq r items).entries ↔
      (z ∈ s.entries ∧ ∀ it ∈ items, superseded it.path it.supersedes z = false) ∨
      ∃ t ∈ items.zipIdx (s.context.get r + 1), mkEntry r t = z) ∧
    (∀ r', (s.putSeq r items).context.get r' =
      if r' = r then s.context.get r + items.length else s.context.get r')
  | [], s, _ => by
    refine ⟨fun z => by simp [putSeq], fun r' => ?_⟩
    simp only [putSeq, List.foldl_nil, List.length_nil, Nat.add_zero]
    split <;> simp_all
  | it :: items, s, hnd => by
    have hnd' : (items.map (·.path)).Nodup := (List.nodup_cons.1 hnd).2
    have hfresh : it.path ∉ items.map (·.path) := (List.nodup_cons.1 hnd).1
    have hput : s.putSeq r (it :: items) = (s.put r it.path it.hash it.supersedes).putSeq r items :=
      rfl
    obtain ⟨ih1, ih2⟩ := putSeq_spec r items (s.put r it.path it.hash it.supersedes) hnd'
    have hc : (s.put r it.path it.hash it.supersedes).context.get r = s.context.get r + 1 := by
      rw [context_put]; simp
    rw [hput]
    refine ⟨fun z => ?_, fun r' => ?_⟩
    · rw [ih1, hc, mem_put_entries]
      simp only [List.zipIdx_cons, List.forall_mem_cons]
      simp only [List.mem_cons, exists_eq_or_imp]
      have he0 : ∀ it' ∈ items, superseded it'.path it'.supersedes
          ⟨it.path, ⟨r, s.context.get r + 1⟩, it.hash⟩ = false := by
        intro it' hit'
        have : it.path ≠ it'.path := fun h => hfresh (List.mem_map.2 ⟨it', hit', h.symm⟩)
        simp [superseded, this]
      have hmk : mkEntry r (it, s.context.get r + 1) = ⟨it.path, ⟨r, s.context.get r + 1⟩, it.hash⟩ :=
        rfl
      rw [hmk]
      constructor
      · rintro (⟨rfl | ⟨hz, hsup⟩, hall⟩ | hex)
        · exact .inr (.inl rfl)
        · exact .inl ⟨hz, hsup, hall⟩
        · exact .inr (.inr (by rw [Nat.add_assoc] at hex; exact hex))
      · rintro (⟨hz, hsup, hall⟩ | rfl | hex)
        · exact .inl ⟨.inr ⟨hz, hsup⟩, hall⟩
        · exact .inl ⟨.inl rfl, he0⟩
        · exact .inr (by rw [Nat.add_assoc]; exact hex)
    · rw [ih2, hc, context_put]
      simp only [List.length_cons]
      by_cases hr : r' = r
      · subst hr; simp only [ite_true]; omega
      · simp only [hr, ite_false]

/-- `putMany` is not a second semantics: it is literally the sequence of single `put`s, in
list order (item `i` gets counter `context.get self + 1 + i`), whether or not paths repeat. -/
theorem putMany_eq_putSeq (s : State) (r : ReplicaId) (items : List PutItem) :
    s.putMany r items = s.putSeq r items := by
  unfold putMany
  simp only
  split
  · next h =>
    have hst := pathStrict_of_strictPaths h
    have hperm := List.mergeSort_perm (items.zipIdx (s.context.get r + 1)) itemLe
    have hnd : (items.map (·.path)).Nodup := by
      have h1 : (((items.zipIdx (s.context.get r + 1)).mergeSort itemLe).map (·.1.path)).Nodup := by
        rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
        exact List.Pairwise.imp cmp_lt_ne hst
      have h2 := h1.perm (hperm.map _)
      have : (items.zipIdx (s.context.get r + 1)).map (·.1.path) = items.map (·.path) := by
        rw [show (fun x : PutItem × Nat => x.1.path) = (fun it : PutItem => it.path) ∘ Prod.fst
          from rfl, ← List.map_map, List.zipIdx_map_fst]
      rwa [this] at h2
    obtain ⟨hs1, hs2⟩ := putSeq_spec r items s hnd
    apply ext
    · apply entries_ext
      intro z
      rw [hs1]
      simp only [putManyFast]
      rw [mem_union z (sorted_newEntries r hst) (by
        rw [pruneGo_eq _ _ _ hst (pathSorted_of_sorted s.sorted)]; exact s.sorted.filter _)]
      rw [pruneGo_eq _ _ _ hst (pathSorted_of_sorted s.sorted)]
      simp only [List.mem_map, List.mem_mergeSort, List.reverseAux_nil, List.mem_filter,
        supersededBy, Bool.not_eq_true', List.any_eq_false, Bool.not_eq_true]
      have hitems : ∀ P : PutItem → Prop,
          (∀ t ∈ items.zipIdx (s.context.get r + 1), P t.1) ↔ ∀ it ∈ items, P it := by
        intro P
        constructor
        · intro H it hit
          rw [← List.zipIdx_map_fst (s.context.get r + 1) items, List.mem_map] at hit
          obtain ⟨t, ht, rfl⟩ := hit
          exact H t ht
        · intro H t ht
          apply H
          rw [← List.zipIdx_map_fst (s.context.get r + 1) items]
          exact List.mem_map.2 ⟨t, ht, rfl⟩
      rw [hitems (fun it => superseded it.path it.supersedes z = false)]
      exact Or.comm
    · apply context_ext
      intro r'
      rw [hs2]
      simp only [putManyFast]
      split
      · next hn =>
        have : items = [] := List.length_eq_zero_iff.1 hn
        subst this
        split <;> simp_all
      · rw [VersionVector.get_merge, VersionVector.get_single]
        split
        · next hr => subst hr; omega
        · omega
  · rfl

end LeanCrdt.State
