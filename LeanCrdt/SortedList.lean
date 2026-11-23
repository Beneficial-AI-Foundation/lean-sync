import LeanCrdt.Types

/-!
# Strictly sorted lists as finite sets

Executable module (imports `Init` only). Provides the one generic merge used for entries
(one pass: O(|xs| + |ys|) comparisons and predicate calls), plus its correctness theory:

* `eq_of_sorted_of_mem_iff`: two strictly sorted lists with the same members are equal
  (this is what makes the representation canonical);
* `mergeWith ka kb xs ys`: a single tail-recursive pass over two strictly sorted lists that keeps
  common elements, elements only in `xs` satisfying `ka`, and elements only in `ys` satisfying `kb`.
  It is proved equal to a structural specification `mergeSpec`, whose membership and sortedness
  are then characterised.
-/

set_option linter.unusedSectionVars false

namespace LeanCrdt

open Std

section Order
variable {α : Type} [Ord α] [TransOrd α] [LawfulEqOrd α]

theorem cmp_lt_irrefl (a : α) : compare a a ≠ .lt := by
  rw [ReflOrd.compare_self]; decide

theorem cmp_lt_asymm {a b : α} (h : compare a b = .lt) : compare b a ≠ .lt := by
  intro h'
  have := OrientedCmp.gt_of_lt h'
  rw [this] at h; cases h

theorem cmp_lt_trans {a b c : α} (h₁ : compare a b = .lt) (h₂ : compare b c = .lt) :
    compare a c = .lt := TransCmp.lt_trans h₁ h₂

theorem cmp_lt_ne {a b : α} (h : compare a b = .lt) : a ≠ b := by
  rintro rfl; exact cmp_lt_irrefl a h

theorem cmp_gt_iff {a b : α} : compare a b = .gt ↔ compare b a = .lt := OrientedCmp.gt_iff_lt

theorem cmp_eq_iff {a b : α} : compare a b = .eq ↔ a = b := LawfulEqOrd.compare_eq_iff_eq

end Order

/-- Two lists that are pairwise-related by an asymmetric relation and have the same members are
equal. Instantiated with "strictly less" this gives canonicity of sorted lists. -/
theorem eq_of_pairwise_of_mem_iff {α : Type} {R : α → α → Prop}
    (asymm : ∀ a b, R a b → ¬ R b a) :
    ∀ {l₁ l₂ : List α}, l₁.Pairwise R → l₂.Pairwise R → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (.head _)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (.head _)) (by simp)
  | a :: as, b :: bs, h₁, h₂, h => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      apply Classical.byContradiction
      intro hne
      have ha : a ∈ bs := by
        have := (h a).1 (.head _)
        simp only [List.mem_cons] at this
        exact this.resolve_left hne
      have hb : b ∈ as := by
        have := (h b).2 (.head _)
        simp only [List.mem_cons] at this
        exact this.resolve_left (Ne.symm hne)
      exact asymm _ _ (h₁.1 b hb) (h₂.1 a ha)
    subst hab
    have ha : ∀ x, x ∈ as → x ≠ a := fun x hx hxa => by
      subst hxa; exact asymm _ _ (h₁.1 x hx) (h₁.1 x hx)
    have hb : ∀ x, x ∈ bs → x ≠ a := fun x hx hxa => by
      subst hxa; exact asymm _ _ (h₂.1 x hx) (h₂.1 x hx)
    congr 1
    apply eq_of_pairwise_of_mem_iff asymm h₁.2 h₂.2
    intro x
    constructor
    · intro hx
      have := (h x).1 (.tail _ hx)
      simp only [List.mem_cons] at this
      exact this.resolve_left (ha x hx)
    · intro hx
      have := (h x).2 (.tail _ hx)
      simp only [List.mem_cons] at this
      exact this.resolve_left (hb x hx)

section Merge
variable {α : Type} [Ord α]

/-- Structural specification of `mergeWith` (not used at runtime: it is not tail-recursive). -/
def mergeSpec (ka kb : α → Bool) : List α → List α → List α
  | [], ys => ys.filter kb
  | x :: xs, [] => (x :: xs).filter ka
  | x :: xs, y :: ys =>
    match compare x y with
    | .lt => if ka x then x :: mergeSpec ka kb xs (y :: ys) else mergeSpec ka kb xs (y :: ys)
    | .gt => if kb y then y :: mergeSpec ka kb (x :: xs) ys else mergeSpec ka kb (x :: xs) ys
    | .eq => x :: mergeSpec ka kb xs ys
termination_by xs ys => xs.length + ys.length

/-- Tail-recursive worker of `mergeWith`; `acc` holds the output so far, reversed. -/
def mergeGo (ka kb : α → Bool) : List α → List α → List α → List α
  | [], ys, acc => acc.reverseAux (ys.filter kb)
  | x :: xs, [], acc => acc.reverseAux ((x :: xs).filter ka)
  | x :: xs, y :: ys, acc =>
    match compare x y with
    | .lt => mergeGo ka kb xs (y :: ys) (if ka x then x :: acc else acc)
    | .gt => mergeGo ka kb (x :: xs) ys (if kb y then y :: acc else acc)
    | .eq => mergeGo ka kb xs ys (x :: acc)
termination_by xs ys => xs.length + ys.length

/-- One-pass merge of two strictly sorted lists: keep elements in both; keep elements of only
`xs` satisfying `ka`; keep elements of only `ys` satisfying `kb`. Cost: O(|xs| + |ys|)
comparisons, plus one call of `ka`/`kb` per element present on one side only (the predicates'
own cost is the caller's). -/
@[inline] def mergeWith (ka kb : α → Bool) (xs ys : List α) : List α := mergeGo ka kb xs ys []

/-- Sorted union of two strictly sorted lists. -/
@[inline] def union (xs ys : List α) : List α := mergeWith (fun _ => true) (fun _ => true) xs ys

theorem mergeGo_eq (ka kb : α → Bool) (xs ys acc : List α) :
    mergeGo ka kb xs ys acc = acc.reverseAux (mergeSpec ka kb xs ys) := by
  fun_induction mergeGo ka kb xs ys acc with
  | case1 ys acc => simp [mergeSpec]
  | case2 x xs acc => simp [mergeSpec]
  | case3 x xs y ys acc h ih =>
    simp only [dite_eq_ite] at ih
    rw [ih, mergeSpec, h]; split <;> simp_all
  | case4 x xs y ys acc h ih =>
    simp only [dite_eq_ite] at ih
    rw [ih, mergeSpec, h]; split <;> simp_all
  | case5 x xs y ys acc h ih =>
    rw [ih, mergeSpec, h]; simp

theorem mergeWith_eq (ka kb : α → Bool) (xs ys : List α) :
    mergeWith ka kb xs ys = mergeSpec ka kb xs ys := by
  simp [mergeWith, mergeGo_eq]

theorem mem_mergeSpec_sub {ka kb : α → Bool} {xs ys : List α} {z : α}
    (h : z ∈ mergeSpec ka kb xs ys) : z ∈ xs ∨ z ∈ ys := by
  fun_induction mergeSpec ka kb xs ys <;> simp only [List.mem_cons, List.mem_filter] at * <;> grind

variable [TransOrd α] [LawfulEqOrd α]

theorem StrictlySorted.cons_iff {x : α} {xs : List α} :
    StrictlySorted (x :: xs) ↔ (∀ y ∈ xs, compare x y = .lt) ∧ StrictlySorted xs :=
  List.pairwise_cons

theorem StrictlySorted.not_mem_of_lt {x y : α} {ys : List α} (hy : StrictlySorted (y :: ys))
    (h : compare x y = .lt) : x ∉ y :: ys := by
  intro hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact cmp_lt_irrefl _ h
  · exact cmp_lt_asymm h ((StrictlySorted.cons_iff.1 hy).1 x hx)

theorem StrictlySorted.head_not_mem {x : α} {xs : List α} (h : StrictlySorted (x :: xs)) :
    x ∉ xs := fun hx => cmp_lt_irrefl x ((StrictlySorted.cons_iff.1 h).1 x hx)

theorem StrictlySorted.filter (p : α → Bool) {l : List α} (h : StrictlySorted l) :
    StrictlySorted (l.filter p) := List.Pairwise.filter p h

theorem eq_of_sorted_of_mem_iff {l₁ l₂ : List α} (h₁ : StrictlySorted l₁)
    (h₂ : StrictlySorted l₂) (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ :=
  eq_of_pairwise_of_mem_iff (fun _ _ hab hba => cmp_lt_asymm hab hba) h₁ h₂ h

theorem sorted_mergeSpec {ka kb : α → Bool} {xs ys : List α}
    (hx : StrictlySorted xs) (hy : StrictlySorted ys) :
    StrictlySorted (mergeSpec ka kb xs ys) := by
  fun_induction mergeSpec ka kb xs ys with
  | case1 ys => exact hy.filter _
  | case2 x xs => exact hx.filter _
  | case3 x xs y ys hc _ ih =>
    have ih := ih (StrictlySorted.cons_iff.1 hx).2 hy
    refine StrictlySorted.cons_iff.2 ⟨fun z hz => ?_, ih⟩
    rcases mem_mergeSpec_sub hz with hz | hz
    · exact (StrictlySorted.cons_iff.1 hx).1 z hz
    · simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hc
      · exact cmp_lt_trans hc ((StrictlySorted.cons_iff.1 hy).1 z hz)
  | case4 x xs y ys _ _ ih => exact ih (StrictlySorted.cons_iff.1 hx).2 hy
  | case5 x xs y ys hc _ ih =>
    have ih := ih hx (StrictlySorted.cons_iff.1 hy).2
    have hc' : compare y x = .lt := cmp_gt_iff.1 hc
    refine StrictlySorted.cons_iff.2 ⟨fun z hz => ?_, ih⟩
    rcases mem_mergeSpec_sub hz with hz | hz
    · simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hc'
      · exact cmp_lt_trans hc' ((StrictlySorted.cons_iff.1 hx).1 z hz)
    · exact (StrictlySorted.cons_iff.1 hy).1 z hz
  | case6 x xs y ys _ _ ih => exact ih hx (StrictlySorted.cons_iff.1 hy).2
  | case7 x xs y ys hc ih =>
    have ih := ih (StrictlySorted.cons_iff.1 hx).2 (StrictlySorted.cons_iff.1 hy).2
    have hxy : x = y := cmp_eq_iff.1 hc
    subst hxy
    refine StrictlySorted.cons_iff.2 ⟨fun z hz => ?_, ih⟩
    rcases mem_mergeSpec_sub hz with hz | hz
    · exact (StrictlySorted.cons_iff.1 hx).1 z hz
    · exact (StrictlySorted.cons_iff.1 hy).1 z hz

theorem mem_mergeSpec {ka kb : α → Bool} {xs ys : List α} (z : α)
    (hx : StrictlySorted xs) (hy : StrictlySorted ys) :
    z ∈ mergeSpec ka kb xs ys ↔
      (z ∈ xs ∧ z ∈ ys) ∨ (z ∈ xs ∧ z ∉ ys ∧ ka z = true) ∨ (z ∈ ys ∧ z ∉ xs ∧ kb z = true) := by
  fun_induction mergeSpec ka kb xs ys with
  | case1 ys => simp
  | case2 x xs => simp only [List.mem_filter]; simp
  | case3 x xs y ys hc hk ih =>
    have ih := ih (StrictlySorted.cons_iff.1 hx).2 hy
    have h1 : x ∉ y :: ys := StrictlySorted.not_mem_of_lt hy hc
    have h2 : x ∉ xs := StrictlySorted.head_not_mem hx
    simp only [List.mem_cons] at *
    grind
  | case4 x xs y ys hc hk ih =>
    have ih := ih (StrictlySorted.cons_iff.1 hx).2 hy
    have h1 : x ∉ y :: ys := StrictlySorted.not_mem_of_lt hy hc
    have h2 : x ∉ xs := StrictlySorted.head_not_mem hx
    simp only [List.mem_cons] at *
    grind
  | case5 x xs y ys hc hk ih =>
    have ih := ih hx (StrictlySorted.cons_iff.1 hy).2
    have h1 : y ∉ x :: xs := StrictlySorted.not_mem_of_lt hx (cmp_gt_iff.1 hc)
    have h2 : y ∉ ys := StrictlySorted.head_not_mem hy
    simp only [List.mem_cons] at *
    grind
  | case6 x xs y ys hc hk ih =>
    have ih := ih hx (StrictlySorted.cons_iff.1 hy).2
    have h1 : y ∉ x :: xs := StrictlySorted.not_mem_of_lt hx (cmp_gt_iff.1 hc)
    have h2 : y ∉ ys := StrictlySorted.head_not_mem hy
    simp only [List.mem_cons] at *
    grind
  | case7 x xs y ys hc ih =>
    have ih := ih (StrictlySorted.cons_iff.1 hx).2 (StrictlySorted.cons_iff.1 hy).2
    have hxy : x = y := cmp_eq_iff.1 hc
    subst hxy
    have h2 : x ∉ xs := StrictlySorted.head_not_mem hx
    have h3 : x ∉ ys := StrictlySorted.head_not_mem hy
    simp only [List.mem_cons] at *
    grind

theorem sorted_mergeWith {ka kb : α → Bool} {xs ys : List α}
    (hx : StrictlySorted xs) (hy : StrictlySorted ys) :
    StrictlySorted (mergeWith ka kb xs ys) := by
  rw [mergeWith_eq]; exact sorted_mergeSpec hx hy

theorem mem_mergeWith {ka kb : α → Bool} {xs ys : List α} (z : α)
    (hx : StrictlySorted xs) (hy : StrictlySorted ys) :
    z ∈ mergeWith ka kb xs ys ↔
      (z ∈ xs ∧ z ∈ ys) ∨ (z ∈ xs ∧ z ∉ ys ∧ ka z = true) ∨ (z ∈ ys ∧ z ∉ xs ∧ kb z = true) := by
  rw [mergeWith_eq]; exact mem_mergeSpec z hx hy

theorem sorted_union {xs ys : List α} (hx : StrictlySorted xs) (hy : StrictlySorted ys) :
    StrictlySorted (union xs ys) := sorted_mergeWith hx hy

theorem mem_union {xs ys : List α} (z : α) (hx : StrictlySorted xs) (hy : StrictlySorted ys) :
    z ∈ union xs ys ↔ z ∈ xs ∨ z ∈ ys := by
  rw [union, mem_mergeWith z hx hy]; grind

end Merge

/-! ## Sorted sets built by insertion (used for the small sibling lists of `versions`) -/

section SetOf
variable {α : Type} [Ord α] [TransOrd α] [LawfulEqOrd α]

/-- Strictly sorted, duplicate-free list of the elements of `l` (tail-recursive fold of
`union`). Cost O(k²) comparisons for k = `l.length`: each insertion rebuilds the accumulator.
Meant for short lists, such as the sibling hashes of one path; a collect-sort-dedup
implementation would make it O(k log k). -/
def sortedSetOf (l : List α) : List α := l.foldl (fun acc x => union [x] acc) []

theorem sortedSetOf_spec (l : List α) :
    StrictlySorted (sortedSetOf l) ∧ ∀ z, z ∈ sortedSetOf l ↔ z ∈ l := by
  suffices h : ∀ acc : List α, StrictlySorted acc →
      StrictlySorted (l.foldl (fun acc x => union [x] acc) acc) ∧
      ∀ z, z ∈ l.foldl (fun acc x => union [x] acc) acc ↔ z ∈ acc ∨ z ∈ l by
    have := h [] List.Pairwise.nil
    exact ⟨this.1, fun z => by simpa [sortedSetOf] using this.2 z⟩
  induction l with
  | nil => intro acc h; simpa using h
  | cons x xs ih =>
    intro acc hacc
    have hs : StrictlySorted [x] := List.pairwise_singleton _ _
    have hu := sorted_union hs hacc
    obtain ⟨h1, h2⟩ := ih _ hu
    refine ⟨h1, fun z => ?_⟩
    rw [List.foldl_cons, h2, mem_union z hs hacc]
    simp; grind

theorem sorted_sortedSetOf (l : List α) : StrictlySorted (sortedSetOf l) := (sortedSetOf_spec l).1

theorem mem_sortedSetOf {l : List α} {z : α} : z ∈ sortedSetOf l ↔ z ∈ l :=
  (sortedSetOf_spec l).2 z

end SetOf

end LeanCrdt
