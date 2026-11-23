import LeanSync.Wire

/-!
# Sorted hash sets

Executable module (imports `Init` only). Blob bookkeeping keeps hash lists strictly sorted so
that set difference and deduplication are single passes. All loops are tail-recursive.
-/

set_option linter.unusedSectionVars false

namespace LeanSync

open LeanCrdt

/-! ## Sort and deduplicate: O(k log k) -/

def hashLe (a b : Hash) : Bool := compare a b != .gt

/-- Drop adjacent duplicates of a non-strictly sorted list; `acc` is reversed output. -/
def dedupGo : List Hash → List Hash → List Hash
  | [], acc => acc.reverse
  | x :: xs, [] => dedupGo xs [x]
  | x :: xs, a :: acc => if x = a then dedupGo xs (a :: acc) else dedupGo xs (x :: a :: acc)

def sortDedup (l : List Hash) : List Hash := dedupGo (l.mergeSort hashLe) []

theorem hashLe_trans (a b c : Hash) (h1 : hashLe a b = true) (h2 : hashLe b c = true) :
    hashLe a c = true := by
  simp only [hashLe, bne_iff_ne, ne_eq] at *
  have i1 : (compare a b).isLE := by revert h1; cases compare a b <;> decide
  have i2 : (compare b c).isLE := by revert h2; cases compare b c <;> decide
  have := Std.TransCmp.isLE_trans i1 i2
  revert this; cases compare a c <;> decide

theorem hashLe_total (a b : Hash) : (hashLe a b || hashLe b a) = true := by
  simp only [hashLe, Bool.or_eq_true, bne_iff_ne, ne_eq]
  cases h : compare a b
  · exact .inl (by decide)
  · exact .inl (by decide)
  · right; rw [cmp_gt_iff.1 h]; decide

/-- The reversed accumulator is strictly sorted, everything still to come is ≥ its head, and
members are preserved. -/
theorem dedupGo_spec : ∀ (xs acc : List Hash), xs.Pairwise (fun a b => hashLe a b = true) →
    StrictlySorted acc.reverse → (∀ a ∈ acc.head?, ∀ x ∈ xs, hashLe a x = true) →
    StrictlySorted (dedupGo xs acc) ∧ ∀ z, z ∈ dedupGo xs acc ↔ z ∈ acc ∨ z ∈ xs
  | [], acc, _, hs, _ => by simp [dedupGo, hs]
  | x :: xs, [], hp, _, _ => by
    have := dedupGo_spec xs [x] (List.pairwise_cons.1 hp).2 (by simp [StrictlySorted])
      (by intro a ha y hy; simp at ha; subst ha; exact (List.pairwise_cons.1 hp).1 y hy)
    refine ⟨this.1, fun z => ?_⟩
    rw [dedupGo, this.2]; simp
  | x :: xs, a :: acc, hp, hs, hh => by
    have hax : hashLe a x = true := hh a rfl x (.head _)
    have hrest : ∀ y ∈ xs, hashLe x y = true := (List.pairwise_cons.1 hp).1
    simp only [dedupGo]
    split
    · next hxa =>
      subst hxa
      have := dedupGo_spec xs (x :: acc) (List.pairwise_cons.1 hp).2 hs
        (by intro b hb y hy; simp at hb; subst hb; exact hrest y hy)
      refine ⟨this.1, fun z => ?_⟩
      rw [this.2]; simp; grind
    · next hxa =>
      have hlt : compare a x = .lt := by
        simp only [hashLe, bne_iff_ne, ne_eq] at hax
        cases h : compare a x
        · rfl
        · exact absurd (cmp_eq_iff.1 h).symm hxa
        · exact absurd h hax
      have hs' : StrictlySorted (x :: a :: acc).reverse := by
        rw [List.reverse_cons]
        unfold StrictlySorted at hs ⊢
        rw [List.pairwise_append]
        refine ⟨hs, List.pairwise_singleton _ _, ?_⟩
        intro y hy z hz
        simp at hz; subst hz
        simp only [List.reverse_cons, List.mem_append, List.mem_reverse, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · rw [List.reverse_cons] at hs
          exact cmp_lt_trans ((List.pairwise_append.1 hs).2.2 y (by simpa using hy) a (by simp)) hlt
        · exact hlt
      have := dedupGo_spec xs (x :: a :: acc) (List.pairwise_cons.1 hp).2 hs'
        (by intro b hb y hy; simp at hb; subst hb; exact hrest y hy)
      refine ⟨this.1, fun z => ?_⟩
      rw [this.2]; simp; grind

theorem sortDedup_spec (l : List Hash) :
    StrictlySorted (sortDedup l) ∧ ∀ z, z ∈ sortDedup l ↔ z ∈ l := by
  have hp := List.pairwise_mergeSort hashLe_trans hashLe_total l
  have := dedupGo_spec (l.mergeSort hashLe) [] hp List.Pairwise.nil (by simp)
  refine ⟨this.1, fun z => ?_⟩
  rw [sortDedup, this.2, List.Perm.mem_iff (List.mergeSort_perm l hashLe)]; simp

theorem sorted_sortDedup (l : List Hash) : StrictlySorted (sortDedup l) := (sortDedup_spec l).1
theorem mem_sortDedup {l : List Hash} {z : Hash} : z ∈ sortDedup l ↔ z ∈ l := (sortDedup_spec l).2 z

/-! ## Set difference of sorted lists: one pass -/

def sdiffGo : List Hash → List Hash → List Hash → List Hash
  | [], _, acc => acc.reverse
  | x :: xs, [], acc => acc.reverseAux (x :: xs)
  | x :: xs, y :: ys, acc =>
    match compare x y with
    | .lt => sdiffGo xs (y :: ys) (x :: acc)
    | .eq => sdiffGo xs ys acc
    | .gt => sdiffGo (x :: xs) ys acc
termination_by xs ys => xs.length + ys.length

/-- `xs` minus `ys`, for strictly sorted inputs. -/
def sdiff (xs ys : List Hash) : List Hash := sdiffGo xs ys []

theorem sdiffGo_eq (xs ys acc : List Hash) (hx : StrictlySorted xs) (hy : StrictlySorted ys) :
    sdiffGo xs ys acc = acc.reverseAux (xs.filter (fun x => x ∉ ys)) := by
  fun_induction sdiffGo xs ys acc with
  | case1 ys acc => simp
  | case2 x xs acc => simp only [List.not_mem_nil, not_false_eq_true, decide_true]
                      rw [List.filter_eq_self.2 (fun _ _ => rfl)]
  | case3 x xs y ys acc hc ih =>
    rw [ih (List.pairwise_cons.1 hx).2 hy]
    have hxy : x ∉ y :: ys := by
      intro hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact cmp_lt_irrefl _ hc
      · exact cmp_lt_irrefl _ (cmp_lt_trans hc ((List.pairwise_cons.1 hy).1 x hm))
    rw [List.filter_cons_of_pos (by simpa using hxy)]; rfl
  | case4 x xs y ys acc hc ih =>
    have hxy : x = y := cmp_eq_iff.1 hc
    subst hxy
    rw [ih (List.pairwise_cons.1 hx).2 (List.pairwise_cons.1 hy).2]
    congr 1
    rw [List.filter_cons_of_neg (by simp)]
    apply List.filter_congr
    intro z hz
    have hxz := (List.pairwise_cons.1 hx).1 z hz
    have : z ≠ x := fun e => by subst e; exact cmp_lt_irrefl _ hxz
    simp [this]
  | case5 x xs y ys acc hc ih =>
    rw [ih hx (List.pairwise_cons.1 hy).2]
    congr 1
    apply List.filter_congr
    intro z hz
    have hyx : compare y x = .lt := cmp_gt_iff.1 hc
    have hyz : compare y z = .lt := by
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hyx
      · exact cmp_lt_trans hyx ((List.pairwise_cons.1 hx).1 z hz)
    have : z ≠ y := fun e => by subst e; exact cmp_lt_irrefl _ hyz
    simp [this]

theorem sdiff_eq {xs ys : List Hash} (hx : StrictlySorted xs) (hy : StrictlySorted ys) :
    sdiff xs ys = xs.filter (fun x => x ∉ ys) := by
  rw [sdiff, sdiffGo_eq _ _ _ hx hy]; rfl

theorem sorted_sdiff {xs ys : List Hash} (hx : StrictlySorted xs) (hy : StrictlySorted ys) :
    StrictlySorted (sdiff xs ys) := by
  rw [sdiff_eq hx hy]; exact hx.filter _

theorem mem_sdiff {xs ys : List Hash} (hx : StrictlySorted xs) (hy : StrictlySorted ys) (z : Hash) :
    z ∈ sdiff xs ys ↔ z ∈ xs ∧ z ∉ ys := by
  rw [sdiff_eq hx hy]; simp

/-! ## Single-element updates -/

def insertH (h : Hash) (l : List Hash) : List Hash := union [h] l
def eraseH (h : Hash) (l : List Hash) : List Hash := l.filter (· != h)

theorem sorted_insertH {h : Hash} {l : List Hash} (hl : StrictlySorted l) : StrictlySorted (insertH h l) :=
  sorted_union (List.pairwise_singleton _ _) hl

theorem mem_insertH {h : Hash} {l : List Hash} (hl : StrictlySorted l) (z : Hash) :
    z ∈ insertH h l ↔ z = h ∨ z ∈ l := by
  rw [insertH, mem_union z (List.pairwise_singleton _ _) hl]; simp

theorem sorted_eraseH {h : Hash} {l : List Hash} (hl : StrictlySorted l) : StrictlySorted (eraseH h l) :=
  hl.filter _

theorem mem_eraseH {h : Hash} {l : List Hash} (z : Hash) : z ∈ eraseH h l ↔ z ∈ l ∧ z ≠ h := by
  simp [eraseH]

/-- Hashes referenced by a state and absent from `blobs` (sorted): O(n log n). -/
def computeMissing (s : State) (blobs : List Hash) : List Hash :=
  sdiff (sortDedup (s.entries.map (·.hash))) blobs

theorem mem_computeMissing (s : State) {blobs : List Hash} (hb : StrictlySorted blobs) (h : Hash) :
    h ∈ computeMissing s blobs ↔ (∃ e ∈ s.entries, e.hash = h) ∧ h ∉ blobs := by
  rw [computeMissing, mem_sdiff (sorted_sortDedup _) hb, mem_sortDedup]; simp

theorem sorted_computeMissing (s : State) {blobs : List Hash} (hb : StrictlySorted blobs) :
    StrictlySorted (computeMissing s blobs) := sorted_sdiff (sorted_sortDedup _) hb

/-- Membership in a sorted array by binary search (for replies; not used in proofs). -/
def binSearchGo (arr : Array Hash) (h : Hash) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      match arr[mid]? with
      | none => false
      | some x =>
        match compare x h with
        | .eq => true
        | .lt => binSearchGo arr h fuel (mid + 1) hi
        | .gt => binSearchGo arr h fuel lo mid
    else false

def binSearch (arr : Array Hash) (h : Hash) : Bool := binSearchGo arr h (arr.size + 1) 0 arr.size

end LeanSync
