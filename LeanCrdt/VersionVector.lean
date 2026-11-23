import LeanCrdt.SortedList

/-!
# Version vectors (the causal context)

Executable module (imports `Init` only). A version vector maps each replica to the number of
its events seen. It is stored canonically, as a list strictly sorted by replica id with no zero
entries, so equal vectors are equal Lean values (`VersionVector.ext`).
-/

set_option linter.unusedSectionVars false

namespace LeanCrdt

open Std

/-- Strictly sorted by key. -/
def KeySorted (l : List (ReplicaId × Nat)) : Prop :=
  l.Pairwise (fun a b => compare a.1 b.1 = .lt)

/-- Lookup with default `0` (tail-recursive). -/
def getL : List (ReplicaId × Nat) → ReplicaId → Nat
  | [], _ => 0
  | (k, n) :: rest, r => if k = r then n else getL rest r

/-- Canonical version vector: sorted by replica, all counters positive (absent means 0). -/
structure VersionVector where
  entries : List (ReplicaId × Nat)
  sorted : KeySorted entries
  pos : ∀ p ∈ entries, 0 < p.2

namespace VersionVector

def empty : VersionVector := ⟨[], .nil, by simp⟩

instance : Inhabited VersionVector := ⟨empty⟩

/-- Number of events of replica `r` covered. -/
def get (v : VersionVector) (r : ReplicaId) : Nat := getL v.entries r

/-- `v` has seen the event `d`. -/
def covers (v : VersionVector) (d : Dot) : Bool := decide (d.counter ≤ v.get d.replica)

/-- Structural specification of the pointwise-max merge (not used at runtime). -/
def mergeSpec : List (ReplicaId × Nat) → List (ReplicaId × Nat) → List (ReplicaId × Nat)
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | (k, n) :: xs, (k', m) :: ys =>
    match compare k k' with
    | .lt => (k, n) :: mergeSpec xs ((k', m) :: ys)
    | .gt => (k', m) :: mergeSpec ((k, n) :: xs) ys
    | .eq => (k, max n m) :: mergeSpec xs ys
termination_by xs ys => xs.length + ys.length

/-- Tail-recursive pointwise-max merge; `acc` is the output so far, reversed. -/
def mergeGo : List (ReplicaId × Nat) → List (ReplicaId × Nat) → List (ReplicaId × Nat) →
    List (ReplicaId × Nat)
  | [], ys, acc => acc.reverseAux ys
  | x :: xs, [], acc => acc.reverseAux (x :: xs)
  | (k, n) :: xs, (k', m) :: ys, acc =>
    match compare k k' with
    | .lt => mergeGo xs ((k', m) :: ys) ((k, n) :: acc)
    | .gt => mergeGo ((k, n) :: xs) ys ((k', m) :: acc)
    | .eq => mergeGo xs ys ((k, max n m) :: acc)
termination_by xs ys => xs.length + ys.length

theorem mergeGo_eq (xs ys acc : List (ReplicaId × Nat)) :
    mergeGo xs ys acc = acc.reverseAux (mergeSpec xs ys) := by
  fun_induction mergeGo xs ys acc with
  | case1 => simp [mergeSpec]
  | case2 => simp [mergeSpec]
  | case3 k n xs k' m ys acc h ih => rw [ih, mergeSpec, h]; simp
  | case4 k n xs k' m ys acc h ih => rw [ih, mergeSpec, h]; simp
  | case5 k n xs k' m ys acc h ih => rw [ih, mergeSpec, h]; simp

theorem getL_cons (k : ReplicaId) (n : Nat) (l : List (ReplicaId × Nat)) (r : ReplicaId) :
    getL ((k, n) :: l) r = if k = r then n else getL l r := rfl

theorem getL_eq_zero {l : List (ReplicaId × Nat)} {r : ReplicaId} (h : ∀ q ∈ l, q.1 ≠ r) :
    getL l r = 0 := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨k, n⟩ := q
    rw [getL_cons, ih (fun q hq => h q (.tail _ hq))]; simp [h (k, n) (.head _)]

theorem getL_eq_zero_of_lt {k : ReplicaId} {n : Nat} {l : List (ReplicaId × Nat)}
    {r : ReplicaId} (hs : KeySorted ((k, n) :: l)) (hr : compare r k = .lt) :
    getL ((k, n) :: l) r = 0 := by
  apply getL_eq_zero
  intro q hq hqr
  subst hqr
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact cmp_lt_irrefl _ hr
  · exact cmp_lt_asymm hr ((List.pairwise_cons.1 hs).1 q hq)

theorem mem_mergeSpec_key {xs ys : List (ReplicaId × Nat)} {p : ReplicaId × Nat}
    (h : p ∈ mergeSpec xs ys) : (∃ q ∈ xs, q.1 = p.1) ∨ (∃ q ∈ ys, q.1 = p.1) := by
  fun_induction mergeSpec xs ys with
  | case1 => exact .inr ⟨p, h, rfl⟩
  | case2 => exact .inl ⟨p, h, rfl⟩
  | case3 k n xs k' m ys _ ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact .inl ⟨_, .head _, rfl⟩
    · rcases ih h with ⟨q, hq, e⟩ | ⟨q, hq, e⟩
      · exact .inl ⟨q, .tail _ hq, e⟩
      · exact .inr ⟨q, hq, e⟩
  | case4 k n xs k' m ys _ ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact .inr ⟨_, .head _, rfl⟩
    · rcases ih h with ⟨q, hq, e⟩ | ⟨q, hq, e⟩
      · exact .inl ⟨q, hq, e⟩
      · exact .inr ⟨q, .tail _ hq, e⟩
  | case5 k n xs k' m ys _ ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact .inl ⟨_, .head _, rfl⟩
    · rcases ih h with ⟨q, hq, e⟩ | ⟨q, hq, e⟩
      · exact .inl ⟨q, .tail _ hq, e⟩
      · exact .inr ⟨q, .tail _ hq, e⟩

theorem pos_mergeSpec {xs ys : List (ReplicaId × Nat)} (hx : ∀ p ∈ xs, 0 < p.2)
    (hy : ∀ p ∈ ys, 0 < p.2) : ∀ p ∈ mergeSpec xs ys, 0 < p.2 := by
  fun_induction mergeSpec xs ys with
  | case1 => exact hy
  | case2 => exact hx
  | case3 k n xs k' m ys _ ih =>
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hx _ (.head _)
    · exact ih (fun q hq => hx q (.tail _ hq)) hy p hp
  | case4 k n xs k' m ys _ ih =>
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hy _ (.head _)
    · exact ih hx (fun q hq => hy q (.tail _ hq)) p hp
  | case5 k n xs k' m ys _ ih =>
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · have := hx _ (.head _); simp at this ⊢; omega
    · exact ih (fun q hq => hx q (.tail _ hq)) (fun q hq => hy q (.tail _ hq)) p hp

theorem sorted_mergeSpec {xs ys : List (ReplicaId × Nat)} (hx : KeySorted xs)
    (hy : KeySorted ys) : KeySorted (mergeSpec xs ys) := by
  fun_induction mergeSpec xs ys with
  | case1 => exact hy
  | case2 => exact hx
  | case3 k n xs k' m ys hc ih =>
    have hx' := List.pairwise_cons.1 hx
    have hy' := List.pairwise_cons.1 hy
    refine List.pairwise_cons.2 ⟨fun p hp => ?_, ih hx'.2 hy⟩
    rcases mem_mergeSpec_key hp with ⟨q, hq, e⟩ | ⟨q, hq, e⟩
    · rw [← e]; exact hx'.1 q hq
    · rw [← e]
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hc
      · exact cmp_lt_trans hc (hy'.1 q hq)
  | case4 k n xs k' m ys hc ih =>
    have hx' := List.pairwise_cons.1 hx
    have hy' := List.pairwise_cons.1 hy
    have hc' := cmp_gt_iff.1 hc
    refine List.pairwise_cons.2 ⟨fun p hp => ?_, ih hx hy'.2⟩
    rcases mem_mergeSpec_key hp with ⟨q, hq, e⟩ | ⟨q, hq, e⟩
    · rw [← e]
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hc'
      · exact cmp_lt_trans hc' (hx'.1 q hq)
    · rw [← e]; exact hy'.1 q hq
  | case5 k n xs k' m ys hc ih =>
    have hx' := List.pairwise_cons.1 hx
    have hy' := List.pairwise_cons.1 hy
    have hkk : k = k' := cmp_eq_iff.1 hc
    subst hkk
    refine List.pairwise_cons.2 ⟨fun p hp => ?_, ih hx'.2 hy'.2⟩
    rcases mem_mergeSpec_key hp with ⟨q, hq, e⟩ | ⟨q, hq, e⟩
    · rw [← e]; exact hx'.1 q hq
    · rw [← e]; exact hy'.1 q hq

theorem getL_mergeSpec {xs ys : List (ReplicaId × Nat)} (hx : KeySorted xs)
    (hy : KeySorted ys) (r : ReplicaId) :
    getL (mergeSpec xs ys) r = max (getL xs r) (getL ys r) := by
  fun_induction mergeSpec xs ys with
  | case1 => simp [getL]
  | case2 => simp [getL]
  | case3 k n xs k' m ys hc ih =>
    have ih := ih (List.pairwise_cons.1 hx).2 hy
    rw [getL_cons, getL_cons, ih]
    by_cases hk : k = r
    · subst hk
      simp only [ite_true]; rw [getL_eq_zero_of_lt hy hc]; simp
    · simp [hk]
  | case4 k n xs k' m ys hc ih =>
    have ih := ih hx (List.pairwise_cons.1 hy).2
    rw [getL_cons, getL_cons (k := k'), ih]
    by_cases hk : k' = r
    · subst hk
      simp only [ite_true]; rw [getL_eq_zero_of_lt hx (cmp_gt_iff.1 hc)]; simp
    · simp [hk]
  | case5 k n xs k' m ys hc ih =>
    have ih := ih (List.pairwise_cons.1 hx).2 (List.pairwise_cons.1 hy).2
    have hkk : k = k' := cmp_eq_iff.1 hc
    subst hkk
    rw [getL_cons, getL_cons, getL_cons, ih]
    by_cases hk : k = r
    · simp [hk]
    · simp [hk]

/-- Pointwise maximum, by one linear tail-recursive pass over the two sorted lists. -/
def merge (a b : VersionVector) : VersionVector where
  entries := mergeGo a.entries b.entries []
  sorted := by rw [mergeGo_eq]; exact sorted_mergeSpec a.sorted b.sorted
  pos := by rw [mergeGo_eq]; exact pos_mergeSpec a.pos b.pos

/-- The vector with the single entry `r ↦ n` (`n > 0`). -/
def single (r : ReplicaId) (n : Nat) (hn : 0 < n) : VersionVector :=
  ⟨[(r, n)], List.pairwise_singleton _ _, by simpa using hn⟩

theorem get_merge (a b : VersionVector) (r : ReplicaId) :
    (merge a b).get r = max (a.get r) (b.get r) := by
  simp only [get, merge, mergeGo_eq, List.reverseAux_nil]
  exact getL_mergeSpec a.sorted b.sorted r

theorem get_single (r : ReplicaId) (n : Nat) (hn : 0 < n) (r' : ReplicaId) :
    (single r n hn).get r' = if r' = r then n else 0 := by
  simp only [get, single, getL_cons, getL]
  by_cases h : r' = r
  · subst h; simp
  · have h' : r ≠ r' := fun e => h e.symm
    simp [h, h']

theorem get_empty (r : ReplicaId) : empty.get r = 0 := rfl

theorem mem_iff_get {l : List (ReplicaId × Nat)} (hs : KeySorted l) (hp : ∀ p ∈ l, 0 < p.2)
    (p : ReplicaId × Nat) : p ∈ l ↔ 0 < p.2 ∧ getL l p.1 = p.2 := by
  induction l with
  | nil => simp [getL]; omega
  | cons q l ih =>
    obtain ⟨k, n⟩ := q
    have hs' := List.pairwise_cons.1 hs
    have ih := ih hs'.2 (fun p h => hp p (.tail _ h))
    rw [getL_cons, List.mem_cons]
    constructor
    · rintro (rfl | h)
      · exact ⟨hp _ (.head _), by simp⟩
      · have hk : k ≠ p.1 := fun e => by
          have := hs'.1 p h; rw [e] at this; exact cmp_lt_irrefl _ this
        simp only [hk, ite_false]; exact ih.1 h
    · rintro ⟨h0, h⟩
      by_cases hk : k = p.1
      · simp only [hk, ite_true] at h
        left; obtain ⟨p1, p2⟩ := p; simp_all
      · simp only [hk, ite_false] at h
        exact .inr (ih.2 ⟨h0, h⟩)

/-- Canonicity: version vectors with the same lookups are equal. -/
theorem ext {a b : VersionVector} (h : ∀ r, a.get r = b.get r) : a = b := by
  obtain ⟨la, sa, pa⟩ := a
  obtain ⟨lb, sb, pb⟩ := b
  have : la = lb := by
    apply eq_of_pairwise_of_mem_iff (R := fun a b => compare a.1 b.1 = .lt)
      (fun _ _ hab hba => cmp_lt_asymm hab hba) (by exact sa) (by exact sb)
    intro p
    rw [mem_iff_get sa pa, mem_iff_get sb pb]
    have := h p.1
    simp only [get] at this
    rw [this]
  subst this
  rfl

theorem covers_iff (v : VersionVector) (d : Dot) : v.covers d = true ↔ d.counter ≤ v.get d.replica := by
  simp [covers]

theorem covers_merge (a b : VersionVector) (d : Dot) :
    (merge a b).covers d = (a.covers d || b.covers d) := by
  simp only [covers, get_merge]
  by_cases h1 : d.counter ≤ a.get d.replica <;> by_cases h2 : d.counter ≤ b.get d.replica <;>
    simp [h1, h2] <;> omega

end VersionVector
end LeanCrdt
