import LeanCrdt.VersionVector

/-!
# The replicated state and its public API

Executable module (imports `Init` only, through `LeanCrdt.Types`).

The state is an optimized OR-map of multi-value registers in dot-store form:
* `entries`: every live version of every file, as `(path, dot, hash)` triples, strictly sorted by
  `(path, dot, hash)`. A path exists iff it has at least one entry. There are no per-path
  tombstones.
* `context`: a version vector of every event this state has seen, including events whose
  entries were later superseded or deleted. Deletion and supersession are represented as
  "covered by `context` but absent from `entries`".

Every function whose recursion depth could grow with the number of files, siblings or replicas
is a self tail call (compiled to a loop), or a core list function with a tail-recursive
`@[csimp]` implementation (`filter`, `map`, `foldl`, `reverse`, `any`, `elem`, `zipIdx`,
`mergeSort`).

This module also contains the lemmas needed to build the invariants of the results of each
operation; the user-facing theorems are in `LeanCrdt.Laws`.
-/

set_option linter.unusedSectionVars false

namespace LeanCrdt

open Std

/-- The whole replicated state. Both lists are in canonical form, so equal contents means equal
values, and the merge laws hold as `=`. -/
structure State where
  entries : List Entry
  context : VersionVector
  sorted : StrictlySorted entries
  covered : ∀ e ∈ entries, 0 < e.dot.counter ∧ e.dot.counter ≤ context.get e.dot.replica

/-- One element of a batch for `State.putMany`. -/
structure PutItem where
  path : String
  hash : Hash
  supersedes : List Hash
  deriving Inhabited

namespace State

def empty : State := ⟨[], .empty, .nil, by simp⟩

instance : Inhabited State := ⟨empty⟩

theorem ext {a b : State} (he : a.entries = b.entries) (hc : a.context = b.context) : a = b := by
  cases a; cases b; simp only at he hc; subst he hc; rfl

/-- `s` has seen the event that wrote `e` and no longer holds `e`: `e` was superseded or
deleted in `s`'s causal past. -/
def Supersedes (s : State) (e : Entry) : Prop :=
  s.context.covers e.dot = true ∧ e ∉ s.entries

/-- Literal equality, computed by tail-recursive list comparisons (`List.beq` is a loop). -/
def beq (a b : State) : Bool := a.entries == b.entries && a.context.entries == b.context.entries

/-! ## Merge -/

/-- Join: `context` is the pointwise max. An entry survives iff it is in both states, or it is
in one state and the other has not seen its dot. One linear pass over both entry lists. -/
def merge (a b : State) : State where
  entries := mergeWith (fun e => !b.context.covers e.dot) (fun e => !a.context.covers e.dot)
    a.entries b.entries
  context := a.context.merge b.context
  sorted := sorted_mergeWith a.sorted b.sorted
  covered := by
    intro e he
    rw [mem_mergeWith e a.sorted b.sorted] at he
    rw [VersionVector.get_merge]
    rcases he with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · have := a.covered e h; omega
    · have := a.covered e h; omega
    · have := b.covered e h; omega

theorem mem_merge_entries (a b : State) (e : Entry) :
    e ∈ (merge a b).entries ↔
      (e ∈ a.entries ∧ e ∈ b.entries) ∨
      (e ∈ a.entries ∧ e ∉ b.entries ∧ b.context.covers e.dot = false) ∨
      (e ∈ b.entries ∧ e ∉ a.entries ∧ a.context.covers e.dot = false) := by
  simp only [merge]
  rw [mem_mergeWith e a.sorted b.sorted]
  simp

theorem context_merge_eq (a b : State) : (merge a b).context = a.context.merge b.context := rfl

/-- Merge a list of states, left to right, starting from `empty`. -/
def mergeAll (l : List State) : State := l.foldl merge empty

/-! ## Queries -/

/-- Distinct hashes of the entries of `l` at path `p`, strictly sorted. -/
def versionsOf (l : List Entry) (p : String) : List Hash :=
  sortedSetOf ((l.filter (fun e => e.path == p)).map (·.hash))

/-- Distinct hashes of the current versions of `p`, strictly sorted by `Hash` order (bytes).
`[]` means the path does not exist. Linear in the number of entries. -/
def versions (s : State) (p : String) : List Hash := versionsOf s.entries p

/-- More than one distinct current version: a conflict for the user to resolve. -/
def isConflicted (s : State) (p : String) : Bool := (s.versions p).length ≥ 2

def pathsStep (acc : List String) (e : Entry) : List String :=
  match acc with
  | q :: _ => if q = e.path then acc else e.path :: acc
  | [] => [e.path]

/-- All existing paths, strictly sorted (UTF-8 byte order), without duplicates. -/
def paths (s : State) : List String := s.entries.reverse.foldl pathsStep []

def snapStep (acc : List (String × List Hash)) (e : Entry) : List (String × List Hash) :=
  match acc with
  | (q, hs) :: rest => if q = e.path then (q, union [e.hash] hs) :: rest else (e.path, [e.hash]) :: acc
  | [] => [(e.path, [e.hash])]

/-- Every existing path with its versions, in one linear pass (proved equal to
`s.paths.map (fun p => (p, s.versions p))`). -/
def snapshot (s : State) : List (String × List Hash) := s.entries.reverse.foldl snapStep []

/-! ## Local operations

`self` is the local replica's id. Each `put` issues the next dot `(self, context.get self + 1)`.
-/

/-- The entry `x` is at path `p` with a hash listed in `S`. -/
def superseded (p : String) (S : List Hash) (x : Entry) : Bool := x.path == p && S.contains x.hash

theorem sorted_single (e : Entry) : StrictlySorted [e] := List.pairwise_singleton _ _

/-- Write version `h` of `p`, superseding the local versions of `p` whose hash is in
`supersedes` (normally: the versions the host had seen). Versions not listed, including any
that arrived by merge after the host looked, are kept as siblings. -/
def put (s : State) (self : ReplicaId) (p : String) (h : Hash) (supersedes : List Hash) : State where
  entries := union [⟨p, ⟨self, s.context.get self + 1⟩, h⟩]
    (s.entries.filter (fun x => !superseded p supersedes x))
  context := s.context.merge (.single self (s.context.get self + 1) (Nat.succ_pos _))
  sorted := sorted_union (sorted_single _) (s.sorted.filter _)
  covered := by
    intro e he
    rw [mem_union e (sorted_single _) (s.sorted.filter _)] at he
    rw [VersionVector.get_merge, VersionVector.get_single]
    rcases he with he | he
    · simp only [List.mem_singleton] at he
      subst he
      simp
    · have := s.covered e (List.mem_filter.1 he).1
      omega

/-- Delete the local versions of `p` whose hash is in `supersedes`. Issues no dot and leaves no
per-path tombstone: the deleted entries stay covered by `context`. Pass `s.versions p` to
delete everything seen. -/
def delete (s : State) (p : String) (supersedes : List Hash) : State where
  entries := s.entries.filter (fun x => !superseded p supersedes x)
  context := s.context
  sorted := s.sorted.filter _
  covered := fun e he => s.covered e (List.mem_filter.1 he).1

/-- Resolve a conflict (or simply edit): write `h`, superseding every version currently seen. -/
def resolve (s : State) (self : ReplicaId) (p : String) (h : Hash) : State :=
  s.put self p h (s.versions p)

/-! ## Batch put -/

/-- Reference semantics of a batch: the `put`s one after the other, in list order. -/
def putSeq (s : State) (self : ReplicaId) (items : List PutItem) : State :=
  items.foldl (fun s it => s.put self it.path it.hash it.supersedes) s

/-- The entry written by batch item `t.1`, which received counter `t.2`. -/
def mkEntry (self : ReplicaId) (t : PutItem × Nat) : Entry := ⟨t.1.path, ⟨self, t.2⟩, t.1.hash⟩

/-- Paths strictly increasing (adjacent check, tail-recursive). -/
def strictPaths : List (PutItem × Nat) → Bool
  | a :: b :: rest => compare a.1.path b.1.path == .lt && strictPaths (b :: rest)
  | _ => true

def PathStrict (l : List (PutItem × Nat)) : Prop :=
  l.Pairwise (fun a b => compare a.1.path b.1.path = .lt)

theorem pathStrict_of_strictPaths : ∀ {l : List (PutItem × Nat)}, strictPaths l = true → PathStrict l
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [strictPaths, Bool.and_eq_true, beq_iff_eq] at h
    have ih := pathStrict_of_strictPaths h.2
    refine List.pairwise_cons.2 ⟨fun x hx => ?_, ih⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h.1
    · exact cmp_lt_trans h.1 ((List.pairwise_cons.1 ih).1 x hx)

/-- Entries are sorted by path, non-strictly. -/
def PathSorted (l : List Entry) : Prop := l.Pairwise (fun a b => compare a.path b.path ≠ .gt)

theorem path_le_of_lt {a b : Entry} (h : compare a b = .lt) : compare a.path b.path ≠ .gt := by
  rw [Entry.compare_def, Ordering.then_eq_lt] at h
  rcases h with h | ⟨h, _⟩ <;> rw [h] <;> decide

theorem pathSorted_of_sorted {l : List Entry} (h : StrictlySorted l) : PathSorted l :=
  List.Pairwise.imp path_le_of_lt h

/-- Drop the entries of `es` superseded by an item of `ts` (both sorted by path): one
tail-recursive pass. -/
def pruneGo : List (PutItem × Nat) → List Entry → List Entry → List Entry
  | _, [], acc => acc.reverse
  | [], e :: es, acc => acc.reverseAux (e :: es)
  | t :: ts, e :: es, acc =>
    match compare t.1.path e.path with
    | .lt => pruneGo ts (e :: es) acc
    | .gt => pruneGo (t :: ts) es (e :: acc)
    | .eq => pruneGo (t :: ts) es (if t.1.supersedes.contains e.hash then acc else e :: acc)
termination_by ts es => ts.length + es.length

/-- Superseded by some item of the batch. -/
def supersededBy (ts : List (PutItem × Nat)) (x : Entry) : Bool :=
  ts.any (fun t => superseded t.1.path t.1.supersedes x)

theorem cmp_path_lt_of_le_lt {a b c : String} (h₁ : compare a b ≠ .gt) (h₂ : compare b c = .lt) :
    compare a c = .lt :=
  TransCmp.lt_of_isLE_of_lt (by revert h₁; cases compare a b <;> decide) h₂

theorem cmp_path_lt_of_lt_le {a b c : String} (h₁ : compare a b = .lt) (h₂ : compare b c ≠ .gt) :
    compare a c = .lt :=
  TransCmp.lt_of_lt_of_isLE h₁ (by revert h₂; cases compare b c <;> decide)

theorem pruneGo_eq (ts : List (PutItem × Nat)) (es acc : List Entry) (hts : PathStrict ts)
    (hes : PathSorted es) :
    pruneGo ts es acc = acc.reverseAux (es.filter (fun x => !supersededBy ts x)) := by
  fun_induction pruneGo ts es acc with
  | case1 ts acc => simp only [List.filter_nil]; rfl
  | case2 e es acc =>
    simp only [supersededBy, List.any_nil, Bool.not_false]
    rw [List.filter_eq_self.2 (fun _ _ => rfl)]
  | case3 t ts e es acc hc ih =>
    rw [ih (List.pairwise_cons.1 hts).2 hes]
    congr 1
    apply List.filter_congr
    intro x hx
    have hne : x.path ≠ t.1.path := by
      intro hxp
      have hle : compare e.path x.path ≠ .gt := by
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · rw [ReflOrd.compare_self]; decide
        · exact (List.pairwise_cons.1 hes).1 x hx
      have := cmp_path_lt_of_lt_le hc hle
      rw [hxp] at this; exact cmp_lt_irrefl _ this
    simp [supersededBy, superseded, hne]
  | case4 t ts e es acc hc ih =>
    rw [ih hts (List.pairwise_cons.1 hes).2]
    have hc' : compare e.path t.1.path = .lt := cmp_gt_iff.1 hc
    have hnot : supersededBy (t :: ts) e = false := by
      simp only [supersededBy, List.any_eq_false, superseded, Bool.and_eq_true, beq_iff_eq,
        not_and]
      intro t' ht' hp
      simp only [List.mem_cons] at ht'
      rcases ht' with rfl | ht'
      · rw [hp] at hc'; exact (cmp_lt_irrefl _ hc').elim
      · have := cmp_lt_trans hc' ((List.pairwise_cons.1 hts).1 t' ht')
        rw [hp] at this; exact (cmp_lt_irrefl _ this).elim
    simp [hnot]
  | case5 t ts e es acc hc ih =>
    simp only [dite_eq_ite] at ih
    rw [ih hts (List.pairwise_cons.1 hes).2]
    have hp : t.1.path = e.path := cmp_eq_iff.1 hc
    have hrest : ts.any (fun t => superseded t.1.path t.1.supersedes e) = false := by
      simp only [List.any_eq_false, superseded, Bool.and_eq_true, beq_iff_eq, not_and]
      intro t' ht' hp'
      have := (List.pairwise_cons.1 hts).1 t' ht'
      rw [hp, ← hp'] at this; exact (cmp_lt_irrefl _ this).elim
    have hsup : supersededBy (t :: ts) e = t.1.supersedes.contains e.hash := by
      rw [supersededBy, List.any_cons, hrest]; simp [superseded, hp]
    split <;> simp_all

/-- `le` for sorting batch items by path. -/
def itemLe (a b : PutItem × Nat) : Bool := compare a.1.path b.1.path != .gt

theorem sorted_newEntries (self : ReplicaId) {l : List (PutItem × Nat)} (h : PathStrict l) :
    StrictlySorted (l.map (mkEntry self)) := by
  unfold StrictlySorted
  rw [List.pairwise_map]
  apply List.Pairwise.imp _ h
  intro a b hab
  simp [Entry.compare_def, mkEntry, hab]

/-- The fast path of `putMany`, for a batch already sorted with strictly increasing paths. -/
def putManyFast (s : State) (self : ReplicaId) (n : Nat) (sortedT : List (PutItem × Nat))
    (hs : PathStrict sortedT)
    (hbound : ∀ t ∈ sortedT, s.context.get self + 1 ≤ t.2 ∧ t.2 ≤ s.context.get self + n) :
    State where
  entries := union (sortedT.map (mkEntry self)) (pruneGo sortedT s.entries [])
  context := if hn : n = 0 then s.context
    else s.context.merge (.single self (s.context.get self + n) (by omega))
  sorted := by
    apply sorted_union (sorted_newEntries self hs)
    rw [pruneGo_eq _ _ _ hs (pathSorted_of_sorted s.sorted)]
    exact s.sorted.filter _
  covered := by
    intro e he
    rw [mem_union e (sorted_newEntries self hs)
      (by rw [pruneGo_eq _ _ _ hs (pathSorted_of_sorted s.sorted)]; exact s.sorted.filter _)] at he
    rcases he with he | he
    · simp only [List.mem_map] at he
      obtain ⟨t, ht, rfl⟩ := he
      have hb := hbound t ht
      have hn : n ≠ 0 := by omega
      simp only [hn, dite_false, VersionVector.get_merge, VersionVector.get_single, mkEntry]
      simp; omega
    · rw [pruneGo_eq _ _ _ hs (pathSorted_of_sorted s.sorted)] at he
      simp only [List.reverseAux_nil, List.mem_filter] at he
      have := s.covered e he.1
      split
      · exact this
      · simp only [VersionVector.get_merge]; omega

theorem bound_of_mem_sorted {items : List PutItem} {c : Nat} {t : PutItem × Nat}
    (ht : t ∈ (items.zipIdx (c + 1)).mergeSort itemLe) :
    c + 1 ≤ t.2 ∧ t.2 ≤ c + items.length := by
  rw [List.mem_mergeSort] at ht
  obtain ⟨x, i⟩ := t
  have := List.mem_zipIdx ht
  simp only; omega

/-- Batch put, in one pass: equal to `putSeq` (the `put`s one after the other, item `i`
getting counter `context.get self + 1 + i`), as proved by `putMany_eq_putSeq`. Cost:
O(k log k) to sort the k items, plus one merge-like pass over the state. If two items have
the same path, it falls back to `putSeq`. -/
def putMany (s : State) (self : ReplicaId) (items : List PutItem) : State :=
  let sortedT := (items.zipIdx (s.context.get self + 1)).mergeSort itemLe
  if h : strictPaths sortedT = true then
    putManyFast s self items.length sortedT (pathStrict_of_strictPaths h)
      (fun _ ht => bound_of_mem_sorted ht)
  else
    putSeq s self items

end State
end LeanCrdt
