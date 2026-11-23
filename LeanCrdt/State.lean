import LeanCrdt.VersionVector

/-!
# The replicated state and its public API

Executable module (imports `Init` only, through `LeanCrdt.Types`).

The state is an "optimized OR-map of multi-value registers" in dot-store form:
* `entries`: every live version of every file, as `(path, dot, hash)` triples, strictly sorted by
  `(path, dot, hash)`. A path is present iff it has at least one entry. There are no per-path
  tombstones.
* `context`: a version vector of all events this state has seen, including those whose entries
  were later superseded or deleted. "Seen (covered by `context`) but absent from `entries`" is
  exactly how deletion and supersession are represented.

Every function whose recursion depth could scale with the number of files, siblings or replicas
is tail-recursive (compiled to a loop).
-/

namespace LeanCrdt

/-- The whole replicated state. Both lists are in canonical form, so `State` has decidable,
literal equality and the merge laws hold as `=`. -/
structure State where
  entries : List Entry
  context : VersionVector
  sorted : StrictlySorted entries
  covered : ∀ e ∈ entries, 0 < e.dot.counter ∧ e.dot.counter ≤ context.get e.dot.replica

namespace State

def empty : State := ⟨[], .empty, .nil, by simp⟩

instance : Inhabited State := ⟨empty⟩

/-- `s` has seen the event that wrote `e` and no longer holds `e`: `e` was superseded or
deleted in `s`'s causal past. -/
def Supersedes (s : State) (e : Entry) : Prop :=
  s.context.covers e.dot = true ∧ e ∉ s.entries

/-! ## Merge (STAGE-1 PLACEHOLDER bodies) -/

/-- Join: `context` is the pointwise max; an entry survives iff it is in both states, or it is
in one state and the other has not seen its dot. Linear in the total number of entries (times a
version-vector lookup for entries present on one side only). -/
def merge (a b : State) : State := sorry

/-- Merge a list of states, left to right, starting from `empty`. -/
def mergeAll (l : List State) : State := l.foldl merge empty

/-! ## Queries (STAGE-1 PLACEHOLDER bodies) -/

/-- All paths that currently exist, strictly sorted (by UTF-8 bytes), without duplicates. -/
def paths (s : State) : List String := sorry

/-- Distinct hashes of the current versions of `p`, strictly sorted by `Hash` order.
`[]` means the path does not exist. -/
def versions (s : State) (p : String) : List Hash := sorry

/-- More than one distinct current version: a conflict for the user to resolve. -/
def isConflicted (s : State) (p : String) : Bool := (s.versions p).length ≥ 2

/-- Every existing path with its versions, in one linear pass (for the host to materialise or
diff the whole tree without `paths.length` calls to `versions`). -/
def snapshot (s : State) : List (String × List Hash) := sorry

/-! ## Local operations (STAGE-1 PLACEHOLDER bodies)

`self` is the local replica's id. Each `put` issues the next dot `(self, context.get self + 1)`.
-/

/-- Write version `h` of `p`, superseding the local versions of `p` whose hash is in
`supersedes` (normally: the versions the user/host had seen). Versions not listed, including
any that arrived by merge after the host looked, are kept as siblings. -/
def put (s : State) (self : ReplicaId) (p : String) (h : Hash) (supersedes : List Hash) : State :=
  sorry

/-- Delete the local versions of `p` whose hash is in `supersedes`. Issues no dot and leaves no
per-path tombstone: the deleted entries stay covered by `context`. Pass `s.versions p` to delete
everything seen. -/
def delete (s : State) (p : String) (supersedes : List Hash) : State := sorry

/-- Resolve a conflict (or simply edit): write `h`, superseding every version currently seen. -/
def resolve (s : State) (self : ReplicaId) (p : String) (h : Hash) : State :=
  s.put self p h (s.versions p)

end State
end LeanCrdt
