import LeanCrdt.Types

/-!
# Version vectors (the causal context)

Executable module. A version vector maps each replica to the number of its events seen; it is
stored canonically as a list strictly sorted by replica id with no zero entries, so equal
vectors are equal as Lean values.
-/

namespace LeanCrdt

/-- Canonical version vector: sorted by replica, all counters positive (absent means 0). -/
structure VersionVector where
  entries : List (ReplicaId × Nat)
  sorted : entries.Pairwise (fun a b => compare a.1 b.1 = .lt)
  pos : ∀ p ∈ entries, 0 < p.2

namespace VersionVector

def empty : VersionVector := ⟨[], .nil, by simp⟩

instance : Inhabited VersionVector := ⟨empty⟩

/-- Number of events of replica `r` covered (tail-recursive). -/
def get (v : VersionVector) (r : ReplicaId) : Nat := go v.entries
where
  go : List (ReplicaId × Nat) → Nat
    | [] => 0
    | (r', n) :: rest => if r' = r then n else go rest

/-- `v` has seen the event `d`. -/
def covers (v : VersionVector) (d : Dot) : Bool := decide (d.counter ≤ v.get d.replica)

/-- Pointwise maximum, by a linear tail-recursive merge of the sorted lists.
STAGE-1 PLACEHOLDER: body to be written in stage 2. -/
def merge (a b : VersionVector) : VersionVector := sorry

/-- Set the entry of `r` to `n > 0`. STAGE-1 PLACEHOLDER. -/
def set (v : VersionVector) (r : ReplicaId) (n : Nat) (hn : 0 < n) : VersionVector := sorry

end VersionVector
end LeanCrdt
