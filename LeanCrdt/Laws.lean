import LeanCrdt.State

/-!
# Theorems about the CRDT

STAGE 1: statements only. Every `sorry` below is a placeholder to be replaced by a proof in
stage 2; none may remain at the end of stage 2.

All equalities are literal `=` on `State` (canonical representation; no quotient or
observational equivalence is involved).
-/

namespace LeanCrdt.State

/-- Semilattice order: `a ≤ b` iff `b` already contains everything `a` knows. -/
def Le (a b : State) : Prop := merge a b = b

/-! ## 1. Join-semilattice laws (state-based CRDT) -/

theorem merge_comm (a b : State) : merge a b = merge b a := sorry
theorem merge_assoc (a b c : State) : merge (merge a b) c = merge a (merge b c) := sorry
theorem merge_idem (a : State) : merge a a = a := sorry
theorem merge_empty (a : State) : merge a empty = a := sorry

/-- Convergence: any two replicas that have merged the same collection of states, in any order
and grouping, are equal. (Grouping is covered by `merge_assoc`; this covers order.) -/
theorem mergeAll_perm {l l' : List State} (h : l.Perm l') : mergeAll l = mergeAll l' := sorry

/-- Local operations are inflations, so merging a state with its own past never undoes them
(no resurrection of deleted or superseded versions). -/
theorem le_put (s : State) (r p h S) : Le s (s.put r p h S) := sorry
theorem le_delete (s : State) (p S) : Le s (s.delete p S) := sorry

/-! ## 2. Exact meaning of merge -/

theorem context_merge (a b : State) (r : ReplicaId) :
    (merge a b).context.get r = max (a.context.get r) (b.context.get r) := sorry

theorem mem_merge (a b : State) (e : Entry) :
    e ∈ (merge a b).entries ↔
      (e ∈ a.entries ∧ ¬ b.Supersedes e) ∨ (e ∈ b.entries ∧ ¬ a.Supersedes e) := sorry

/-! ## 3. No lost update -/

/-- A version present in `a` is still a current version of its path after merging with any `b`,
unless `b` has seen the event that wrote it and no longer holds it (superseded or deleted it). -/
theorem no_lost_update (a b : State) (e : Entry) (he : e ∈ a.entries) :
    e.hash ∈ (merge a b).versions e.path ∨ b.Supersedes e := sorry

/-! ## 4. Queries -/

theorem mem_versions (s : State) (p : String) (h : Hash) :
    h ∈ s.versions p ↔ ∃ e ∈ s.entries, e.path = p ∧ e.hash = h := sorry
theorem versions_sorted (s : State) (p : String) : StrictlySorted (s.versions p) := sorry
theorem mem_paths (s : State) (p : String) :
    p ∈ s.paths ↔ ∃ e ∈ s.entries, e.path = p := sorry
theorem paths_sorted (s : State) : StrictlySorted s.paths := sorry
theorem mem_paths_iff (s : State) (p : String) : p ∈ s.paths ↔ s.versions p ≠ [] := sorry
theorem snapshot_eq (s : State) : s.snapshot = s.paths.map (fun p => (p, s.versions p)) := sorry
theorem isConflicted_iff (s : State) (p : String) :
    s.isConflicted p = true ↔ ∃ h₁ h₂, h₁ ≠ h₂ ∧ h₁ ∈ s.versions p ∧ h₂ ∈ s.versions p := sorry

/-! ## 5. Local operations -/

theorem mem_versions_put (s : State) (r p h S q x) :
    x ∈ (s.put r p h S).versions q ↔
      (q = p ∧ x = h) ∨ (x ∈ s.versions q ∧ ¬ (q = p ∧ x ∈ S)) := sorry
theorem context_put (s : State) (r p h S r') :
    (s.put r p h S).context.get r' =
      if r' = r then s.context.get r + 1 else s.context.get r' := sorry
theorem mem_versions_delete (s : State) (p S q x) :
    x ∈ (s.delete p S).versions q ↔ x ∈ s.versions q ∧ ¬ (q = p ∧ x ∈ S) := sorry
theorem context_delete (s : State) (p S) : (s.delete p S).context = s.context := sorry
theorem versions_resolve (s : State) (r p h) : (s.resolve r p h).versions p = [h] := sorry

/-! ## 6. Concurrency semantics (decisions 2 and 3)

The hypothesis `b.context.get r ≤ a.context.get r` says "`b` has not seen the edit about to be
made by `r` on `a`". It always holds when `a` is replica `r`'s own state and `b` is any other
state, given the system assumption that `r` is the only issuer of `r`-dots and its state is
never rolled back. -/

/-- An edit survives a merge with any state that has not seen it, whatever that state did. -/
theorem put_survives_merge (a b : State) (r p h S) (hb : b.context.get r ≤ a.context.get r) :
    h ∈ (merge (a.put r p h S) b).versions p := sorry

/-- Decision 3: concurrent edit and delete of the same path: the edit wins. -/
theorem edit_wins_over_concurrent_delete (a b : State) (r p h S T)
    (hb : b.context.get r ≤ a.context.get r) :
    h ∈ (merge (a.put r p h S) (b.delete p T)).versions p := sorry

/-- Decision 2: concurrent edits of the same path are all kept, and differing ones are
reported as a conflict. -/
theorem concurrent_puts_kept (a b : State) (r₁ r₂ p h₁ h₂ S₁ S₂) (hr : r₁ ≠ r₂)
    (h1 : b.context.get r₁ ≤ a.context.get r₁) (h2 : a.context.get r₂ ≤ b.context.get r₂) :
    let m := merge (a.put r₁ p h₁ S₁) (b.put r₂ p h₂ S₂)
    h₁ ∈ m.versions p ∧ h₂ ∈ m.versions p ∧ (h₁ ≠ h₂ → m.isConflicted p = true) := sorry

/-- Decision 2: resolving supersedes every sibling it saw: merged with anything in the
resolver's causal past, only the resolution remains. -/
theorem resolve_supersedes (a b : State) (r p h) (hb : Le b a) :
    (merge (a.resolve r p h) b).versions p = [h] := sorry

end LeanCrdt.State
