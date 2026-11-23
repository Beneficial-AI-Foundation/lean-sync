# CRDT core: design note (stage 1)

Branch `crdt-core` · Lean 4.36.0 · core + `Init` only (no `Std` import at all).
Lean sources: `LeanCrdt/Types.lean`, `LeanCrdt/VersionVector.lean`, `LeanCrdt/State.lean` (executable),
`LeanCrdt/Laws.lean` (theorem statements). At this stage the operation bodies and all proofs are
`sorry` placeholders, marked `STAGE-1 PLACEHOLDER`; the types, orders and their lawfulness proofs are real.

## Model: an OR-map of multi-value registers in "dot store + causal context" form

The state is two canonical lists:

```lean
structure Entry where path : String; dot : Dot; hash : Hash        -- one live version of one file
structure Dot   where replica : ReplicaId; counter : Nat             -- one local edit event
structure ReplicaId where hi : UInt64; lo : UInt64                   -- 128 bits, host-generated
structure Hash  where bytes : ByteArray                              -- opaque content hash

structure VersionVector where
  entries : List (ReplicaId × Nat)
  sorted  : entries.Pairwise (fun a b => compare a.1 b.1 = .lt)
  pos     : ∀ p ∈ entries, 0 < p.2                                   -- absent ↔ 0

structure State where
  entries : List Entry                    -- strictly sorted by (path, dot, hash)
  context : VersionVector                 -- every event this state has seen
  sorted  : StrictlySorted entries
  covered : ∀ e ∈ entries, 0 < e.dot.counter ∧ e.dot.counter ≤ context.get e.dot.replica
```

* **Dots rather than per-path version vectors.** Each `put` by replica `r` issues the dot
  `(r, context.get r + 1)` and attaches it to the new entry. A single state-wide version vector
  (`context`) records which dots have been seen. This is the standard optimized OR-map/MV-register
  construction (Almeida, Shoker, Baquero, *Delta state replicated data types*, 2018). Compared with
  per-path version vectors it stores one dot per version instead of one vector per path, and it
  needs **no per-path tombstones**: "seen in `context` but absent from `entries`" *is* the deletion or
  supersession record. With whole-state merges every context is downward-closed, so a version vector
  represents it exactly (deltas would need dot sets; see risks).
* **Merge.** `context` is the pointwise max. An entry survives iff it is in both states, or it is in
  one and the other has not seen its dot. This gives, with no special cases: concurrent puts on a path
  become siblings (decision 2), an edit concurrent with a delete survives because the deleter has not
  seen its dot (decision 3), and a resolution, which is a `put` superseding all seen siblings, wins over
  exactly the siblings it saw.

**Representation choice: canonical, with literal equality.** Both lists are kept strictly sorted
(entries by `(path, dot, hash)`, vectors by replica, no zero counters), and the invariants are fields of
the structures. Two states with the same contents are therefore equal Lean values, and the laws are
literal `merge a b = merge b a`. The proof strategy is: (1) prove a membership characterization of each
operation, (2) prove that it preserves sortedness, (3) use the extensionality lemma "two strictly sorted
lists with the same members are equal". Commutativity, associativity and idempotence then reduce to
propositional facts about membership and `max`. Why this and not a `HashMap` up to equivalence:
* *Proof effort:* there is no quotient, no equivalence to prove congruent for every operation and query,
  and `Std.HashMap` lemmas are not needed. The work is one generic sorted-merge lemma set plus ext.
* *Runtime at 20k paths, few replicas, rare siblings:* merge is a single linear pass, O(n + m)
  comparisons plus an O(#replicas) vector lookup for entries present on one side only. The hash map
  would only win on point operations: `put`/`delete` here are O(position of the path) (they rebuild the
  list prefix) and `versions p` is O(position). The host should use `snapshot` (one pass) rather than
  calling `versions` per path. Memory is about 4 small objects per version.
* *Wasm and imports:* only `Init` is imported (`String` and `ByteArray` orders are core externs
  `lean_string_compare`/`lean_byte_array_compare`). `Std.Data.HashMap` and its lemma modules stay out.
* *Encoding:* the canonical order is the natural deterministic encoding order. Equal states encode to
  equal bytes, and the decoder only has to check sortedness to rebuild the invariants.
* *Determinism:* every observable order is a byte/number order that is the same on native and wasm.
  No `USize` or object hash ever enters the state.

## Public API (`LeanCrdt.State`)

| | |
|---|---|
| `empty : State` | |
| `merge : State → State → State`, `mergeAll : List State → State` | join |
| `put s self p h supersedes` | write version `h` of `p` and remove the local versions of `p` whose hash ∈ `supersedes`; new dot `(self, ctx(self)+1)` |
| `delete s p supersedes` | remove the local versions of `p` whose hash ∈ `supersedes`; issues no dot |
| `resolve s self p h` | `put s self p h (s.versions p)`: supersede every seen sibling (also the normal "edit") |
| `paths s : List String` | existing paths, strictly sorted by UTF-8 bytes |
| `versions s p : List Hash` | distinct current hashes of `p`, strictly sorted; `[]` = absent |
| `isConflicted s p : Bool` | `(versions s p).length ≥ 2` |
| `snapshot s : List (String × List Hash)` | `paths` with their `versions`, in one pass |

Supersession is **by hash**, as the brief asks. A version that arrives by merge after the host looked is
kept as a sibling unless it has the same hash as one the host saw; in that case removing it loses no
content. `delete` with a partial list leaves the file alive with the remaining versions.

## Theorems (exact statements in `LeanCrdt/Laws.lean`)

Here `Supersedes b e := b.context.covers e.dot ∧ e ∉ b.entries` ("`b` saw the event that wrote `e` and no
longer holds it"), and `Le a b := merge a b = b`.
1. Semilattice: `merge_comm`, `merge_assoc`, `merge_idem`, `merge_empty`, `mergeAll_perm`
   (`l.Perm l' → mergeAll l = mergeAll l'`). Inflation: `le_put`, `le_delete` (`Le s (s.put …)`), i.e.
   merging with your own past never undoes a local op.
2. Exact merge semantics: `context_merge` (`get = max`) and
   `mem_merge : e ∈ (merge a b).entries ↔ (e ∈ a.entries ∧ ¬ b.Supersedes e) ∨ (e ∈ b.entries ∧ ¬ a.Supersedes e)`.
3. **No lost update:** `no_lost_update : e ∈ a.entries → e.hash ∈ (merge a b).versions e.path ∨ b.Supersedes e`.
4. Queries: `mem_versions`, `versions_sorted`, `mem_paths`, `paths_sorted`, `mem_paths_iff`, `snapshot_eq`, `isConflicted_iff`.
5. Local ops: `mem_versions_put`, `context_put`, `mem_versions_delete`, `context_delete`, `versions_resolve` (`= [h]`).
6. Concurrency: `put_survives_merge`, `edit_wins_over_concurrent_delete` (decision 3), `concurrent_puts_kept`
   (decision 2: both kept, and `isConflicted` if they differ), `resolve_supersedes` (merged with anything
   in the resolver's past, only the resolution remains). Their hypothesis `b.context.get r ≤ a.context.get r`
   formalises "`b` has not seen the edit `r` is about to make".

**What is assumed, not proved.** A dot names one event globally: replica `r` alone issues `r`-dots, from a
state that is never rolled back. Lean cannot check this; the theorems in group 6 carry it as the explicit
hypothesis above. The laws in groups 1–5 hold for all states, with no assumption.

## Deletes, tombstones and retained garbage

There are no per-path tombstones. A deleted or superseded version disappears from `entries` immediately;
its dot stays covered by `context`. **The only garbage kept forever is the version vector: one
`(ReplicaId, Nat)` entry per replica id that has ever made an edit.** It grows by one entry per new
device, reinstall or cleared browser storage (each gets a new id), and never shrinks. Pruning would need
a coordination protocol, which is out of scope. Deleting files costs no space.

## Risks

1. **Dot reuse after rollback (data loss).** If a replica restarts from an older persisted state and
   reuses its id, it reissues dots that others have already seen. The new edits can then be dropped as
   "seen and deleted". Host rule: *persist the state before sending any of its dots to another replica*,
   or take a fresh id whenever persistence is in doubt. This is the most important integration rule.
2. **Bulk import is quadratic.** 20,000 `put`s on an empty state rebuild the list prefixes, about 2·10⁸
   cons cells. A `putMany` (sort the batch, then one merge-like pass) would fix this (see question).
3. **Paths are raw strings.** Unicode normalisation (NFC/NFD) and case-insensitive filesystems are the
   host's job. Two spellings are two files to the CRDT.
4. **Rename = delete + add.** A rename concurrent with an edit of the old path keeps both files: the
   edited old path and the new path.
5. **Deltas later.** Delta-state sync needs non-contiguous contexts (dot sets) or causal delivery of
   deltas. The version-vector context is correct only for whole-state merges.
6. **Stack.** All list walks will be self tail calls, which Lean compiles to loops. Library helpers with
   non-tail compiled code (`List.foldr`, derived `DecidableEq`/`BEq` on lists) must be avoided in
   executable paths. State equality for the host/tests gets a tail-recursive implementation.
7. **Proof engineering.** Merges are well-founded recursion on two lists. They are proved through
   `fun_induction` against a structural specification. This is the main stage-2 effort, and I do not
   expect statements to need weakening.
