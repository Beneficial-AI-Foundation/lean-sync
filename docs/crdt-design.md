# CRDT core: design and status

Branch `crdt-core` · Lean 4.36.0 · Lean core (`Init`) only: no `Std`, no Mathlib, no Batteries.
Status: implemented, every stated theorem proved (no `sorry`, no `axiom`, no `native_decide`, no
`unsafe`/`implemented_by`), tested natively. Not yet built for wasm.

| File | Contents | Runtime? |
|---|---|---|
| `LeanCrdt/Types.lean` | `ReplicaId`, `Hash`, `Dot`, `Entry`, their orders and lawfulness | yes |
| `LeanCrdt/SortedList.lean` | generic tail-recursive sorted merge (`mergeWith`) and its correctness | yes |
| `LeanCrdt/VersionVector.lean` | canonical version vectors, pointwise-max merge | yes |
| `LeanCrdt/State.lean` | the state, merge, queries, local operations, `putMany` | yes |
| `LeanCrdt/Laws.lean` | the user-facing theorems | proofs only |
| `Tests/Main.lean`, `scripts/test-crdt.sh` | native tests, stack test | tests |

## ⚠ HOST RULE: persist before you share, or use a fresh replica id

**Before any state containing a new local edit is sent to another replica, that state must be
durably persisted. If the host cannot guarantee that the state it loads at startup is the latest
one it ever sent, for example after restoring a backup, a partial storage loss, or the same storage
in two tabs, it must use a new replica id from then on.**

The reason: each local edit by replica `r` is named by a dot `(r, n)`, where `n = context[r] + 1`.
Correctness relies on a dot naming exactly one edit. If `r` restarts from an older state, it reissues
dots that peers have already seen, now attached to different content. A peer that saw the old dot
and then deleted or superseded it treats the new edit as "seen and removed" and **silently drops
it**. That is exactly the lost update this design otherwise rules out.

Lean cannot check this rule. The concurrency theorems state it as an explicit hypothesis,
`b.context.get r ≤ a.context.get r` ("`b` has not seen what `r` is about to write"), and that
hypothesis holds for every peer `b` precisely when the rule is followed. Two tabs on the same storage
count as two replicas, so each needs its own id.

## Model: an OR-map of multi-value registers in "dot store + causal context" form

```lean
structure ReplicaId where hi : UInt64; lo : UInt64          -- 128 bits, host-generated
structure Hash  where bytes : ByteArray                     -- opaque content hash
structure Dot   where replica : ReplicaId; counter : Nat    -- one local edit event
structure Entry where path : String; dot : Dot; hash : Hash -- one live version of one file
structure VersionVector where
  entries : List (ReplicaId × Nat)           -- strictly sorted by replica, all counters > 0
  sorted : KeySorted entries; pos : ∀ p ∈ entries, 0 < p.2
structure State where
  entries : List Entry                       -- strictly sorted by (path, dot, hash)
  context : VersionVector                    -- every event this state has seen
  sorted  : StrictlySorted entries
  covered : ∀ e ∈ entries, 0 < e.dot.counter ∧ e.dot.counter ≤ context.get e.dot.replica
```

* **Dots and one causal context**, as in the standard optimized OR-map/MV-register (Almeida,
  Shoker, Baquero, *Delta state replicated data types*, 2018). We use these rather than a version
  vector per path:
  - each version stores one dot rather than one vector;
  - there are no per-path tombstones: "covered by `context` but absent from `entries`" is the
    record of a deletion or supersession;
  - with whole-state merges, every context is downward-closed, so a version vector represents it exactly.
* **Merge.** `context` is the pointwise max. An entry survives iff it is in both states, or it is in
  one and the other has not seen its dot. With no special cases, this gives:
  - concurrent puts on one path become siblings (decision 2);
  - an edit concurrent with a delete survives, because the deleter never saw its dot (decision 3);
  - a resolution, which is a `put` superseding the siblings it saw, removes exactly those siblings.

**Representation: canonical, with literal equality.** Both lists are strictly sorted and the
invariants are fields of the structures, so equal contents means equal values. Every law is stated
with Lean's `=`. No observational equivalence is involved.

The proofs follow one pattern:
1. characterise what each operation's result contains;
2. prove the result stays sorted;
3. apply "two strictly sorted lists with the same members are equal" (`eq_of_sorted_of_mem_iff`)
   and its version-vector analogue (`VersionVector.ext`).

Why this beats a hash map up to equivalence:
- no quotient, and no congruence proofs for every operation and query;
- no `Std` import, so no `HashMap` lemma modules are linked into the wasm (see the spike);
- merge is a single pass over both entry lists. It is linear only while the number of replica ids
  r stays small; see "Cost" below;
- every observable order is a byte or number order that is the same on native and wasm:
  - `String` uses `lean_string_compare` (UTF-8 bytes, the same as code-point order);
  - `ByteArray` uses `lean_byte_array_compare`;
  - `UInt64` and `Nat` compare numerically.
- No `USize` or object hash enters the state.

For a future binary encoding, the canonical order is the natural one: equal states encode to equal
bytes. A decoder must re-check sortedness, positivity and coverage to rebuild the invariants.

## Public API (`LeanCrdt.State`)

| | |
|---|---|
| `empty`, `merge a b`, `mergeAll l` | join; `mergeAll` folds `merge` from `empty` |
| `put s self p h supersedes` | write version `h` of `p` with dot `(self, ctx(self)+1)`; drop the local versions of `p` whose hash is in `supersedes` |
| `putMany s self items` | batch put: sort the batch, then one pass over the state; **proved equal** to the `put`s one after the other (`putSeq`) |
| `delete s p supersedes` | drop the local versions of `p` whose hash is in `supersedes`; issues no dot |
| `resolve s self p h` | `put s self p h (s.versions p)`: supersede every seen version (also the normal "edit") |
| `paths s` | existing paths, strictly sorted by UTF-8 bytes |
| `versions s p` | distinct current hashes of `p`, strictly sorted; `[]` = absent |
| `isConflicted s p` | `(versions s p).length ≥ 2` |
| `snapshot s` | every path with its versions, in one pass over the entries |
| `beq a b` | literal equality, computed with loops |

`self` is passed explicitly: the state is shared data and carries no notion of which replica owns it.

**Supersession is by hash.** A version that arrives by merge after the host looked is kept as a
sibling, unless its hash equals one the host saw; in that case removing it loses no content.
Two concurrent versions with the same hash are two entries but one element of `versions`, so they
are not a conflict.

## Theorems (all in `LeanCrdt/Laws.lean`, all proved)

Definitions used below:
- `Supersedes b e := b.context.covers e.dot = true ∧ e ∉ b.entries`: `b` saw the event that wrote
  `e` and no longer holds `e`.
- `Le a b := merge a b = b`.

1. **Semilattice:** `merge_comm`, `merge_assoc`, `merge_idem`, `merge_empty`, and
   `mergeAll_perm : l.Perm l' → mergeAll l = mergeAll l'`.
2. **Local operations only grow the state:** `le_put`, `le_delete`. Merging with your own past never
   undoes a local operation.
3. **Exact merge semantics:**
   - `context_merge : (merge a b).context.get r = max (a.context.get r) (b.context.get r)`;
   - `mem_merge : e ∈ (merge a b).entries ↔ (e ∈ a.entries ∧ ¬ b.Supersedes e) ∨ (e ∈ b.entries ∧ ¬ a.Supersedes e)`.
4. **No lost update:**
   `no_lost_update : e ∈ a.entries → e.hash ∈ (merge a b).versions e.path ∨ b.Supersedes e`.
   This holds for every `a`, `b`, `e`, with no hypothesis.
5. **Queries:**
   - `mem_versions : h ∈ s.versions p ↔ ∃ e ∈ s.entries, e.path = p ∧ e.hash = h`;
   - `versions_sorted`, `mem_paths`, `paths_sorted`, `mem_paths_iff`, `isConflicted_iff`;
   - `snapshot_eq : s.snapshot = s.paths.map (fun p => (p, s.versions p))`.
6. **Local operations:**
   - `mem_versions_put : x ∈ (s.put r p h S).versions q ↔ (q = p ∧ x = h) ∨ (x ∈ s.versions q ∧ ¬(q = p ∧ x ∈ S))`;
   - `context_put`, `mem_versions_delete`, `context_delete`;
   - `versions_resolve : (s.resolve r p h).versions p = [h]`.
7. **Concurrency.** Each theorem takes the host-rule hypothesis `b.context.get r ≤ a.context.get r`:
   - `put_survives_merge`;
   - `edit_wins_over_concurrent_delete` (decision 3);
   - `concurrent_puts_kept` (decision 2): both versions are kept, and the path `isConflicted` if they differ;
   - `resolve_supersedes : Le b a → (merge (a.resolve r p h) b).versions p = [h]`.
8. **Batch:** `putMany_eq_putSeq : s.putMany r items = s.putSeq r items`. This holds unconditionally,
   so every law above transfers to `putMany`. Dots are assigned in list order: item `i` gets
   `ctx(self)+1+i`. When two items share a path, `putMany` falls back to `putSeq`.

The 26 statements fixed in stage 1 are unchanged. A Lean file that restates each one verbatim and
discharges it with the current theorem typechecks. The theorems added since stage 1 are
`putSeq_spec`, `putMany_eq_putSeq` and helper lemmas.

`#print axioms` on the headline theorems lists only `propext`, `Classical.choice` and
`Quot.sound`: the standard axioms that core tactics such as `simp` and `grind` rely on.

## Deletes, tombstones and retained garbage

There are no per-path tombstones. A deleted or superseded version leaves `entries` immediately,
and its dot stays covered by `context`. **The only data kept forever is the version vector: one
`(ReplicaId, Nat)` entry for every replica id that has ever made an edit.**
- It grows by one entry for every new device, reinstall, cleared browser storage or fresh id taken
  under the host rule.
- It never shrinks. Pruning would need a coordination protocol, which is out of scope.

Deleting files costs no space.

## Consequences accepted by the user

* **Rename is delete + add.** A rename concurrent with an edit of the old path leaves both files: the
  edited old path and the new path. A unit test checks this.
* **Each new replica id adds a permanent version-vector entry** (see above).
* **Paths are raw strings.** Unicode normalisation (NFC/NFD), case-insensitive filesystems and
  path syntax are the host's job. Two spellings are two files.

## Tests (native, `scripts/test-crdt.sh`)

The script first builds the library, which checks every proof. It then greps `LeanCrdt/` for the
forbidden constructs and runs the following tests:
- **unit:** decisions 2 and 3, resolution, partial deletes, no resurrection, same-hash siblings,
  rename, `putMany` with a repeated path, the snapshot, Unicode order;
- **sim:** 40 seeds × 300 random operations on 4 replicas.
  - Operations: `put`, `delete`, `resolve`, `putMany`, `merge`.
  - After each merge it checks:
    - commutativity, associativity, idempotence and the identity;
    - `merge` against a naive quadratic reference merge;
    - no lost update and the query specifications.
  - After each `put` it checks that the edit survives merging with every peer, including a peer
    that deleted the path.
  - At the end it checks convergence under 5 random permutations, 5 random groupings and gossip.
  - The seed is printed on failure. A deliberately broken merge was caught by 800+ failing checks.
- **scale:** 20,000 paths built with `putMany`. Two replicas diverge with 10,000 and 6,667 edits and
  2,858 deletes, then merge. The test checks the laws, the expected number of surviving paths
  (18,095) and of conflicts (2,857), single operations on the large state, and a smaller test of
  300 single `put`s against `putMany`.
- **stack:** `main` runs on a thread whose stack is `LEAN_STACK_SIZE_KB`, plus a 128 KB buffer;
  the default is 1 GB, so plain `ulimit -s` has no effect. With it set to 256 KB:
  - a trivial non-tail recursion of depth 13,000 must crash. That is the spike's ~13k-frame
    browser budget, and the measured native maximum here is about 12,100 frames;
  - the non-tail *specification* `mergeSpec` must crash on the scale sizes, at about 4,850
    elements per list;
  - scale, unit and sim must pass.
  - "Crash" means exit status 134 (SIGABRT) **and** the runtime's "Stack overflow detected"
    message. Any other failure counts as a test failure. A self-check confirms that a bogus
    subcommand, which exits 2, is not mistaken for an overflow.

  The 20k scale test also passes at 64 KB (about 6,000 trivial frames), as does a 100k-path run.
  Caveat: native and wasm frame sizes differ. The calibration is in frames of a trivial function.

Measured on this machine with `crdt-tests bench [n]` (native, indicative):

| Operation | 20k paths | 100k paths |
|---|---|---|
| `put` + `merge` (10k entries differ) | ≈ 1.2 ms | ≈ 8 ms |
| `put` + `snapshot` | ≈ 1.4 ms | ≈ 18 ms |
| `putMany` of 20k items onto a 20k-path state | ≈ 6.5 ms | |

The whole 20k scale test takes about 0.6 s. Most of that is its 2,858 single deletes: each one is O(n).

## Cost (true bounds)

Notation:
- n, m: number of entries (live versions) in each state;
- r: entries in a context, i.e. replica ids that have **ever** edited, including retired devices,
  reinstalls and fresh ids;
- k: entries at one path, i.e. its siblings;
- b: items in a batch;
- |S|: length of a `supersedes` list.

Costs count comparisons of paths, hashes and ids.

| Operation | Cost | Effectively linear when |
|---|---|---|
| `merge` | O(n + m) comparisons, plus one `covers` lookup (an O(r) scan of the other context) per entry present on one side only: **O((n + m)·r)** worst case, plus O(r) for the context | r is a handful, or the states mostly agree |
| `versions`, `isConflicted` | O(n) scan + **O(k²)** sort and dedup of the path's hashes | siblings are rare (k ≤ a few) |
| `snapshot` | **O(n + Σₚ kₚ²)** | siblings are rare |
| `paths` | O(n) | always |
| `put` | O(n + r + k·\|S\|) | always, for small r and k |
| `delete` | O(n + k·\|S\|) | always, for small k |
| `putMany` | O(b log b + n + r), plus O(\|S\|) per entry at a batch path; repeated paths fall back to `putSeq`, which is O(b·n) | paths in a batch are distinct |
| `VersionVector.merge` | O(r) | always |

With as many writer ids as entries, `merge` becomes quadratic. A path with many siblings makes
`versions` and `snapshot` quadratic in that path's sibling count. These bounds are acceptable under
the user's operating assumptions (a handful of replicas, rare siblings), and are listed as known
limits below.

## Remaining risks and limitations

1. **Host rule** (above). This is the one integration rule whose violation loses data.
2. **Point operations are O(n).** `put`, `delete` and `versions` rebuild or scan the list. Deleting
   k files one at a time is O(k·n): 2,858 deletes on 20k paths took 0.5 s natively, and 14k deletes
   on 100k paths took 18 s. Use `putMany` for bulk writes and `snapshot` for bulk reads. A proved
   `deleteMany`, along the lines of `putMany`, is the obvious next step if bulk deletes matter.
3. **Not yet run under wasm.** The import closure is `Init` only, but startup time and size under
   wasm are not yet measured.
4. **Deltas later** need non-contiguous contexts (dot sets) or causal delivery. The version-vector
   context is correct for whole-state merges only.
5. **`merge` is O((n + m)·r)** (see "Cost"). `covers` scans the context list for every one-sided
   entry. It is fine for a handful of replica ids, but r counts every id ever used and never shrinks.
   Suggested fix, not implemented: index the other context once per merge, for example as a sorted
   `Array` searched by binary search, giving O((n + m)·log r). It needs a new lemma that the indexed
   lookup equals `VersionVector.get`; the merge laws themselves would not change.
6. **`versions`/`snapshot` are quadratic in the siblings of one path** (`sortedSetOf` and
   `snapStep` insert each hash into a sorted list). Suggested fix, not implemented: collect the
   path's hashes, then sort once (`List.mergeSort`, tail-recursive in core) and drop adjacent
   duplicates, giving O(k log k). Its proof obligations are the same kind as `putMany`'s
   (permutation, sortedness, then strict sortedness after dedup), and `versionsOf_eq` would carry
   the rest over unchanged.
7. **Stack.** Executable code uses only self tail calls and core functions that have tail-recursive
   implementations. `Tests/` itself uses a `partial def` of logarithmic depth. The stack test guards
   this; it is calibrated natively, not in a browser.
