import LeanCrdt.State

/-!
# Native tests for the CRDT core

Usage: `crdt-tests [unit | sim [seed] [count] | scale [n] | control [n] | deep [n] | bench [n] | delbench [n] [fast] | all]` (default: `all`).

* `unit`    semantic unit tests (decisions 2 and 3, resolve, delete, putMany, queries);
* `sim`     seeded randomized simulation: replicas doing random operations and merging in random
            orders and groupings; checks convergence and the proved properties at runtime;
* `scale`   realistic size (default 20,000 paths) exercising every executable operation;
* `control` runs the *non-tail-recursive* specification `mergeSpec` on lists of the scale test's
            size. It exists to fail: under the small stack used by `scripts/test-stack.sh` it must
            crash, which shows that the limit is tight enough for `scale` passing to mean something.
-/

open LeanCrdt LeanCrdt.State

namespace Tests

def rid (n : Nat) : ReplicaId := ⟨0x1234, n.toUInt64⟩
def hs (s : String) : Hash := ⟨s.toUTF8⟩

instance : ToString Hash where
  toString h := String.ofList (h.bytes.toList.map (fun b => Char.ofNat b.toNat))

def showVersions (l : List Hash) : String := toString (l.map toString)

structure Ctx where
  failures : IO.Ref Nat
  checks : IO.Ref Nat
  label : String

def check (c : Ctx) (name : String) (cond : Bool) (detail : Unit → String := fun _ => "") : IO Unit := do
  c.checks.modify (· + 1)
  unless cond do
    c.failures.modify (· + 1)
    IO.eprintln s!"FAIL [{c.label}] {name} {detail ()}"

/-! ## Unit tests -/

def unitTests (c : Ctx) : IO Unit := do
  let A := rid 1
  let B := rid 2
  let p := "docs/a.txt"
  -- basic put / query
  let s0 := State.empty
  check c "empty has no paths" (s0.paths == [])
  let a1 := s0.put A p (hs "v1") []
  check c "put creates path" (a1.paths == [p])
  check c "put version" (a1.versions p == [hs "v1"])
  check c "not conflicted" (!a1.isConflicted p)
  -- replicate to B
  let b1 := State.empty.merge a1
  check c "replicated" (b1.beq a1)
  -- decision 2: concurrent edits become siblings
  let a2 := a1.resolve A p (hs "va")
  let b2 := b1.resolve B p (hs "vb")
  let m := a2.merge b2
  check c "concurrent edits: both kept" (m.versions p == [hs "va", hs "vb"])
    (fun _ => showVersions (m.versions p))
  check c "concurrent edits: conflicted" (m.isConflicted p)
  check c "merge commutes here" ((b2.merge a2).beq m)
  -- resolve supersedes the siblings it saw
  let a3 := (a2.merge b2).resolve A p (hs "vr")
  check c "resolved locally" (a3.versions p == [hs "vr"])
  check c "resolution wins over the siblings it saw" ((a3.merge b2).versions p == [hs "vr"])
  check c "resolution wins (other order)" ((b2.merge a3).versions p == [hs "vr"])
  -- an edit concurrent with the resolution stays a sibling
  let b3 := b2.resolve B p (hs "vb2")
  check c "edit concurrent with resolution is kept"
    ((a3.merge b3).versions p == [hs "vb2", hs "vr"])
    (fun _ => showVersions ((a3.merge b3).versions p))
  -- decision 3: concurrent edit and delete: the edit wins
  let base := State.empty.put A "x" (hs "x0") []
  let bBase := State.empty.merge base
  let aEdit := base.resolve A "x" (hs "x1")
  let bDel := bBase.delete "x" (bBase.versions "x")
  check c "delete removes locally" (bDel.versions "x" == [] && bDel.paths == [])
  check c "edit wins over concurrent delete" ((aEdit.merge bDel).versions "x" == [hs "x1"])
  check c "edit wins over concurrent delete (other order)" ((bDel.merge aEdit).versions "x" == [hs "x1"])
  -- a delete that saw the edit removes it, and old states cannot resurrect it
  let bDel2 := (bDel.merge aEdit).delete "x" [hs "x1"]
  check c "causal delete removes" (bDel2.paths == [])
  check c "no resurrection from old state" ((bDel2.merge base).paths == [] && (bDel2.merge aEdit).paths == [])
  -- partial delete keeps unseen siblings
  let pd := m.delete p [hs "va"]
  check c "partial delete keeps the rest" (pd.versions p == [hs "vb"])
  -- supersession by hash keeps a sibling the host had not seen
  let sib := m.put A p (hs "vc") [hs "va"]
  check c "put keeps unlisted siblings" (sib.versions p == [hs "vb", hs "vc"])
  -- identical concurrent content is not a conflict
  let sameA := a1.resolve A p (hs "same")
  let sameB := b1.resolve B p (hs "same")
  let same := sameA.merge sameB
  check c "same hash: not conflicted" (!same.isConflicted p && same.versions p == [hs "same"])
  check c "same hash: two entries kept internally" (same.entries.length == 2)
  -- rename (delete + add) concurrent with an edit of the old path leaves both files
  let rn := (State.empty.put A "old" (hs "o") [])
  let rnB := State.empty.merge rn
  let renamed := (rn.delete "old" [hs "o"]).put A "new" (hs "o") []
  let edited := rnB.resolve B "old" (hs "o2")
  check c "rename concurrent with edit keeps both"
    ((renamed.merge edited).paths == ["new", "old"])
  -- putMany equals the sequence of puts, including with a repeated path (fallback)
  let items : List PutItem :=
    [⟨"b", hs "1", []⟩, ⟨"a", hs "2", []⟩, ⟨"docs/a.txt", hs "3", [hs "va"]⟩, ⟨"c", hs "4", []⟩]
  check c "putMany = putSeq" ((m.putMany A items).beq (m.putSeq A items))
  let dupItems : List PutItem := [⟨"a", hs "1", []⟩, ⟨"a", hs "2", [hs "1"]⟩]
  check c "putMany = putSeq (repeated path)" ((m.putMany A dupItems).beq (m.putSeq A dupItems))
  check c "putMany repeated path: second supersedes first"
    ((m.putMany A dupItems).versions "a" == [hs "2"])
  -- snapshot
  let big := m.putMany A items
  check c "snapshot = paths.map versions"
    (big.snapshot == big.paths.map (fun q => (q, big.versions q)))
  check c "paths sorted" (big.paths == ["a", "b", "c", "docs/a.txt"])
  -- deleteMany / deletePaths
  let d0 := (State.empty.putMany A [⟨"f/1", hs "1", []⟩, ⟨"f/2", hs "2", []⟩, ⟨"g", hs "g", []⟩])
  let dB := (State.empty.merge d0).resolve B "f/1" (hs "1b")  -- B edits f/1 concurrently
  -- a third replica (its own id: reusing B here would break the host rule) adds a sibling to f/2
  let dA := d0.merge (State.empty.merge d0 |>.put (rid 3) "f/2" (hs "2s") [])
  check c "deleteMany: f/2 has siblings" (dA.versions "f/2" == [hs "2", hs "2s"])
  let dupItems : List DeleteItem :=
    [⟨"f/2", some [hs "2"]⟩, ⟨"nope", none⟩, ⟨"f/2", some [hs "2s"]⟩, ⟨"g", some [hs "other"]⟩]
  check c "deleteMany = deleteSeq (duplicates, absent path)"
    ((dA.deleteMany dupItems).beq (dA.deleteSeq dupItems))
  check c "deleteMany: both siblings removed by two items for the same path"
    ((dA.deleteMany dupItems).versions "f/2" == [])
  check c "deleteMany: unlisted hash kept" ((dA.deleteMany dupItems).versions "g" == [hs "g"])
  check c "deleteMany: absent path is a no-op" ((dA.deleteMany [⟨"nope", none⟩]).beq dA)
  check c "deleteMany: partial delete keeps the other sibling"
    ((dA.deleteMany [⟨"f/2", some [hs "2"]⟩]).versions "f/2" == [hs "2s"])
  let folder := dA.deletePaths ["f/1", "f/2"]
  check c "deletePaths removes all siblings" (folder.paths == ["g"])
  check c "deletePaths = sequential deletes of everything seen"
    (folder.beq (["f/1", "f/2"].foldl (fun s p => s.delete p (s.versions p)) dA))
  check c "deleteMany edit wins: concurrent edit survives a folder delete"
    ((folder.merge dB).versions "f/1" == [hs "1b"] && (dB.merge folder).versions "f/1" == [hs "1b"])
  check c "deleteMany: the not-edited file stays deleted" ((folder.merge dB).versions "f/2" == [])
  check c "deleteMany: empty batch is a no-op" ((dA.deleteMany []).beq dA)
  -- non-ASCII paths are ordered by UTF-8 bytes (= code points)
  let u := (State.empty.put A "é" (hs "1") []).put A "z" (hs "2") [] |>.put A "Z" (hs "3") []
  check c "unicode order" (u.paths == ["Z", "z", "é"])

/-! ## Randomized simulation -/

/-- splitmix64: deterministic and platform-independent. -/
structure Rng where
  s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

def Rng.below (g : Rng) (n : Nat) : Nat × Rng :=
  let (x, g) := g.next
  (x.toNat % n, g)

abbrev SimM := StateT Rng IO

def rand (n : Nat) : SimM Nat := modifyGet (fun g => g.below n)

def pick {α} [Inhabited α] (l : List α) : SimM α := do
  let i ← rand l.length
  return l[i]!

/-- Random sublist. -/
def subset {α} (l : List α) : SimM (List α) := do
  let mut out := []
  for x in l do
    if (← rand 2) == 0 then out := x :: out
  return out.reverse

def shuffle {α} [Inhabited α] (l : List α) : SimM (List α) := do
  let mut arr := l.toArray
  for i in [0:arr.size] do
    let j := i + (← rand (arr.size - i))
    let t := arr[i]!
    arr := arr.set! i arr[j]!
    arr := arr.set! j t
  return arr.toList

/-- Merge a list in a random grouping (random binary tree). -/
partial def randomTree (l : List State) : SimM State := do
  match l with
  | [] => return State.empty
  | [x] => return x
  | _ =>
    let k := 1 + (← rand (l.length - 1))
    let a ← randomTree (l.take k)
    let b ← randomTree (l.drop k)
    if (← rand 2) == 0 then return a.merge b else return b.merge a

/-- Naive reference merge (quadratic, written from the specification, independent of the
sorted-list code): the set of entries `e` with `e ∈ a ∧ (b covers e → e ∈ b)` or symmetrically. -/
def refMergeEntries (a b : State) : List Entry :=
  let fromA := a.entries.filter (fun e => !b.context.covers e.dot || b.entries.contains e)
  let fromB := b.entries.filter (fun e => (!a.context.covers e.dot || a.entries.contains e) && !fromA.contains e)
  fromA ++ fromB

def sameSet (x y : List Entry) : Bool := x.all (y.contains ·) && y.all (x.contains ·) && x.length == y.length

def paths0 : List String := ["a", "b", "c/d", "c/e", "é", "f"]
def hashes0 : List Hash := ["0", "1", "2", "3", "4"].map hs

def checkMergeProps (c : Ctx) (a b x : State) : IO Unit := do
  let m := a.merge b
  check c "comm" (m.beq (b.merge a))
  check c "idem" ((a.merge a).beq a)
  check c "assoc" (((a.merge b).merge x).beq (a.merge (b.merge x)))
  check c "empty identity" ((a.merge State.empty).beq a)
  check c "merge = reference" (sameSet m.entries (refMergeEntries a b))
  for e in a.entries do
    let kept := (m.versions e.path).contains e.hash
    let superseded := b.context.covers e.dot && !b.entries.contains e
    check c "no lost update" (kept || superseded)
  check c "snapshot spec" (m.snapshot == m.paths.map (fun q => (q, m.versions q)))
  for q in m.paths do
    check c "isConflicted spec" (m.isConflicted q == ((m.versions q).length ≥ 2))

def simOnce (c : Ctx) (steps nrep : Nat) : SimM Unit := do
  let mut reps : Array State := Array.replicate nrep State.empty
  for _ in [0:steps] do
    let i ← rand nrep
    let me := rid i
    let s := reps[i]!
    let op ← rand 100
    if op < 30 then
      -- put, superseding a random subset of what is seen
      let p ← pick paths0
      let h ← pick hashes0
      let sup ← subset (s.versions p)
      let s' := s.put me p h sup
      -- the edit survives merging with any other replica (none has seen it)
      for j in [0:nrep] do
        check c "put survives merge" (((s'.merge reps[j]!).versions p).contains h)
        check c "put survives merge with a delete"
          (((s'.merge (reps[j]!.delete p (reps[j]!.versions p))).versions p).contains h)
      check c "inflation (put)" ((s.merge s').beq s')
      reps := reps.set! i s'
    else if op < 42 then
      let p ← pick paths0
      let sup ← subset (s.versions p)
      let s' := s.delete p sup
      check c "inflation (delete)" ((s.merge s').beq s')
      reps := reps.set! i s'
    else if op < 50 then
      let p ← pick paths0
      if (s.versions p).length > 0 then
        let h ← pick hashes0
        let s' := s.resolve me p h
        check c "resolve result" (s'.versions p == [h])
        check c "resolve vs own past" ((s'.merge s).versions p == [h])
        reps := reps.set! i s'
    else if op < 56 then
      let n ← rand 4
      let mut items : List PutItem := []
      for _ in [0:n] do
        let p ← pick paths0
        items := items ++ [⟨p, ← pick hashes0, ← subset (s.versions p)⟩]
      let s' := s.putMany me items
      check c "putMany = putSeq" (s'.beq (s.putSeq me items))
      reps := reps.set! i s'
    else if op < 64 then
      let n ← rand 5
      let mut items : List DeleteItem := []
      for _ in [0:n] do
        let p ← pick ("absent" :: paths0)
        let sup ← if (← rand 3) == 0 then pure none
          else if (← rand 2) == 0 then pure (some (← subset (s.versions p)))
          else pure (some (← subset hashes0))
        items := items ++ [⟨p, sup⟩]
      let s' := s.deleteMany items
      check c "deleteMany = deleteSeq" (s'.beq (s.deleteSeq items))
      check c "inflation (deleteMany)" ((s.merge s').beq s')
      reps := reps.set! i s'
    else
      let j ← rand nrep
      let k ← rand nrep
      checkMergeProps c s reps[j]! reps[k]!
      reps := reps.set! i (s.merge reps[j]!)
  -- convergence: any order and grouping of the final states gives the same result
  let all := reps.toList
  let ref := mergeAll all
  for _ in [0:5] do
    let perm ← shuffle all
    check c "convergence: mergeAll of a permutation" ((mergeAll perm).beq ref)
    check c "convergence: random grouping" ((← randomTree perm).beq ref)
  -- gossip until quiescent: every replica ends equal to the join
  let mut gossip := reps
  for _ in [0:2] do
    for a in [0:nrep] do
      for b in [0:nrep] do
        gossip := gossip.set! a (gossip[a]!.merge gossip[b]!)
  for g in gossip do
    check c "convergence: gossip" (g.beq ref)

def simTests (c : Ctx) (seed count : Nat) : IO Unit := do
  for k in [0:count] do
    let sd := seed + k
    let before ← c.failures.get
    let c' := { c with label := s!"sim seed={sd}" }
    let _ ← (simOnce c' 300 4).run ⟨sd.toUInt64⟩
    let after ← c.failures.get
    if after != before then
      IO.eprintln s!"simulation failed: rerun with `crdt-tests sim {sd} 1`"

/-! ## Scale -/

def scalePaths (n : Nat) (tag : String) : List PutItem :=
  (List.range n).map (fun i => ⟨s!"dir{i % 97}/file{i}.txt", hs s!"{tag}{i}", []⟩)

def scaleTests (c : Ctx) (n : Nat) : IO Unit := do
  let A := rid 1
  let B := rid 2
  let t0 ← IO.monoMsNow
  let items := scalePaths n "a"
  let a := State.empty.putMany A items
  check c "putMany size" (a.entries.length == n)
  let b0 := State.empty.merge a
  -- B edits every other file and deletes every 7th; A edits every 3rd concurrently
  let bItems := (List.range n).filter (· % 2 == 0) |>.map
    (fun i => (⟨s!"dir{i % 97}/file{i}.txt", hs s!"b{i}", [hs s!"a{i}"]⟩ : PutItem))
  let b1 := b0.putMany B bItems
  let dels := (List.range n).filter (· % 7 == 0)
  let b2 := dels.foldl
    (fun s i => let p := s!"dir{i % 97}/file{i}.txt"; s.delete p (s.versions p)) b1
  let delPaths := dels.map (fun i => s!"dir{i % 97}/file{i}.txt")
  check c "scale: deletePaths = single deletes" ((b1.deletePaths delPaths).beq b2)
  check c "scale: deleteMany = single deletes"
    ((b1.deleteMany (delPaths.map (fun p => ⟨p, some (b1.versions p)⟩))).beq b2)
  let aItems := (List.range n).filter (· % 3 == 0) |>.map
    (fun i => (⟨s!"dir{i % 97}/file{i}.txt", hs s!"a'{i}", [hs s!"a{i}"]⟩ : PutItem))
  let a2 := a.putMany A aItems
  let m := a2.merge b2
  let m' := b2.merge a2
  check c "scale: merge commutes" (m.beq m')
  check c "scale: idempotent" ((m.merge m).beq m)
  check c "scale: assoc" (((a2.merge b2).merge b0).beq (a2.merge (b2.merge b0)))
  let snap := m.snapshot
  let ps := m.paths
  check c "scale: snapshot length" (snap.length == ps.length)
  -- a path disappears iff B deleted it and A did not edit it concurrently (edit wins)
  let expectedPaths := n - ((List.range n).filter (fun i => i % 7 == 0 && i % 3 != 0)).length
  check c "scale: surviving paths" (ps.length == expectedPaths)
    (fun _ => s!"{ps.length} vs {expectedPaths}")
  let conflicts := snap.foldl (fun k (_, vs) => if vs.length ≥ 2 then k + 1 else k) 0
  -- both edited concurrently (i ≡ 0 mod 6) and B did not then delete its version (i ≢ 0 mod 7)
  let expected := (List.range n).filter (fun i => i % 6 == 0 && i % 7 != 0) |>.length
  check c "scale: expected conflicts" (conflicts == expected) (fun _ => s!"{conflicts} vs {expected}")
  -- a few single operations on the large state
  let p0 := "dir0/file0.txt"
  let m2 := m.resolve A p0 (hs "r")
  check c "scale: resolve" (m2.versions p0 == [hs "r"] && !m2.isConflicted p0)
  let m3 := m2.put B "zzz/new" (hs "n") [] |>.delete "dir1/file1.txt" [hs "a1"]
  -- expected path count from the paths actually present in `m2` (correct for any `n`):
  -- "zzz/new" is added if absent; "dir1/file1.txt" disappears iff its only version is "a1"
  let added := if m2.versions "zzz/new" == [] then 1 else 0
  let removed := if m2.versions "dir1/file1.txt" == [hs "a1"] then 1 else 0
  let expectedM3 := m2.paths.length + added - removed
  check c "scale: single ops" (m3.paths.length == expectedM3 && m3.versions "zzz/new" == [hs "n"]
    && (m3.versions "dir1/file1.txt").all (· != hs "a1"))
    (fun _ => s!"{m3.paths.length} vs {expectedM3}")
  -- single puts on a state built one put at a time (small, quadratic)
  let small := (List.range 300).foldl (fun s i => s.put A s!"p{i}" (hs s!"{i}") []) State.empty
  check c "single puts" (small.paths.length == 300 && small.beq (State.empty.putMany A
    ((List.range 300).map (fun i => ⟨s!"p{i}", hs s!"{i}", []⟩))))
  check c "scale: mergeAll" ((mergeAll [a2, b2, b0, a]).beq (mergeAll [b0, a, b2, a2]))
  let t1 ← IO.monoMsNow
  IO.println s!"scale: n={n}, paths={ps.length}, conflicts={conflicts}, {t1 - t0} ms"

/-- Rough timing of `merge` and `snapshot` at size `n`, with a data dependency on each
iteration so that nothing can be shared between iterations. -/
def benchTest (n : Nat) : IO Unit := do
  let A := rid 1
  let B := rid 2
  let a := State.empty.putMany A (scalePaths n "a")
  let b := (State.empty.merge a).putMany B ((List.range n).filter (· % 2 == 0) |>.map
    (fun i => (⟨s!"dir{i % 97}/file{i}.txt", hs s!"b{i}", [hs s!"a{i}"]⟩ : PutItem)))
  let iters := 50
  let t0 ← IO.monoNanosNow
  let mut acc := 0
  for i in [0:iters] do
    let bi := b.put B "zzz" (hs s!"{i}") []
    let m := a.merge bi
    acc := acc + m.entries.length
  let t1 ← IO.monoNanosNow
  let mut acc2 := 0
  for i in [0:iters] do
    let bi := b.put B "zzz" (hs s!"{i}") []
    acc2 := acc2 + bi.snapshot.length
  let t2 ← IO.monoNanosNow
  let items := scalePaths n "c"
  let mut acc3 := 0
  for i in [0:iters] do
    acc3 := acc3 + (a.putMany (rid (10 + i)) items).entries.length
  let t3 ← IO.monoNanosNow
  IO.println s!"bench n={n}: put+merge {(t1 - t0) / 1000 / iters} us/iter, put+snapshot {(t2 - t1) / 1000 / iters} us/iter, putMany of {n} items onto {n} paths {(t3 - t2) / 1000 / iters} us/iter ({acc}, {acc2}, {acc3})"

/-- Before/after timing of deleting every 7th of `n` paths: single `delete`s versus
`deletePaths`/`deleteMany`. One run of each, on states that differ per run so nothing is shared. -/
def delBench (n : Nat) (withSingle : Bool) : IO Unit := do
  let A := rid 1
  let a := State.empty.putMany A (scalePaths n "a")
  let ps := (List.range n).filter (· % 7 == 0) |>.map (fun i => s!"dir{i % 97}/file{i}.txt")
  let mut out := ""
  if withSingle then
    let t0 ← IO.monoNanosNow
    let mut acc := 0
    for i in [0:1] do
      let ai := a.put A "zzz" (hs s!"{i}") []
      acc := acc + (ps.foldl (fun s p => s.delete p (s.versions p)) ai).entries.length
    let t1 ← IO.monoNanosNow
    out := out ++ s!"{ps.length} single deletes {(t1 - t0) / 1000000} ms ({acc}); "
  let t2 ← IO.monoNanosNow
  let mut acc2 := 0
  for i in [0:1] do
    let ai := a.put A "zzz" (hs s!"{i}") []
    acc2 := acc2 + (ai.deletePaths ps).entries.length
  let t3 ← IO.monoNanosNow
  let items : List DeleteItem := ps.map (fun p => ⟨p, some [hs "x", hs "y"]⟩)
  let mut acc3 := 0
  for i in [0:1] do
    let ai := a.put A "zzz" (hs s!"{i}") []
    acc3 := acc3 + (ai.deleteMany items).entries.length
  let t4 ← IO.monoNanosNow
  IO.println s!"delbench n={n}: {out}deletePaths {(t3 - t2) / 1000} us ({acc2}); deleteMany with explicit hashes {(t4 - t3) / 1000} us ({acc3})"

/-- Deliberately non-tail-recursive: the structural specification of the merge. -/
def controlTest (n : Nat) : IO Unit := do
  let xs := (List.range n).map (fun i => s!"x{i + 1000000}")
  let ys := (List.range n).map (fun i => s!"y{i + 1000000}")
  let r := mergeSpec (fun _ => true) (fun _ => true) xs ys
  IO.println s!"control: non-tail mergeSpec on 2 × {n} elements returned {r.length} (did not overflow)"

/-- A trivial non-tail recursion, the native analogue of the spike's `!deep N` probe (which found
about 13,000 frames available in Node). Used to calibrate the stack limit of the stack test. -/
def deep : Nat → Nat
  | 0 => 0
  | n + 1 => deep n + 1

end Tests

open Tests in
def main (args : List String) : IO UInt32 := do
  let failures ← IO.mkRef 0
  let checks ← IO.mkRef 0
  let c : Ctx := ⟨failures, checks, "unit"⟩
  match args with
  | ["unit"] => unitTests c
  | "sim" :: rest =>
    let seed := (rest[0]? >>= String.toNat?).getD 1
    let count := (rest[1]? >>= String.toNat?).getD 40
    simTests c seed count
  | "scale" :: rest => scaleTests { c with label := "scale" } ((rest[0]? >>= String.toNat?).getD 20000)
  | "bench" :: rest => benchTest ((rest[0]? >>= String.toNat?).getD 20000)
  | "delbench" :: rest =>
    delBench ((rest[0]? >>= String.toNat?).getD 20000) (rest[1]? != some "fast")
  | "deep" :: rest =>
    let n := (rest[0]? >>= String.toNat?).getD 13000
    IO.println s!"deep: non-tail recursion of depth {n} returned {deep n}"
  | "control" :: rest => controlTest ((rest[0]? >>= String.toNat?).getD 20000)
  | [] | ["all"] =>
    unitTests c
    simTests c 1 40
    scaleTests { c with label := "scale" } 20000
  | _ => IO.eprintln "usage: crdt-tests [unit | sim [seed] [count] | scale [n] | control [n] | deep [n] | bench [n] | delbench [n] [fast] | all]"; return 2
  let n ← failures.get
  IO.println s!"{← checks.get} checks run"
  if n == 0 then IO.println "all tests passed"; return 0
  else IO.eprintln s!"{n} check(s) failed"; return 1
