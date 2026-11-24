import LeanSync
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Native tests for the sync protocol and wire format

Usage: `sync-tests [unit | codec | sim [seed] [count] | sim-lenient [seed] [count] | mutation |
scale [n] | control [n] | deep [n] | debug seed | trace seed count file | vectors file | all]`.

* `unit`      hand-written flows: handshake, state exchange, persist-before-send, stale events,
              protocol errors, blob re-planning, the `noBlob` → `have` chain, rollback mode,
              start-up errors, pending summary, queries;
* `codec`     round trips (states, messages, events, effects) and a fuzz of the decoders:
              every prefix truncation of several encodings, random mutations, random bytes;
* `sim`       a seeded multi-device simulator with a model host and network, fault injection,
              per-step checks (save-before-send, a global dot registry, executability of every
              effect, node invariants) and a convergence check after a quiescence phase;
* `mutation`  the simulator run on deliberately broken step functions, each of which must be caught;
* `scale`     one device with n paths, full initial sync of two fresh devices (index and blobs).

Test code may use `partial def` and `Std`; recursion over data is tail-recursive (loops).
-/

open LeanSync LeanCrdt

namespace SyncTests

/-! ## Basics -/

instance : Hashable Hash := ⟨fun h => hash h.bytes⟩

structure Ctx where
  failures : IO.Ref Nat
  checks : IO.Ref Nat
  label : String

def check (c : Ctx) (name : String) (cond : Bool) (detail : Unit → String := fun _ => "") : IO Unit := do
  c.checks.modify (· + 1)
  unless cond do
    c.failures.modify (· + 1)
    IO.eprintln s!"FAIL [{c.label}] {name} {detail ()}"

/-- A 32-byte hash determined by `n`. -/
def h32 (n : Nat) : Hash :=
  ⟨((List.range 32).map (fun i => if i < 24 then (0xAB : UInt8) else ((n >>> (8 * (31 - i))) % 256).toUInt8)).toByteArray⟩

def mkDigest (b : ByteArray) : Digest :=
  if h : b.size = 32 then ⟨b, h⟩ else ⟨⟨Array.replicate 32 0⟩, by rw [← ByteArray.size_data]; simp⟩

/-- FNV-1a, 64 bits, from a given offset. -/
def fnv (seed : UInt64) (b : ByteArray) : UInt64 :=
  b.foldl (fun h x => (h ^^^ x.toUInt64) * 0x100000001b3) seed

def u64be (x : UInt64) : List UInt8 := (List.range 8).map (fun i => (x >>> (8 * (7 - i).toUInt64)).toUInt8)

/-- The model host's digest: 32 bytes from four FNV passes (not cryptographic; only equality of
inputs ⇔ equality of digests matters, up to negligible collisions). -/
def digestOf (b : ByteArray) : Digest :=
  mkDigest ((u64be (fnv 0xcbf29ce484222325 b) ++ u64be (fnv 0x84222325cbf29ce4 b) ++
    u64be (fnv 0x1234567890abcdef b) ++ u64be (fnv 0xfedcba0987654321 b)).toByteArray)

def baEq (a b : ByteArray) : Bool := a.data == b.data

def showMsg : Message → String
  | .hello .. => "hello" | .digest _ => "digest" | .state _ s => s!"state({s.entries.length})"
  | .want hs => s!"want{hs.length}" | .noBlob hs => s!"noBlob{hs.length}" | .have hs => s!"have{hs.length}"
  | .bye r => s!"bye({repr r})"

def showEff : Effect → String
  | .send p m => s!"send {p.val} {showMsg m}"
  | .close p r => s!"close {p.val} {repr r}"
  | .persist t _ => s!"persist {t}"
  | .fetch p hs => s!"fetch {p.val} {hs.length}"
  | .serveBlob p _ => s!"serve {p.val}"
  | .notify _ => "notify"
  | .reply _ => "reply"

def isStateSend : Effect → Bool
  | .send _ (.state _ _) => true
  | _ => false

def strictlySortedB {α} [Ord α] : List α → Bool
  | a :: b :: rest => compare a b == .lt && strictlySortedB (b :: rest)
  | _ => true

/-! ## Random numbers (splitmix64) -/

structure Rng where
  s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-! ## The simulated world: devices with a model host, and a network -/

inductive Item where
  | msg (b : ByteArray)
  | blob (h : Hash)
  | bad (h : Hash)      -- the sender's host could not read the blob: stream aborted

instance : Inhabited Item := ⟨.blob default⟩
instance : Inhabited Event := ⟨.query .status⟩

structure Conn where
  id : Nat
  a : Nat
  b : Nat
  qab : Array Item := #[]   -- from a to b
  qba : Array Item := #[]
  helloA : Bool := false    -- a has sent its hello on this connection
  helloB : Bool := false
  expA : List Hash := []    -- streams a accepts (it fetched them on this connection)
  expB : List Hash := []

instance : Inhabited Node := ⟨{ self := ⟨0, 0⟩, current := State.empty }⟩
instance : Inhabited Conn := ⟨{ id := 0, a := 0, b := 0 }⟩

structure Dev where
  replica : ReplicaId
  m : Machine := .uninit
  view : HostView := {}
  record : Option ByteArray := none
  store : Std.HashSet Hash := {}
  pending : Option (Nat × ByteArray) := none
  acked : Array ByteArray := #[]
  inc : Nat := 0

instance : Inhabited Dev := ⟨{ replica := ⟨0, 0⟩ }⟩

structure Stats where
  events : Nat := 0
  stateSends : Nat := 0
  fetches : Nat := 0
  blobsDelivered : Nat := 0
  localOps : Nat := 0
  connects : Nat := 0
  drops : Nat := 0
  crashes : Nat := 0
  persistFails : Nat := 0
  blobFails : Nat := 0
  blobLosses : Nat := 0
  garbage : Nat := 0
  truncs : Nat := 0
  dups : Nat := 0
  viaProcess : Nat := 0
  closes : Nat := 0
  stepNanos : Nat := 0

structure World where
  devs : Array Dev
  conns : Array Conn := #[]
  nextConn : Nat := 1
  nextReplica : Nat := 100
  rng : Rng
  stepFn : Machine → Event → Machine × List Effect := step
  useProcess : Bool := true
  checkView : Bool := true
  checkInv : Bool := true
  violations : Array String := #[]
  registry : Std.HashMap (UInt64 × UInt64 × Nat) (String × Hash) := {}
  log : Array (Nat × Effect) := #[]
  keepLog : Bool := false
  work : Array (Nat × Event) := #[]
  stats : Stats := {}
  /-- `trace` subcommand: record every event each device processed, with the native output of
  `process` on its encoding, for replay through the wasm build (`test/wasm-replay.mjs`). -/
  keepTrace : Bool := false
  trace : ByteArray := .empty

abbrev WM := StateT World IO

def rand (n : Nat) : WM Nat := do
  if n == 0 then return 0
  let w ← get
  let (x, g) := w.rng.next
  set { w with rng := g }
  return x.toNat % n

def violate (msg : String) : WM Unit :=
  modify fun w => { w with violations := w.violations.push msg }

def getDev (i : Nat) : WM Dev := return (← get).devs[i]!
def setDev (i : Nat) (d : Dev) : WM Unit := modify fun w => { w with devs := w.devs.set! i d }
def modStats (f : Stats → Stats) : WM Unit := modify fun w => { w with stats := f w.stats }

def connIdx (id : Nat) : WM (Option Nat) := return (← get).conns.findIdx? (·.id == id)

def dropConnRaw (id : Nat) : WM (Option Conn) := do
  match ← connIdx id with
  | none => return none
  | some i =>
    let w ← get
    let c := w.conns[i]!
    set { w with conns := w.conns.eraseIdx! i }
    return some c

def enqueue (d : Nat) (ev : Event) : WM Unit := modify fun w => { w with work := w.work.push (d, ev) }

/-- Drop a connection: both ends are told (if they are running). -/
def dropConn (id : Nat) : WM Unit := do
  if let some c ← dropConnRaw id then
    enqueue c.a (.disconnected ⟨id.toUInt32⟩)
    enqueue c.b (.disconnected ⟨id.toUInt32⟩)

/-- Protocol order: the first Lean message a device sends on a connection is its `hello` (or a
`bye`). Checked on every message put on the wire. -/
def checkOrder (id d : Nat) (m : Message) : WM Unit := do
  if let some i ← connIdx id then
    let w ← get
    let c := w.conns[i]!
    let sent := if c.a == d then c.helloA else c.helloB
    match m with
    | .hello .. =>
      let c := if c.a == d then { c with helloA := true } else { c with helloB := true }
      set { w with conns := w.conns.set! i c }
    | .bye _ => pure ()
    | _ => unless sent do violate s!"device {d} sent {showMsg m} on connection {id} before its own hello"

/-- Push an item on connection `id` from device `d`. -/
def pushItem (id d : Nat) (it : Item) : WM Bool := do
  match ← connIdx id with
  | none => return false
  | some i =>
    let w ← get
    let c := w.conns[i]!
    let c := if c.a == d then { c with qab := c.qab.push it } else { c with qba := c.qba.push it }
    set { w with conns := w.conns.set! i c }
    return true

def addExpect (id d : Nat) (hs : List Hash) : WM Unit := do
  if let some i ← connIdx id then
    let w ← get
    let c := w.conns[i]!
    let c := if c.a == d then { c with expA := hs ++ c.expA } else { c with expB := hs ++ c.expB }
    set { w with conns := w.conns.set! i c }

/-! ### Checks run after each event -/

def checkSentState (d : Nat) (dg : Digest) (s : State) : WM Unit := do
  let dev ← getDev d
  let bytes := encodeState s
  unless dev.acked.any (baEq · bytes) do
    violate s!"save-before-send: device {d} sent a state that its host never acknowledged as persisted"
  unless (digestOf bytes) == dg do
    violate s!"device {d} sent a state with a digest that is not the digest of its bytes"
  for e in s.entries do
    let key := (e.dot.replica.hi, e.dot.replica.lo, e.dot.counter)
    match (← get).registry[key]? with
    | some (p, h) =>
      unless p == e.path && h == e.hash do
        violate s!"dot reuse: dot ({e.dot.replica.lo}, {e.dot.counter}) sent with two contents ({p} / {e.path})"
    | none => modify fun w => { w with registry := w.registry.insert key (e.path, e.hash) }

def checkNode (d : Nat) : WM Unit := do
  let w ← get
  unless w.checkInv do return
  let dev := w.devs[d]!
  match dev.m with
  | .uninit => pure ()
  | .running n =>
    unless strictlySortedB (n.sessions.map (·.peer)) do violate s!"device {d}: sessions not sorted by peer"
    unless strictlySortedB n.blobs do violate s!"device {d}: blobs not strictly sorted"
    unless strictlySortedB n.missing do violate s!"device {d}: missing not strictly sorted"
    unless n.missing == computeMissing n.current n.blobs do
      violate s!"device {d}: missing is not refs(current) minus blobs"
    unless n.inflight.map (·.1) == dev.pending.map (·.1) do
      violate s!"device {d}: Lean's in-flight persist does not match the host's"
    unless n.blobs.all (dev.store.contains ·) do violate s!"device {d}: Lean believes a blob is present that the host lacks"
    unless checkWire n.current do violate s!"device {d}: current state not WireOk"
    if n.rollback then violate s!"device {d}: rollback detected in a run without host-rule violations"

/-! ### Carrying out effects -/

def runEffect (d : Nat) (e : Effect) : WM Unit := do
  let w ← get
  if w.keepLog then set { w with log := w.log.push (d, e) }
  match e with
  | .send p m =>
    if let .state dg s := m then
      modStats fun s => { s with stateSends := s.stateSends + 1 }
      checkSentState d dg s
    -- a connection that is already gone (its disconnect not yet delivered to this device) drops
    -- the message, as a real host would; `HostView` checks the device was told nothing else
    checkOrder p.val.toNat d m
    let _ ← pushItem p.val.toNat d (.msg (encodeMessage m))
  | .close p _ =>
    modStats fun s => { s with closes := s.closes + 1 }
    if let some c ← dropConnRaw p.val.toNat then
      let other := if c.a == d then c.b else c.a
      enqueue other (.disconnected p)
  | .persist t s =>
    let dev ← getDev d
    if dev.pending.isSome then violate s!"device {d}: second persist while one is pending"
    setDev d { dev with pending := some (t, encodeState s) }
  | .fetch p hs =>
    modStats fun s => { s with fetches := s.fetches + 1 }
    addExpect p.val.toNat d hs
    checkOrder p.val.toNat d (.want hs)
    let _ ← pushItem p.val.toNat d (.msg (encodeMessage (.want hs)))
  | .serveBlob p h =>
    let dev ← getDev d
    if let some i ← connIdx p.val.toNat then
      let c := (← get).conns[i]!
      unless (if c.a == d then c.helloA else c.helloB) do
        violate s!"device {d} served a blob on connection {p.val} before its own hello"
    let it := if dev.store.contains h then Item.blob h else Item.bad h
    let _ ← pushItem p.val.toNat d it
  | .notify _ | .reply _ => pure ()

/-- Append one trace record: `kind:u8 device:u32le len:u32le event len:u32le effects`
(kind 0 = event and native output, 1 = the device's machine was reset (crash), 2 = new world). -/
def traceRec (kind : UInt8) (d : Nat) (ev out : ByteArray) : WM Unit := do
  if (← get).keepTrace then
    let u32 (acc : ByteArray) (n : Nat) : ByteArray :=
      ((((acc.push (n % 256).toUInt8).push (n / 256 % 256).toUInt8).push (n / 65536 % 256).toUInt8).push
        (n / 16777216 % 256).toUInt8)
    modify fun w =>
      { w with trace := (u32 (u32 (u32 (w.trace.push kind) d) ev.size ++ ev) out.size) ++ out }

/-- Process one event at device `d`: step (directly or through the byte boundary), check every
effect against the host view, carry the effects out, check the node. -/
def processEvent (d : Nat) (ev : Event) : WM Unit := do
  modStats fun s => { s with events := s.events + 1 }
  let dev ← getDev d
  let w ← get
  if w.keepTrace then
    let input := encodeEvent ev
    traceRec 0 d input (process dev.m input).2
  let viaBytes ← if w.useProcess then (do return (← rand 4) == 0) else pure false
  let (m', effs) ← if viaBytes then do
      modStats fun s => { s with viaProcess := s.viaProcess + 1 }
      let input := encodeEvent ev
      match decodeEvent input with
      | .error e => violate s!"event envelope does not decode: {repr e}"; pure (w.stepFn dev.m ev)
      | .ok _ =>
        let (m', out) := process dev.m input
        match decodeEffects out with
        | .ok effs =>
          unless baEq (encodeEffects effs) out do violate "effect envelope does not re-encode identically"
          pure (m', effs)
        | .error e => violate s!"effect envelope does not decode: {repr e}"; pure (w.stepFn dev.m ev)
    else do
      let t0 ← IO.monoNanosNow
      let r := w.stepFn dev.m ev
      let t1 ← IO.monoNanosNow
      modStats fun s => { s with stepNanos := s.stepNanos + (t1 - t0) }
      pure r
  -- host view: apply the event, then every effect in order
  let mut view := dev.view.onEvent ev
  if w.checkView then
    for e in effs do
      match view.exec e with
      | some v => view := v
      | none => violate s!"device {d}: effect not executable: {showEff e} (after event)"
  setDev d { dev with m := m', view := view }
  for e in effs do runEffect d e
  checkNode d

/-- Run the work queue to exhaustion (a loop, not recursion). -/
partial def drainWork : WM Unit := do
  let w ← get
  if w.work.isEmpty then return
  let (d, ev) := w.work[0]!
  set { w with work := w.work.eraseIdx! 0 }
  processEvent d ev
  drainWork

def feed (d : Nat) (ev : Event) : WM Unit := do
  enqueue d ev
  drainWork

/-! ### Host actions -/

def isRunning (d : Nat) : WM Bool := do
  match (← getDev d).m with
  | .running _ => return true
  | .uninit => return false

def nodeOf (d : Nat) : WM (Option Node) := do
  match (← getDev d).m with
  | .running n => return some n
  | .uninit => return none

def connected (i j : Nat) : WM Bool :=
  return (← get).conns.any (fun c => (c.a == i && c.b == j) || (c.a == j && c.b == i))

def connect (i j : Nat) : WM Nat := do
  let w ← get
  let id := w.nextConn
  set { w with nextConn := id + 1, conns := w.conns.push { id, a := i, b := j } }
  modStats fun s => { s with connects := s.connects + 1 }
  enqueue i (.connected ⟨id.toUInt32⟩)
  enqueue j (.connected ⟨id.toUInt32⟩)
  drainWork
  return id

def ackPersist (d : Nat) : WM Unit := do
  let dev ← getDev d
  if let some (t, bytes) := dev.pending then
    setDev d { dev with record := some bytes, acked := dev.acked.push bytes, pending := none }
    feed d (.persisted t (digestOf bytes))

def failPersist (d : Nat) : WM Unit := do
  let dev ← getDev d
  if let some (t, _) := dev.pending then
    modStats fun s => { s with persistFails := s.persistFails + 1 }
    setDev d { dev with pending := none }
    feed d (.persistFailed t)

/-- Deliver the head of one direction of a connection. `failBlob` turns a blob into a failure. -/
def deliver (id : Nat) (fromA : Bool) (failBlob : Bool := false) : WM Unit := do
  match ← connIdx id with
  | none => pure ()
  | some i =>
    let w ← get
    let c := w.conns[i]!
    let q := if fromA then c.qab else c.qba
    if q.isEmpty then return
    let it := q[0]!
    let c := if fromA then { c with qab := q.eraseIdx! 0 } else { c with qba := q.eraseIdx! 0 }
    let dst := if fromA then c.b else c.a
    let p : PeerId := ⟨id.toUInt32⟩
    match it with
    | .msg b =>
      set { w with conns := w.conns.set! i c }
      feed dst (.received p b)
    | .bad h =>
      set { w with conns := w.conns.set! i c }
      feed dst (.blobFailed p h)
    | .blob h =>
      let exp := if fromA then c.expB else c.expA
      if exp.contains h then
        let c := if fromA then { c with expB := exp.erase h } else { c with expA := exp.erase h }
        set { w with conns := w.conns.set! i c }
        if failBlob then
          modStats fun s => { s with blobFails := s.blobFails + 1 }
          feed dst (.blobFailed p h)
        else
          let dev ← getDev dst
          setDev dst { dev with store := dev.store.insert h }
          modStats fun s => { s with blobsDelivered := s.blobsDelivered + 1 }
          feed dst (.blobStored h (some p))
      else
        set { w with conns := w.conns.set! i c }   -- unsolicited stream: the host ignores it

def freshReplica : WM ReplicaId := do
  let w ← get
  set { w with nextReplica := w.nextReplica + 1 }
  return ⟨0x5151, w.nextReplica.toUInt64⟩

/-- Start (or restart) a device from its persisted record. -/
def boot (d : Nat) : WM Unit := do
  let dev ← getDev d
  let all := dev.store.toList
  -- half the time, report the blob inventory in chunks after `init` (before any connection)
  let chunked := (← rand 2) == 0
  let first := if chunked then [] else all
  match dev.record with
  | some r => feed d (.init dev.replica r first)
  | none =>
    let r ← freshReplica
    setDev d { dev with replica := r }
    feed d (.initFresh r first)
  if chunked then
    let mut rest := all
    while !rest.isEmpty do
      let k := 1 + (← rand 3)
      feed d (.blobsStored (rest.take k))
      rest := rest.drop k

/-- Crash: the in-flight write may or may not have completed; every connection drops. -/
def crash (d : Nat) : WM Unit := do
  modStats fun s => { s with crashes := s.crashes + 1 }
  let dev ← getDev d
  let completes := (← rand 2) == 0
  let record := match dev.pending with
    | some (_, b) => if completes then some b else dev.record
    | none => dev.record
  setDev d { dev with m := .uninit, view := {}, pending := none, record, inc := dev.inc + 1 }
  traceRec 1 d .empty .empty
  let ids := (← get).conns.filter (fun c => c.a == d || c.b == d) |>.map (·.id)
  for id in ids do
    if let some c ← dropConnRaw id then
      let other := if c.a == d then c.b else c.a
      enqueue other (.disconnected ⟨id.toUInt32⟩)
  drainWork
  boot d

def paths0 : Array String := #["a", "b", "c/d", "c/e", "é", "z"]

def randomOp (d : Nat) : WM Unit := do
  let some n ← nodeOf d | return
  let k ← rand 10
  let op : LocalOp ←
    if k < 5 then do
      let cnt := 1 + (← rand 3)
      let mut items := #[]
      for _ in [0:cnt] do
        let p := paths0[← rand paths0.size]!
        let h := h32 (← rand 40)
        let vs := n.current.versions p
        let sup := if (← rand 3) == 0 then [] else vs
        items := items.push ({ path := p, hash := h, supersedes := sup } : PutItem)
      pure (.putMany items.toList)
    else if k < 8 then do
      let p := paths0[← rand paths0.size]!
      pure (.resolve p (h32 (← rand 40)))
    else do
      let p := paths0[← rand paths0.size]!
      let q := paths0[← rand paths0.size]!
      let it2 : DeleteItem := { path := q, supersedes := some (n.current.versions q) }
      pure (.deleteMany [{ path := p, supersedes := none }, it2])
  -- the host stores the blobs first
  let dev ← getDev d
  let hs := match op with
    | .putMany items => items.map (fun (it : PutItem) => it.hash)
    | .resolve _ h => [h]
    | .deleteMany _ => []
  setDev d { dev with store := hs.foldl (fun s h => s.insert h) dev.store }
  modStats fun s => { s with localOps := s.localOps + 1 }
  feed d (.localOp op)

/-- Directions with something queued: (connection id, from a?). -/
def busyDirs : WM (Array (Nat × Bool)) := do
  let w ← get
  let mut out := #[]
  for c in w.conns do
    if !c.qab.isEmpty then out := out.push (c.id, true)
    if !c.qba.isEmpty then out := out.push (c.id, false)
  return out

/-- Inject a fault into one direction of a connection: garbage, a truncated copy of the head
message, or a duplicate of the head message. (Bit-level corruption that still decodes is not
injected: the transport (DTLS/SCTP) has integrity, and the trust model excludes it.) -/
def injectFault : WM Unit := do
  let w ← get
  if w.conns.isEmpty then return
  let c := w.conns[← rand w.conns.size]!
  let fromA := (← rand 2) == 0
  let q := if fromA then c.qab else c.qba
  let k ← rand 3
  let src := if fromA then c.a else c.b
  if k == 0 then
    let len ← rand 40
    let mut b := ByteArray.empty
    for _ in [0:len] do b := b.push (← rand 256).toUInt8
    modStats fun s => { s with garbage := s.garbage + 1 }
    let _ ← pushItem c.id src (.msg b)
  else
    match q[0]? with
    | some (Item.msg b) =>
      if k == 1 && b.size > 1 then
        let len ← rand b.size
        modStats fun s => { s with truncs := s.truncs + 1 }
        let _ ← pushItem c.id src (.msg (b.extract 0 len))
      else
        modStats fun s => { s with dups := s.dups + 1 }
        let _ ← pushItem c.id src (.msg b)
    | _ => pure ()

/-- Lose a blob from a device's storage, only if another device still has it. -/
def loseBlob : WM Unit := do
  let w ← get
  let d ← rand w.devs.size
  let dev := w.devs[d]!
  let hs := dev.store.toList
  if hs.isEmpty then return
  let h := hs[← rand hs.length]!
  let copies : Nat := w.devs.foldl (fun acc x => if x.store.contains h then acc + 1 else acc) 0
  if copies ≥ 2 then
    modStats fun s => { s with blobLosses := s.blobLosses + 1 }
    setDev d { dev with store := dev.store.erase h }
    feed d (.blobLost h)

/-- One random scheduler step. -/
def randomStep : WM Unit := do
  let w ← get
  let nd := w.devs.size
  let r ← rand 100
  if r < 14 then randomOp (← rand nd)
  else if r < 21 then
    let i ← rand nd; let j ← rand nd
    if i != j && !(← connected i j) then let _ ← connect i j
  else if r < 25 then
    if !w.conns.isEmpty then
      modStats fun s => { s with drops := s.drops + 1 }
      dropConn (w.conns[← rand w.conns.size]!).id
      drainWork
  else if r < 70 then
    let dirs ← busyDirs
    if !dirs.isEmpty then
      let (id, fromA) := dirs[← rand dirs.size]!
      deliver id fromA (failBlob := (← rand 40) == 0)
  else if r < 88 then ackPersist (← rand nd)
  else if r < 89 then failPersist (← rand nd)
  else if r < 90 then crash (← rand nd)
  else if r < 92 then injectFault
  else if r < 93 then loseBlob
  else pure ()

/-- Deliver everything and acknowledge every persist until nothing moves. -/
partial def drainAll (fuel : Nat) : WM Bool := do
  if fuel == 0 then return false
  let dirs ← busyDirs
  if let some (id, fromA) := dirs[0]? then
    deliver id fromA
    drainAll (fuel - 1)
  else
    let w ← get
    match w.devs.findIdx? (·.pending.isSome) with
    | some d => ackPersist d; drainAll (fuel - 1)
    | none => return true

def dropAll : WM Unit := do
  for c in (← get).conns do dropConn c.id
  drainWork

/-- The final checks: equal states, all published, all blobs everywhere. -/
def checkConverged : WM Unit := do
  let w ← get
  let mut first : Option State := none
  for d in [0:w.devs.size] do
    let dev := w.devs[d]!
    match dev.m with
    | .uninit => violate s!"device {d} not running at the end"
    | .running n =>
      match first with
      | none => first := some n.current
      | some s => unless s.beq n.current do violate s!"device {d} did not converge to device 0's state"
      match n.published with
      | some P => unless P.state.beq n.current do violate s!"device {d}: published ≠ current at quiescence"
      | none => violate s!"device {d}: nothing published at quiescence"
      if n.inflight.isSome || dev.pending.isSome then violate s!"device {d}: persist in flight at quiescence"
      unless n.missing.isEmpty do violate s!"device {d}: {n.missing.length} blob(s) still missing at quiescence"
      for e in n.current.entries do
        unless dev.store.contains e.hash do violate s!"device {d}: blob of {e.path} absent from the host store"

/-- Quiescence: no more operations or faults; fresh sessions in a connected topology; drain. -/
def quiesce (variant : Nat) (ackFirst : Bool := false) : WM Unit := do
  dropAll
  if ackFirst then
    unless ← drainAll 2000000 do violate "did not quiesce"
  let nd := (← get).devs.size
  let fuel := 2000000
  match variant % 3 with
  | 0 =>   -- full mesh
    for i in [0:nd] do
      for j in [i+1:nd] do let _ ← connect i j
    unless ← drainAll fuel do violate "mesh: did not quiesce"
  | 1 =>   -- chain 0–1–2–…, all at once (transitivity through intermediate devices)
    for i in [0:nd-1] do let _ ← connect i (i + 1)
    unless ← drainAll fuel do violate "chain: did not quiesce"
  | _ =>   -- sequential pairwise sessions, only two devices online at a time
    let pairs := (List.range (nd - 1)).map (fun i => (i, i + 1)) ++
      ((List.range (nd - 1)).reverse.map (fun i => (i + 1, i)))
    for (i, j) in pairs do
      let id ← connect i j
      unless ← drainAll fuel do violate "pairwise: did not quiesce"
      dropConn id
      drainWork
  unless ← drainAll fuel do violate "did not quiesce"
  checkConverged

def newWorld (nd : Nat) (seed : Nat) (stepFn : Machine → Event → Machine × List Effect := step)
    (useProcess := true) : World :=
  { devs := (Array.range nd).map (fun i => ({ replica := ⟨0x5151, i.toUInt64 + 1⟩ } : Dev)),
    rng := ⟨seed.toUInt64 * 0x2545F4914F6CDD1D + 1⟩, stepFn, useProcess }

/-- One simulated run: boot, random phase, quiescence. Returns the violations. -/
def simRun (seed nd steps : Nat) (stepFn : Machine → Event → Machine × List Effect := step)
    (useProcess := true) (ackFirst := false) : IO (Array String × Stats) := do
  let act : WM Unit := do
    for d in [0:nd] do boot d
    for _ in [0:steps] do randomStep
    quiesce seed ackFirst
  let ((), w) ← act.run (newWorld nd seed stepFn useProcess)
  return (w.violations, w.stats)

def simTests (c : Ctx) (seed count : Nat) (nd steps : Nat := 4) (steps' : Nat := 400)
    (ackFirst := false) : IO Unit := do
  let _ := steps
  let mut tot : Stats := {}
  let mut bad := 0
  for s in [seed:seed + count] do
    let (vs, st) ← simRun s nd steps' step true ackFirst
    tot := { events := tot.events + st.events, stateSends := tot.stateSends + st.stateSends,
             fetches := tot.fetches + st.fetches, blobsDelivered := tot.blobsDelivered + st.blobsDelivered,
             localOps := tot.localOps + st.localOps, connects := tot.connects + st.connects,
             drops := tot.drops + st.drops, crashes := tot.crashes + st.crashes,
             persistFails := tot.persistFails + st.persistFails, blobFails := tot.blobFails + st.blobFails,
             blobLosses := tot.blobLosses + st.blobLosses, garbage := tot.garbage + st.garbage,
             truncs := tot.truncs + st.truncs, dups := tot.dups + st.dups,
             viaProcess := tot.viaProcess + st.viaProcess, closes := tot.closes + st.closes }
    check c s!"sim seed {s}" vs.isEmpty (fun _ => s!"(seed {s}) {vs.size} violation(s), first: {vs.toList.take 2}")
    unless vs.isEmpty do bad := bad + 1
  IO.println s!"sim: seeds {seed}..{seed + count - 1}, {nd} devices, {steps'} random steps + quiescence per seed; {bad} failing seed(s)"
  IO.println s!"  totals: events {tot.events} (via byte boundary {tot.viaProcess}), local ops {tot.localOps}, state sends {tot.stateSends}, fetches {tot.fetches}, blobs delivered {tot.blobsDelivered}, connects {tot.connects}"
  IO.println s!"  faults: drops {tot.drops}, crashes {tot.crashes}, persist failures {tot.persistFails}, blob failures {tot.blobFails}, blob losses {tot.blobLosses}, garbage {tot.garbage}, truncated {tot.truncs}, duplicated {tot.dups}, sessions closed by Lean {tot.closes}"

/-! ## Mutation check: broken step functions must be caught -/

/-- (a) state messages carry the current state instead of the published one. -/
def mutCurrent (m : Machine) (ev : Event) : Machine × List Effect :=
  let (m', effs) := step m ev
  match m' with
  | .running n => (m', effs.map fun
      | .send p (.state d _) => .send p (.state d n.current)
      | e => e)
  | .uninit => (m', effs)

/-- (b) `have` is never sent. -/
def mutNoHave (m : Machine) (ev : Event) : Machine × List Effect :=
  let (m', effs) := step m ev
  (m', effs.filter fun
    | .send _ (.have _) => false
    | _ => true)

/-- (c) received states are ignored. -/
def mutIgnoreState (m : Machine) (ev : Event) : Machine × List Effect :=
  match ev with
  | .received _ b =>
    match decodeMessage b with
    | .ok (.state _ _) => (m, [])
    | _ => step m ev
  | _ => step m ev

/-- (d) a message to a peer after it disconnected. -/
def mutSendAfterClose (m : Machine) (ev : Event) : Machine × List Effect :=
  let (m', effs) := step m ev
  match ev with
  | .disconnected p => (m', effs ++ [.send p (.digest (digestOf ByteArray.empty))])
  | _ => (m', effs)

/-! ## Unit tests -/

def runW {α} (w : World) (act : WM α) : IO (α × World) := act.run w

def logOf (w : World) (d : Nat) : List Effect := (w.log.toList.filter (·.1 == d)).map (·.2)

def unitWorld (nd : Nat) : World := { newWorld nd 7 with useProcess := false, keepLog := true }

def clearLog : WM Unit := modify fun w => { w with log := #[] }

def nodeOr (w : World) (d : Nat) : Option Node :=
  match w.devs[d]!.m with
  | .running n => some n
  | .uninit => none

def putOp (d : Nat) (p : String) (h : Hash) : WM Unit := do
  let dev ← getDev d
  setDev d { dev with store := dev.store.insert h }
  let sup := match (← nodeOf d) with
    | some n => n.current.versions p
    | none => []
  feed d (.localOp (.putMany [{ path := p, hash := h, supersedes := sup }]))

/-- Deliver only messages (not blob streams) until none is queued. -/
partial def deliverMsgs (fuel : Nat := 100000) : WM Unit := do
  if fuel == 0 then return
  let w ← get
  let mut found : Option (Nat × Bool) := none
  for c in w.conns do
    if found.isNone then
      if let some (Item.msg _) := c.qab[0]? then found := some (c.id, true)
      else if let some (Item.msg _) := c.qba[0]? then found := some (c.id, false)
  match found with
  | some (id, fromA) => deliver id fromA; deliverMsgs (fuel - 1)
  | none => pure ()

def hasNotice (effs : List Effect) (f : Notice → Bool) : Bool :=
  effs.any fun | .notify n => f n | _ => false

/-- Deliver messages and acknowledge persists until neither moves; blob streams stay queued. -/
partial def syncMsgs (fuel : Nat := 10000) : WM Unit := do
  if fuel == 0 then return
  deliverMsgs
  match (← get).devs.findIdx? (·.pending.isSome) with
  | some d => ackPersist d; syncMsgs (fuel - 1)
  | none => pure ()

/-- Directed chain A–B–C: only A holds the blobs; B learns the index and starts fetching from A,
but A's streams are held back; then C connects to B only, learns the index from B and asks B, which
answers `noBlob`. Then everything is delivered, **without reconnecting**: C can obtain the blobs only
through B's `have`. -/
def chainRun (seed : Nat) (f : Machine → Event → Machine × List Effect) : IO (Array String) := do
  let act : WM Unit := do
    for d in [0:3] do boot d; ackPersist d
    let k := 1 + (← rand 4)
    for i in [0:k] do
      putOp 0 s!"chain/{i}" (h32 (900 + 10 * seed + i)); ackPersist 0
    let _ ← connect 0 1
    syncMsgs
    let _ ← connect 1 2
    syncMsgs
    unless ← drainAll 100000 do violate "chain: did not quiesce"
    checkConverged
  let ((), w) ← act.run (newWorld 3 seed f false)
  return w.violations

/-- One strict simulator run plus the directed chain scenario. -/
def mutRun (s : Nat) (f : Machine → Event → Machine × List Effect) : IO (Array String) := do
  let (vs, _) ← simRun s 4 300 f false
  let vc ← chainRun s f
  return vs ++ vc

def mutationTests (c : Ctx) (budget : Nat := 30) : IO Unit := do
  let muts : List (String × (Machine → Event → Machine × List Effect)) :=
    [("state sends carry current", mutCurrent), ("no have", mutNoHave),
     ("ignore received states", mutIgnoreState), ("send after disconnect", mutSendAfterClose)]
  for (name, f) in muts do
    let mut caught := 0
    let mut firstMsg := ""
    for s in [1:budget + 1] do
      let vs ← mutRun s f
      if !vs.isEmpty then
        caught := caught + 1
        if firstMsg == "" then firstMsg := vs[0]!
    IO.println s!"mutation '{name}': caught on {caught}/{budget} seeds (e.g. {firstMsg})"
    check c s!"mutation '{name}' is caught" (caught > 0)
  -- and the real step function passes the same budget
  let mut clean := 0
  for s in [1:budget + 1] do
    let vs ← mutRun s step
    if vs.isEmpty then clean := clean + 1
  IO.println s!"unmutated step: clean on {clean}/{budget} seeds"
  check c "unmutated step passes the mutation budget" (clean == budget)

def unitTests (c : Ctx) : IO Unit := do
  -- 1. two empty devices: hello only, no state sent
  let (_, w) ← runW (unitWorld 2) do
    boot 0; boot 1; ackPersist 0; ackPersist 1
    clearLog
    let _ ← connect 0 1
    let _ ← drainAll 1000
  check c "equal digests: hellos only" (w.log.all (fun (_, e) => !isStateSend e))
  check c "equal digests: both sent hello" ((logOf w 0).any (fun | .send _ (.hello ..) => true | _ => false) &&
    (logOf w 1).any (fun | .send _ (.hello ..) => true | _ => false))
  check c "no violations (1)" w.violations.isEmpty (fun _ => toString w.violations)
  -- 2. state exchange and blob transfer
  let (_, w) ← runW (unitWorld 2) do
    boot 0; boot 1; ackPersist 0; ackPersist 1
    putOp 0 "x" (h32 1); ackPersist 0
    let _ ← connect 0 1
    let _ ← drainAll 1000
    checkConverged
  check c "state exchange converges with blobs" w.violations.isEmpty (fun _ => toString w.violations)
  check c "state was sent" ((logOf w 0).any isStateSend)
  -- 3. persist before send: an edit mid-session goes out only after its ack
  let (_, w) ← runW (unitWorld 2) do
    boot 0; boot 1; ackPersist 0; ackPersist 1
    let _ ← connect 0 1
    let _ ← drainAll 1000
    clearLog
    putOp 0 "y" (h32 2)
    deliverMsgs
  check c "edit mid-session: nothing sent before the ack"
    ((logOf w 0).all (fun | .send _ _ => false | _ => true)) (fun _ => toString ((logOf w 0).map showEff))
  check c "edit mid-session: a persist was requested" ((logOf w 0).any (fun | .persist .. => true | _ => false))
  let (_, w2) ← runW { w with log := #[] } do
    ackPersist 0
  check c "edit mid-session: state sent right after the ack" ((logOf w2 0).any isStateSend)
    (fun _ => toString ((logOf w2 0).map showEff))
  let sent := (logOf w2 0).filterMap (fun | .send _ (.state _ s) => some s | _ => none)
  check c "edit mid-session: the sent state contains the edit" (sent.any (fun s => s.versions "y" == [h32 2]))
  -- 4. stale, duplicate and out-of-order host events
  let (_, w) ← runW (unitWorld 1) do
    boot 0; ackPersist 0
    putOp 0 "x" (h32 1)
    clearLog
    feed 0 (.persisted 99 (digestOf ByteArray.empty))   -- wrong tag
    feed 0 (.persisted 0 (digestOf ByteArray.empty))    -- stale (already acknowledged)
  let n := (nodeOr w 0).get!
  check c "wrong/stale persisted tag ignored" (n.inflight.isSome && (n.published.map (·.state.entries.length)) == some 0)
  check c "wrong/stale persisted tag: no effects" ((logOf w 0).isEmpty) (fun _ => toString ((logOf w 0).map showEff))
  let (_, w) ← runW w do
    ackPersist 0
    clearLog
    let dev ← getDev 0
    setDev 0 { dev with store := dev.store.insert (h32 77) }
    feed 0 (.blobStored (h32 1) none)     -- duplicate: already present (local put)
    feed 0 (.blobStored (h32 77) none)    -- unsolicited: harmless
    feed 0 (.blobStored (h32 77) none)    -- duplicate of that
  let n := (nodeOr w 0).get!
  check c "duplicate blobStored: no effects" ((logOf w 0).length ≤ 1)
  check c "unsolicited blob recorded, not missing" (n.blobs.contains (h32 77) && n.missing.isEmpty)
  check c "no violations (4)" w.violations.isEmpty (fun _ => toString w.violations)
  -- 5. protocol errors: message before hello, bad version, own replica id
  let (_, w) ← runW (unitWorld 1) do
    boot 0; ackPersist 0
    feed 0 (.connected ⟨50⟩); feed 0 (.connected ⟨51⟩); feed 0 (.connected ⟨52⟩)
    clearLog
    feed 0 (.received ⟨50⟩ (encodeMessage (.digest (digestOf ByteArray.empty))))
    let badv := encodeMessage (.hello 1 ⟨9, 9⟩ (digestOf ByteArray.empty)) |>.set! 0 2
    feed 0 (.received ⟨51⟩ badv)
    let self := (← getDev 0).replica
    feed 0 (.received ⟨52⟩ (encodeMessage (.hello 1 self (digestOf ByteArray.empty))))
  let effs := logOf w 0
  check c "message before hello → bye protocolError + close"
    (effs.any (fun | .send ⟨50⟩ (.bye .protocolError) => true | _ => false) &&
     effs.any (fun | .close ⟨50⟩ .protocolError => true | _ => false))
  check c "bad version → incompatible" (effs.any (fun | .close ⟨51⟩ .incompatible => true | _ => false))
  check c "own replica id → sameReplicaId" (effs.any (fun | .close ⟨52⟩ .sameReplicaId => true | _ => false))
  check c "closed sessions removed" ((nodeOr w 0).get!.sessions.isEmpty)
  -- 6. disconnect mid-fetch re-plans to another peer
  let (_, w) ← runW (unitWorld 3) do
    for d in [0:3] do boot d; ackPersist d
    putOp 0 "x" (h32 5); ackPersist 0
    -- device 1 gets the blob from 0 first
    let id01 ← connect 0 1
    let _ ← drainAll 1000
    dropConn id01; drainWork
    -- device 2 connects to both; its first fetch goes to the lower connection id
    let a ← connect 2 0
    let _ ← connect 2 1
    deliverMsgs
    let n2 := (← nodeOf 2).get!
    let firstPeer := n2.sessions.find? (fun s => !s.inflight.isEmpty)
    clearLog
    match firstPeer with
    | some s => dropConn s.peer.val.toNat; drainWork
    | none => violate "no fetch in flight"
    let _ := a
  let effs := logOf w 2
  check c "disconnect mid-fetch: re-planned to the other peer" (effs.any (fun | .fetch .. => true | _ => false))
    (fun _ => toString (effs.map showEff))
  let (_, w) ← runW w do
    let _ ← drainAll 1000
    checkConverged
  check c "disconnect mid-fetch: converges" w.violations.isEmpty (fun _ => toString w.violations)
  -- 7. transitive chain: A has the blob, B is fetching it, C asks B → noBlob → have → re-fetch
  let (_, w) ← runW (unitWorld 3) do
    for d in [0:3] do boot d; ackPersist d
    putOp 0 "x" (h32 9); ackPersist 0
    let _ ← connect 0 1
    let _ ← connect 1 2
    -- index everywhere, blob streams held back
    for _ in [0:20] do
      deliverMsgs
      for d in [0:3] do ackPersist d
    let n2 := (← nodeOf 2).get!
    unless n2.missing == [h32 9] do violate "C does not miss the blob"
    clearLog
    let _ ← drainAll 10000
    checkConverged
  let effs := logOf w 1
  check c "chain: B sent have to C" (effs.any (fun | .send _ (.have _) => true | _ => false))
    (fun _ => toString (effs.map showEff))
  check c "chain: everyone has the blob" w.violations.isEmpty (fun _ => toString w.violations)
  -- 8. blobFailed marks the peer as lacking the blob, and the request goes elsewhere
  let (_, w) ← runW (unitWorld 3) do
    for d in [0:3] do boot d; ackPersist d
    putOp 0 "x" (h32 3); ackPersist 0
    let id01 ← connect 0 1
    let _ ← drainAll 1000
    dropConn id01; drainWork
    let _ ← connect 2 0
    let _ ← connect 2 1
    deliverMsgs
    let n2 := (← nodeOf 2).get!
    match n2.sessions.find? (fun s => !s.inflight.isEmpty) with
    | some s =>
      clearLog
      feed 2 (.blobFailed s.peer (h32 3))
      let n2 := (← nodeOf 2).get!
      unless (n2.sessions.find? (·.peer == s.peer)).any (fun x => x.lacks.contains (h32 3)) do
        violate "blobFailed did not mark lacks"
    | none => violate "no fetch in flight"
  check c "blobFailed marks lacks" w.violations.isEmpty (fun _ => toString w.violations)
  check c "blobFailed: request re-planned" ((logOf w 2).any (fun | .fetch .. => true | _ => false))
  -- 9. rollback detection and rollback mode
  -- device 0 of a fresh world boots with the first fresh replica id
  let me : ReplicaId := ⟨0x5151, 100⟩
  let foreign := (List.range 5).foldl (fun s i => s.put me s!"r{i}" (h32 (200 + i)) []) State.empty
  let (_, w) ← runW (unitWorld 1) do
    boot 0; ackPersist 0
    unless (← getDev 0).replica == me do violate "unexpected replica id"
    putOp 0 "x" (h32 1); ackPersist 0
    feed 0 (.connected ⟨60⟩)
    feed 0 (.received ⟨60⟩ (encodeMessage (.hello 1 ⟨7, 7⟩ (digestOf ByteArray.empty))))
    clearLog
    feed 0 (.received ⟨60⟩ (encodeMessage (.state (digestOf (encodeState foreign)) foreign)))
  -- the host sends ⟨60⟩ messages nowhere (no connection object): only inspect effects
  let effs := logOf w 0
  check c "rollback: notice emitted" (hasNotice effs (fun | .rollbackDetected => true | _ => false))
  check c "rollback: flag set" ((nodeOr w 0).get!.rollback)
  let (_, w) ← runW { w with log := #[] } do
    feed 0 (.localOp (.putMany [{ path := "q", hash := h32 4, supersedes := [] }]))
    ackPersist 0
    feed 0 (.connected ⟨61⟩)
    feed 0 (.received ⟨61⟩ (encodeMessage (.hello 1 ⟨8, 8⟩ (digestOf ByteArray.empty))))
    feed 0 (.received ⟨61⟩ (encodeMessage (.want [h32 1])))
  let effs := logOf w 0
  check c "rollback: local op rejected" (hasNotice effs (fun | .opRejected _ => true | _ => false))
  check c "rollback: no state sent" (effs.all (fun e => !isStateSend e)) (fun _ => toString (effs.map showEff))
  check c "rollback: hello still sent" (effs.any (fun | .send ⟨61⟩ (.hello ..) => true | _ => false))
  check c "rollback: digest still announced" (effs.any (fun | .send ⟨61⟩ (.hello ..) => true | .send ⟨61⟩ (.digest _) => true | _ => false))
  check c "rollback: blobs still served" (effs.any (fun | .serveBlob ⟨61⟩ _ => true | _ => false))
  -- (r0 carries the colliding dot (me, 1) and is dropped by the merge: that is the damage the host
  -- rule exists to prevent; r4 has a dot we never issued and is kept)
  check c "rollback: incoming state was merged" ((nodeOr w 0).get!.current.versions "r4" == [h32 204])
  -- 10. start-up errors and initialisation order
  let (m1, e1) := step .uninit (.connected ⟨1⟩)
  check c "notInitialized" (hasNotice e1 (fun | .notInitialized => true | _ => false) && (match m1 with | .uninit => true | _ => false))
  let corrupt := (encodeState foreign).set! 5 0xFF
  let (m2, e2) := step .uninit (.init me corrupt [])
  check c "corrupt record → startupFailed, stays uninit"
    (hasNotice e2 (fun | .startupFailed _ => true | _ => false) && (match m2 with | .uninit => true | _ => false))
  let (m3, e3) := step m2 (.initFresh ⟨0x77, 1⟩ [])
  check c "initFresh after startupFailed runs and persists" ((match m3 with | .running _ => true | _ => false) &&
    e3.any (fun | .persist 0 _ => true | _ => false))
  let (_, e4) := step m3 (.initFresh ⟨0x77, 2⟩ [])
  check c "alreadyInitialized" (hasNotice e4 (fun | .alreadyInitialized => true | _ => false))
  let (m5, _) := step .uninit (.init me (encodeState foreign) [h32 200])
  check c "init restores the record" (match m5 with | .running n => n.current.beq foreign | _ => false)
  -- 11. pending summary: waiting vs fetching; queries
  let (_, w) ← runW (unitWorld 2) do
    for d in [0:2] do boot d; ackPersist d
    putOp 0 "x" (h32 11); ackPersist 0
    let id01 ← connect 0 1
    deliverMsgs; ackPersist 1; deliverMsgs
    dropConn id01; drainWork
    clearLog
    ackPersist 1
  -- device 1 knows "x" but nobody reachable has the blob
  let n1 := (nodeOr w 1).get!
  check c "pending: one missing blob" (n1.missing == [h32 11])
  check c "pendingSummary: waiting" (n1.summary == (0, 0, 1)) (fun _ => toString n1.summary)
  let (_, w) ← runW { w with log := #[] } do
    let _ ← connect 1 0
    deliverMsgs
  let n1 := (nodeOr w 1).get!
  check c "pendingSummary: fetching" (n1.summary == (1, 0, 0)) (fun _ => toString n1.summary)
  check c "pendingSummary notice emitted" (hasNotice (logOf w 1) (fun | .pendingSummary 1 0 0 => true | _ => false))
  let (_, w) ← runW { w with log := #[] } do
    feed 1 (.query .snapshot); feed 1 (.query .pending); feed 1 (.query .status)
  let replies := (logOf w 1).filterMap (fun | .reply r => some r | _ => none)
  check c "three replies" (replies.length == 3)
  check c "snapshot reply marks x absent" (replies.any fun
    | .snapshot files => files.any (fun (p, vs) => p == "x" && vs.all (fun v => !v.present))
    | _ => false)
  check c "pending reply names the requested peer" (replies.any fun
    | .pending items => items.any (fun (h, st) => h == h32 11 && (match st with | .requested _ => true | _ => false))
    | _ => false)
  check c "status reply lists the session" (replies.any fun
    | .status _ _ _ peers => peers.length == 1
    | _ => false)
  let (_, w) ← runW w do
    let _ ← drainAll 1000
    checkConverged
  check c "pending case converges" w.violations.isEmpty (fun _ => toString w.violations)
  -- 11b. queued: 33 missing blobs and one peer with 32 request slots
  let (_, w) ← runW (unitWorld 2) do
    for d in [0:2] do boot d; ackPersist d
    let items := (List.range 33).map (fun i => ({ path := s!"q/{i}", hash := h32 (500 + i), supersedes := [] } : PutItem))
    let dev ← getDev 0
    setDev 0 { dev with store := items.foldl (fun st it => st.insert it.hash) dev.store }
    feed 0 (.localOp (.putMany items)); ackPersist 0
    let _ ← connect 0 1
    syncMsgs
    clearLog
    feed 1 (.query .pending)
  let n1 := (nodeOr w 1).get!
  check c "queued: summary is 32 fetching, 1 queued, 0 waiting" (n1.summary == (32, 1, 0))
    (fun _ => toString n1.summary)
  let pend := (logOf w 1).filterMap (fun | .reply (.pending items) => some items | _ => none)
  let items := pend.headD []
  let nReq := (items.filter (fun x => match x.2 with | .requested _ => true | _ => false)).length
  let nQ := (items.filter (fun x => match x.2 with | .queued => true | _ => false)).length
  let nW := (items.filter (fun x => match x.2 with | .waiting => true | _ => false)).length
  check c "queued: pending reply has 32 requested, 1 queued, 0 waiting" (nReq == 32 && nQ == 1 && nW == 0)
    (fun _ => s!"{nReq} {nQ} {nW}")
  let (_, w) ← runW w do
    let _ ← drainAll 100000
    checkConverged
  check c "queued case converges" w.violations.isEmpty (fun _ => toString w.violations)
  -- 11c. start-up inventory reported late: a peer connecting before it is complete
  let (_, w) ← runW (unitWorld 2) do
    for d in [0:2] do boot d; ackPersist d
    putOp 0 "inv" (h32 600); ackPersist 0
    -- restart device 0, reporting no blobs at `init` (the inventory comes later)
    let dev ← getDev 0
    setDev 0 { dev with m := .uninit, view := {} }
    feed 0 (.init dev.replica dev.record.get! [])
    ackPersist 0
    let _ ← connect 0 1
    syncMsgs
  let n1 := (nodeOr w 1).get!
  check c "late inventory: the peer was told noBlob, so the blob is waiting" (n1.summary == (0, 0, 1))
    (fun _ => toString n1.summary)
  let (_, w) ← runW { w with log := #[] } do
    feed 0 (.blobsStored [h32 600])
    let _ ← drainAll 100000
    checkConverged
  check c "late inventory: blobsStored sends `have` to the peer" (logOf w 0 |>.any fun
    | .send _ (.have [h]) => h == h32 600 | _ => false)
  check c "late inventory: converges once the inventory arrives" w.violations.isEmpty
    (fun _ => toString w.violations)
  -- 11d. a failed persist: notice, no retry in the same step, retry with the latest state later
  let (_, w) ← runW (unitWorld 1) do
    boot 0; ackPersist 0
    putOp 0 "f" (h32 700)
    clearLog
    failPersist 0                       -- the host reports the write failed
  let effs := logOf w 0
  check c "persistFailed: saveFailed notice" (hasNotice effs (fun | .saveFailed => true | _ => false))
  check c "persistFailed: no persist in the same step" (!effs.any (fun | .persist _ _ => true | _ => false))
  let (_, w) ← runW { w with log := #[] } do
    for t in [0:5] do feed 0 (.persistFailed (100 + t))   -- stale or duplicated failures
    putOp 0 "g" (h32 701)              -- the next real event
  let effs := logOf w 0
  let persists := effs.filterMap (fun | .persist _ s => some s | _ => none)
  check c "stale failures alone trigger no write" (persists.length == 1)
    (fun _ => s!"{persists.length} persists")
  check c "the next event retries with the latest state" (match persists, nodeOr w 0 with
    | [s], some n => s.beq n.current && (n.current.versions "f").length == 1 && (n.current.versions "g").length == 1
    | _, _ => false)
  -- 11e. a host whose storage always fails: failure events alone end the exchange
  let (_, w) ← runW (unitWorld 1) do
    boot 0; ackPersist 0
    clearLog
    putOp 0 "h" (h32 702)
  let mut m := (w.devs[0]!).m
  let mut pending : List Nat := ((logOf w 0).filterMap (fun | .persist t _ => some t | _ => none))
  let mut rounds := 0
  while !pending.isEmpty && rounds < 100 do
    let t := pending.head!
    let (m', effs) := step m (.persistFailed t)
    m := m'
    pending := pending.tail ++ effs.filterMap (fun | .persist t _ => some t | _ => none)
    rounds := rounds + 1
  check c "always-failing host: the failure loop ends after one round" (pending.isEmpty && rounds == 1)
    (fun _ => s!"{rounds} rounds")
  -- 11f. operations that change nothing schedule no write and no notice
  let (_, w) ← runW (unitWorld 1) do
    boot 0; ackPersist 0
    putOp 0 "k" (h32 703); ackPersist 0
    clearLog
    feed 0 (.localOp (.putMany []))
    feed 0 (.localOp (.deleteMany [{ path := "absent", supersedes := none }]))
  let effs := logOf w 0
  check c "no-op operations: no persist" (!effs.any (fun | .persist _ _ => true | _ => false))
  check c "no-op operations: no indexChanged" (!hasNotice effs (fun | .indexChanged => true | _ => false))
  check c "no-op operations: not dirty" (match nodeOr w 0 with | some n => !n.dirty | none => false)
  -- 12. too many peers
  let (_, w) ← runW (unitWorld 1) do
    boot 0; ackPersist 0
    clearLog
    for i in [0:maxSessions + 1] do feed 0 (.connected ⟨(300 + i).toUInt32⟩)
  check c "session cap: extra connection closed"
    ((logOf w 0).any (fun | .close _ .tooManyPeers => true | _ => false) &&
      (nodeOr w 0).get!.sessions.length == maxSessions)

/-! ## Codec tests and fuzz -/

abbrev RM := StateT Rng IO

def rr (n : Nat) : RM Nat := do
  if n == 0 then return 0
  let g ← get
  let (x, g) := g.next
  set g
  return x.toNat % n

def randomState (size : Nat) : RM State := do
  let reps : Array ReplicaId := #[⟨1, 1⟩, ⟨2, 0xFFFFFFFFFFFFFFFF⟩, ⟨0xFFFFFFFFFFFFFFF0, 3⟩]
  let mut st : Array State := #[State.empty, State.empty, State.empty]
  for _ in [0:size] do
    let i ← rr 3
    let p := s!"dir{← rr 4}/f{← rr 12}" ++ (if (← rr 5) == 0 then "é" else "")
    let s := st[i]!
    let k ← rr 6
    let hv ← rr 1000
    let sup ← rr 2
    let other ← rr 3
    let s' :=
      if k < 3 then s.put reps[i]! p (h32 hv) (if sup == 0 then [] else s.versions p)
      else if k < 4 then s.delete p (s.versions p)
      else s.merge st[other]!
    st := st.set! i s'
  return st[0]!.merge (st[1]!.merge st[2]!)

def randomHashes (k : Nat) : RM (List Hash) := do
  let mut l := []
  for _ in [0:k] do l := h32 (← rr 100000) :: l
  return sortDedup l

def randomDigest : RM Digest := do return digestOf (ByteArray.mk #[(← rr 256).toUInt8, (← rr 256).toUInt8])

def randomMessage (st : State) : RM Message := do
  match ← rr 7 with
  | 0 => return .hello (← rr 256).toUInt8 ⟨(← rr 1000).toUInt64, 0xFFFFFFFFFFFFFFFF⟩ (← randomDigest)
  | 1 => return .digest (← randomDigest)
  | 2 => return .state (← randomDigest) st
  | 3 => return .want (← randomHashes (1 + (← rr 40)))
  | 4 => return .noBlob (← randomHashes (1 + (← rr 40)))
  | 5 => return .have (← randomHashes (1 + (← rr 40)))
  | _ => return .bye #[CloseReason.protocolError, .incompatible, .sameReplicaId, .tooManyPeers, .stateTooLarge][← rr 5]!

def randomEvent (st : State) : RM Event := do
  let p : PeerId := ⟨(← rr 70000).toUInt32⟩
  match ← rr 14 with
  | 0 => return .init ⟨1, (← rr 99).toUInt64⟩ (encodeState st) (← randomHashes (← rr 5))
  | 1 => return .initFresh ⟨2, 3⟩ (← randomHashes (← rr 5))
  | 2 => return .connected p
  | 3 => return .disconnected p
  | 4 => return .received p (encodeMessage (← randomMessage st))
  | 5 => return .localOp (.putMany [{ path := "a/b", hash := h32 1, supersedes := [h32 2, h32 3] },
                                   { path := "é", hash := h32 4, supersedes := [] }])
  | 6 => return .localOp (.deleteMany [{ path := "x", supersedes := none }, { path := "y", supersedes := some [h32 5] }])
  | 7 => return .localOp (.resolve "z" (h32 (← rr 50)))
  | 8 => return .persisted (← rr 1000000) (← randomDigest)
  | 9 => return .persistFailed (← rr 5)
  | 10 => return .blobStored (h32 (← rr 9)) (if (← rr 2) == 0 then none else some p)
  | 11 => return .blobFailed p (h32 7)
  | 12 => return .blobLost (h32 8)
  | _ => return .query #[Query.snapshot, .pending, .status][← rr 3]!

def randomEffects (st : State) : RM (List Effect) := do
  let p : PeerId := ⟨(← rr 70000).toUInt32⟩
  let mut out := []
  for _ in [0:1 + (← rr 6)] do
    let k ← rr 8
    let m ← randomMessage st
    let hs ← randomHashes (1 + (← rr 30))
    let t ← rr 100
    let hi ← rr 10
    let ni ← rr 14
    let ri ← rr 3
    let notices : Array Notice := #[Notice.indexChanged, .blobsChanged, .peerStatus p .inSync (some ⟨1, 2⟩),
      .peerClosed p .incompatible true, .peerLeft p, .peerError p (.badVersion 7), .rollbackDetected,
      .opRejected "nope é", .badEvent .trailing, .startupFailed .nonCanonical, .notInitialized,
      .alreadyInitialized, .pendingSummary 3 5 4, .saveFailed]
    let replies : Array Reply := #[Reply.snapshot [("a", [⟨h32 1, true⟩, ⟨h32 2, false⟩]), ("b", [])],
      .pending [(h32 3, .waiting), (h32 4, .requested p), (h32 5, .queued)], .status true false true [(p, .syncing)]]
    let e : Effect :=
      if k == 0 then .send p m
      else if k == 1 then .close p .stateTooLarge
      else if k == 2 then .persist t st
      else if k == 3 then .fetch p hs
      else if k == 4 then .serveBlob p (h32 hi)
      else if k == 5 then .notify (notices[ni]?.getD .indexChanged)
      else if k == 6 then .reply (replies[ri]?.getD (.pending []))
      -- the same state message again (to another peer): encoded once, then as `sendAgain`
      else .send ⟨p.val + t.toUInt32⟩ (.state (digestOf ByteArray.empty) st)
    out := e :: out
  return out

/-- Mutate a byte string. -/
def mutate (b : ByteArray) : RM ByteArray := do
  if b.size == 0 then return b
  let i ← rr b.size
  match ← rr 6 with
  | 0 => return b.set! i (b[i]! ^^^ (1 <<< (← rr 8)).toUInt8)                       -- bit flip
  | 1 => return b.set! i (← rr 256).toUInt8                                          -- overwrite
  | 2 => return (b.extract 0 i).push (← rr 256).toUInt8 ++ b.extract i b.size        -- insert
  | 3 => return b.extract 0 i ++ b.extract (i + 1) b.size                            -- delete
  | 4 =>                                                                             -- duplicate a span
    let len := 1 + (← rr (min 16 (b.size - i)))
    return b.extract 0 (i + len) ++ b.extract i b.size
  | _ =>                                                                             -- huge varint count
    let huge : ByteArray := ⟨#[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F]⟩
    return b.extract 0 i ++ huge ++ b.extract (i + 1) b.size

structure FuzzStats where
  rejected : Nat := 0
  accepted : Nat := 0

/-- Decode `b`; an accepted value must re-encode to exactly `b`. -/
def fuzzOne (c : Ctx) (name : String) (dec : ByteArray → Option ByteArray) (b : ByteArray) (fs : FuzzStats) :
    IO FuzzStats := do
  match dec b with
  | none => return { fs with rejected := fs.rejected + 1 }
  | some re =>
    unless baEq re b do check c s!"{name}: accepted input re-encodes identically" false
    return { fs with accepted := fs.accepted + 1 }

def decS (b : ByteArray) : Option ByteArray := match decodeState b with | .ok s => some (encodeState s) | .error _ => none
def decM (b : ByteArray) : Option ByteArray := match decodeMessage b with | .ok m => some (encodeMessage m) | .error _ => none
def decE (b : ByteArray) : Option ByteArray := match decodeEvent b with | .ok e => some (encodeEvent e) | .error _ => none
def decF (b : ByteArray) : Option ByteArray := match decodeEffects b with | .ok e => some (encodeEffects e) | .error _ => none

def codecTests (c : Ctx) (mutations : Nat := 24000) : IO Unit := do
  -- P1 regression: one step sending the published state to 32 peers (plus the persist) must carry
  -- the state at most twice in the envelope, and the envelope must decode back
  let items := (List.range 20000).map (fun i => ({ path := s!"dir{i % 100}/file{i}", hash := h32 i, supersedes := [] } : PutItem))
  let big := State.empty.putMany ⟨1, 1⟩ items
  let dg := digestOf (encodeState big)
  let effs : List Effect := .persist 3 big :: (List.range 32).map (fun i => .send ⟨i.toUInt32⟩ (.state dg big))
  let env := encodeEffects effs
  let st := (encodeState big).size
  IO.println s!"codec: 32 state sends + persist of a {st}-byte state: envelope {env.size} bytes"
  check c "dedup: envelope holds at most two copies of the state" (env.size < 2 * st + 1000)
  check c "dedup: envelope decodes back to the same effects" (match decodeEffects env with
    | .ok effs' => effs'.length == 33 && baEq (encodeEffects effs') env
    | .error _ => false)
  let act : RM Unit := do
    -- round trips of random states
    for i in [0:200] do
      let s ← randomState (5 + i % 60)
      check c "random state is WireOk" (checkWire s)
      match decodeState (encodeState s) with
      | .ok s' => check c "state round trip" (s'.beq s)
      | .error e => check c "state round trip" false (fun _ => repr e |>.pretty)
    -- equal states built differently encode to equal bytes
    let a ← randomState 30
    let b ← randomState 30
    check c "merge order does not change the bytes" (baEq (encodeState (a.merge b)) (encodeState (b.merge a)))
    -- messages, events, effects
    let st ← randomState 25
    for _ in [0:300] do
      let m ← randomMessage st
      let bytes := encodeMessage m
      check c "message round trip (bytes)" (decM bytes == some bytes)
      let ev ← randomEvent st
      let eb := encodeEvent ev
      check c "event round trip (bytes)" (decE eb == some eb) (fun _ => s!"{eb.size} bytes")
      let effs ← randomEffects st
      let fb := encodeEffects effs
      check c "effects round trip (bytes)" (decF fb == some fb)
    -- truncation at every prefix length
    let s30 ← randomState 60
    IO.println s!"codec: truncation subject state has {s30.entries.length} entries, {s30.context.entries.length} replicas"
    let subjects : List (String × (ByteArray → Option ByteArray) × ByteArray) :=
      [("state", decS, encodeState s30),
       ("state message", decM, encodeMessage (.state (digestOf ByteArray.empty) s30)),
       ("want", decM, encodeMessage (.want (← randomHashes 20))),
       ("hello", decM, encodeMessage (.hello 1 ⟨0xFFFFFFFFFFFFFFFF, 5⟩ (digestOf ByteArray.empty))),
       ("init event", decE, encodeEvent (.init ⟨1, 2⟩ (encodeState s30) [h32 1, h32 2])),
       ("effects", decF, encodeEffects [.send ⟨3⟩ (.state (digestOf ByteArray.empty) s30), .persist 4 s30])]
    let mut prefixes := 0
    for (name, dec, full) in subjects do
      check c s!"{name}: full encoding accepted" (dec full == some full)
      for len in [0:full.size] do
        prefixes := prefixes + 1
        check c s!"{name}: prefix of length {len} rejected" (dec (full.extract 0 len)).isNone
    IO.println s!"codec: {prefixes} proper prefixes checked, all must be rejected"
    -- random mutations
    let mut fsS : FuzzStats := {}
    let mut fsM : FuzzStats := {}
    let mut fsE : FuzzStats := {}
    let msgs := #[encodeMessage (.state (digestOf ByteArray.empty) st), encodeMessage (.want (← randomHashes 8)),
      encodeMessage (.hello 1 ⟨1, 2⟩ (digestOf ByteArray.empty)), encodeMessage (.bye .incompatible),
      encodeMessage (.digest (digestOf ByteArray.empty)), encodeMessage (.noBlob [h32 1, h32 2])]
    let small ← randomState 8
    let evs := #[encodeEvent (.init ⟨1, 2⟩ (encodeState small) [h32 1]),
      encodeEvent (.received ⟨4⟩ (encodeMessage (.want [h32 3]))),
      encodeEvent (.localOp (.putMany [{ path := "p", hash := h32 1, supersedes := [h32 2] }])),
      encodeEvent (.localOp (.deleteMany [{ path := "q", supersedes := some [h32 1] }, { path := "r", supersedes := none }])),
      encodeEvent (.persisted 300 (digestOf ByteArray.empty)), encodeEvent (.blobStored (h32 3) (some ⟨9⟩))]
    let states := #[encodeState st, encodeState small, encodeState State.empty]
    for i in [0:mutations] do
      let k := i % 3
      let rounds := 1 + (← rr 3)
      if k == 0 then
        let mut b := states[← rr states.size]!
        for _ in [0:rounds] do b ← mutate b
        fsS ← fuzzOne c "decodeState" decS b fsS
      else if k == 1 then
        let mut b := msgs[← rr msgs.size]!
        for _ in [0:rounds] do b ← mutate b
        fsM ← fuzzOne c "decodeMessage" decM b fsM
      else
        let mut b := evs[← rr evs.size]!
        for _ in [0:rounds] do b ← mutate b
        fsE ← fuzzOne c "decodeEvent" decE b fsE
    IO.println s!"codec: {mutations} mutants: state {fsS.rejected} rejected / {fsS.accepted} accepted, message {fsM.rejected}/{fsM.accepted}, event {fsE.rejected}/{fsE.accepted}"
    -- random byte strings, with and without a valid header
    let mut fsR : FuzzStats := {}
    for i in [0:6000] do
      let len ← rr 64
      let mut b := ByteArray.empty
      if i % 2 == 0 then b := (b.push 1).push (1 + (i / 2 % 3)).toUInt8
      for _ in [0:len] do b := b.push (← rr 256).toUInt8
      fsR ← fuzzOne c "decodeState (random)" decS b fsR
      fsR ← fuzzOne c "decodeMessage (random)" decM b fsR
      fsR ← fuzzOne c "decodeEvent (random)" decE b fsR
    IO.println s!"codec: 18000 random-byte decodes: {fsR.rejected} rejected / {fsR.accepted} accepted"
    -- oversized input is rejected before parsing
    let big := ByteArray.mk (Array.replicate (maxMessageBytes + 1) 0)
    check c "oversized message rejected" (decM big).isNone
  let _ ← act.run ⟨0xC0DEC⟩

/-! ## Scale -/

def scaleTest (c : Ctx) (n : Nat) : IO Unit := do
  let items := (List.range n).map (fun i => ({ path := s!"files/{i / 100}/f{i}.txt", hash := h32 (i + 1), supersedes := [] } : PutItem))
  let w0 : World := { newWorld 3 1 with useProcess := false, checkView := false, checkInv := false }
  let t0 ← IO.monoMsNow
  let (_, w) ← runW w0 do
    boot 0; boot 1; boot 2
    ackPersist 0; ackPersist 1; ackPersist 2
    let dev ← getDev 0
    setDev 0 { dev with store := items.foldl (fun s it => s.insert it.hash) dev.store }
    feed 0 (.localOp (.putMany items))
    ackPersist 0
  let t1 ← IO.monoMsNow
  let (ok, w) ← runW w do
    let _ ← connect 0 1
    let _ ← connect 0 2
    let ok ← drainAll 10000000
    checkConverged
    return ok
  let t2 ← IO.monoMsNow
  check c "scale: quiesced" ok
  check c "scale: converged with all blobs" w.violations.isEmpty (fun _ => toString (w.violations.toList.take 3))
  let n1 := (nodeOr w 1).get!
  check c "scale: device 1 has every path" (n1.current.paths.length == n)
  IO.println s!"scale: time inside Lean's step: {w.stats.stepNanos / 1000000} ms in total"
  IO.println s!"scale: n={n}, putMany+persist {t1 - t0} ms, full sync of 2 devices (index + {w.stats.blobsDelivered} blobs, {w.stats.events} events) {t2 - t1} ms"

/-- Deliberately non-tail-recursive serialisation of the entries (depth = number of entries). It
exists to fail under the small stack: it shows that the scale sync passing there means the real
encoder and decoder do not recurse once per entry. -/
def naiveEnc : List Entry → List UInt8
  | [] => []
  | e :: es => e.path.toUTF8.toList ++ naiveEnc es

def controlTest (n : Nat) : IO Unit := do
  let items := (List.range n).map (fun i => ({ path := s!"f{i}", hash := h32 i, supersedes := [] } : PutItem))
  let s := State.empty.putMany ⟨1, 1⟩ items
  IO.println s!"control: non-tail encoding of {n} entries produced {(naiveEnc s.entries).length} bytes (did not overflow)"

/-- Trivial non-tail recursion, to calibrate the small-stack run (as in `crdt-tests deep`). -/
def deep : Nat → Nat
  | 0 => 0
  | n + 1 => deep n + 1

/-! ## Golden vectors for the JS codec (`sync-tests vectors FILE`, read by test/unit/codec.test.mjs)

One JSON object per line: `{"event": <JS event>, "hex": <Lean encodeEvent>}` or
`{"effects": [<JS effect>...], "hex": <Lean encodeEffects>}`. The JSON is written in the shape the
JS codec uses (app/js/codec.mjs): byte strings as hex, replica halves as decimal strings. Every
renderer below is an exhaustive `match`, so a new constructor in LeanSync breaks this file's build
until it is rendered here; the JS test separately checks its tables against the constructor lists
printed by scripts/wasm/Ctors.lean. -/

def jHex (b : ByteArray) : String :=
  "\"" ++ String.join (b.data.toList.map fun x =>
    let s := (Nat.toDigits 16 x.toNat).asString; if s.length == 1 then "0" ++ s else s) ++ "\""
def jStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c.toNat < 32 then s!"\\u{String.mk ((List.replicate (4 - (Nat.toDigits 16 c.toNat).length) '0') ++ Nat.toDigits 16 c.toNat)}"
    else c.toString) ++ "\""
def jObj (kvs : List (String × String)) : String :=
  "{" ++ ",".intercalate (kvs.map fun (k, v) => jStr k ++ ":" ++ v) ++ "}"
def jArr (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"
def jBool (b : Bool) : String := if b then "true" else "false"
def jRep (r : ReplicaId) : String := jObj [("hi", jStr (toString r.hi.toNat)), ("lo", jStr (toString r.lo.toNat))]
def jHash (h : Hash) : String := jHex h.bytes
def jHashes (hs : List Hash) : String := jArr (hs.map jHash)
def jPeer (p : PeerId) : String := toString p.val.toNat

def jEvent : Event → String
  | .init r st bs => jObj [("type", jStr "init"), ("replica", jRep r), ("stored", jHex st), ("blobs", jHashes bs)]
  | .initFresh r bs => jObj [("type", jStr "initFresh"), ("replica", jRep r), ("blobs", jHashes bs)]
  | .connected p => jObj [("type", jStr "connected"), ("peer", jPeer p)]
  | .disconnected p => jObj [("type", jStr "disconnected"), ("peer", jPeer p)]
  | .received p b => jObj [("type", jStr "received"), ("peer", jPeer p), ("bytes", jHex b)]
  | .localOp (.putMany items) => jObj [("type", jStr "putMany"), ("items", jArr (items.map fun it =>
      jObj [("path", jStr it.path), ("hash", jHash it.hash), ("supersedes", jHashes it.supersedes)]))]
  | .localOp (.deleteMany items) => jObj [("type", jStr "deleteMany"), ("items", jArr (items.map fun it =>
      jObj [("path", jStr it.path), ("supersedes", match it.supersedes with | none => "null" | some hs => jHashes hs)]))]
  | .localOp (.resolve p h) => jObj [("type", jStr "resolve"), ("path", jStr p), ("hash", jHash h)]
  | .persisted t d => jObj [("type", jStr "persisted"), ("tag", toString t), ("digest", jHex d.bytes)]
  | .persistFailed t => jObj [("type", jStr "persistFailed"), ("tag", toString t)]
  | .blobStored h src => jObj [("type", jStr "blobStored"), ("hash", jHash h), ("peer", match src with | none => "null" | some p => jPeer p)]
  | .blobsStored hs => jObj [("type", jStr "blobsStored"), ("hashes", jHashes hs)]
  | .blobFailed p h => jObj [("type", jStr "blobFailed"), ("peer", jPeer p), ("hash", jHash h)]
  | .blobLost h => jObj [("type", jStr "blobLost"), ("hash", jHash h)]
  | .query q => jObj [("type", jStr "query"), ("q", jStr (match q with | .snapshot => "snapshot" | .pending => "pending" | .status => "status"))]

def jReason : CloseReason → String
  | .protocolError => jStr "protocolError" | .incompatible => jStr "incompatible"
  | .sameReplicaId => jStr "sameReplicaId" | .tooManyPeers => jStr "tooManyPeers" | .stateTooLarge => jStr "stateTooLarge"
def jStatus : PeerStatus → String
  | .handshaking => jStr "handshaking" | .syncing => jStr "syncing" | .inSync => jStr "inSync"
def jErr : DecodeError → List (String × String)
  | .truncated => [("error", jStr "truncated"), ("value", "0")]
  | .trailing => [("error", jStr "trailing"), ("value", "0")]
  | .tooLarge => [("error", jStr "tooLarge"), ("value", "0")]
  | .badVersion v => [("error", jStr "badVersion"), ("value", toString v)]
  | .badKind k => [("error", jStr "badKind"), ("value", toString k)]
  | .badTag t => [("error", jStr "badTag"), ("value", toString t)]
  | .nonCanonical => [("error", jStr "nonCanonical"), ("value", "0")]
  | .badUtf8 => [("error", jStr "badUtf8"), ("value", "0")]
def jNotice : Notice → List (String × String)
  | .indexChanged => [("notice", jStr "indexChanged")]
  | .blobsChanged => [("notice", jStr "blobsChanged")]
  | .peerStatus p s r => [("notice", jStr "peerStatus"), ("peer", jPeer p), ("status", jStatus s),
      ("replica", match r with | none => "null" | some r => jRep r)]
  | .peerClosed p r b => [("notice", jStr "peerClosed"), ("peer", jPeer p), ("reason", jReason r), ("byPeer", jBool b)]
  | .peerLeft p => [("notice", jStr "peerLeft"), ("peer", jPeer p)]
  | .peerError p e => [("notice", jStr "peerError"), ("peer", jPeer p)] ++ jErr e
  | .rollbackDetected => [("notice", jStr "rollbackDetected")]
  | .opRejected why => [("notice", jStr "opRejected"), ("why", jStr why)]
  | .badEvent e => [("notice", jStr "badEvent")] ++ jErr e
  | .saveFailed => [("notice", jStr "saveFailed")]
  | .startupFailed e => [("notice", jStr "startupFailed")] ++ jErr e
  | .pendingSummary f q w => [("notice", jStr "pendingSummary"), ("fetching", toString f), ("queued", toString q), ("waiting", toString w)]
  | .notInitialized => [("notice", jStr "notInitialized")]
  | .alreadyInitialized => [("notice", jStr "alreadyInitialized")]
def jPend : Hash × PendingStatus → String
  | (h, .requested p) => jObj [("hash", jHash h), ("status", jStr "requested"), ("peer", jPeer p)]
  | (h, .queued) => jObj [("hash", jHash h), ("status", jStr "queued")]
  | (h, .waiting) => jObj [("hash", jHash h), ("status", jStr "waiting")]
def jReply : Reply → List (String × String)
  | .snapshot files => [("reply", jStr "snapshot"), ("files", jArr (files.map fun (p, vs) =>
      jObj [("path", jStr p), ("versions", jArr (vs.map fun v => jObj [("hash", jHash v.hash), ("present", jBool v.present)]))]))]
  | .pending items => [("reply", jStr "pending"), ("items", jArr (items.map jPend))]
  | .status pf d rb peers => [("reply", jStr "status"), ("persistInFlight", jBool pf), ("dirty", jBool d), ("rollback", jBool rb),
      ("peers", jArr (peers.map fun (p, s) => jObj [("peer", jPeer p), ("status", jStatus s)]))]
def jEffect : Effect → String
  | .send p m => jObj [("type", jStr "send"), ("peer", jPeer p), ("bytes", jHex (encodeMessage m))]
  | .close p r => jObj [("type", jStr "close"), ("peer", jPeer p), ("reason", jReason r)]
  | .persist t s => jObj [("type", jStr "persist"), ("tag", toString t), ("state", jHex (encodeState s))]
  | .fetch p hs => jObj [("type", jStr "fetch"), ("peer", jPeer p), ("hashes", jHashes hs), ("bytes", jHex (encodeMessage (.want hs)))]
  | .serveBlob p h => jObj [("type", jStr "serveBlob"), ("peer", jPeer p), ("hash", jHash h)]
  | .notify n => jObj ([("type", jStr "notify")] ++ jNotice n)
  | .reply r => jObj ([("type", jStr "reply")] ++ jReply r)

/-- One sample of every constructor (and every tag-carrying sub-constructor), with edge values. -/
def sampleEvents (st : State) : List Event :=
  let big : ReplicaId := ⟨0xFFFFFFFFFFFFFFFF, 0x8000000000000000⟩
  let p : PeerId := ⟨0xFFFFFFFF⟩
  [ .init big (encodeState st) [h32 1, h32 2], .init ⟨0, 0⟩ ByteArray.empty [],
    .initFresh ⟨1, 127⟩ [], .initFresh big [h32 3],
    .connected ⟨0⟩, .connected p, .disconnected ⟨128⟩,
    .received ⟨300⟩ (encodeMessage (.hello 1 big (mkDigest (ByteArray.mk (Array.replicate 32 9))))), .received ⟨1⟩ ByteArray.empty,
    .localOp (.putMany []), .localOp (.putMany [{ path := "日本/ファイル \"q\" \\ x", hash := h32 4, supersedes := [h32 5, h32 6] }, { path := "", hash := h32 7, supersedes := [] }]),
    .localOp (.deleteMany []), .localOp (.deleteMany [{ path := "a", supersedes := none }, { path := "b/c", supersedes := some [] }, { path := "d", supersedes := some [h32 8] }]),
    .localOp (.resolve "x y" (h32 9)), .localOp (.resolve "\uFEFFbom-first.txt" (h32 9)),
    .persisted 0 (mkDigest (ByteArray.mk (Array.replicate 32 0xAB))), .persisted 1099511627776 (mkDigest (ByteArray.mk (Array.replicate 32 1))),
    .persistFailed 0, .persistFailed 16384,
    .blobStored (h32 10) none, .blobStored (h32 11) (some p),
    .blobsStored [], .blobsStored ((List.range 300).map h32),
    .blobFailed ⟨5⟩ (h32 12), .blobLost (h32 13),
    .query .snapshot, .query .pending, .query .status ]

def sampleEffectLists (st : State) : List (List Effect) :=
  let p : PeerId := ⟨77⟩
  let d := mkDigest (ByteArray.mk (Array.replicate 32 3))
  let errs : List DecodeError := [.truncated, .trailing, .tooLarge, .badVersion 2, .badKind 300, .badTag 99, .nonCanonical, .badUtf8]
  let reasons : List CloseReason := [.protocolError, .incompatible, .sameReplicaId, .tooManyPeers, .stateTooLarge]
  [ [],
    [.send p (.hello 1 ⟨1, 2⟩ d), .send p (.digest d), .send p (.state d st), .send ⟨78⟩ (.state d st), .send ⟨79⟩ (.state d st),
     .send p (.noBlob [h32 1]), .send p (.have [h32 2, h32 3]), .send p (.bye .sameReplicaId)],
    reasons.map (.close p ·),
    [.persist 0 st, .persist 1099511627776 State.empty],
    [.fetch p [h32 4], .fetch ⟨0xFFFFFFFF⟩ ((List.range 32).map h32), .serveBlob p (h32 5)],
    [.notify .indexChanged, .notify .blobsChanged, .notify (.peerStatus p .handshaking none),
     .notify (.peerStatus p .syncing (some ⟨0xFFFFFFFFFFFFFFFF, 0⟩)), .notify (.peerStatus p .inSync (some ⟨3, 4⟩)),
     .notify (.peerLeft p), .notify .rollbackDetected, .notify (.opRejected "path too long: é"), .notify .notInitialized,
     .notify .alreadyInitialized, .notify (.pendingSummary 0 0 0), .notify (.pendingSummary 32 1 4096), .notify .saveFailed],
    reasons.map (fun r => .notify (.peerClosed p r (r == .incompatible))),
    errs.map (fun e => .notify (.peerError p e)) ++ errs.map (fun e => .notify (.badEvent e)) ++ errs.map (fun e => .notify (.startupFailed e)),
    [.reply (.snapshot []), .reply (.snapshot [("a", [⟨h32 1, true⟩, ⟨h32 2, false⟩]), ("b/ü", []), ("c", [⟨h32 3, false⟩]), ("\uFEFFbom", [⟨h32 4, true⟩])]),
     .reply (.pending []), .reply (.pending [(h32 3, .waiting), (h32 4, .requested p), (h32 5, .queued)]),
     .reply (.status false false false []), .reply (.status true true true [(p, .handshaking), (⟨78⟩, .syncing), (⟨79⟩, .inSync)])] ]

def vectorsCmd (file : String) (randomCount : Nat := 300) : IO Unit := do
  let ((), _) ← (do
    let st ← randomState 25
    let mut lines : Array String := #[]
    for e in sampleEvents st do lines := lines.push (jObj [("event", jEvent e), ("hex", jHex (encodeEvent e))])
    for l in sampleEffectLists st do lines := lines.push (jObj [("effects", jArr (l.map jEffect)), ("hex", jHex (encodeEffects l))])
    for _ in [0:randomCount] do
      let st ← randomState (← rr 20)
      let e ← randomEvent st
      lines := lines.push (jObj [("event", jEvent e), ("hex", jHex (encodeEvent e))])
      let l ← randomEffects st
      lines := lines.push (jObj [("effects", jArr (l.map jEffect)), ("hex", jHex (encodeEffects l))])
    IO.FS.writeFile file ("\n".intercalate lines.toList ++ "\n")
    IO.println s!"vectors: {lines.size} lines -> {file}" : RM Unit).run ⟨12345⟩

end SyncTests


namespace SyncTests

def bh32 (n : Nat) : Hash :=
  ⟨⟨((List.range 28).map (fun _ => (0:UInt8)) ++ [(n / 16777216 % 256).toUInt8, (n / 65536 % 256).toUInt8,
    (n / 256 % 256).toUInt8, (n % 256).toUInt8]).toArray⟩⟩

def bdg (n : Nat) : Digest :=
  ⟨⟨((List.range 31).map (fun _ => (0:UInt8)) ++ [n.toUInt8]).toArray⟩, by rw [← ByteArray.size_data]; simp⟩

/-- Per-event cost of `step` on a node whose index has `n` entries (compiled; indicative). -/
def stepBench (n : Nat) : IO Unit := do
  let items := (List.range n).map (fun i => ({ path := s!"dir{i % 100}/file{i}", hash := bh32 i, supersedes := [] } : PutItem))
  let a2 := (step (step (step .uninit (.initFresh ⟨1,1⟩ [])).1 (.persisted 0 (bdg 1))).1 (.localOp (.putMany items))).1
  let st := match a2 with | .running x => x.current | _ => State.empty
  let b3 := (step (step (step (step .uninit (.initFresh ⟨2,2⟩ [])).1 (.persisted 0 (bdg 2))).1 (.connected ⟨7⟩)).1
    (.received ⟨7⟩ (encodeMessage (.hello 1 ⟨1,1⟩ (bdg 3))))).1
  let t0 ← IO.monoNanosNow
  let b4 := (step b3 (.received ⟨7⟩ (encodeMessage (.state (bdg 3) st)))).1
  let b5 := (step b4 (.persisted 1 (bdg 3))).1
  let blen := match b5 with | .running x => x.missing.length | _ => 0
  let t1 ← IO.monoNanosNow
  IO.println s!"stepbench n={n}: merge + persist of the {n}-entry state: {(t1 - t0) / 1000000} ms (missing {blen})"
  let mut m := b5
  let t2 ← IO.monoNanosNow
  for i in [0:1000] do
    m := (step m (.blobStored (bh32 i) (some ⟨7⟩))).1
  let k := match m with | .running x => x.blobs.length | _ => 0
  let t3 ← IO.monoNanosNow
  IO.println s!"stepbench: blobStored {(t3 - t2) / 1000 / 1000} us/event ({k} blobs)"
  let t4 ← IO.monoNanosNow
  for _ in [0:1000] do
    m := (step m (.query .status)).1
  let k2 := match m with | .running x => x.nextTag | _ => 0
  let t5 ← IO.monoNanosNow
  IO.println s!"stepbench: an event that changes nothing (finish pass only) {(t5 - t4) / 1000 / 1000} us/event ({k2})"
  let a5 := (step (step (step a2 (.persisted 1 (bdg 4))).1 (.connected ⟨5⟩)).1
    (.received ⟨5⟩ (encodeMessage (.hello 1 ⟨2,2⟩ (bdg 3))))).1
  let want := encodeMessage (.want ((List.range 32).map (fun i => bh32 (i * (n / 32)))))
  let mut ma := a5
  let t6 ← IO.monoNanosNow
  for _ in [0:100] do
    ma := (step ma (.received ⟨5⟩ want)).1
  let k3 := match ma with | .running x => x.sessions.length | _ => 0
  let t7 ← IO.monoNanosNow
  IO.println s!"stepbench: want(32) {(t7 - t6) / 1000 / 100} us/event ({k3})"

end SyncTests

open SyncTests in
def main (args : List String) : IO UInt32 := do
  let failures ← IO.mkRef 0
  let checks ← IO.mkRef 0
  let c : Ctx := ⟨failures, checks, "unit"⟩
  match args with
  | ["unit"] => unitTests c
  | ["codec"] => codecTests { c with label := "codec" }
  | "sim" :: rest =>
    let seed := (rest[0]? >>= String.toNat?).getD 1
    let count := (rest[1]? >>= String.toNat?).getD 200
    simTests { c with label := "sim" } seed count
  | "sim-lenient" :: rest =>
    let seed := (rest[0]? >>= String.toNat?).getD 1
    let count := (rest[1]? >>= String.toNat?).getD 200
    simTests { c with label := "sim-lenient" } seed count (ackFirst := true)
  | ["mutation"] => mutationTests { c with label := "mutation" }
  | ["vectors", file] => vectorsCmd file; return 0
  | ["trace", seed, count, file] =>
    -- Simulator runs (4 devices, 400 random steps + quiescence per seed) recorded for wasm replay.
    let s0 := seed.toNat?.getD 1
    let mut out : ByteArray := .empty
    let mut nev := 0
    for s in [s0:s0 + count.toNat?.getD 1] do
      let act : WM Unit := do
        traceRec 2 0 .empty .empty
        for d in [0:4] do boot d
        for _ in [0:400] do randomStep
        quiesce s
      let ((), w) ← act.run { newWorld 4 s with keepTrace := true }
      check c s!"trace seed {s}" w.violations.isEmpty (fun _ => s!"{w.violations.toList.take 2}")
      out := out ++ w.trace
      nev := nev + w.stats.events
    IO.FS.writeBinFile file out
    IO.println s!"trace: {nev} events, {out.size} bytes -> {file}"
  | ["debug", seed] =>
    let sd := seed.toNat?.getD 1
    let act : WM Unit := do
      for d in [0:4] do boot d
      for _ in [0:400] do randomStep
      quiesce sd
    let ((), w) ← act.run { newWorld 4 sd with keepLog := true }
    for v in w.violations do IO.println v
    for (d, e) in w.log do
      match e with
      | .close p r => IO.println s!"LOG dev {d} close {p.val} {repr r}"
      | .notify (.peerError p err) => IO.println s!"LOG dev {d} peerError {p.val} {repr err}"
      | .notify (.peerClosed p r b) => IO.println s!"LOG dev {d} peerClosed {p.val} {repr r} byPeer {b}"
      | .persist t _ => IO.println s!"LOG dev {d} persist {t}"
      | e => if (match e with | .send p _ => decide (p.val ≥ 18) | .fetch p _ => decide (p.val ≥ 18) | _ => false) then IO.println s!"LOG dev {d} {showEff e}" else pure ()
    for d in [0:4] do
      match w.devs[d]!.m with
      | .running n =>
        IO.println s!"dev {d}: entries {n.current.entries.length} ctx {n.current.context.entries.map (fun (r, c) => (r.lo, c))} pub {n.published.map (fun P => (digestOf (encodeState P.state)).bytes.toList.take 4)} rollback {n.rollback} missing {n.missing.length} dirty {n.dirty} inflight {n.inflight.isSome} store {w.devs[d]!.store.size}"
        for x in n.sessions do
          IO.println s!"   sess {x.peer.val} ready {x.ready} hello {x.helloSent} peerD {x.peerDigest.map (·.bytes.toList.take 4)} lastSent {x.lastSent.map (·.bytes.toList.take 4)} infl {x.inflight.length} lacks {x.lacks.length} toldNo {x.toldNo.length}"
        for e in n.current.entries do IO.println s!"   {e.path} ({e.dot.replica.lo},{e.dot.counter}) {e.hash.bytes.toList.drop 30}"
      | .uninit => IO.println s!"dev {d} uninit"
    IO.println s!"conns {w.conns.map (fun c => (c.id, c.a, c.b, c.qab.size, c.qba.size))}"
  | "stepbench" :: rest => stepBench ((rest[0]? >>= String.toNat?).getD 20000); return 0
  | "scale" :: rest => scaleTest { c with label := "scale" } ((rest[0]? >>= String.toNat?).getD 20000)
  | "control" :: rest => controlTest ((rest[0]? >>= String.toNat?).getD 20000)
  | "deep" :: rest =>
    let n := (rest[0]? >>= String.toNat?).getD 13000
    IO.println s!"deep: non-tail recursion of depth {n} returned {deep n}"
  | [] | ["all"] =>
    unitTests c
    codecTests { c with label := "codec" }
    simTests { c with label := "sim" } 1 200
    mutationTests { c with label := "mutation" }
  | _ => IO.eprintln "usage: sync-tests [unit | codec | sim [seed] [count] | sim-lenient [seed] [count] | mutation | scale [n] | control [n] | deep [n] | debug seed | trace seed count file | vectors file | all]"; return 2
  let n ← failures.get
  IO.println s!"{← checks.get} checks run"
  if n == 0 then IO.println "all tests passed"; return 0
  else IO.eprintln s!"{n} check(s) failed"; return 1
