import LeanSync.EffectsWire

/-!
# Host envelopes and the wasm boundary

Executable module (imports `Init` only).

`process` is the single boundary function: an encoded `Event` in (kind 3), the encoded effect
list out (kind 4). The machine lives in an `IO.Ref` between calls (`processIO`, exported to C
as `lean_sync_process`).

Envelope layout (version 1; integers are canonical varints, `bytes` = varint length + bytes,
`hash` = `bytes` of length 32 in events, any length in effects, `peer` = varint < 2^32,
`replica` = hi:varint lo:varint, `str` = varint length + UTF-8):

```
event   := 01 03 tag:u8 ...
  0 init        replica stored:bytes k:varint {hash}^k
  1 initFresh   replica k:varint {hash}^k
  2 connected   peer            3 disconnected peer
  4 received    peer msg:bytes
  5 localOp     0 putMany    k {path:str hash m:varint {hash}^m}^k
                1 deleteMany k {path:str (00 | 01 m:varint {hash}^m)}^k
                2 resolve    path:str hash
  6 persisted   tag:varint digest:32       7 persistFailed tag:varint
  8 blobStored  hash (00 | 01 peer)        9 blobFailed peer hash
  10 blobLost   hash                       11 query (0 snapshot | 1 pending | 2 status)
  12 blobsStored k:varint {hash}^k         (start-up inventory in chunks, or any batch of stored blobs)
```
The effects envelope (Lean → host) is in `LeanSync/EffectsWire.lean`. Decoding of events is total
and linear; any malformed event yields the single effect `notify (badEvent e)`.
-/

set_option linter.unusedSectionVars false

namespace LeanSync

open LeanCrdt

/-! ## A small parser monad over `Parser` (lists go through the tail-recursive `manyGo`) -/

structure Dec (α : Type) where
  run : Parser α

instance : Monad Dec where
  pure x := ⟨fun _ pos => .ok (x, pos)⟩
  bind p f := ⟨fun b pos =>
    match p.run b pos with
    | .ok (x, q) => (f x).run b q
    | .error e => .error e⟩

def Dec.lift {α} (p : Parser α) : Dec α := ⟨p⟩
def Dec.fail {α} (e : DecodeError) : Dec α := ⟨fun _ _ => .error e⟩
def Dec.many {α} (k : Nat) (p : Dec α) : Dec (List α) := ⟨fun b pos => manyGo p.run (fun _ _ => true) b k pos none []⟩

def dByte : Dec UInt8 := .lift readByte
def dVar : Dec Nat := .lift readVarint
def dU64 : Dec UInt64 := .lift readU64
def dReplica : Dec ReplicaId := do let hi ← dU64; let lo ← dU64; pure ⟨hi, lo⟩
def dPeer : Dec PeerId := do
  let v ← dVar
  if v < 2 ^ 32 then pure ⟨v.toUInt32⟩ else .fail .tooLarge
def dBytes (maxLen : Nat) : Dec ByteArray := do
  let n ← dVar
  if n ≤ maxLen then .lift (readBytes n) else .fail .tooLarge
def dHash : Dec Hash := do
  let n ← dVar
  if n = hashLen then (Hash.mk <$> .lift (readBytes n)) else .fail .nonCanonical
def dHashes : Dec (List Hash) := do let k ← dVar; .many k dHash
def dStr : Dec String := .lift (readStr maxPathBytes)
def dDigest : Dec Digest := .lift readDigest
def dBool : Dec Bool := do
  let x ← dByte
  if x = 0 then pure false else if x = 1 then pure true else .fail (.badTag x.toNat)

def dPutItem : Dec PutItem := do
  let path ← dStr; let hash ← dHash; let sup ← dHashes
  pure { path, hash, supersedes := sup }

def dDeleteItem : Dec DeleteItem := do
  let path ← dStr
  let some ← dBool
  if some then do let hs ← dHashes; pure { path, supersedes := .some hs }
  else pure { path, supersedes := none }

def dLocalOp : Dec LocalOp := do
  let t ← dByte
  if t = 0 then do let k ← dVar; let items ← .many k dPutItem; pure (.putMany items)
  else if t = 1 then do let k ← dVar; let items ← .many k dDeleteItem; pure (.deleteMany items)
  else if t = 2 then do let p ← dStr; let h ← dHash; pure (.resolve p h)
  else .fail (.badTag t.toNat)

def dQuery : Dec Query := do
  let t ← dByte
  if t = 0 then pure .snapshot else if t = 1 then pure .pending else if t = 2 then pure .status
  else .fail (.badTag t.toNat)

def dEvent : Dec Event := do
  let t ← dByte
  match t.toNat with
  | 0 => do let r ← dReplica; let st ← dBytes maxStateBytes; let bs ← dHashes; pure (.init r st bs)
  | 1 => do let r ← dReplica; let bs ← dHashes; pure (.initFresh r bs)
  | 2 => do let p ← dPeer; pure (.connected p)
  | 3 => do let p ← dPeer; pure (.disconnected p)
  | 4 => do let p ← dPeer; let m ← dBytes maxMessageBytes; pure (.received p m)
  | 5 => do let op ← dLocalOp; pure (.localOp op)
  | 6 => do let t ← dVar; let d ← dDigest; pure (.persisted t d)
  | 7 => do let t ← dVar; pure (.persistFailed t)
  | 8 => do
    let h ← dHash; let has ← dBool
    if has then do let p ← dPeer; pure (.blobStored h (some p)) else pure (.blobStored h none)
  | 9 => do let p ← dPeer; let h ← dHash; pure (.blobFailed p h)
  | 10 => do let h ← dHash; pure (.blobLost h)
  | 11 => do let q ← dQuery; pure (.query q)
  | 12 => do let hs ← dHashes; pure (.blobsStored hs)
  | n => .fail (.badTag n)

def decodeEvent (b : ByteArray) : Except DecodeError Event :=
  decodeTop (readWithHeader kindEvent dEvent.run) maxEnvelopeBytes b

/-! ## Writers -/

def wLocalOp (acc : ByteArray) : LocalOp → ByteArray
  | .putMany items => wList (fun a (it : PutItem) => wHashes (wHash (wStr a it.path) it.hash) it.supersedes)
      (acc.push 0) items
  | .deleteMany items => wList (fun a (it : DeleteItem) =>
      match it.supersedes with
      | none => wBool (wStr a it.path) false
      | some hs => wHashes (wBool (wStr a it.path) true) hs) (acc.push 1) items
  | .resolve p h => wHash (wStr (acc.push 2) p) h

def wQuery (acc : ByteArray) : Query → ByteArray
  | .snapshot => acc.push 0
  | .pending => acc.push 1
  | .status => acc.push 2

/-- Event encoder (the host's job in production; here for tests and the simulator). -/
def encodeEvent (e : Event) : ByteArray :=
  let acc := (ByteArray.empty.push wireVersion).push kindEvent
  match e with
  | .init r st bs => wHashes (wLen (wReplica (acc.push 0) r) st) bs
  | .initFresh r bs => wHashes (wReplica (acc.push 1) r) bs
  | .connected p => wPeer (acc.push 2) p
  | .disconnected p => wPeer (acc.push 3) p
  | .received p m => wLen (wPeer (acc.push 4) p) m
  | .localOp op => wLocalOp (acc.push 5) op
  | .persisted t d => wBytes (wVar (acc.push 6) t) d.bytes
  | .persistFailed t => wVar (acc.push 7) t
  | .blobStored h none => wBool (wHash (acc.push 8) h) false
  | .blobStored h (some p) => wPeer (wBool (wHash (acc.push 8) h) true) p
  | .blobFailed p h => wHash (wPeer (acc.push 9) p) h
  | .blobLost h => wHash (acc.push 10) h
  | .query q => wQuery (acc.push 11) q
  | .blobsStored hs => wHashes (acc.push 12) hs

/-! ## The boundary -/

/-- The single boundary function: an encoded event in, the encoded effect list out. A malformed
envelope yields `[notify (badEvent e)]` and leaves the machine unchanged. -/
def process (m : Machine) (input : ByteArray) : Machine × ByteArray :=
  match decodeEvent input with
  | .ok ev => let (m', effs) := step m ev; (m', encodeEffects effs)
  | .error e => (m, encodeEffects [.notify (.badEvent e)])

/-- The machine lives here between calls (single-threaded wasm: one call at a time). -/
initialize machineRef : IO.Ref Machine ← IO.mkRef .uninit

/-- Exported entry point for the C shim: `lean_object* lean_sync_process(lean_object* input,
lean_object* world)` returns an `IO` result whose value is the output `ByteArray`. This is the
only impure code in the library: read the machine, step, write it back. -/
@[export lean_sync_process]
def processIO (input : ByteArray) : IO ByteArray := do
  let m ← machineRef.get
  machineRef.set .uninit          -- drop our reference so `step` can update `m` in place
  let (m', out) := process m input
  machineRef.set m'
  return out

end LeanSync
