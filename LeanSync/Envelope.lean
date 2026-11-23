import LeanSync.Step

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
effects := 01 04 k:varint {effect}^k
  0 send peer msg:bytes                    1 close peer reason:u8
  2 persist tag:varint state:bytes          (state = the record to store; hash exactly these bytes)
  3 fetch peer k:varint {hash}^k msg:bytes  (msg = the encoded `want`, to send verbatim)
  4 serveBlob peer hash                    5 notify notice              6 reply reply
```
Notices and replies are listed at `wNotice` and `wReply`. Decoding of events is total and
linear; any malformed event yields the single effect `notify (badEvent e)`.
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
  | n => .fail (.badTag n)

def decodeEvent (b : ByteArray) : Except DecodeError Event :=
  decodeTop (readWithHeader kindEvent dEvent.run) maxEnvelopeBytes b

/-! ## Writers -/

def wPeer (acc : ByteArray) (p : PeerId) : ByteArray := wVar acc p.val.toNat
def wReplica (acc : ByteArray) (r : ReplicaId) : ByteArray := wVar (wVar acc r.hi.toNat) r.lo.toNat
def wLen (acc : ByteArray) (x : ByteArray) : ByteArray := wBytes (wVar acc x.size) x
def wHash (acc : ByteArray) (h : Hash) : ByteArray := wLen acc h.bytes
def wHashes (acc : ByteArray) (hs : List Hash) : ByteArray := hs.foldl wHash (wVar acc hs.length)
def wBool (acc : ByteArray) (b : Bool) : ByteArray := acc.push (if b then 1 else 0)
def wList {α} (w : ByteArray → α → ByteArray) (acc : ByteArray) (l : List α) : ByteArray :=
  l.foldl w (wVar acc l.length)

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

def errCode : DecodeError → UInt8 × Nat
  | .truncated => (0, 0) | .trailing => (1, 0) | .tooLarge => (2, 0) | .badVersion v => (3, v)
  | .badKind k => (4, k) | .badTag t => (5, t) | .nonCanonical => (6, 0) | .badUtf8 => (7, 0)

def wErr (acc : ByteArray) (e : DecodeError) : ByteArray :=
  let (c, v) := errCode e; wVar (acc.push c) v

def statusByte : PeerStatus → UInt8
  | .handshaking => 0 | .syncing => 1 | .inSync => 2

/-- Notices: 0 indexChanged · 1 blobsChanged · 2 peerStatus peer status:u8 (00 | 01 replica) ·
3 peerClosed peer reason:u8 byPeer:u8 · 4 peerLeft peer · 5 peerError peer err ·
6 rollbackDetected · 7 opRejected str · 8 badEvent err · 9 startupFailed err ·
10 notInitialized · 11 alreadyInitialized · 12 pendingSummary fetching:varint waiting:varint.
`err` = code:u8 value:varint (0 truncated, 1 trailing, 2 tooLarge, 3 badVersion v, 4 badKind k,
5 badTag t, 6 nonCanonical, 7 badUtf8). -/
def wNotice (acc : ByteArray) : Notice → ByteArray
  | .indexChanged => acc.push 0
  | .blobsChanged => acc.push 1
  | .peerStatus p s r =>
    let a := (wPeer (acc.push 2) p).push (statusByte s)
    match r with
    | none => wBool a false
    | some r => wReplica (wBool a true) r
  | .peerClosed p r byPeer => wBool ((wPeer (acc.push 3) p).push (reasonByte r)) byPeer
  | .peerLeft p => wPeer (acc.push 4) p
  | .peerError p e => wErr (wPeer (acc.push 5) p) e
  | .rollbackDetected => acc.push 6
  | .opRejected why => wLen (acc.push 7) why.toByteArray
  | .badEvent e => wErr (acc.push 8) e
  | .startupFailed e => wErr (acc.push 9) e
  | .notInitialized => acc.push 10
  | .alreadyInitialized => acc.push 11
  | .pendingSummary f w => wVar (wVar (acc.push 12) f) w

/-- Replies: 0 snapshot k {path:str m {hash present:u8}^m}^k · 1 pending k {hash (00 | 01 peer)}^k ·
2 status persistInFlight:u8 dirty:u8 rollback:u8 k {peer status:u8}^k. -/
def wReply (acc : ByteArray) : Reply → ByteArray
  | .snapshot files => wList (fun a (f : String × List VersionInfo) =>
      wList (fun a (v : VersionInfo) => wBool (wHash a v.hash) v.present) (wStr a f.1) f.2)
      (acc.push 0) files
  | .pending items => wList (fun a (x : Hash × PendingStatus) =>
      match x.2 with
      | .waiting => wBool (wHash a x.1) false
      | .requested p => wPeer (wBool (wHash a x.1) true) p) (acc.push 1) items
  | .status pf d rb peers => wList (fun a (x : PeerId × PeerStatus) => (wPeer a x.1).push (statusByte x.2))
      (wBool (wBool (wBool (acc.push 2) pf) d) rb) peers

def wEffect (acc : ByteArray) : Effect → ByteArray
  | .send p m => wLen (wPeer (acc.push 0) p) (encodeMessage m)
  | .close p r => (wPeer (acc.push 1) p).push (reasonByte r)
  | .persist t s => wLen (wVar (acc.push 2) t) (encodeState s)
  | .fetch p hs => wLen (wHashes (wPeer (acc.push 3) p) hs) (encodeMessage (.want hs))
  | .serveBlob p h => wHash (wPeer (acc.push 4) p) h
  | .notify n => wNotice (acc.push 5) n
  | .reply r => wReply (acc.push 6) r

def encodeEffects (effs : List Effect) : ByteArray :=
  wList wEffect ((ByteArray.empty.push wireVersion).push kindEffects) effs

/-! ## Decoding effects (what the JS host does; here for tests and the simulator) -/

def dErr : Dec DecodeError := do
  let c ← dByte; let v ← dVar
  match c.toNat with
  | 0 => pure .truncated | 1 => pure .trailing | 2 => pure .tooLarge | 3 => pure (.badVersion v)
  | 4 => pure (.badKind v) | 5 => pure (.badTag v) | 6 => pure .nonCanonical | 7 => pure .badUtf8
  | n => .fail (.badTag n)

def dStatus : Dec PeerStatus := do
  let x ← dByte
  match x.toNat with
  | 0 => pure .handshaking | 1 => pure .syncing | 2 => pure .inSync | n => .fail (.badTag n)

def dReason : Dec CloseReason := do
  let x ← dByte
  match reasonOfByte x with
  | some r => pure r
  | none => .fail (.badTag x.toNat)

def dAnyHash : Dec Hash := do let b ← dBytes maxStateBytes; pure ⟨b⟩

def dNotice : Dec Notice := do
  let t ← dByte
  match t.toNat with
  | 0 => pure .indexChanged
  | 1 => pure .blobsChanged
  | 2 => do
    let p ← dPeer; let s ← dStatus; let has ← dBool
    if has then do let r ← dReplica; pure (.peerStatus p s (some r)) else pure (.peerStatus p s none)
  | 3 => do let p ← dPeer; let r ← dReason; let b ← dBool; pure (.peerClosed p r b)
  | 4 => do let p ← dPeer; pure (.peerLeft p)
  | 5 => do let p ← dPeer; let e ← dErr; pure (.peerError p e)
  | 6 => pure .rollbackDetected
  | 7 => do
    let b ← dBytes maxStateBytes
    if h : b.IsValidUTF8 then pure (.opRejected (String.ofByteArray b h)) else .fail .badUtf8
  | 8 => do let e ← dErr; pure (.badEvent e)
  | 9 => do let e ← dErr; pure (.startupFailed e)
  | 10 => pure .notInitialized
  | 11 => pure .alreadyInitialized
  | 12 => do let f ← dVar; let w ← dVar; pure (.pendingSummary f w)
  | n => .fail (.badTag n)

def dReply : Dec Reply := do
  let t ← dByte
  match t.toNat with
  | 0 => do
    let k ← dVar
    let files ← .many k (do
      let p ← dStr; let m ← dVar
      let vs ← .many m (do let h ← dAnyHash; let pr ← dBool; pure (VersionInfo.mk h pr))
      pure (p, vs))
    pure (.snapshot files)
  | 1 => do
    let k ← dVar
    let items ← .many k (do
      let h ← dAnyHash; let has ← dBool
      if has then do let p ← dPeer; pure (h, PendingStatus.requested p) else pure (h, PendingStatus.waiting))
    pure (.pending items)
  | 2 => do
    let pf ← dBool; let d ← dBool; let rb ← dBool; let k ← dVar
    let peers ← .many k (do let p ← dPeer; let s ← dStatus; pure (p, s))
    pure (.status pf d rb peers)
  | n => .fail (.badTag n)

def dEmbedded {α} (dec : ByteArray → Except DecodeError α) : Dec α := do
  let b ← dBytes maxMessageBytes
  match dec b with
  | .ok x => pure x
  | .error e => .fail e

def dEffect : Dec Effect := do
  let t ← dByte
  match t.toNat with
  | 0 => do let p ← dPeer; let m ← dEmbedded decodeMessage; pure (.send p m)
  | 1 => do let p ← dPeer; let r ← dReason; pure (.close p r)
  | 2 => do let tag ← dVar; let s ← dEmbedded decodeState; pure (.persist tag s)
  | 3 => do
    let p ← dPeer; let hs ← (do let k ← dVar; .many k dAnyHash); let m ← dEmbedded decodeMessage
    match m with
    | .want hs' => if hs' == hs then pure (.fetch p hs) else .fail .nonCanonical
    | _ => .fail .nonCanonical
  | 4 => do let p ← dPeer; let h ← dAnyHash; pure (.serveBlob p h)
  | 5 => do let n ← dNotice; pure (.notify n)
  | 6 => do let r ← dReply; pure (.reply r)
  | n => .fail (.badTag n)

def decodeEffects (b : ByteArray) : Except DecodeError (List Effect) :=
  decodeTop (readWithHeader kindEffects (do let k ← dVar; Dec.many k dEffect).run) (8 * maxEnvelopeBytes) b

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
