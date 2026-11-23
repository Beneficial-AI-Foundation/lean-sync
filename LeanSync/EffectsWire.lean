import LeanSync.Step

/-!
# The effects envelope (Lean → host), with a proved round trip

Executable module (imports `Init` only).

```
effects := 01 04 k:nat {effect}^k
effect  := 0 send peer msg:bytes          (msg = the encoded Lean message, sent verbatim)
         | 1 close peer reason:u8
         | 2 persist tag:nat state:bytes   (state = the record to store; hash exactly these bytes)
         | 3 fetch peer k:nat {hash}^k msg:bytes   (msg = the encoded `want`, sent verbatim)
         | 4 serveBlob peer hash
         | 5 notify notice
         | 6 reply reply
         | 7 sendAgain peer               (send the same state message as the last `send` of a state)
nat     := LEB128, any size            bytes := nat length, then the bytes
hash    := bytes                       peer := nat (< 2^32)        bool := 00 | 01
str     := bytes (UTF-8)               replica := hi:nat lo:nat
```
Notices and replies are listed at `encNotice` and `encReply`.

**De-duplication.** All state messages sent in one step carry the same published state. The
encoder writes a state message once and encodes each later `send` of an equal state message as
`sendAgain peer`, so one envelope holds at most one copy of the published state (plus at most one
persisted state), instead of one copy per peer. Equality is checked with `State.beq`, which costs
a comparison pass, not an encoding.

**No total size cap.** The effects envelope is Lean's own output, decoded by the trusted host, so
its decoder imposes no total size limit and reads integers and byte strings of any length; the
limits belong to untrusted inputs (events, peer messages), and every embedded peer message and
state is within its own limit (`EffOk`). The round trip `decodeEffects_encodeEffects` is proved
for every effect list whose sends, fetches and persists are well formed, and `Laws` proves that
every effect list the step function emits is.
-/

set_option linter.unusedSectionVars false
-- one `simp` call serves every constructor of a `cases`, so some lemmas are unused in some branches
set_option linter.unusedSimpArgs false

namespace LeanSync

open LeanCrdt

theorem State.eq_of_beq' {a b : State} (h : State.beq a b = true) : a = b := by
  unfold State.beq at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨he, hc⟩ := h
  have he' : a.entries = b.entries := LawfulBEq.eq_of_beq he
  have hc' : a.context.entries = b.context.entries := LawfulBEq.eq_of_beq hc
  apply State.ext he'
  have : ∀ (u v : VersionVector), u.entries = v.entries → u = v := by
    intro u v huv; cases u; cases v; simp only at huv; subst huv; rfl
  exact this _ _ hc'

/-! ## Primitive encoders, writers, decoders -/

def encLen (x : ByteArray) : List UInt8 := encVar x.size ++ x.data.toList
def encPeer (p : PeerId) : List UInt8 := encVar p.val.toNat
def encBool (b : Bool) : List UInt8 := [if b then 1 else 0]
def encRep (r : ReplicaId) : List UInt8 := encVar r.hi.toNat ++ encVar r.lo.toNat
def encHashE (h : Hash) : List UInt8 := encLen h.bytes
def encList {α} (f : α → List UInt8) (l : List α) : List UInt8 := encVar l.length ++ l.flatMap f

def wPeer (acc : ByteArray) (p : PeerId) : ByteArray := wVar acc p.val.toNat
def wReplica (acc : ByteArray) (r : ReplicaId) : ByteArray := wVar (wVar acc r.hi.toNat) r.lo.toNat
def wLen (acc : ByteArray) (x : ByteArray) : ByteArray := wBytes (wVar acc x.size) x
def wHash (acc : ByteArray) (h : Hash) : ByteArray := wLen acc h.bytes
def wHashes (acc : ByteArray) (hs : List Hash) : ByteArray := hs.foldl wHash (wVar acc hs.length)
def wBool (acc : ByteArray) (b : Bool) : ByteArray := acc.push (if b then 1 else 0)
def wList {α} (w : ByteArray → α → ByteArray) (acc : ByteArray) (l : List α) : ByteArray :=
  l.foldl w (wVar acc l.length)

theorem wPeer_toList (acc : ByteArray) (p : PeerId) :
    (wPeer acc p).data.toList = acc.data.toList ++ encPeer p := wVar_toList _ _
theorem wReplica_toList (acc : ByteArray) (r : ReplicaId) :
    (wReplica acc r).data.toList = acc.data.toList ++ encRep r := by
  simp [wReplica, wVar_toList, encRep]
theorem wLen_toList (acc x : ByteArray) : (wLen acc x).data.toList = acc.data.toList ++ encLen x := by
  simp [wLen, wBytes_toList, wVar_toList, encLen]
theorem wHash_toList (acc : ByteArray) (h : Hash) :
    (wHash acc h).data.toList = acc.data.toList ++ encHashE h := wLen_toList _ _
theorem wBool_toList (acc : ByteArray) (b : Bool) :
    (wBool acc b).data.toList = acc.data.toList ++ encBool b := push_toList _ _
theorem wList_toList {α} (w : ByteArray → α → ByteArray) (f : α → List UInt8)
    (hw : ∀ acc x, (w acc x).data.toList = acc.data.toList ++ f x) (acc : ByteArray) (l : List α) :
    (wList w acc l).data.toList = acc.data.toList ++ encList f l := by
  simp [wList, foldl_toList w f hw, wVar_toList, encList]
theorem wHashes_toList (acc : ByteArray) (hs : List Hash) :
    (wHashes acc hs).data.toList = acc.data.toList ++ encList encHashE hs :=
  wList_toList wHash encHashE wHash_toList acc hs

/-- A natural number of any size (the trusted envelope has no 64-bit cap). -/
def readNat : Parser Nat := fun b pos => readVar (b.size - pos) b pos

theorem readNat_complete : Complete readNat encVar (fun _ => True) := by
  intro b pos n rest hpos _ h
  have hl := length_bytesFrom b pos
  rw [h] at hl
  simp only [List.length_append] at hl
  exact readVar_complete _ n b pos rest (by omega) h

def readLen : Parser ByteArray := fun b pos =>
  match readNat b pos with
  | .ok (n, p) => readBytes n b p
  | .error e => .error e

theorem readLen_complete : Complete readLen encLen (fun _ => True) := by
  intro b pos x rest hpos _ h
  unfold encLen at h; rw [List.append_assoc] at h
  have e1 := readNat_complete b pos x.size _ hpos trivial h
  have e2 := readBytes_complete x.size b _ x rest (le_size_of_bytesFrom hpos h) rfl (bytesFrom_skip h)
  simp only [readLen, e1, e2, encLen, List.length_append]
  congr 2
  rw [Array.length_toList, ByteArray.size_data]; omega

def readHashE : Parser Hash := mapP Hash.mk readLen

theorem readHashE_complete : Complete readHashE encHashE (fun _ => True) := by
  intro b pos h rest hpos _ hb
  exact mapP_of_ok (readLen_complete b pos h.bytes rest hpos trivial hb)

def readPeer : Parser PeerId := fun b pos =>
  match readNat b pos with
  | .ok (n, p) => if n < 2 ^ 32 then .ok (⟨n.toUInt32⟩, p) else .error .tooLarge
  | .error e => .error e

theorem readPeer_complete : Complete readPeer encPeer (fun _ => True) := by
  intro b pos p rest hpos _ h
  have e1 := readNat_complete b pos _ rest hpos trivial h
  have hlt : p.val.toNat < 2 ^ 32 := p.val.toNat_lt
  simp only [readPeer, e1, hlt, ite_true, encPeer]
  congr
  cases p; simp

def readBool : Parser Bool := fun b pos =>
  match readByte b pos with
  | .ok (x, p) => if x = 0 then .ok (false, p) else if x = 1 then .ok (true, p) else .error (.badTag x.toNat)
  | .error e => .error e

theorem readBool_complete : Complete readBool encBool (fun _ => True) := by
  intro b pos x rest hpos _ h
  have e1 := readByte_complete b pos _ rest hpos trivial h
  cases x <;> simp [readBool, e1, encBool]

def readRep : Parser ReplicaId := mapP (fun z => ⟨UInt64.ofNat z.1, UInt64.ofNat z.2⟩) (seqP readNat readNat)

theorem readRep_complete : Complete readRep encRep (fun _ => True) := by
  intro b pos r rest hpos _ h
  have e := seqP_complete readNat_complete readNat_complete b pos (r.hi.toNat, r.lo.toNat) rest hpos
    ⟨trivial, trivial⟩ (by simpa [encRep] using h)
  have := mapP_of_ok (f := fun z => (⟨UInt64.ofNat z.1, UInt64.ofNat z.2⟩ : ReplicaId)) e
  simp only [UInt64.ofNat_toNat] at this
  simpa [readRep, encRep] using this

def readStrE : Parser String := fun b pos =>
  match readLen b pos with
  | .ok (x, p) => if h : x.IsValidUTF8 then .ok (String.ofByteArray x h, p) else .error .badUtf8
  | .error e => .error e

theorem readStrE_complete : Complete readStrE encStr (fun _ => True) := by
  intro b pos s rest hpos _ h
  have e1 := readLen_complete b pos s.toByteArray rest hpos trivial h
  simp only [readStrE, e1, s.isValidUTF8, dite_true]
  rfl

def readList {α} (p : Parser α) : Parser (List α) := fun b pos =>
  match readNat b pos with
  | .ok (k, p1) => manyGo p (fun _ _ => true) b k p1 none []
  | .error e => .error e

theorem chain_true {α} : ∀ (prev : Option α) (l : List α), Chain (fun _ _ => true) prev l
  | _, [] => trivial
  | _, _ :: xs => ⟨rfl, chain_true _ xs⟩

theorem readList_complete {α} {p : Parser α} {f : α → List UInt8} {ok : α → Prop}
    (hp : Complete p f ok) : Complete (readList p) (encList f) (fun l => ∀ x ∈ l, ok x) := by
  intro b pos l rest hpos hl h
  unfold encList at h; rw [List.append_assoc] at h
  have e1 := readNat_complete b pos l.length _ hpos trivial h
  have e2 := manyGo_complete hp (fun _ _ => true) b l _ none [] rest (le_size_of_bytesFrom hpos h)
    (chain_true _ _) hl (bytesFrom_skip h)
  simp only [readList, e1, e2, List.reverse_nil, List.nil_append, encList, List.length_append]
  congr 2; omega

/-! ## Small enumerations -/

def statusByte : PeerStatus → UInt8
  | .handshaking => 0 | .syncing => 1 | .inSync => 2

def readStatus : Parser PeerStatus := fun b pos =>
  match readByte b pos with
  | .ok (x, p) =>
    if x = 0 then .ok (.handshaking, p) else if x = 1 then .ok (.syncing, p)
    else if x = 2 then .ok (.inSync, p) else .error (.badTag x.toNat)
  | .error e => .error e

theorem readStatus_complete : Complete readStatus (fun s => [statusByte s]) (fun _ => True) := by
  intro b pos s rest hpos _ h
  have e1 := readByte_complete b pos _ rest hpos trivial h
  cases s <;> simp [readStatus, e1, statusByte]

def readReason : Parser CloseReason := fun b pos =>
  match readByte b pos with
  | .ok (x, p) =>
    match reasonOfByte x with
    | some r => .ok (r, p)
    | none => .error (.badTag x.toNat)
  | .error e => .error e

theorem readReason_complete : Complete readReason (fun r => [reasonByte r]) (fun _ => True) := by
  intro b pos r rest hpos _ h
  have e1 := readByte_complete b pos _ rest hpos trivial h
  simp [readReason, e1, reasonOfByte_reasonByte]

def errCode : DecodeError → UInt8 × Nat
  | .truncated => (0, 0) | .trailing => (1, 0) | .tooLarge => (2, 0) | .badVersion v => (3, v)
  | .badKind k => (4, k) | .badTag t => (5, t) | .nonCanonical => (6, 0) | .badUtf8 => (7, 0)

def encErr (e : DecodeError) : List UInt8 := (errCode e).1 :: encVar (errCode e).2

def wErr (acc : ByteArray) (e : DecodeError) : ByteArray := wVar (acc.push (errCode e).1) (errCode e).2

theorem wErr_toList (acc : ByteArray) (e : DecodeError) :
    (wErr acc e).data.toList = acc.data.toList ++ encErr e := by
  simp [wErr, wVar_toList, push_toList, encErr]

def errOf (c : UInt8) (v : Nat) : Option DecodeError :=
  if c = 0 then some .truncated else if c = 1 then some .trailing else if c = 2 then some .tooLarge
  else if c = 3 then some (.badVersion v) else if c = 4 then some (.badKind v)
  else if c = 5 then some (.badTag v) else if c = 6 then some .nonCanonical
  else if c = 7 then some .badUtf8 else none

def readErr : Parser DecodeError := fun b pos =>
  match seqP readByte readNat b pos with
  | .ok ((c, v), p) =>
    match errOf c v with
    | some e => .ok (e, p)
    | none => .error (.badTag c.toNat)
  | .error e => .error e

theorem readErr_complete : Complete readErr encErr (fun _ => True) := by
  intro b pos e rest hpos _ h
  have e1 := seqP_complete readByte_complete readNat_complete b pos ((errCode e).1, (errCode e).2) rest hpos
    ⟨trivial, trivial⟩ (by simpa [encErr] using h)
  simp only [readErr, e1]
  cases e <;> simp [errOf, errCode, encErr]

/-! ## Notices -/

def encOptRep : Option ReplicaId → List UInt8
  | none => [0]
  | some r => 1 :: encRep r

def readOptRep : Parser (Option ReplicaId) := fun b pos =>
  match readByte b pos with
  | .ok (x, p) => if x = 0 then .ok (none, p) else if x = 1 then mapP some readRep b p else .error (.badTag x.toNat)
  | .error e => .error e

theorem readOptRep_complete : Complete readOptRep encOptRep (fun _ => True) := by
  intro b pos o rest hpos _ h
  cases o with
  | none =>
    have e1 := readByte_complete b pos 0 rest hpos trivial (by simpa [encOptRep] using h)
    simp [readOptRep, e1, encOptRep]
  | some r =>
    have h' : bytesFrom b pos = [1] ++ (encRep r ++ rest) := by simpa [encOptRep] using h
    have e1 := readByte_complete b pos 1 _ hpos trivial h'
    have e2 := readRep_complete b _ r rest (le_size_of_bytesFrom hpos h') trivial (bytesFrom_skip h')
    simp only [List.length_singleton] at e1 e2
    simp only [readOptRep, e1, mapP_of_ok e2]
    simp [encOptRep]; omega

/-- Notices: 0 indexChanged · 1 blobsChanged · 2 peerStatus peer status:u8 optReplica ·
3 peerClosed peer reason:u8 byPeer:bool · 4 peerLeft peer · 5 peerError peer err ·
6 rollbackDetected · 7 opRejected str · 8 badEvent err · 9 startupFailed err ·
10 notInitialized · 11 alreadyInitialized · 12 pendingSummary fetching queued waiting (nats).
`err` = code:u8 value:nat (0 truncated, 1 trailing, 2 tooLarge, 3 badVersion v, 4 badKind k,
5 badTag t, 6 nonCanonical, 7 badUtf8); `optReplica` = 00 | 01 replica. -/
def encNotice : Notice → List UInt8
  | .indexChanged => [0]
  | .blobsChanged => [1]
  | .peerStatus p s r => 2 :: (encPeer p ++ [statusByte s] ++ encOptRep r)
  | .peerClosed p r b => 3 :: (encPeer p ++ [reasonByte r] ++ encBool b)
  | .peerLeft p => 4 :: encPeer p
  | .peerError p e => 5 :: (encPeer p ++ encErr e)
  | .rollbackDetected => [6]
  | .opRejected why => 7 :: encStr why
  | .badEvent e => 8 :: encErr e
  | .startupFailed e => 9 :: encErr e
  | .notInitialized => [10]
  | .alreadyInitialized => [11]
  | .pendingSummary f q w => 12 :: (encVar f ++ encVar q ++ encVar w)

def wNotice (acc : ByteArray) : Notice → ByteArray
  | .indexChanged => acc.push 0
  | .blobsChanged => acc.push 1
  | .peerStatus p s r =>
    let a := (wPeer (acc.push 2) p).push (statusByte s)
    match r with
    | none => a.push 0
    | some r => wReplica (a.push 1) r
  | .peerClosed p r byPeer => wBool ((wPeer (acc.push 3) p).push (reasonByte r)) byPeer
  | .peerLeft p => wPeer (acc.push 4) p
  | .peerError p e => wErr (wPeer (acc.push 5) p) e
  | .rollbackDetected => acc.push 6
  | .opRejected why => wStr (acc.push 7) why
  | .badEvent e => wErr (acc.push 8) e
  | .startupFailed e => wErr (acc.push 9) e
  | .notInitialized => acc.push 10
  | .alreadyInitialized => acc.push 11
  | .pendingSummary f q w => wVar (wVar (wVar (acc.push 12) f) q) w

theorem wNotice_toList (acc : ByteArray) (n : Notice) :
    (wNotice acc n).data.toList = acc.data.toList ++ encNotice n := by
  cases n with
  | peerStatus p s r =>
    cases r <;> simp [wNotice, encNotice, encOptRep, push_toList, wPeer_toList, wReplica_toList]
  | _ => simp [wNotice, encNotice, push_toList, wPeer_toList, wReplica_toList, wBool_toList, wErr_toList,
      wStr_toList, wVar_toList]

def readNotice : Parser Notice := fun b pos =>
  match readByte b pos with
  | .error e => .error e
  | .ok (t, p1) =>
    if t = 0 then .ok (.indexChanged, p1)
    else if t = 1 then .ok (.blobsChanged, p1)
    else if t = 2 then mapP (fun z => .peerStatus z.1 z.2.1 z.2.2) (seqP readPeer (seqP readStatus readOptRep)) b p1
    else if t = 3 then mapP (fun z => .peerClosed z.1 z.2.1 z.2.2) (seqP readPeer (seqP readReason readBool)) b p1
    else if t = 4 then mapP .peerLeft readPeer b p1
    else if t = 5 then mapP (fun z => .peerError z.1 z.2) (seqP readPeer readErr) b p1
    else if t = 6 then .ok (.rollbackDetected, p1)
    else if t = 7 then mapP .opRejected readStrE b p1
    else if t = 8 then mapP .badEvent readErr b p1
    else if t = 9 then mapP .startupFailed readErr b p1
    else if t = 10 then .ok (.notInitialized, p1)
    else if t = 11 then .ok (.alreadyInitialized, p1)
    else if t = 12 then mapP (fun z => .pendingSummary z.1 z.2.1 z.2.2) (seqP readNat (seqP readNat readNat)) b p1
    else .error (.badTag t.toNat)

/-- Read a tag byte `t` known to be at `pos`. -/
theorem tag_at {b : ByteArray} {pos : Nat} {t : UInt8} {l rest : List UInt8} (hpos : pos ≤ b.size)
    (h : bytesFrom b pos = t :: (l ++ rest)) :
    readByte b pos = .ok (t, pos + 1) ∧ bytesFrom b (pos + 1) = l ++ rest ∧ pos + 1 ≤ b.size := by
  obtain ⟨hlt, hx, hr⟩ := bytesFrom_cons h
  exact ⟨by simp [readByte, hlt, hx], hr, hlt⟩

theorem readNotice_complete : Complete readNotice encNotice (fun _ => True) := by
  intro b pos n rest hpos _ h
  cases n with
  | indexChanged =>
    obtain ⟨e0, -, -⟩ := tag_at (l := []) hpos (by simpa [encNotice] using h)
    simp [readNotice, e0, encNotice]
  | blobsChanged =>
    obtain ⟨e0, -, -⟩ := tag_at (l := []) hpos (by simpa [encNotice] using h)
    simp [readNotice, e0, encNotice]
  | peerStatus p s r =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encNotice] using h)
    have e1 := seqP_complete readPeer_complete (seqP_complete readStatus_complete readOptRep_complete)
      b (pos + 1) (p, s, r) rest hp1 ⟨trivial, trivial, trivial⟩ (by rw [h1]; simp)
    simp only [readNotice, e0, mapP_of_ok e1]
    simp [encNotice]; omega
  | peerClosed p r x =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encNotice] using h)
    have e1 := seqP_complete readPeer_complete (seqP_complete readReason_complete readBool_complete)
      b (pos + 1) (p, r, x) rest hp1 ⟨trivial, trivial, trivial⟩ (by rw [h1]; simp)
    simp only [readNotice, e0, mapP_of_ok e1]
    simp [encNotice]; omega
  | peerLeft p =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encNotice] using h)
    have e1 := readPeer_complete b (pos + 1) p rest hp1 trivial h1
    simp only [readNotice, e0, mapP_of_ok e1]
    simp [encNotice]; omega
  | peerError p e =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encNotice] using h)
    have e1 := seqP_complete readPeer_complete readErr_complete b (pos + 1) (p, e) rest hp1
      ⟨trivial, trivial⟩ (by rw [h1]; simp)
    simp only [readNotice, e0, mapP_of_ok e1]
    simp [encNotice]; omega
  | rollbackDetected =>
    obtain ⟨e0, -, -⟩ := tag_at (l := []) hpos (by simpa [encNotice] using h)
    simp [readNotice, e0, encNotice]
  | opRejected why =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encNotice] using h)
    have e1 := readStrE_complete b (pos + 1) why rest hp1 trivial h1
    simp only [readNotice, e0, mapP_of_ok e1]
    simp [encNotice]; omega
  | badEvent e =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encNotice] using h)
    have e1 := readErr_complete b (pos + 1) e rest hp1 trivial h1
    simp only [readNotice, e0, mapP_of_ok e1]
    simp [encNotice]; omega
  | startupFailed e =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encNotice] using h)
    have e1 := readErr_complete b (pos + 1) e rest hp1 trivial h1
    simp only [readNotice, e0, mapP_of_ok e1]
    simp [encNotice]; omega
  | notInitialized =>
    obtain ⟨e0, -, -⟩ := tag_at (l := []) hpos (by simpa [encNotice] using h)
    simp [readNotice, e0, encNotice]
  | alreadyInitialized =>
    obtain ⟨e0, -, -⟩ := tag_at (l := []) hpos (by simpa [encNotice] using h)
    simp [readNotice, e0, encNotice]
  | pendingSummary f q w =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encNotice] using h)
    have e1 := seqP_complete readNat_complete (seqP_complete readNat_complete readNat_complete)
      b (pos + 1) (f, q, w) rest hp1 ⟨trivial, trivial, trivial⟩ (by rw [h1]; simp)
    simp only [readNotice, e0, mapP_of_ok e1]
    simp [encNotice]; omega

/-! ## Replies -/

def encVer (v : VersionInfo) : List UInt8 := encHashE v.hash ++ encBool v.present
def encFile (f : String × List VersionInfo) : List UInt8 := encStr f.1 ++ encList encVer f.2
def encPend : PendingStatus → List UInt8
  | .waiting => [0]
  | .requested p => 1 :: encPeer p
  | .queued => [2]
def encPendItem (x : Hash × PendingStatus) : List UInt8 := encHashE x.1 ++ encPend x.2
def encPeerStat (x : PeerId × PeerStatus) : List UInt8 := encPeer x.1 ++ [statusByte x.2]

/-- Replies: 0 snapshot k {path:str m {hash present:bool}^m}^k ·
1 pending k {hash (00 waiting | 01 peer requested | 02 queued)}^k ·
2 status persistInFlight:bool dirty:bool rollback:bool k {peer status:u8}^k. -/
def encReply : Reply → List UInt8
  | .snapshot files => 0 :: encList encFile files
  | .pending items => 1 :: encList encPendItem items
  | .status pf d rb peers => 2 :: (encBool pf ++ encBool d ++ encBool rb ++ encList encPeerStat peers)

def wVer (a : ByteArray) (v : VersionInfo) : ByteArray := wBool (wHash a v.hash) v.present
def wFile (a : ByteArray) (f : String × List VersionInfo) : ByteArray := wList wVer (wStr a f.1) f.2
def wPendItem (a : ByteArray) (x : Hash × PendingStatus) : ByteArray :=
  match x.2 with
  | .waiting => (wHash a x.1).push 0
  | .requested p => wPeer ((wHash a x.1).push 1) p
  | .queued => (wHash a x.1).push 2
def wPeerStat (a : ByteArray) (x : PeerId × PeerStatus) : ByteArray := (wPeer a x.1).push (statusByte x.2)

def wReply (acc : ByteArray) : Reply → ByteArray
  | .snapshot files => wList wFile (acc.push 0) files
  | .pending items => wList wPendItem (acc.push 1) items
  | .status pf d rb peers => wList wPeerStat (wBool (wBool (wBool (acc.push 2) pf) d) rb) peers

theorem wVer_toList (a : ByteArray) (v : VersionInfo) : (wVer a v).data.toList = a.data.toList ++ encVer v := by
  simp [wVer, wBool_toList, wHash_toList, encVer]
theorem wFile_toList (a : ByteArray) (f : String × List VersionInfo) :
    (wFile a f).data.toList = a.data.toList ++ encFile f := by
  simp [wFile, wList_toList wVer encVer wVer_toList, wStr_toList, encFile]
theorem wPendItem_toList (a : ByteArray) (x : Hash × PendingStatus) :
    (wPendItem a x).data.toList = a.data.toList ++ encPendItem x := by
  obtain ⟨h, st⟩ := x
  cases st <;> simp [wPendItem, push_toList, wHash_toList, wPeer_toList, encPendItem, encPend]
theorem wPeerStat_toList (a : ByteArray) (x : PeerId × PeerStatus) :
    (wPeerStat a x).data.toList = a.data.toList ++ encPeerStat x := by
  simp [wPeerStat, push_toList, wPeer_toList, encPeerStat]
theorem wReply_toList (acc : ByteArray) (r : Reply) :
    (wReply acc r).data.toList = acc.data.toList ++ encReply r := by
  cases r <;> simp [wReply, encReply, push_toList, wBool_toList, wList_toList wFile encFile wFile_toList,
    wList_toList wPendItem encPendItem wPendItem_toList, wList_toList wPeerStat encPeerStat wPeerStat_toList]

def readVer : Parser VersionInfo := mapP (fun z => ⟨z.1, z.2⟩) (seqP readHashE readBool)
def readFile : Parser (String × List VersionInfo) := seqP readStrE (readList readVer)
def readPend : Parser PendingStatus := fun b pos =>
  match readByte b pos with
  | .ok (x, p) =>
    if x = 0 then .ok (.waiting, p) else if x = 1 then mapP .requested readPeer b p
    else if x = 2 then .ok (.queued, p) else .error (.badTag x.toNat)
  | .error e => .error e
def readPendItem : Parser (Hash × PendingStatus) := seqP readHashE readPend
def readPeerStat : Parser (PeerId × PeerStatus) := seqP readPeer readStatus

theorem readVer_complete : Complete readVer encVer (fun _ => True) := by
  intro b pos v rest hpos _ h
  have e := seqP_complete readHashE_complete readBool_complete b pos (v.hash, v.present) rest hpos
    ⟨trivial, trivial⟩ (by simpa [encVer] using h)
  simpa [readVer, encVer] using mapP_of_ok (f := fun z => (⟨z.1, z.2⟩ : VersionInfo)) e

theorem readFile_complete : Complete readFile encFile (fun _ => True) :=
  fun b pos f rest hpos _ h => seqP_complete readStrE_complete (readList_complete readVer_complete)
    b pos f rest hpos ⟨trivial, fun _ _ => trivial⟩ h

theorem readPend_complete : Complete readPend encPend (fun _ => True) := by
  intro b pos st rest hpos _ h
  cases st with
  | waiting =>
    obtain ⟨e0, -, -⟩ := tag_at (l := []) hpos (by simpa [encPend] using h)
    simp [readPend, e0, encPend]
  | queued =>
    obtain ⟨e0, -, -⟩ := tag_at (l := []) hpos (by simpa [encPend] using h)
    simp [readPend, e0, encPend]
  | requested p =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encPend] using h)
    have e1 := readPeer_complete b (pos + 1) p rest hp1 trivial h1
    simp only [readPend, e0, mapP_of_ok e1]
    simp [encPend]; omega

theorem readPendItem_complete : Complete readPendItem encPendItem (fun _ => True) :=
  fun b pos x rest hpos _ h => seqP_complete readHashE_complete readPend_complete b pos x rest hpos
    ⟨trivial, trivial⟩ h

theorem readPeerStat_complete : Complete readPeerStat encPeerStat (fun _ => True) :=
  fun b pos x rest hpos _ h => seqP_complete readPeer_complete readStatus_complete b pos x rest hpos
    ⟨trivial, trivial⟩ h

def readReply : Parser Reply := fun b pos =>
  match readByte b pos with
  | .error e => .error e
  | .ok (t, p1) =>
    if t = 0 then mapP .snapshot (readList readFile) b p1
    else if t = 1 then mapP .pending (readList readPendItem) b p1
    else if t = 2 then mapP (fun z => .status z.1 z.2.1 z.2.2.1 z.2.2.2)
      (seqP readBool (seqP readBool (seqP readBool (readList readPeerStat)))) b p1
    else .error (.badTag t.toNat)

theorem readReply_complete : Complete readReply encReply (fun _ => True) := by
  intro b pos r rest hpos _ h
  cases r with
  | snapshot files =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encReply] using h)
    have e1 := readList_complete readFile_complete b (pos + 1) files rest hp1 (fun _ _ => trivial) h1
    simp only [readReply, e0, mapP_of_ok e1]
    simp [encReply]; omega
  | pending items =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encReply] using h)
    have e1 := readList_complete readPendItem_complete b (pos + 1) items rest hp1 (fun _ _ => trivial) h1
    simp only [readReply, e0, mapP_of_ok e1]
    simp [encReply]; omega
  | status pf d rb peers =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encReply] using h)
    have e1 := seqP_complete readBool_complete (seqP_complete readBool_complete
      (seqP_complete readBool_complete (readList_complete readPeerStat_complete)))
      b (pos + 1) (pf, d, rb, peers) rest hp1 ⟨trivial, trivial, trivial, fun _ _ => trivial⟩
      (by rw [h1]; simp)
    simp only [readReply, e0, mapP_of_ok e1]
    simp [encReply]; omega

/-! ## Effects -/

/-- What the effects codec needs from an effect: its embedded peer message or state is well formed
for the wire (so that it decodes back). -/
def EffOk : Effect → Prop
  | .send _ m => m.WireOk
  | .persist _ s => s.WireOk
  | .fetch _ hs => HashBatchOk hs
  | _ => True

def encEffect : Effect → List UInt8
  | .send p m => 0 :: (encPeer p ++ encLen (encodeMessage m))
  | .close p r => 1 :: (encPeer p ++ [reasonByte r])
  | .persist t s => 2 :: (encVar t ++ encLen (encodeState s))
  | .fetch p hs => 3 :: (encPeer p ++ encList encHashE hs ++ encLen (encodeMessage (.want hs)))
  | .serveBlob p h => 4 :: (encPeer p ++ encHashE h)
  | .notify n => 5 :: encNotice n
  | .reply r => 6 :: encReply r

def wEffect (acc : ByteArray) : Effect → ByteArray
  | .send p m => wLen (wPeer (acc.push 0) p) (encodeMessage m)
  | .close p r => (wPeer (acc.push 1) p).push (reasonByte r)
  | .persist t s => wLen (wVar (acc.push 2) t) (encodeState s)
  | .fetch p hs => wLen (wHashes (wPeer (acc.push 3) p) hs) (encodeMessage (.want hs))
  | .serveBlob p h => wHash (wPeer (acc.push 4) p) h
  | .notify n => wNotice (acc.push 5) n
  | .reply r => wReply (acc.push 6) r

theorem wEffect_toList (acc : ByteArray) (e : Effect) :
    (wEffect acc e).data.toList = acc.data.toList ++ encEffect e := by
  cases e <;> simp [wEffect, encEffect, push_toList, wLen_toList, wPeer_toList, wVar_toList, wHashes_toList,
    wHash_toList, wNotice_toList, wReply_toList]

def readEmbMsg : Parser Message := fun b pos =>
  match readLen b pos with
  | .ok (x, p) =>
    match decodeMessage x with
    | .ok m => .ok (m, p)
    | .error e => .error e
  | .error e => .error e

theorem readEmbMsg_complete : Complete readEmbMsg (fun m => encLen (encodeMessage m)) Message.WireOk := by
  intro b pos m rest hpos hm h
  have e1 := readLen_complete b pos _ rest hpos trivial h
  have := decodeMessage_encodeMessage' m hm (size_encodeMessage_le m hm)
  simp only [readEmbMsg, e1, this]

def readEmbState : Parser State := fun b pos =>
  match readLen b pos with
  | .ok (x, p) =>
    match decodeState x with
    | .ok s => .ok (s, p)
    | .error e => .error e
  | .error e => .error e

theorem readEmbState_complete : Complete readEmbState (fun s => encLen (encodeState s)) State.WireOk := by
  intro b pos s rest hpos hs h
  have e1 := readLen_complete b pos _ rest hpos trivial h
  simp only [readEmbState, e1, decodeState_encodeState' s hs]

def readFetch : Parser Effect := fun b pos =>
  match seqP readPeer (seqP (readList readHashE) readEmbMsg) b pos with
  | .ok ((p, hs, m), q) =>
    match m with
    | .want hs' => if hs' == hs then .ok (.fetch p hs, q) else .error .nonCanonical
    | _ => .error .nonCanonical
  | .error e => .error e

def readEffect : Parser Effect := fun b pos =>
  match readByte b pos with
  | .error e => .error e
  | .ok (t, p1) =>
    if t = 0 then mapP (fun z => .send z.1 z.2) (seqP readPeer readEmbMsg) b p1
    else if t = 1 then mapP (fun z => .close z.1 z.2) (seqP readPeer readReason) b p1
    else if t = 2 then mapP (fun z => .persist z.1 z.2) (seqP readNat readEmbState) b p1
    else if t = 3 then readFetch b p1
    else if t = 4 then mapP (fun z => .serveBlob z.1 z.2) (seqP readPeer readHashE) b p1
    else if t = 5 then mapP .notify readNotice b p1
    else if t = 6 then mapP .reply readReply b p1
    else .error (.badTag t.toNat)

theorem readEffect_complete : Complete readEffect encEffect EffOk := by
  intro b pos e rest hpos he h
  cases e with
  | send p m =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encEffect] using h)
    have e1 := seqP_complete readPeer_complete readEmbMsg_complete b (pos + 1) (p, m) rest hp1
      ⟨trivial, he⟩ (by rw [h1]; simp)
    simp only [readEffect, e0, mapP_of_ok e1]
    simp [encEffect]; omega
  | close p r =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encEffect] using h)
    have e1 := seqP_complete readPeer_complete readReason_complete b (pos + 1) (p, r) rest hp1
      ⟨trivial, trivial⟩ (by rw [h1]; simp)
    simp only [readEffect, e0, mapP_of_ok e1]
    simp [encEffect]; omega
  | persist t s =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encEffect] using h)
    have e1 := seqP_complete readNat_complete readEmbState_complete b (pos + 1) (t, s) rest hp1
      ⟨trivial, he⟩ (by rw [h1]; simp)
    simp only [readEffect, e0, mapP_of_ok e1]
    simp [encEffect]; omega
  | fetch p hs =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encEffect] using h)
    have e1 := seqP_complete readPeer_complete (seqP_complete (readList_complete readHashE_complete)
      readEmbMsg_complete) b (pos + 1) (p, hs, .want hs) rest hp1
      ⟨trivial, fun _ _ => trivial, he⟩ (by rw [h1]; simp)
    simp only [readEffect, e0, readFetch, e1, beq_self_eq_true, ite_true]
    simp [encEffect]; omega
  | serveBlob p x =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encEffect] using h)
    have e1 := seqP_complete readPeer_complete readHashE_complete b (pos + 1) (p, x) rest hp1
      ⟨trivial, trivial⟩ (by rw [h1]; simp)
    simp only [readEffect, e0, mapP_of_ok e1]
    simp [encEffect]; omega
  | notify n =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encEffect] using h)
    have e1 := readNotice_complete b (pos + 1) n rest hp1 trivial h1
    simp only [readEffect, e0, mapP_of_ok e1]
    simp [encEffect]; omega
  | reply r =>
    obtain ⟨e0, h1, hp1⟩ := tag_at hpos (by simpa [encEffect] using h)
    have e1 := readReply_complete b (pos + 1) r rest hp1 trivial h1
    simp only [readEffect, e0, mapP_of_ok e1]
    simp [encEffect]; omega

/-! ## Effect lists, with state payloads de-duplicated -/

/-- The last state message written in full is this one (equal digest and equal state). -/
def sameState (last : Option (Digest × State)) (d : Digest) (s : State) : Bool :=
  match last with
  | some (d', s') => d == d' && State.beq s s'
  | none => false

/-- `e` sends the same state message as the last one written in full. -/
def isRepeat (last : Option (Digest × State)) : Effect → Bool
  | .send _ (.state d s) => sameState last d s
  | _ => false

/-- The last state message written in full, after writing `e` in full. -/
def nextLast (last : Option (Digest × State)) : Effect → Option (Digest × State)
  | .send _ (.state d s) => some (d, s)
  | _ => last

def peerOf : Effect → PeerId
  | .send p _ => p
  | _ => ⟨0⟩

theorem isRepeat_spec {last : Option (Digest × State)} {e : Effect} (h : isRepeat last e = true) :
    ∃ p d s, e = .send p (.state d s) ∧ last = some (d, s) := by
  cases e with
  | send p m =>
    cases m with
    | state d s =>
      cases last with
      | none => simp [isRepeat, sameState] at h
      | some ds =>
        obtain ⟨d', s'⟩ := ds
        simp only [isRepeat, sameState, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, hb⟩ := h
        rw [State.eq_of_beq' hb]
        exact ⟨p, d, s', rfl, rfl⟩
    | _ => simp [isRepeat] at h
  | _ => simp [isRepeat] at h

def encEffs : Option (Digest × State) → List Effect → List UInt8
  | _, [] => []
  | last, e :: es =>
    if isRepeat last e then (7 :: encPeer (peerOf e)) ++ encEffs last es
    else encEffect e ++ encEffs (nextLast last e) es

/-- The writer: a loop over the effects. -/
def wEffs (acc : ByteArray) (last : Option (Digest × State)) : List Effect → ByteArray
  | [] => acc
  | e :: es =>
    if isRepeat last e then wEffs (wPeer (acc.push 7) (peerOf e)) last es
    else wEffs (wEffect acc e) (nextLast last e) es

theorem wEffs_toList : ∀ (acc : ByteArray) (last : Option (Digest × State)) (effs : List Effect),
    (wEffs acc last effs).data.toList = acc.data.toList ++ encEffs last effs
  | acc, last, [] => by simp [wEffs, encEffs]
  | acc, last, e :: es => by
    unfold wEffs encEffs
    split
    · rw [wEffs_toList]; simp [wPeer_toList, push_toList]
    · rw [wEffs_toList, wEffect_toList]; simp

def encodeEffects (effs : List Effect) : ByteArray :=
  wEffs (wVar ((ByteArray.empty.push wireVersion).push kindEffects) effs.length) none effs

theorem encodeEffects_toList (effs : List Effect) :
    (encodeEffects effs).data.toList = [wireVersion, kindEffects] ++ encVar effs.length ++ encEffs none effs := by
  simp [encodeEffects, wEffs_toList, wVar_toList, push_toList]

/-- The decoding loop: `sendAgain` repeats the last state message written in full. -/
def effsGo (b : ByteArray) : Nat → Nat → Option (Digest × State) → List Effect →
    Except DecodeError (List Effect × Nat)
  | 0, pos, _, acc => .ok (acc.reverse, pos)
  | k + 1, pos, last, acc =>
    match readByte b pos with
    | .error e => .error e
    | .ok (t, p1) =>
      if t = 7 then
        match readPeer b p1 with
        | .error e => .error e
        | .ok (p, p2) =>
          match last with
          | some (d, s) => effsGo b k p2 last (.send p (.state d s) :: acc)
          | none => .error .nonCanonical
      else
        match readEffect b pos with
        | .error e => .error e
        | .ok (e, p2) => effsGo b k p2 (nextLast last e) (e :: acc)

theorem encEffect_head (e : Effect) : ∃ t rest, encEffect e = t :: rest ∧ t ≠ 7 := by
  cases e <;> simp [encEffect]

theorem effsGo_complete (b : ByteArray) : ∀ (effs : List Effect) (pos : Nat) (last : Option (Digest × State))
    (acc : List Effect) (rest : List UInt8), pos ≤ b.size → (∀ e ∈ effs, EffOk e) →
    bytesFrom b pos = encEffs last effs ++ rest →
    effsGo b effs.length pos last acc = .ok (acc.reverse ++ effs, pos + (encEffs last effs).length)
  | [], pos, last, acc, rest, _, _, _ => by simp [effsGo, encEffs]
  | e :: es, pos, last, acc, rest, hpos, hok, h => by
    have hoks : ∀ x ∈ es, EffOk x := fun x hx => hok x (.tail _ hx)
    unfold encEffs at h ⊢
    split
    · next hrep =>
      rw [ite_eq_left hrep, List.append_assoc] at h
      obtain ⟨p, d, s, rfl, rfl⟩ := isRepeat_spec hrep
      have hbt : bytesFrom b pos = 7 :: (encPeer p ++ (encEffs (some (d, s)) es ++ rest)) := by
        rw [h]; rfl
      obtain ⟨e0, h1, hp1⟩ := tag_at hpos hbt
      have e1 := readPeer_complete b (pos + 1) p _ hp1 trivial h1
      have h2 := bytesFrom_skip h1
      have hp2 := le_size_of_bytesFrom hp1 h1
      simp only [List.length_cons, effsGo, e0, ite_true, e1]
      rw [effsGo_complete b es _ (some (d, s)) _ rest hp2 hoks h2]
      simp [peerOf]; omega
    · next hrep =>
      rw [ite_eq_right hrep, List.append_assoc] at h
      obtain ⟨t, r0, het, ht7⟩ := encEffect_head e
      have hbt : bytesFrom b pos = t :: (r0 ++ (encEffs (nextLast last e) es ++ rest)) := by
        rw [h, het]; simp
      obtain ⟨e0, -, -⟩ := tag_at hpos hbt
      have e1 := readEffect_complete b pos e _ hpos (hok e (.head _)) h
      have h2 := bytesFrom_skip h
      have hp2 := le_size_of_bytesFrom hpos h
      simp only [List.length_cons, effsGo, e0, ht7, ite_false, e1]
      rw [effsGo_complete b es _ (nextLast last e) (e :: acc) rest hp2 hoks h2]
      simp; omega

/-- Decode an effects envelope (what the JS host does; here for tests and the round-trip proof).
No total size limit: this is Lean's own, trusted output (see the module comment). -/
def decodeEffects (b : ByteArray) : Except DecodeError (List Effect) :=
  match readWithHeader kindEffects readNat b 0 with
  | .error e => .error e
  | .ok (k, p) =>
    match effsGo b k p none [] with
    | .error e => .error e
    | .ok (effs, q) => if q = b.size then .ok effs else .error .trailing

/-- **Round trip for the effects envelope**: every effect list whose sends, fetches and persists
are well formed decodes back to itself. -/
theorem decodeEffects_encodeEffects (effs : List Effect) (h : ∀ e ∈ effs, EffOk e) :
    decodeEffects (encodeEffects effs) = .ok effs := by
  let b := encodeEffects effs
  have hb : bytesFrom b 0 = ([wireVersion, kindEffects] ++ encVar effs.length) ++ (encEffs none effs ++ []) := by
    rw [bytesFrom_zero, encodeEffects_toList, List.append_nil]
  have e1 := readWithHeader_complete (kind := kindEffects) readNat_complete b 0 effs.length _ (Nat.zero_le _) trivial
    (by rw [hb])
  have h2 := bytesFrom_skip hb
  have hp2 := le_size_of_bytesFrom (Nat.zero_le _) hb
  have e2 := effsGo_complete b effs _ none [] [] hp2 h h2
  have hsz : b.size = ([wireVersion, kindEffects] ++ encVar effs.length ++ encEffs none effs).length := by
    rw [← ByteArray.size_data, ← Array.length_toList, encodeEffects_toList]
  unfold decodeEffects
  rw [show (encodeEffects effs) = b from rfl, e1]
  simp only
  rw [e2]
  simp [hsz]; omega

end LeanSync
