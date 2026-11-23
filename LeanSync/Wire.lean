import LeanSync.Bytes

/-!
# Wire format v1: states and peer messages

Executable module (imports `Init` only).

Every top-level value starts with the format version byte (`1`) and a kind byte. Integers are
canonical unsigned LEB128 below 2^64; replica ids are two such integers (`hi`, `lo`); hashes and
digests are exactly 32 bytes; strings are a varint byte length and UTF-8.

```
state    := 01 01 body
body     := r:varint {hi:varint lo:varint counter:varint≥1}^r      (replica ids strictly increasing)
            n:varint {path:str idx:varint counter:varint hash:32}^n  (entries strictly increasing)
            -- the entry's dot is (ctx[idx].replica, counter) with 1 ≤ counter ≤ ctx[idx].counter
message  := 01 02 tag:u8 ...
            0 hello maxVersion:u8 hi:varint lo:varint digest:32   1 digest digest:32
            2 state digest:32 body                                3 want / 4 noBlob / 5 have
            6 bye reason:u8                                         k:varint∈[1,1024] {hash:32}^k ↑
```
(↑ = strictly increasing.) Decoders (`decodeState`, `decodeMessage`) are total, make one
tail-recursive pass over their input, check order only between neighbours, and reject anything
that is not exactly the encoding of the value they return (`Laws`: `encodeState_of_decodeState`).
-/

set_option linter.unusedSectionVars false

namespace LeanSync

open LeanCrdt

/-! ## Limits (part of wire version 1: both sides must agree) -/

def wireVersion : UInt8 := 1
def maxStateBytes : Nat := 64 * 1024 * 1024          -- encoded state, header included
def maxMessageBytes : Nat := maxStateBytes + 64      -- one peer message
def maxEnvelopeBytes : Nat := 2 * maxStateBytes      -- one event in
def maxPathBytes : Nat := 4096                       -- UTF-8 bytes of one path
def maxBatch : Nat := 1024                           -- hashes in one want/noBlob/have
def maxSessions : Nat := 32
def maxInflightPerPeer : Nat := 32                   -- outstanding blob requests per session
def maxToldNo : Nat := 4096                          -- remembered `noBlob` answers per session

/-! ## Kinds (second byte of every top-level value) -/

def kindState : UInt8 := 1
def kindMessage : UInt8 := 2
def kindEvent : UInt8 := 3
def kindEffects : UInt8 := 4

/-! ## Headers -/

/-- Read `[wireVersion, kind]`, then `p`. -/
def readWithHeader {α} (kind : UInt8) (p : Parser α) : Parser α := fun b pos =>
  match expectByte wireVersion .badVersion b pos with
  | .error e => .error e
  | .ok (_, p1) =>
    match expectByte kind .badKind b p1 with
    | .error e => .error e
    | .ok (_, p2) => p b p2

theorem readWithHeader_sound {α} {kind : UInt8} {p : Parser α} {enc : α → List UInt8} {Q : α → Prop}
    (hp : Sound p enc Q) : Sound (readWithHeader kind p) (fun x => [wireVersion, kind] ++ enc x) Q := by
  intro b pos x pos' h
  unfold readWithHeader at h
  split at h
  · cases h
  · next u p1 h1 =>
    split at h
    · cases h
    · next v p2 h2 =>
      obtain ⟨-, hp1, hb1⟩ := expectByte_sound _ _ b pos u p1 h1
      obtain ⟨-, hp2, hb2⟩ := expectByte_sound _ _ b p1 v p2 h2
      obtain ⟨hq, hp3, hb3⟩ := hp b p2 x pos' h
      refine ⟨hq, ?_, ?_⟩
      · simp at hp1 hp2; simp [hp3, hp2, hp1]; omega
      · rw [hb1, hb2, hb3]; rfl

theorem readWithHeader_complete {α} {kind : UInt8} {p : Parser α} {enc : α → List UInt8}
    {ok : α → Prop} (hp : Complete p enc ok) :
    Complete (readWithHeader kind p) (fun x => [wireVersion, kind] ++ enc x) ok := by
  intro b pos x rest hpos hx h
  have h1 : bytesFrom b pos = [wireVersion] ++ ([kind] ++ (enc x ++ rest)) := by rw [h]; rfl
  have e1 := expectByte_complete wireVersion .badVersion b pos () _ hpos trivial h1
  have h2 := bytesFrom_skip h1
  have hpos2 := le_size_of_bytesFrom hpos h1
  have e2 := expectByte_complete kind .badKind b _ () _ hpos2 trivial h2
  have h3 := bytesFrom_skip h2
  have hpos3 := le_size_of_bytesFrom hpos2 h2
  have e3 := hp b _ x rest hpos3 hx h3
  simp only [List.length_singleton] at e1 e2 e3
  simp only [readWithHeader, e1, e2, e3, List.length_append]
  congr 2; simp only [List.length_cons, List.length_nil]; omega

/-- Whole-input decoding: size limit first, then the parser must consume everything. -/
def decodeTop {α} (p : Parser α) (maxLen : Nat) (b : ByteArray) : Except DecodeError α :=
  if b.size ≤ maxLen then
    match p b 0 with
    | .ok (x, pos) => if pos = b.size then .ok x else .error .trailing
    | .error e => .error e
  else .error .tooLarge

theorem decodeTop_sound {α} {p : Parser α} {enc : α → List UInt8} {Q : α → Prop}
    (hp : Sound p enc Q) {maxLen : Nat} {b : ByteArray} {x : α} (h : decodeTop p maxLen b = .ok x) :
    Q x ∧ b.data.toList = enc x ∧ b.size ≤ maxLen := by
  unfold decodeTop at h
  split at h
  · next hle =>
    split at h
    · next y pos hy =>
      split at h
      · next hend =>
        simp only [Except.ok.injEq] at h
        subst h
        obtain ⟨hq, -, hb⟩ := hp b 0 y pos hy
        rw [hend, bytesFrom_of_ge (Nat.le_refl _), bytesFrom_zero] at hb
        exact ⟨hq, by simpa using hb, hle⟩
      · cases h
    · cases h
  · cases h

theorem decodeTop_complete {α} {p : Parser α} {enc : α → List UInt8} {ok : α → Prop}
    (hp : Complete p enc ok) {maxLen : Nat} {b : ByteArray} {x : α} (hx : ok x)
    (hb : b.data.toList = enc x) (hlen : (enc x).length ≤ maxLen) : decodeTop p maxLen b = .ok x := by
  have hsz : b.size = (enc x).length := by rw [← ByteArray.size_data, ← Array.length_toList, hb]
  have := hp b 0 x [] (Nat.zero_le _) hx (by rw [bytesFrom_zero, hb]; simp)
  unfold decodeTop
  rw [ite_eq_left (by omega), this]
  simp [hsz]

/-! ## Context (version vector) entries -/

def encCtxEntry (p : ReplicaId × Nat) : List UInt8 := encU64 p.1.hi ++ encU64 p.1.lo ++ encVar p.2

def readCtxEntry : Parser (ReplicaId × Nat) := fun b pos =>
  match readU64 b pos with
  | .error e => .error e
  | .ok (hi, p1) =>
    match readU64 b p1 with
    | .error e => .error e
    | .ok (lo, p2) =>
      match readVarint b p2 with
      | .error e => .error e
      | .ok (c, p3) => if 0 < c then .ok ((⟨hi, lo⟩, c), p3) else .error .nonCanonical

def CtxOk (p : ReplicaId × Nat) : Prop := 0 < p.2 ∧ p.2 < varBound

theorem readCtxEntry_sound : Sound readCtxEntry encCtxEntry CtxOk := by
  intro b pos x pos' h
  unfold readCtxEntry at h
  split at h
  · cases h
  · next hi p1 h1 =>
    split at h
    · cases h
    · next lo p2 h2 =>
      split at h
      · cases h
      · next c p3 h3 =>
        split at h
        · next hc =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨-, hp1, hb1⟩ := readU64_sound b pos hi p1 h1
          obtain ⟨-, hp2, hb2⟩ := readU64_sound b p1 lo p2 h2
          obtain ⟨hv, hp3, hb3⟩ := readVarint_sound b p2 c p3 h3
          refine ⟨⟨hc, hv⟩, ?_, ?_⟩
          · simp [encCtxEntry, hp3, hp2, hp1]; omega
          · simp [encCtxEntry, hb1, hb2, hb3]
        · cases h

theorem readCtxEntry_complete : Complete readCtxEntry encCtxEntry CtxOk := by
  intro b pos x rest hpos hx h
  obtain ⟨⟨hi, lo⟩, c⟩ := x
  simp only [encCtxEntry, List.append_assoc] at h
  have e1 := readU64_complete b pos hi _ hpos trivial h
  have h2 := bytesFrom_skip h
  have hpos2 := le_size_of_bytesFrom hpos h
  have e2 := readU64_complete b _ lo _ hpos2 trivial h2
  have h3 := bytesFrom_skip h2
  have hpos3 := le_size_of_bytesFrom hpos2 h2
  have e3 := readVarint_complete b _ c _ hpos3 hx.2 h3
  simp only [readCtxEntry, e1, e2, e3, hx.1, ite_true, encCtxEntry, List.length_append]
  congr 2; omega

/-- Check for strictly increasing replica ids. -/
def chkCtx : Option (ReplicaId × Nat) → (ReplicaId × Nat) → Bool
  | none, _ => true
  | some a, x => compare a.1 x.1 == .lt

/-! ## Entries -/

/-- Position of replica `r` in a context list (tail-recursive). -/
def idxGo (r : ReplicaId) : List (ReplicaId × Nat) → Nat → Nat
  | [], i => i
  | (k, _) :: rest, i => if k = r then i else idxGo r rest (i + 1)

def idxOf (ctx : List (ReplicaId × Nat)) (r : ReplicaId) : Nat := idxGo r ctx 0

theorem idxGo_getElem : ∀ {l : List (ReplicaId × Nat)} (_ : KeySorted l) (i : Nat) (hi : i < l.length)
    (k : Nat), idxGo l[i].1 l k = k + i
  | [], _, i, hi, _ => by simp at hi
  | (k0, n0) :: rest, hs, i, hi, k => by
    cases i with
    | zero => simp [idxGo]
    | succ j =>
      have hj : j < rest.length := by simp at hi; omega
      have hne : k0 ≠ rest[j].1 := by
        intro e
        have := (List.pairwise_cons.1 hs).1 rest[j] (List.getElem_mem hj)
        rw [e] at this; exact cmp_lt_irrefl _ this
      simp only [List.getElem_cons_succ, idxGo, hne, ite_false]
      rw [idxGo_getElem (List.pairwise_cons.1 hs).2 j hj (k + 1)]; omega

theorem idxOf_getElem {l : List (ReplicaId × Nat)} (hs : KeySorted l) (i : Nat) (hi : i < l.length) :
    idxOf l l[i].1 = i := by
  unfold idxOf; rw [idxGo_getElem hs i hi 0]; omega

def encEntry (ctx : List (ReplicaId × Nat)) (e : Entry) : List UInt8 :=
  encStr e.path ++ encVar (idxOf ctx e.dot.replica) ++ encVar e.dot.counter ++ encHash e.hash

def readEntry (arr : Array (ReplicaId × Nat)) : Parser Entry := fun b pos =>
  match readStr maxPathBytes b pos with
  | .error e => .error e
  | .ok (path, p1) =>
    match readVarint b p1 with
    | .error e => .error e
    | .ok (i, p2) =>
      if hi : i < arr.size then
        match readVarint b p2 with
        | .error e => .error e
        | .ok (c, p3) =>
          if 0 < c ∧ c ≤ arr[i].2 then
            match readHash b p3 with
            | .error e => .error e
            | .ok (h, p4) => .ok (⟨path, ⟨arr[i].1, c⟩, h⟩, p4)
          else .error .nonCanonical
      else .error .nonCanonical

/-- What `readEntry` guarantees, and what it needs to read an entry back. -/
def EntryOk (ctx : List (ReplicaId × Nat)) (e : Entry) : Prop :=
  (∃ i, ∃ hi : i < ctx.length, ctx[i].1 = e.dot.replica ∧ 0 < e.dot.counter ∧ e.dot.counter ≤ ctx[i].2) ∧
  e.hash.bytes.size = hashLen ∧ e.path.toByteArray.size ≤ maxPathBytes

theorem readEntry_sound {ctx : List (ReplicaId × Nat)} (hs : KeySorted ctx) :
    Sound (readEntry ctx.toArray) (encEntry ctx) (EntryOk ctx) := by
  intro b pos x pos' h
  unfold readEntry at h
  split at h
  · cases h
  · next path p1 h1 =>
    split at h
    · cases h
    · next i p2 h2 =>
      split at h
      · next hi =>
        split at h
        · cases h
        · next c p3 h3 =>
          split at h
          · next hc =>
            split at h
            · cases h
            · next hh p4 h4 =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hi' : i < ctx.length := by simpa using hi
              obtain ⟨hpq, hp1, hb1⟩ := readStr_sound _ b pos path p1 h1
              obtain ⟨-, hp2, hb2⟩ := readVarint_sound b p1 i p2 h2
              obtain ⟨-, hp3, hb3⟩ := readVarint_sound b p2 c p3 h3
              obtain ⟨hhq, hp4, hb4⟩ := readHash_sound b p3 hh p4 h4
              have hidx : idxOf ctx (ctx.toArray[i]).1 = i := by
                simp only [List.getElem_toArray]; exact idxOf_getElem hs i hi'
              refine ⟨⟨⟨i, hi', by simp, hc.1, by simpa using hc.2⟩, hhq, hpq⟩, ?_, ?_⟩
              · simp only [encEntry, hidx, List.length_append]; omega
              · simp only [encEntry, hidx, List.append_assoc]; rw [hb1, hb2, hb3, hb4]
          · cases h
      · cases h

theorem readEntry_complete {ctx : List (ReplicaId × Nat)} (hs : KeySorted ctx)
    (hb : ∀ p ∈ ctx, p.2 < varBound) (hlen : ctx.length < varBound) :
    Complete (readEntry ctx.toArray) (encEntry ctx) (EntryOk ctx) := by
  intro b pos x rest hpos hx h
  obtain ⟨⟨i, hi, hr, hc0, hc1⟩, hh, hp⟩ := hx
  have hidx : idxOf ctx x.dot.replica = i := by rw [← hr]; exact idxOf_getElem hs i hi
  simp only [encEntry, hidx, List.append_assoc] at h
  have e1 := readStr_complete maxPathBytes (by decide) b pos x.path _ hpos hp h
  have h2 := bytesFrom_skip h
  have hpos2 := le_size_of_bytesFrom hpos h
  have e2 := readVarint_complete b _ i _ hpos2 (by omega) h2
  have h3 := bytesFrom_skip h2
  have hpos3 := le_size_of_bytesFrom hpos2 h2
  have e3 := readVarint_complete b _ x.dot.counter _ hpos3
    (Nat.lt_of_le_of_lt hc1 (hb _ (List.getElem_mem hi))) h3
  have h4 := bytesFrom_skip h3
  have hpos4 := le_size_of_bytesFrom hpos3 h3
  have e4 := readHash_complete b _ x.hash rest hpos4 hh h4
  have hi' : i < ctx.toArray.size := by simpa using hi
  have hc : 0 < x.dot.counter ∧ x.dot.counter ≤ (ctx.toArray[i]).2 := by
    simp only [List.getElem_toArray]; exact ⟨hc0, hc1⟩
  simp only [readEntry, e1, e2, e3, e4, hi', dite_true, hc, and_self, ite_true]
  obtain ⟨path, ⟨r, c⟩, hsh⟩ := x
  simp only [List.getElem_toArray, hr, encEntry, hidx, List.length_append]
  congr 2; omega

/-! ## States -/

def encStateBody (s : State) : List UInt8 :=
  encVar s.context.entries.length ++ s.context.entries.flatMap encCtxEntry ++
    encVar s.entries.length ++ s.entries.flatMap (encEntry s.context.entries)

def encState (s : State) : List UInt8 := [wireVersion, kindState] ++ encStateBody s

theorem ctx_of_manyGo {b : ByteArray} {r p1 : Nat} {ctx : List (ReplicaId × Nat)} {p2 : Nat}
    (h : manyGo readCtxEntry chkCtx b r p1 none [] = .ok (ctx, p2)) :
    KeySorted ctx ∧ (∀ p ∈ ctx, 0 < p.2) := by
  obtain ⟨xs, rfl, -, hch, hq, -, -⟩ := manyGo_sound readCtxEntry_sound chkCtx b r p1 none [] ctx p2 h
  refine ⟨?_, fun p hp => (hq p (by simpa using hp)).1⟩
  exact pairwise_of_chain (R := fun a b => compare a.1 b.1 = .lt)
    (fun _ _ _ h1 h2 => cmp_lt_trans h1 h2) (fun a x h => by simpa [chkCtx] using h) hch

theorem es_of_manyGo {b : ByteArray} {ctx : List (ReplicaId × Nat)} (hs : KeySorted ctx)
    (hpos : ∀ p ∈ ctx, 0 < p.2) {n p3 : Nat} {es : List Entry} {p4 : Nat}
    (h : manyGo (readEntry ctx.toArray) chkLt b n p3 none [] = .ok (es, p4)) :
    StrictlySorted es ∧
      ∀ e ∈ es, 0 < e.dot.counter ∧ e.dot.counter ≤ getL ctx e.dot.replica := by
  obtain ⟨xs, rfl, -, hch, hq, -, -⟩ := manyGo_sound (readEntry_sound hs) chkLt b n p3 none [] es p4 h
  refine ⟨sorted_of_chain hch, fun e he => ?_⟩
  obtain ⟨⟨i, hi, hr, hc0, hc1⟩, -, -⟩ := hq e he
  have hm : ctx[i] ∈ ctx := List.getElem_mem hi
  have := (VersionVector.mem_iff_get hs hpos ctx[i]).1 hm
  rw [← hr, this.2]
  exact ⟨hc0, hc1⟩

/-- Read a state body and rebuild its invariants (sortedness, positive counters, coverage)
from what the parse checked. -/
def readStateBody : Parser State := fun b pos =>
  match readVarint b pos with
  | .error e => .error e
  | .ok (r, p1) =>
    match hc : manyGo readCtxEntry chkCtx b r p1 none [] with
    | .error e => .error e
    | .ok (ctx, p2) =>
      match readVarint b p2 with
      | .error e => .error e
      | .ok (n, p3) =>
        match he : manyGo (readEntry ctx.toArray) chkLt b n p3 none [] with
        | .error e => .error e
        | .ok (es, p4) =>
          .ok (⟨es, ⟨ctx, (ctx_of_manyGo hc).1, (ctx_of_manyGo hc).2⟩,
            (es_of_manyGo (ctx_of_manyGo hc).1 (ctx_of_manyGo hc).2 he).1,
            (es_of_manyGo (ctx_of_manyGo hc).1 (ctx_of_manyGo hc).2 he).2⟩, p4)

/-- Field-level limits of a state (everything in `WireOk` except the total size). -/
def _root_.LeanCrdt.State.FieldsOk (s : State) : Prop :=
  (∀ e ∈ s.entries, e.hash.bytes.size = hashLen ∧ e.path.toByteArray.size ≤ maxPathBytes) ∧
  (∀ p ∈ s.context.entries, p.2 < varBound) ∧
  s.context.entries.length < varBound ∧ s.entries.length < varBound

theorem readStateBody_sound : Sound readStateBody encStateBody State.FieldsOk := by
  intro b pos x pos' h
  unfold readStateBody at h
  split at h
  · cases h
  · next r p1 h1 =>
    split at h
    · cases h
    · next ctx p2 hc =>
      split at h
      · cases h
      · next n p3 h3 =>
        split at h
        · cases h
        · next es p4 he =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hks := (ctx_of_manyGo hc).1
          obtain ⟨hr1, hpr1, hb1⟩ := readVarint_sound b pos r p1 h1
          obtain ⟨cs, hcs, hlc, -, hqc, hpc, hbc⟩ :=
            manyGo_sound readCtxEntry_sound chkCtx b r p1 none [] ctx p2 hc
          simp only [List.reverse_nil, List.nil_append] at hcs; subst hcs
          obtain ⟨hr3, hpr3, hb3⟩ := readVarint_sound b p2 n p3 h3
          obtain ⟨xs, hxs, hle, -, hqe, hpe, hbe⟩ :=
            manyGo_sound (readEntry_sound hks) chkLt b n p3 none [] es p4 he
          simp only [List.reverse_nil, List.nil_append] at hxs; subst hxs
          refine ⟨⟨fun e he => ⟨(hqe e he).2.1, (hqe e he).2.2⟩, fun p hp => (hqc p hp).2,
            by rw [hlc]; exact hr1, by rw [hle]; exact hr3⟩, ?_, ?_⟩
          · simp only [encStateBody, List.length_append, hlc, hle]; omega
          · simp only [encStateBody, List.append_assoc, hlc, hle]
            rw [hb1, hbc, hb3, hbe]

theorem entryOk_of_mem (s : State) (hfe : ∀ e ∈ s.entries, e.hash.bytes.size = hashLen ∧
    e.path.toByteArray.size ≤ maxPathBytes) (e : Entry) (he : e ∈ s.entries) :
    EntryOk s.context.entries e := by
  obtain ⟨hc0, hc1⟩ := s.covered e he
  have hm : (e.dot.replica, getL s.context.entries e.dot.replica) ∈ s.context.entries :=
    (VersionVector.mem_iff_get s.context.sorted s.context.pos _).2
      ⟨by simp only [VersionVector.get] at hc1; omega, rfl⟩
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hm
  refine ⟨⟨i, hi, by rw [hget], hc0, by rw [hget]; exact hc1⟩, (hfe e he).1, (hfe e he).2⟩

theorem readStateBody_complete : Complete readStateBody encStateBody State.FieldsOk := by
  intro b pos s rest hpos hs h
  obtain ⟨hfe, hfc, hlc, hle⟩ := hs
  have hks := s.context.sorted
  have hpz := s.context.pos
  simp only [encStateBody, List.append_assoc] at h
  have e1 := readVarint_complete b pos _ _ hpos hlc h
  have h2 := bytesFrom_skip h
  have hpos2 := le_size_of_bytesFrom hpos h
  have e2 := manyGo_complete readCtxEntry_complete chkCtx b s.context.entries _ none [] _ hpos2
    (chain_of_pairwise (R := fun (a b : ReplicaId × Nat) => compare a.1 b.1 = .lt)
      (fun a x h => by simp [chkCtx, h]) (fun _ _ => rfl) hks)
    (fun p hp => ⟨hpz p hp, hfc p hp⟩) h2
  have h3 := bytesFrom_skip h2
  have hpos3 := le_size_of_bytesFrom hpos2 h2
  have e3 := readVarint_complete b _ _ _ hpos3 hle h3
  have h4 := bytesFrom_skip h3
  have hpos4 := le_size_of_bytesFrom hpos3 h3
  have e4 := manyGo_complete (readEntry_complete hks hfc hlc) chkLt b s.entries _ none [] rest hpos4
    (chain_of_sorted s.sorted) (entryOk_of_mem s hfe) h4
  unfold readStateBody
  simp only [e1]
  split
  · next e hc => rw [e2] at hc; cases hc
  · next ctx p2 hc =>
    rw [e2] at hc
    simp only [List.reverse_nil, List.nil_append, Except.ok.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [e3]
    split
    · next e he => rw [e4] at he; cases he
    · next es p4 he =>
      rw [e4] at he
      simp only [List.reverse_nil, List.nil_append, Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [Except.ok.injEq, Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      simp only [encStateBody, List.length_append]; omega

/-! ## Runtime state encoder -/

def wCtxEntry (acc : ByteArray) (p : ReplicaId × Nat) : ByteArray :=
  wVar (wVar (wVar acc p.1.hi.toNat) p.1.lo.toNat) p.2

theorem wCtxEntry_toList (acc : ByteArray) (p : ReplicaId × Nat) :
    (wCtxEntry acc p).data.toList = acc.data.toList ++ encCtxEntry p := by
  simp [wCtxEntry, wVar_toList, encCtxEntry, encU64]

def wEntry (ctx : List (ReplicaId × Nat)) (acc : ByteArray) (e : Entry) : ByteArray :=
  wBytes (wVar (wVar (wStr acc e.path) (idxOf ctx e.dot.replica)) e.dot.counter) e.hash.bytes

theorem wEntry_toList (ctx : List (ReplicaId × Nat)) (acc : ByteArray) (e : Entry) :
    (wEntry ctx acc e).data.toList = acc.data.toList ++ encEntry ctx e := by
  simp [wEntry, wBytes_toList, wVar_toList, wStr_toList, encEntry, encHash]

/-- Append the state body: two loops (`foldl`), no recursion over the data. Cost: O(n·r) for
n entries and r context entries (the replica index is found by a scan of the context). -/
def wStateBody (acc : ByteArray) (s : State) : ByteArray :=
  let ctx := s.context.entries
  s.entries.foldl (wEntry ctx) (wVar (ctx.foldl wCtxEntry (wVar acc ctx.length)) s.entries.length)

theorem wStateBody_toList (acc : ByteArray) (s : State) :
    (wStateBody acc s).data.toList = acc.data.toList ++ encStateBody s := by
  simp [wStateBody, foldl_toList _ _ (wEntry_toList _), foldl_toList _ _ wCtxEntry_toList,
    wVar_toList, encStateBody]

/-- The canonical encoding of a state (header included). This is the persisted record and the
digest preimage. -/
def encodeState (s : State) : ByteArray :=
  wStateBody ((ByteArray.empty.push wireVersion).push kindState) s

theorem encodeState_toList (s : State) : (encodeState s).data.toList = encState s := by
  rw [encodeState, wStateBody_toList]
  simp [encState, ByteArray.push]

theorem size_encodeState (s : State) : (encodeState s).size = (encState s).length := by
  rw [← ByteArray.size_data, ← Array.length_toList, encodeState_toList]

/-- A hash the protocol accepts: exactly 32 bytes (SHA-256). -/
def _root_.LeanCrdt.Hash.WireOk (h : Hash) : Prop := h.bytes.size = hashLen

/-- A state the wire can carry: 32-byte hashes, paths of at most `maxPathBytes` bytes, counters
below 2^64, and an encoding of at most `maxStateBytes` bytes. (Sortedness, positive counters and
coverage are already fields of `State`; the entry and replica counts are bounded by the size.) -/
def _root_.LeanCrdt.State.WireOk (s : State) : Prop :=
  (∀ e ∈ s.entries, Hash.WireOk e.hash ∧ e.path.toByteArray.size ≤ maxPathBytes) ∧
  (∀ p ∈ s.context.entries, p.2 < varBound) ∧
  (encodeState s).size ≤ maxStateBytes

theorem length_le_flatMap {α} (f : α → List UInt8) (hf : ∀ x, f x ≠ []) :
    ∀ (l : List α), l.length ≤ (l.flatMap f).length
  | [] => by simp
  | x :: xs => by
    have := length_le_flatMap f hf xs
    have hx : 1 ≤ (f x).length := by
      cases h : f x with
      | nil => exact absurd h (hf x)
      | cons _ _ => simp
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

theorem fieldsOk_of_wireOk {s : State} (h : s.WireOk) : s.FieldsOk := by
  obtain ⟨he, hc, hsz⟩ := h
  rw [size_encodeState] at hsz
  have hl1 := length_le_flatMap encCtxEntry (fun x => by simp [encCtxEntry, encU64, encVar_ne_nil]) s.context.entries
  have hl2 := length_le_flatMap (encEntry s.context.entries)
    (fun x => by simp [encEntry, encStr, encVar_ne_nil]) s.entries
  simp only [encState, encStateBody, List.length_append] at hsz
  refine ⟨he, hc, ?_, ?_⟩
  · unfold varBound maxStateBytes at *; omega
  · unfold varBound maxStateBytes at *; omega

/-- Decode a state record and rebuild its invariants. Total, one pass. -/
def decodeState (b : ByteArray) : Except DecodeError State :=
  decodeTop (readWithHeader kindState readStateBody) maxStateBytes b

theorem decodeState_encodeState' (s : State) (h : s.WireOk) :
    decodeState (encodeState s) = .ok s := by
  apply decodeTop_complete (readWithHeader_complete readStateBody_complete) (fieldsOk_of_wireOk h)
  · rw [encodeState_toList]; rfl
  · have := h.2.2; rw [size_encodeState] at this; exact this

theorem encodeState_of_decodeState' {b : ByteArray} {s : State} (h : decodeState b = .ok s) :
    encodeState s = b := by
  obtain ⟨-, hb, -⟩ := decodeTop_sound (readWithHeader_sound readStateBody_sound) h
  apply ByteArray.eq_of_toList
  rw [encodeState_toList, hb]; rfl

theorem wireOk_of_decodeState' {b : ByteArray} {s : State} (h : decodeState b = .ok s) : s.WireOk := by
  obtain ⟨hq, -, hle⟩ := decodeTop_sound (readWithHeader_sound readStateBody_sound) h
  exact ⟨hq.1, hq.2.1, by rw [encodeState_of_decodeState' h]; exact hle⟩

/-! ## Decidable well-formedness (used by the step function) -/

def checkFields (s : State) : Bool :=
  s.entries.all (fun e => e.hash.bytes.size == hashLen && decide (e.path.toByteArray.size ≤ maxPathBytes)) &&
  s.context.entries.all (fun p => decide (p.2 < varBound)) &&
  decide (s.context.entries.length < varBound) && decide (s.entries.length < varBound)

theorem checkFields_iff (s : State) : checkFields s = true ↔ s.FieldsOk := by
  simp [checkFields, State.FieldsOk, and_assoc]

/-- `s.WireOk`, decided (one pass over the entries plus one encoding). -/
def checkWire (s : State) : Bool :=
  s.entries.all (fun e => e.hash.bytes.size == hashLen && decide (e.path.toByteArray.size ≤ maxPathBytes)) &&
  s.context.entries.all (fun p => decide (p.2 < varBound)) &&
  decide ((encodeState s).size ≤ maxStateBytes)

theorem checkWire_iff (s : State) : checkWire s = true ↔ s.WireOk := by
  simp [checkWire, State.WireOk, Hash.WireOk, and_assoc]

/-! ## Hash batches -/

/-- A strictly sorted, non-empty batch of at most `maxBatch` 32-byte hashes. -/
def HashBatchOk (hs : List Hash) : Prop :=
  StrictlySorted hs ∧ 0 < hs.length ∧ hs.length ≤ maxBatch ∧ ∀ h ∈ hs, h.bytes.size = hashLen

instance (hs : List Hash) : Decidable (StrictlySorted hs) :=
  inferInstanceAs (Decidable (List.Pairwise _ hs))

/-- `HashBatchOk`, decided. -/
def checkBatch (hs : List Hash) : Bool :=
  decide (StrictlySorted hs) && decide (0 < hs.length) && decide (hs.length ≤ maxBatch) &&
    hs.all (fun h => h.bytes.size == hashLen)

theorem checkBatch_iff (hs : List Hash) : checkBatch hs = true ↔ HashBatchOk hs := by
  simp [checkBatch, HashBatchOk, and_assoc]

def encBatch (hs : List Hash) : List UInt8 := encVar hs.length ++ hs.flatMap encHash

def readBatch : Parser (List Hash) := fun b pos =>
  match readVarint b pos with
  | .error e => .error e
  | .ok (k, p1) => if 0 < k ∧ k ≤ maxBatch then manyGo readHash chkLt b k p1 none [] else .error .tooLarge

theorem readBatch_sound : Sound readBatch encBatch HashBatchOk := by
  intro b pos x pos' h
  unfold readBatch at h
  split at h
  · cases h
  · next k p1 h1 =>
    split at h
    · next hk =>
      obtain ⟨-, hp1, hb1⟩ := readVarint_sound b pos k p1 h1
      obtain ⟨xs, rfl, hlen, hch, hq, hp2, hb2⟩ := manyGo_sound readHash_sound chkLt b k p1 none [] x pos' h
      refine ⟨⟨sorted_of_chain hch, by omega, by omega, hq⟩, ?_, ?_⟩
      · simp [encBatch, hlen, hp2, hp1]; omega
      · simp [encBatch, hlen, hb1, hb2]
    · cases h

theorem readBatch_complete : Complete readBatch encBatch HashBatchOk := by
  intro b pos hs rest hpos hok h
  obtain ⟨hsort, h0, hmax, hsz⟩ := hok
  simp only [encBatch, List.append_assoc] at h
  have e1 := readVarint_complete b pos hs.length _ hpos (by unfold varBound maxBatch at *; omega) h
  have e2 := manyGo_complete readHash_complete chkLt b hs _ none [] rest (le_size_of_bytesFrom hpos h)
    (chain_of_sorted hsort) hsz (bytesFrom_skip h)
  simp only [readBatch, e1, h0, hmax, and_self, ite_true, e2, List.reverse_nil, List.nil_append,
    encBatch, List.length_append]
  congr 2; omega

def wBatch (acc : ByteArray) (hs : List Hash) : ByteArray :=
  hs.foldl (fun a h => wBytes a h.bytes) (wVar acc hs.length)

theorem wBatch_toList (acc : ByteArray) (hs : List Hash) :
    (wBatch acc hs).data.toList = acc.data.toList ++ encBatch hs := by
  simp [wBatch, foldl_toList (fun a (h : Hash) => wBytes a h.bytes) encHash (fun a h => wBytes_toList a h.bytes),
    wVar_toList, encBatch]

/-! ## Messages -/

def reasonByte : CloseReason → UInt8
  | .protocolError => 0
  | .incompatible => 1
  | .sameReplicaId => 2
  | .tooManyPeers => 3
  | .stateTooLarge => 4

def reasonOfByte (x : UInt8) : Option CloseReason :=
  if x = 0 then some .protocolError
  else if x = 1 then some .incompatible
  else if x = 2 then some .sameReplicaId
  else if x = 3 then some .tooManyPeers
  else if x = 4 then some .stateTooLarge
  else none

theorem reasonOfByte_reasonByte (r : CloseReason) : reasonOfByte (reasonByte r) = some r := by
  cases r <;> decide

theorem reasonByte_of {x : UInt8} {r : CloseReason} (h : reasonOfByte x = some r) : reasonByte r = x := by
  unfold reasonOfByte at h
  by_cases h0 : x = 0
  · subst h0; simp at h; subst h; rfl
  by_cases h1 : x = 1
  · subst h1; simp at h; subst h; rfl
  by_cases h2 : x = 2
  · subst h2; simp at h; subst h; rfl
  by_cases h3 : x = 3
  · subst h3; simp at h; subst h; rfl
  by_cases h4 : x = 4
  · subst h4; simp at h; subst h; rfl
  simp [h0, h1, h2, h3, h4] at h

def Message.WireOk : Message → Prop
  | .hello _ _ _ => True
  | .digest _ => True
  | .state _ s => s.WireOk
  | .want hs => HashBatchOk hs
  | .noBlob hs => HashBatchOk hs
  | .have hs => HashBatchOk hs
  | .bye _ => True

/-- `Message.WireOk`, decided. -/
def checkMessage : Message → Bool
  | .state _ s => checkWire s
  | .want hs => checkBatch hs
  | .noBlob hs => checkBatch hs
  | .have hs => checkBatch hs
  | _ => true

theorem checkMessage_iff (m : Message) : checkMessage m = true ↔ m.WireOk := by
  cases m <;> simp [checkMessage, Message.WireOk, checkWire_iff, checkBatch_iff]

def encMsgBody : Message → List UInt8
  | .hello v r d => [0, v] ++ encU64 r.hi ++ encU64 r.lo ++ encDigest d
  | .digest d => 1 :: encDigest d
  | .state d s => 2 :: (encDigest d ++ encStateBody s)
  | .want hs => 3 :: encBatch hs
  | .noBlob hs => 4 :: encBatch hs
  | .have hs => 5 :: encBatch hs
  | .bye r => [6, reasonByte r]

def encMsg (m : Message) : List UInt8 := [wireVersion, kindMessage] ++ encMsgBody m

def readStateMsg : Parser Message := fun b pos =>
  match readDigest b pos with
  | .error e => .error e
  | .ok (d, p1) =>
    match readStateBody b p1 with
    | .error e => .error e
    | .ok (s, p2) => if p2 - p1 + 2 ≤ maxStateBytes then .ok (.state d s, p2) else .error .tooLarge

def readHelloP : Parser (UInt8 × ((UInt64 × UInt64) × Digest)) :=
  seqP readByte (seqP (seqP readU64 readU64) readDigest)

def readBye : Parser Message := fun b pos =>
  match readByte b pos with
  | .error e => .error e
  | .ok (x, p1) =>
    match reasonOfByte x with
    | some r => .ok (.bye r, p1)
    | none => .error (.badTag x.toNat)

def readMsgBody : Parser Message := fun b pos =>
  match readByte b pos with
  | .error e => .error e
  | .ok (t, p1) =>
    if t = 0 then mapP (fun z => Message.hello z.1 ⟨z.2.1.1, z.2.1.2⟩ z.2.2) readHelloP b p1
    else if t = 1 then mapP Message.digest readDigest b p1
    else if t = 2 then readStateMsg b p1
    else if t = 3 then mapP Message.want readBatch b p1
    else if t = 4 then mapP Message.noBlob readBatch b p1
    else if t = 5 then mapP Message.have readBatch b p1
    else if t = 6 then readBye b p1
    else .error (.badTag t.toNat)

theorem readByte_ok {b : ByteArray} {pos : Nat} {t : UInt8} {p1 : Nat} (h : readByte b pos = .ok (t, p1)) :
    p1 = pos + 1 ∧ bytesFrom b pos = t :: bytesFrom b p1 := by
  obtain ⟨-, hp, hb⟩ := readByte_sound b pos t p1 h
  exact ⟨by simpa using hp, by simpa using hb⟩

theorem readMsgBody_sound : Sound readMsgBody encMsgBody Message.WireOk := by
  intro b pos m pos' h
  unfold readMsgBody at h
  split at h
  · cases h
  · next t p1 ht =>
    obtain ⟨hp1, hb1⟩ := readByte_ok ht
    subst hp1
    split at h
    · next h0 =>
      subst h0
      obtain ⟨z, hz, rfl⟩ := mapP_ok h
      obtain ⟨-, hp, hb⟩ := seqP_sound readByte_sound (seqP_sound (seqP_sound readU64_sound readU64_sound)
        readDigest_sound) b (pos + 1) z pos' hz
      refine ⟨trivial, ?_, ?_⟩
      · simp [encMsgBody] at hp ⊢; omega
      · rw [hb1, hb]; simp [encMsgBody]
    split at h
    · next h1 =>
      subst h1
      obtain ⟨z, hz, rfl⟩ := mapP_ok h
      obtain ⟨-, hp, hb⟩ := readDigest_sound b (pos + 1) z pos' hz
      exact ⟨trivial, by simp [encMsgBody, hp]; omega, by rw [hb1, hb]; rfl⟩
    split at h
    · next h2 =>
      subst h2
      unfold readStateMsg at h
      split at h
      · cases h
      · next d q1 hd =>
        split at h
        · cases h
        · next s q2 hs =>
          split at h
          · next hle =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨-, hpd, hbd⟩ := readDigest_sound b (pos + 1) d q1 hd
            obtain ⟨hf, hps, hbs⟩ := readStateBody_sound b q1 s q2 hs
            refine ⟨⟨hf.1, hf.2.1, ?_⟩, ?_, ?_⟩
            · rw [size_encodeState]; simp [encState]; omega
            · simp [encMsgBody, hps, hpd]; omega
            · rw [hb1, hbd, hbs]; simp [encMsgBody]
          · cases h
    split at h
    · next h3 =>
      subst h3
      obtain ⟨z, hz, rfl⟩ := mapP_ok h
      obtain ⟨hq, hp, hb⟩ := readBatch_sound b (pos + 1) z pos' hz
      exact ⟨hq, by simp [encMsgBody, hp]; omega, by rw [hb1, hb]; rfl⟩
    split at h
    · next h4 =>
      subst h4
      obtain ⟨z, hz, rfl⟩ := mapP_ok h
      obtain ⟨hq, hp, hb⟩ := readBatch_sound b (pos + 1) z pos' hz
      exact ⟨hq, by simp [encMsgBody, hp]; omega, by rw [hb1, hb]; rfl⟩
    split at h
    · next h5 =>
      subst h5
      obtain ⟨z, hz, rfl⟩ := mapP_ok h
      obtain ⟨hq, hp, hb⟩ := readBatch_sound b (pos + 1) z pos' hz
      exact ⟨hq, by simp [encMsgBody, hp]; omega, by rw [hb1, hb]; rfl⟩
    split at h
    · next h6 =>
      subst h6
      unfold readBye at h
      split at h
      · cases h
      · next x q1 hx =>
        obtain ⟨hq1, hbx⟩ := readByte_ok hx
        split at h
        · next r hr =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨trivial, by simp [encMsgBody, hq1], ?_⟩
          rw [hb1, hbx, ← reasonByte_of hr]; rfl
        · cases h
    · cases h

theorem readMsgBody_complete : Complete readMsgBody encMsgBody Message.WireOk := by
  intro b pos m rest hpos hm h
  have tagOk : ∀ (t : UInt8) (l : List UInt8), bytesFrom b pos = t :: (l ++ rest) →
      readByte b pos = .ok (t, pos + 1) ∧ bytesFrom b (pos + 1) = l ++ rest ∧ pos + 1 ≤ b.size := by
    intro t l ht
    obtain ⟨hlt, hx, hr⟩ := bytesFrom_cons ht
    exact ⟨by simp [readByte, hlt, hx], hr, hlt⟩
  cases m with
  | hello v r d =>
    obtain ⟨e0, h1, hp1⟩ := tagOk 0 (encMsgBody (.hello v r d)).tail (by rw [h]; simp [encMsgBody])
    have e1 := seqP_complete readByte_complete (seqP_complete (seqP_complete readU64_complete readU64_complete)
      readDigest_complete) b (pos + 1) (v, (r.hi, r.lo), d) rest hp1 ⟨trivial, ⟨trivial, trivial⟩, trivial⟩
      (by rw [h1]; simp [encMsgBody])
    simp only [readMsgBody, e0, ite_true, readHelloP, mapP_of_ok e1]
    simp [encMsgBody]; omega
  | digest d =>
    obtain ⟨e0, h1, hp1⟩ := tagOk 1 (encDigest d) (by rw [h]; rfl)
    have e1 := readDigest_complete b (pos + 1) d rest hp1 trivial h1
    simp only [readMsgBody, e0, mapP_of_ok e1]
    simp [encMsgBody]; omega
  | state d s =>
    obtain ⟨e0, h1, hp1⟩ := tagOk 2 (encDigest d ++ encStateBody s) (by rw [h]; rfl)
    rw [List.append_assoc] at h1
    have e1 := readDigest_complete b (pos + 1) d _ hp1 trivial h1
    have e2 := readStateBody_complete b _ s rest (le_size_of_bytesFrom hp1 h1) (fieldsOk_of_wireOk hm) (bytesFrom_skip h1)
    have hsz := hm.2.2
    rw [size_encodeState] at hsz
    simp only [encState, List.length_append, List.length_cons, List.length_nil] at hsz
    simp only [readMsgBody, e0, readStateMsg, e1, e2]
    simp [encMsgBody]
    rw [ite_eq_left (by omega)]
    congr 2; omega
  | want hs =>
    obtain ⟨e0, h1, hp1⟩ := tagOk 3 (encBatch hs) (by rw [h]; rfl)
    have e1 := readBatch_complete b (pos + 1) hs rest hp1 hm h1
    simp only [readMsgBody, e0, mapP_of_ok e1]
    simp [encMsgBody]; omega
  | noBlob hs =>
    obtain ⟨e0, h1, hp1⟩ := tagOk 4 (encBatch hs) (by rw [h]; rfl)
    have e1 := readBatch_complete b (pos + 1) hs rest hp1 hm h1
    simp only [readMsgBody, e0, mapP_of_ok e1]
    simp [encMsgBody]; omega
  | «have» hs =>
    obtain ⟨e0, h1, hp1⟩ := tagOk 5 (encBatch hs) (by rw [h]; rfl)
    have e1 := readBatch_complete b (pos + 1) hs rest hp1 hm h1
    simp only [readMsgBody, e0, mapP_of_ok e1]
    simp [encMsgBody]; omega
  | bye r =>
    obtain ⟨e0, h1, hp1⟩ := tagOk 6 [reasonByte r] (by rw [h]; rfl)
    obtain ⟨hlt, hx, -⟩ := bytesFrom_cons h1
    have e1 : readByte b (pos + 1) = .ok (reasonByte r, pos + 1 + 1) := by simp [readByte, hlt, hx]
    simp only [readMsgBody, e0, readBye, e1, reasonOfByte_reasonByte]
    simp [encMsgBody]

def wMsgBody (acc : ByteArray) : Message → ByteArray
  | .hello v r d => wBytes (wVar (wVar ((acc.push 0).push v) r.hi.toNat) r.lo.toNat) d.bytes
  | .digest d => wBytes (acc.push 1) d.bytes
  | .state d s => wStateBody (wBytes (acc.push 2) d.bytes) s
  | .want hs => wBatch (acc.push 3) hs
  | .noBlob hs => wBatch (acc.push 4) hs
  | .have hs => wBatch (acc.push 5) hs
  | .bye r => (acc.push 6).push (reasonByte r)

theorem push_toList (acc : ByteArray) (x : UInt8) : (acc.push x).data.toList = acc.data.toList ++ [x] :=
  wByte_toList acc x

theorem wMsgBody_toList (acc : ByteArray) (m : Message) :
    (wMsgBody acc m).data.toList = acc.data.toList ++ encMsgBody m := by
  cases m <;> simp [wMsgBody, encMsgBody, wBytes_toList, wVar_toList, wStateBody_toList,
    wBatch_toList, encDigest, encU64]

def encodeMessage (m : Message) : ByteArray :=
  wMsgBody ((ByteArray.empty.push wireVersion).push kindMessage) m

theorem encodeMessage_toList (m : Message) : (encodeMessage m).data.toList = encMsg m := by
  rw [encodeMessage, wMsgBody_toList]; simp [encMsg]

theorem size_encodeMessage (m : Message) : (encodeMessage m).size = (encMsg m).length := by
  rw [← ByteArray.size_data, ← Array.length_toList, encodeMessage_toList]

def decodeMessage (b : ByteArray) : Except DecodeError Message :=
  decodeTop (readWithHeader kindMessage readMsgBody) maxMessageBytes b

theorem decodeMessage_encodeMessage' (m : Message) (h : m.WireOk) (hlen : (encodeMessage m).size ≤ maxMessageBytes) :
    decodeMessage (encodeMessage m) = .ok m := by
  apply decodeTop_complete (readWithHeader_complete readMsgBody_complete) h
  · rw [encodeMessage_toList]; rfl
  · rw [size_encodeMessage] at hlen; exact hlen

theorem encodeMessage_of_decodeMessage' {b : ByteArray} {m : Message} (h : decodeMessage b = .ok m) :
    encodeMessage m = b := by
  obtain ⟨-, hb, -⟩ := decodeTop_sound (readWithHeader_sound readMsgBody_sound) h
  apply ByteArray.eq_of_toList
  rw [encodeMessage_toList, hb]; rfl

theorem wireOk_of_decodeMessage' {b : ByteArray} {m : Message} (h : decodeMessage b = .ok m) :
    m.WireOk := (decodeTop_sound (readWithHeader_sound readMsgBody_sound) h).1

theorem decodeMessage_tooLarge' {b : ByteArray} (h : maxMessageBytes < b.size) :
    decodeMessage b = .error .tooLarge := by
  simp [decodeMessage, decodeTop]; omega

theorem length_encHashes (hs : List Hash) (h : ∀ x ∈ hs, x.bytes.size = hashLen) :
    (hs.flatMap encHash).length = hashLen * hs.length := by
  induction hs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [ih (fun y hy => h y (.tail _ hy))]
    have : (encHash x).length = hashLen := by
      simp [encHash, ByteArray.size_data, h x (.head _)]
    rw [this, Nat.mul_succ]; omega

theorem length_encU64 (x : UInt64) : (encU64 x).length ≤ 10 :=
  length_encVar_of_lt (by unfold varBound; exact x.toNat_lt)

theorem length_encDigest (d : Digest) : (encDigest d).length = 32 := by
  simp [encDigest, ByteArray.size_data, d.size_eq]

theorem length_encBatch_le {hs : List Hash} (h : HashBatchOk hs) : (encBatch hs).length ≤ 10 + 32 * 1024 := by
  obtain ⟨-, -, hmax, hsz⟩ := h
  simp only [encBatch, List.length_append, length_encHashes hs hsz]
  have := length_encVar_of_lt (n := hs.length) (by unfold varBound maxBatch at *; omega)
  unfold hashLen maxBatch at *; omega

/-- Every well-formed message fits the message limit. -/
theorem size_encodeMessage_le (m : Message) (h : m.WireOk) : (encodeMessage m).size ≤ maxMessageBytes := by
  rw [size_encodeMessage]
  cases m with
  | hello v r d =>
    have := length_encU64 r.hi; have := length_encU64 r.lo
    simp [encMsg, encMsgBody, length_encDigest, maxMessageBytes, maxStateBytes]; omega
  | digest d => simp [encMsg, encMsgBody, length_encDigest, maxMessageBytes, maxStateBytes]
  | state d s =>
    have hs := h.2.2
    rw [size_encodeState] at hs
    simp only [encState, List.length_append, List.length_cons, List.length_nil] at hs
    simp [encMsg, encMsgBody, length_encDigest, maxMessageBytes]; omega
  | want hs => have := length_encBatch_le h; simp [encMsg, encMsgBody, maxMessageBytes, maxStateBytes]; omega
  | noBlob hs => have := length_encBatch_le h; simp [encMsg, encMsgBody, maxMessageBytes, maxStateBytes]; omega
  | «have» hs => have := length_encBatch_le h; simp [encMsg, encMsgBody, maxMessageBytes, maxStateBytes]; omega
  | bye r => simp [encMsg, encMsgBody, maxMessageBytes, maxStateBytes]

end LeanSync
