import LeanSync.Types

/-!
# Byte-level codec primitives and their correctness

Executable module (imports `Init` only).

Every decoder is a `Parser`: it reads from a `ByteArray` at a position and returns a value and
the next position, or an error. It never panics: every array access is bounds-checked.

Specifications are byte *lists*: `enc x : List UInt8` is the encoding of `x`, and
`bytesFrom b pos` is the list of bytes of `b` from `pos` on. Two properties per parser:
* `Sound p enc Q`: whatever `p` returns satisfies `Q` and is exactly what it consumed:
  `bytesFrom b pos = enc x ++ bytesFrom b pos'` and `pos' = pos + (enc x).length`.
  This is what makes decoding canonical: only `enc x` decodes to `x`.
* `Complete p enc ok`: on input starting with `enc x` (for `ok x`), `p` returns `x`.

Encoders used at runtime append to a `ByteArray` accumulator (`w*` functions, tail-recursive
where the data can be long) and are proved to append exactly `enc x`.
-/

set_option linter.unusedSectionVars false

namespace LeanSync

open LeanCrdt

/-! ## Byte views -/

/-- The bytes of `b` from position `pos` on. -/
def bytesFrom (b : ByteArray) (pos : Nat) : List UInt8 := b.data.toList.drop pos

theorem length_bytesFrom (b : ByteArray) (pos : Nat) : (bytesFrom b pos).length = b.size - pos := by
  simp [bytesFrom, ← ByteArray.size_data]

theorem bytesFrom_of_lt {b : ByteArray} {pos : Nat} (h : pos < b.size) :
    bytesFrom b pos = b[pos] :: bytesFrom b (pos + 1) := by
  unfold bytesFrom
  rw [List.drop_eq_getElem_cons (by rw [Array.length_toList, ByteArray.size_data]; exact h)]
  simp [ByteArray.getElem_eq_getElem_data]

theorem bytesFrom_of_ge {b : ByteArray} {pos : Nat} (h : b.size ≤ pos) : bytesFrom b pos = [] := by
  unfold bytesFrom
  simp only [List.drop_eq_nil_iff, Array.length_toList, ByteArray.size_data]
  exact h

theorem bytesFrom_zero (b : ByteArray) : bytesFrom b 0 = b.data.toList := by simp [bytesFrom]

theorem ByteArray.eq_of_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  cases a; cases b; simp only [ByteArray.mk.injEq]; exact Array.toList_inj.1 h

theorem lt_size_of_bytesFrom {b : ByteArray} {pos : Nat} {x : UInt8} {rest : List UInt8}
    (h : bytesFrom b pos = x :: rest) : pos < b.size := by
  have := length_bytesFrom b pos
  rw [h] at this; simp at this; omega

theorem bytesFrom_cons {b : ByteArray} {pos : Nat} {x : UInt8} {rest : List UInt8}
    (h : bytesFrom b pos = x :: rest) :
    ∃ hlt : pos < b.size, b[pos] = x ∧ bytesFrom b (pos + 1) = rest := by
  have hlt := lt_size_of_bytesFrom h
  rw [bytesFrom_of_lt hlt] at h
  simp only [List.cons.injEq] at h
  exact ⟨hlt, h.1, h.2⟩

/-- Skipping `l.length` bytes of a known prefix `l`. -/
theorem bytesFrom_skip {b : ByteArray} {pos : Nat} {l rest : List UInt8}
    (h : bytesFrom b pos = l ++ rest) : bytesFrom b (pos + l.length) = rest := by
  unfold bytesFrom at h ⊢
  rw [← List.drop_drop, h, List.drop_left]

/-! ## Parsers -/

abbrev Parser (α : Type) := ByteArray → Nat → Except DecodeError (α × Nat)

/-- What a successful parse guarantees. -/
def Sound {α} (p : Parser α) (enc : α → List UInt8) (Q : α → Prop) : Prop :=
  ∀ b pos x pos', p b pos = .ok (x, pos') →
    Q x ∧ pos' = pos + (enc x).length ∧ bytesFrom b pos = enc x ++ bytesFrom b pos'

/-- A parser reads back every encoding of a value satisfying `ok`. -/
def Complete {α} (p : Parser α) (enc : α → List UInt8) (ok : α → Prop) : Prop :=
  ∀ b pos x rest, pos ≤ b.size → ok x → bytesFrom b pos = enc x ++ rest →
    p b pos = .ok (x, pos + (enc x).length)

theorem le_size_of_bytesFrom {b : ByteArray} {pos : Nat} {l rest : List UInt8} (hpos : pos ≤ b.size)
    (h : bytesFrom b pos = l ++ rest) : pos + l.length ≤ b.size := by
  have := length_bytesFrom b pos
  rw [h] at this; simp at this; omega

/-! ## One byte -/

def readByte : Parser UInt8 := fun b pos =>
  if h : pos < b.size then .ok (b[pos], pos + 1) else .error .truncated

theorem readByte_sound : Sound readByte (fun x => [x]) (fun _ => True) := by
  intro b pos x pos' h
  unfold readByte at h
  split at h
  · next hlt =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, rfl, by rw [bytesFrom_of_lt hlt]; rfl⟩
  · cases h

theorem readByte_complete : Complete readByte (fun x => [x]) (fun _ => True) := by
  intro b pos x rest _ _ h
  obtain ⟨hlt, hx, _⟩ := bytesFrom_cons h
  simp [readByte, hlt, hx]

/-- Expect a fixed byte; `err v` reports any other value `v`. -/
def expectByte (x : UInt8) (err : Nat → DecodeError) : Parser Unit := fun b pos =>
  if h : pos < b.size then
    if b[pos] = x then .ok ((), pos + 1) else .error (err b[pos].toNat)
  else .error .truncated

theorem expectByte_sound (x : UInt8) (err : Nat → DecodeError) :
    Sound (expectByte x err) (fun _ => [x]) (fun _ => True) := by
  intro b pos u pos' h
  unfold expectByte at h
  split at h
  · next hlt =>
    split at h
    · next hx =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨trivial, rfl, by rw [bytesFrom_of_lt hlt, hx]; rfl⟩
    · cases h
  · cases h

theorem expectByte_complete (x : UInt8) (err : Nat → DecodeError) :
    Complete (expectByte x err) (fun _ => [x]) (fun _ => True) := by
  intro b pos u rest _ _ h
  obtain ⟨hlt, hx, _⟩ := bytesFrom_cons h
  simp [expectByte, hlt, hx]

/-! ## Varints: canonical unsigned LEB128 -/

/-- LEB128 encoding: 7 bits per byte, least significant first, high bit = "more follows".
The last byte is nonzero unless the number is `0`, so the encoding is unique. -/
def encVar (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: encVar (n / 128)
termination_by n
decreasing_by omega

theorem encVar_ne_nil (n : Nat) : encVar n ≠ [] := by
  rw [encVar]; split <;> simp

theorem length_encVar_le : ∀ (k n : Nat), n < 128 ^ (k + 1) → (encVar n).length ≤ k + 1
  | 0, n, h => by rw [encVar]; simp at h; simp [h]
  | k + 1, n, h => by
    rw [encVar]
    split
    · simp
    · have : n / 128 < 128 ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [Nat.pow_succ] at h; exact h
      have := length_encVar_le k (n / 128) this
      simp; omega

/-- `fuel` bounds the number of bytes read (10 for 64-bit values). Recursion depth ≤ fuel. -/
def readVar : Nat → Parser Nat
  | 0 => fun _ _ => .error .nonCanonical
  | f + 1 => fun b pos =>
    if h : pos < b.size then
      if b[pos] < 128 then .ok (b[pos].toNat, pos + 1)
      else match readVar f b (pos + 1) with
        | .ok (v, p') => if v = 0 then .error .nonCanonical else .ok (b[pos].toNat - 128 + 128 * v, p')
        | .error e => .error e
    else .error .truncated

theorem toUInt8_toNat_of_lt {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8]; omega

theorem readVar_sound : ∀ f, Sound (readVar f) encVar (fun _ => True)
  | 0 => by intro b pos x pos' h; simp [readVar] at h
  | f + 1 => by
    intro b pos x pos' h
    simp only [readVar] at h
    split at h
    · next hlt =>
      split at h
      · next hsmall =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hx : b[pos].toNat < 128 := hsmall
        refine ⟨trivial, ?_, ?_⟩
        · rw [encVar, ite_eq_left hx]; simp
        · rw [bytesFrom_of_lt hlt, encVar, ite_eq_left hx]
          simp [Nat.toUInt8, UInt8.ofNat_toNat]
      · next hbig =>
        split at h
        · next v p' hv =>
          split at h
          · cases h
          · next hv0 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨-, hp, hb⟩ := readVar_sound f b (pos + 1) v p' hv
            have hx : 128 ≤ b[pos].toNat := by
              have : ¬ b[pos].toNat < 128 := hbig
              omega
            have hx2 : b[pos].toNat < 256 := b[pos].toNat_lt
            have hge : ¬ (b[pos].toNat - 128 + 128 * v < 128) := by omega
            have hmod : (b[pos].toNat - 128 + 128 * v) % 128 = b[pos].toNat - 128 := by omega
            have hdiv : (b[pos].toNat - 128 + 128 * v) / 128 = v := by omega
            refine ⟨trivial, ?_, ?_⟩
            · rw [encVar, ite_eq_right hge, hmod, hdiv]; simp [hp]; omega
            · rw [bytesFrom_of_lt hlt, encVar, ite_eq_right hge, hmod, hdiv, hb]
              have : (b[pos].toNat - 128 + 128).toUInt8 = b[pos] := by
                rw [Nat.sub_add_cancel hx]; simp [Nat.toUInt8, UInt8.ofNat_toNat]
              simp [this]
        · cases h
    · cases h

theorem readVar_complete : ∀ f n b pos rest, (encVar n).length ≤ f →
    bytesFrom b pos = encVar n ++ rest → readVar f b pos = .ok (n, pos + (encVar n).length)
  | 0, n, _, _, _, hl, _ => by have := encVar_ne_nil n; cases h : encVar n <;> simp_all
  | f + 1, n, b, pos, rest, hl, h => by
    by_cases hn : n < 128
    · rw [encVar, ite_eq_left hn] at h hl ⊢
      obtain ⟨hlt, hx, _⟩ := bytesFrom_cons h
      have : b[pos].toNat = n := by rw [hx]; exact toUInt8_toNat_of_lt (by omega)
      simp [readVar, hlt, UInt8.lt_iff_toNat_lt, this, hn]
    · rw [encVar, ite_eq_right hn] at h hl
      obtain ⟨hlt, hx, hrest⟩ := bytesFrom_cons h
      have hxn : b[pos].toNat = n % 128 + 128 := by rw [hx]; exact toUInt8_toNat_of_lt (by omega)
      have ih := readVar_complete f (n / 128) b (pos + 1) rest (by simp at hl; omega) hrest
      have hnz : n / 128 ≠ 0 := by omega
      have hbig : ¬ b[pos] < 128 := by rw [UInt8.lt_iff_toNat_lt]; simp [hxn]
      rw [encVar, ite_eq_right hn]
      simp only [readVar, hlt, dite_true, hbig, ite_false, ih, hnz, Except.ok.injEq, Prod.mk.injEq,
        List.length_cons]
      constructor
      · rw [hxn]; omega
      · omega

def varBound : Nat := 2 ^ 64

/-- A canonical varint below 2^64 (at most 10 bytes). -/
def readVarint : Parser Nat := fun b pos =>
  match readVar 10 b pos with
  | .ok (v, p) => if v < varBound then .ok (v, p) else .error .tooLarge
  | .error e => .error e

theorem readVarint_sound : Sound readVarint encVar (· < varBound) := by
  intro b pos x pos' h
  unfold readVarint at h
  split at h
  · next v p hv =>
    split at h
    · next hlt =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hlt, (readVar_sound 10 b pos v p hv).2⟩
    · cases h
  · cases h

theorem length_encVar_of_lt {n : Nat} (h : n < varBound) : (encVar n).length ≤ 10 :=
  length_encVar_le 9 n (by unfold varBound at h; omega)

theorem readVarint_complete : Complete readVarint encVar (· < varBound) := by
  intro b pos x rest _ hx h
  unfold readVarint
  rw [readVar_complete 10 x b pos rest (length_encVar_of_lt hx) h]
  simp [hx]

/-- A `UInt64` as a varint. -/
def encU64 (x : UInt64) : List UInt8 := encVar x.toNat

def readU64 : Parser UInt64 := fun b pos =>
  match readVarint b pos with
  | .ok (v, p) => .ok (UInt64.ofNat v, p)
  | .error e => .error e

theorem readU64_sound : Sound readU64 encU64 (fun _ => True) := by
  intro b pos x pos' h
  unfold readU64 at h
  split at h
  · next v p hv =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hlt, hp, hb⟩ := readVarint_sound b pos v p hv
    have : (UInt64.ofNat v).toNat = v := by unfold varBound at hlt; simp; omega
    exact ⟨trivial, by simp [encU64, this, hp], by simp [encU64, this, hb]⟩
  · cases h

theorem readU64_complete : Complete readU64 encU64 (fun _ => True) := by
  intro b pos x rest hpos _ h
  unfold readU64
  rw [readVarint_complete b pos x.toNat rest hpos (by unfold varBound; exact x.toNat_lt) h]
  simp [encU64]

/-! ## Fixed-length byte strings -/

def readBytes (n : Nat) : Parser ByteArray := fun b pos =>
  if pos + n ≤ b.size then .ok (b.extract pos (pos + n), pos + n) else .error .truncated

theorem toList_extract (b : ByteArray) (i j : Nat) :
    (b.extract i j).data.toList = (b.data.toList.drop i).take (j - i) := by
  simp [ByteArray.data_extract, Array.toList_extract, List.extract]

theorem readBytes_sound (n : Nat) :
    Sound (readBytes n) (fun x => x.data.toList) (fun x => x.size = n) := by
  intro b pos x pos' h
  unfold readBytes at h
  split at h
  · next hle =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hsz : (b.extract pos (pos + n)).size = n := by
      rw [ByteArray.size_extract]; omega
    refine ⟨hsz, ?_, ?_⟩
    · have : (b.extract pos (pos + n)).data.toList.length = n := by
        rw [Array.length_toList, ByteArray.size_data]; exact hsz
      rw [this]
    · show bytesFrom b pos = (b.extract pos (pos + n)).data.toList ++ bytesFrom b (pos + n)
      rw [toList_extract]; unfold bytesFrom
      rw [show pos + n - pos = n by omega, ← List.drop_drop]
      exact (List.take_append_drop _ _).symm
  · cases h

theorem readBytes_complete (n : Nat) :
    Complete (readBytes n) (fun x => x.data.toList) (fun x => x.size = n) := by
  intro b pos x rest hpos hx h
  have hxl : x.data.toList.length = n := by rw [Array.length_toList, ByteArray.size_data]; exact hx
  have hle : pos + n ≤ b.size := by have := le_size_of_bytesFrom hpos h; rw [hxl] at this; exact this
  unfold readBytes
  rw [ite_eq_left hle, hxl]
  congr
  apply ByteArray.eq_of_toList
  rw [toList_extract, show pos + n - pos = n by omega]
  unfold bytesFrom at h
  rw [h, ← hxl, List.take_left]

/-! ## Hashes and digests (exactly 32 bytes) -/

def hashLen : Nat := 32

def encHash (h : Hash) : List UInt8 := h.bytes.data.toList

def readHash : Parser Hash := fun b pos =>
  match readBytes hashLen b pos with
  | .ok (x, p) => .ok (⟨x⟩, p)
  | .error e => .error e

theorem readHash_sound : Sound readHash encHash (fun h => h.bytes.size = hashLen) := by
  intro b pos x pos' h
  unfold readHash at h
  split at h
  · next y p hy =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact readBytes_sound hashLen b pos y p hy
  · cases h

theorem readHash_complete : Complete readHash encHash (fun h => h.bytes.size = hashLen) := by
  intro b pos x rest hpos hx h
  unfold readHash
  rw [readBytes_complete hashLen b pos x.bytes rest hpos hx h]
  rfl

def encDigest (d : Digest) : List UInt8 := d.bytes.data.toList

def readDigest : Parser Digest := fun b pos =>
  if h : pos + 32 ≤ b.size then
    .ok (⟨b.extract pos (pos + 32), by rw [ByteArray.size_extract]; omega⟩, pos + 32)
  else .error .truncated

theorem readDigest_sound : Sound readDigest encDigest (fun _ => True) := by
  intro b pos x pos' h
  unfold readDigest at h
  split at h
  · next hle =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := readBytes_sound 32 b pos _ _ (by unfold readBytes; rw [ite_eq_left hle])
    exact ⟨trivial, this.2⟩
  · cases h

theorem readDigest_complete : Complete readDigest encDigest (fun _ => True) := by
  intro b pos x rest hpos _ h
  have := readBytes_complete 32 b pos x.bytes rest hpos x.size_eq h
  unfold readBytes at this
  split at this
  · next hle =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at this
    unfold readDigest
    rw [dite_eq_left hle]
    have hl : (encDigest x).length = 32 := by
      simp [encDigest, ByteArray.size_data, x.size_eq]
    rw [hl]
    congr
    cases x; exact this.1
  · cases this

/-! ## Strings: varint byte length, then UTF-8 (validated) -/

def encStr (s : String) : List UInt8 := encVar s.toByteArray.size ++ s.toByteArray.data.toList

def readStr (maxLen : Nat) : Parser String := fun b pos =>
  match readVarint b pos with
  | .ok (n, p1) =>
    if n ≤ maxLen then
      match readBytes n b p1 with
      | .ok (x, p2) => if h : x.IsValidUTF8 then .ok (String.ofByteArray x h, p2) else .error .badUtf8
      | .error e => .error e
    else .error .tooLarge
  | .error e => .error e

theorem readStr_sound (maxLen : Nat) :
    Sound (readStr maxLen) encStr (fun s => s.toByteArray.size ≤ maxLen) := by
  intro b pos x pos' h
  unfold readStr at h
  split at h
  · next n p1 hn =>
    split at h
    · next hle =>
      split at h
      · next y p2 hy =>
        split at h
        · next hv =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨-, hp1, hb1⟩ := readVarint_sound b pos n p1 hn
          obtain ⟨hsz, hp2, hb2⟩ := readBytes_sound n b p1 y p2 hy
          refine ⟨by simp [hsz, hle], ?_, ?_⟩
          · simp [encStr, hsz, hp1, hp2]; omega
          · simp [encStr, hsz, hb1, hb2]
        · cases h
      · cases h
    · cases h
  · cases h

theorem readStr_complete (maxLen : Nat) (hmax : maxLen < varBound) :
    Complete (readStr maxLen) encStr (fun s => s.toByteArray.size ≤ maxLen) := by
  intro b pos x rest hpos hx h
  unfold encStr at h
  rw [List.append_assoc] at h
  have hsz : x.toByteArray.size < varBound := by omega
  unfold readStr
  simp only [readVarint_complete b pos _ _ hpos hsz h, hx, ite_true]
  rw [readBytes_complete _ _ _ x.toByteArray rest (le_size_of_bytesFrom hpos h) rfl (bytesFrom_skip h)]
  simp only [x.isValidUTF8, dite_true, Except.ok.injEq, Prod.mk.injEq]
  refine ⟨by trivial, ?_⟩
  simp [encStr]; omega

/-! ## Lists: a counted sequence, each item checked against the previous one -/

/-- Adjacent-pair condition along a list, starting from `prev`. -/
def Chain {α} (chk : Option α → α → Bool) : Option α → List α → Prop
  | _, [] => True
  | prev, x :: xs => chk prev x = true ∧ Chain chk (some x) xs

/-- Read `k` items, checking each against the previous one; tail-recursive. A lying count fails
as `truncated` once the input runs out, since nothing is preallocated. -/
def manyGo {α} (p : Parser α) (chk : Option α → α → Bool) (b : ByteArray) :
    Nat → Nat → Option α → List α → Except DecodeError (List α × Nat)
  | 0, pos, _, acc => .ok (acc.reverse, pos)
  | k + 1, pos, prev, acc =>
    match p b pos with
    | .ok (x, pos') => if chk prev x then manyGo p chk b k pos' (some x) (x :: acc) else .error .nonCanonical
    | .error e => .error e

theorem manyGo_sound {α} {p : Parser α} {enc : α → List UInt8} {Q : α → Prop}
    (hp : Sound p enc Q) (chk : Option α → α → Bool) (b : ByteArray) :
    ∀ k pos prev acc l pos', manyGo p chk b k pos prev acc = .ok (l, pos') →
      ∃ xs, l = acc.reverse ++ xs ∧ xs.length = k ∧ Chain chk prev xs ∧ (∀ x ∈ xs, Q x) ∧
        pos' = pos + (xs.flatMap enc).length ∧ bytesFrom b pos = xs.flatMap enc ++ bytesFrom b pos'
  | 0, pos, prev, acc, l, pos', h => by
    simp only [manyGo, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, rfl, trivial, by simp, by simp, by simp⟩
  | k + 1, pos, prev, acc, l, pos', h => by
    simp only [manyGo] at h
    split at h
    · next x p1 hx =>
      split at h
      · next hc =>
        obtain ⟨hq, hp1, hb1⟩ := hp b pos x p1 hx
        obtain ⟨xs, rfl, hlen, hch, hqs, hp2, hb2⟩ :=
          manyGo_sound hp chk b k p1 (some x) (x :: acc) l pos' h
        refine ⟨x :: xs, by simp, by simp [hlen], ⟨hc, hch⟩, ?_, ?_, ?_⟩
        · intro y hy; simp only [List.mem_cons] at hy; rcases hy with rfl | hy; exact hq; exact hqs y hy
        · simp [hp2, hp1]; omega
        · simp [hb1, hb2]
      · cases h
    · cases h

theorem manyGo_complete {α} {p : Parser α} {enc : α → List UInt8} {ok : α → Prop}
    (hp : Complete p enc ok) (chk : Option α → α → Bool) (b : ByteArray) :
    ∀ (xs : List α) pos prev acc rest, pos ≤ b.size → Chain chk prev xs → (∀ x ∈ xs, ok x) →
      bytesFrom b pos = xs.flatMap enc ++ rest →
      manyGo p chk b xs.length pos prev acc = .ok (acc.reverse ++ xs, pos + (xs.flatMap enc).length)
  | [], pos, prev, acc, rest, _, _, _, _ => by simp [manyGo]
  | x :: xs, pos, prev, acc, rest, hpos, hch, hok, h => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    have hx := hp b pos x _ hpos (hok x (.head _)) h
    simp only [List.length_cons, manyGo, hx, hch.1, ite_true]
    rw [manyGo_complete hp chk b xs _ (some x) (x :: acc) rest (le_size_of_bytesFrom hpos h) hch.2
      (fun y hy => hok y (.tail _ hy)) (bytesFrom_skip h)]
    simp; omega

/-- A chain of a transitive relation is pairwise. -/
theorem pairwise_of_chain {α} {R : α → α → Prop} (htrans : ∀ a b c, R a b → R b c → R a c)
    {f : Option α → α → Bool} (hf : ∀ a x, f (some a) x = true → R a x) :
    ∀ {prev : Option α} {l : List α}, Chain f prev l → l.Pairwise R
  | _, [], _ => List.Pairwise.nil
  | _, x :: xs, ⟨_, hrest⟩ => by
    have ih := pairwise_of_chain htrans hf hrest
    refine List.pairwise_cons.2 ⟨?_, ih⟩
    intro y hy
    cases xs with
    | nil => cases hy
    | cons z zs =>
      have hxz := hf x z hrest.1
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hxz
      · exact htrans _ _ _ hxz ((List.pairwise_cons.1 ih).1 y hy)

/-- A pairwise list is a chain, given the check accepts its first element. -/
theorem chain_of_pairwise {α} {R : α → α → Prop} {f : Option α → α → Bool}
    (hf : ∀ a x, R a x → f (some a) x = true) :
    ∀ {prev : Option α} {l : List α}, (∀ x ∈ l.head?, f prev x = true) → l.Pairwise R →
      Chain f prev l
  | _, [], _, _ => trivial
  | _, x :: xs, h0, hp => by
    refine ⟨h0 x rfl, chain_of_pairwise hf ?_ (List.pairwise_cons.1 hp).2⟩
    intro y hy
    cases xs with
    | nil => cases hy
    | cons z zs =>
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hf _ _ ((List.pairwise_cons.1 hp).1 _ (.head _))

/-- The check for strictly increasing sequences (`none` = first item). -/
def chkLt {α} [Ord α] : Option α → α → Bool
  | none, _ => true
  | some a, x => compare a x == .lt

theorem chkLt_iff {α} [Ord α] (a x : α) : chkLt (some a) x = true ↔ compare a x = .lt := by
  simp [chkLt]

theorem sorted_of_chain {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α] {prev : Option α} {l : List α}
    (h : Chain chkLt prev l) : StrictlySorted l :=
  pairwise_of_chain (R := fun a b => compare a b = .lt) (fun _ _ _ => cmp_lt_trans) (fun a x h => (chkLt_iff a x).1 h) h

theorem chain_of_sorted {α : Type} [Ord α] {l : List α} (h : StrictlySorted l) : Chain chkLt none l :=
  chain_of_pairwise (R := fun a b => compare a b = .lt) (fun a x h => (chkLt_iff a x).2 h) (fun _ _ => rfl) h

/-! ## Writers: append to an accumulator -/

def wByte (acc : ByteArray) (x : UInt8) : ByteArray := acc.push x

theorem wByte_toList (acc : ByteArray) (x : UInt8) :
    (wByte acc x).data.toList = acc.data.toList ++ [x] := by
  cases acc; simp [wByte, ByteArray.push]

def wVar (acc : ByteArray) (n : Nat) : ByteArray :=
  if n < 128 then acc.push n.toUInt8 else wVar (acc.push (n % 128 + 128).toUInt8) (n / 128)
termination_by n
decreasing_by omega

theorem wVar_toList (acc : ByteArray) (n : Nat) :
    (wVar acc n).data.toList = acc.data.toList ++ encVar n := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    rw [wVar, encVar]
    split
    · exact wByte_toList acc _
    · rw [ih (n / 128) (by omega), ← wByte, wByte_toList]; simp

def wBytes (acc : ByteArray) (x : ByteArray) : ByteArray := acc ++ x

theorem wBytes_toList (acc x : ByteArray) :
    (wBytes acc x).data.toList = acc.data.toList ++ x.data.toList := by
  simp [wBytes, ByteArray.data_append]

def wStr (acc : ByteArray) (s : String) : ByteArray :=
  wBytes (wVar acc s.toByteArray.size) s.toByteArray

theorem wStr_toList (acc : ByteArray) (s : String) :
    (wStr acc s).data.toList = acc.data.toList ++ encStr s := by
  simp [wStr, wBytes_toList, wVar_toList, encStr]

/-- `l.foldl w acc`, which is a loop, appends `l.flatMap enc`. -/
theorem foldl_toList {α} (w : ByteArray → α → ByteArray) (enc : α → List UInt8)
    (hw : ∀ acc x, (w acc x).data.toList = acc.data.toList ++ enc x) :
    ∀ (l : List α) (acc : ByteArray), (l.foldl w acc).data.toList = acc.data.toList ++ l.flatMap enc
  | [], acc => by simp
  | x :: xs, acc => by simp [foldl_toList w enc hw xs, hw]

/-! ## Combinators -/

def seqP {α β} (p : Parser α) (q : Parser β) : Parser (α × β) := fun b pos =>
  match p b pos with
  | .error e => .error e
  | .ok (x, p1) =>
    match q b p1 with
    | .error e => .error e
    | .ok (y, p2) => .ok ((x, y), p2)

theorem seqP_sound {α β} {p : Parser α} {q : Parser β} {e1 : α → List UInt8} {e2 : β → List UInt8}
    {Q1 : α → Prop} {Q2 : β → Prop} (hp : Sound p e1 Q1) (hq : Sound q e2 Q2) :
    Sound (seqP p q) (fun z => e1 z.1 ++ e2 z.2) (fun z => Q1 z.1 ∧ Q2 z.2) := by
  intro b pos z pos' h
  unfold seqP at h
  split at h
  · cases h
  · next x p1 h1 =>
    split at h
    · cases h
    · next y p2 h2 =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hq1, hp1, hb1⟩ := hp b pos x p1 h1
      obtain ⟨hq2, hp2, hb2⟩ := hq b p1 y p2 h2
      refine ⟨⟨hq1, hq2⟩, by simp [hp2, hp1]; omega, by simp [hb1, hb2]⟩

theorem seqP_complete {α β} {p : Parser α} {q : Parser β} {e1 : α → List UInt8} {e2 : β → List UInt8}
    {ok1 : α → Prop} {ok2 : β → Prop} (hp : Complete p e1 ok1) (hq : Complete q e2 ok2) :
    Complete (seqP p q) (fun z => e1 z.1 ++ e2 z.2) (fun z => ok1 z.1 ∧ ok2 z.2) := by
  intro b pos z rest hpos hz h
  simp only [List.append_assoc] at h
  have r1 := hp b pos z.1 _ hpos hz.1 h
  have r2 := hq b _ z.2 rest (le_size_of_bytesFrom hpos h) hz.2 (bytesFrom_skip h)
  simp only [seqP, r1, r2, List.length_append]
  congr 2; omega

def mapP {α β} (f : α → β) (p : Parser α) : Parser β := fun b pos =>
  match p b pos with
  | .error e => .error e
  | .ok (x, q) => .ok (f x, q)

theorem mapP_ok {α β} {f : α → β} {p : Parser α} {b : ByteArray} {pos : Nat} {y : β} {q : Nat}
    (h : mapP f p b pos = .ok (y, q)) : ∃ x, p b pos = .ok (x, q) ∧ y = f x := by
  unfold mapP at h
  split at h
  · cases h
  · next x q' h1 =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨x, h1, rfl⟩

theorem mapP_of_ok {α β} {f : α → β} {p : Parser α} {b : ByteArray} {pos : Nat} {x : α} {q : Nat}
    (h : p b pos = .ok (x, q)) : mapP f p b pos = .ok (f x, q) := by
  simp [mapP, h]

end LeanSync
