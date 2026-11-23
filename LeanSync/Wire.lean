import LeanSync.Types

/-!
# Wire format v1: limits, well-formedness, encoders and total decoders

Executable module (imports `Init` only).

STAGE 1: the limits and the `WireOk` predicates are real; every function body marked
`STAGE-1 PLACEHOLDER` is a `sorry` to be replaced in stage 2. None may remain at the end.

Layout (see `docs/sync-design.md`, "Wire format"): every top-level value starts with the format
version byte (`1`) and a kind byte; integers are canonical unsigned LEB128 below 2^64; replica ids
are 16 bytes big-endian; hashes and digests are exactly 32 bytes; strings are a length-prefixed
UTF-8 byte string.
-/

namespace LeanSync

open LeanCrdt

/-! ## Limits (part of wire version 1: both sides must agree) -/

def wireVersion : UInt8 := 1
def maxStateBytes : Nat := 64 * 1024 * 1024          -- encoded state, header included
def maxMessageBytes : Nat := maxStateBytes + 64      -- one peer message
def maxEnvelopeBytes : Nat := 2 * maxStateBytes      -- one event in / one effect list out
def maxPathBytes : Nat := 4096                       -- UTF-8 bytes of one path
def maxBatch : Nat := 1024                           -- hashes in one want/noBlob/have
def maxSessions : Nat := 32
def maxInflightPerPeer : Nat := 32                   -- outstanding blob requests per session
def maxToldNo : Nat := 4096                          -- remembered `noBlob` answers per session
def hashBytes : Nat := 32
def varintBound : Nat := 2 ^ 64                      -- every encoded integer is below this

/-! ## Kinds (second byte of every top-level value) -/

def kindState : UInt8 := 1
def kindMessage : UInt8 := 2
def kindEvent : UInt8 := 3
def kindEffects : UInt8 := 4

/-! ## Well-formedness for the wire (what the encoder can represent and the decoder accepts) -/

/-- A hash the protocol accepts: exactly 32 bytes (SHA-256). -/
def _root_.LeanCrdt.Hash.WireOk (h : Hash) : Prop := h.bytes.size = hashBytes

/-- A strictly sorted, non-empty batch of at most `maxBatch` wire hashes. -/
def HashBatchOk (hs : List Hash) : Prop :=
  StrictlySorted hs ∧ 0 < hs.length ∧ hs.length ≤ maxBatch ∧ ∀ h ∈ hs, Hash.WireOk h

/-- Encoder (stage 2). Total; the output starts with `[wireVersion, kindState]`. -/
def encodeState (s : State) : ByteArray :=
  sorry -- STAGE-1 PLACEHOLDER

/-- A state the wire can carry: 32-byte hashes, paths of at most `maxPathBytes` bytes, counters
below 2^64, and an encoding of at most `maxStateBytes` bytes. (Sortedness, positive counters and
coverage are already fields of `State`.) -/
def _root_.LeanCrdt.State.WireOk (s : State) : Prop :=
  (∀ e ∈ s.entries, Hash.WireOk e.hash ∧ e.path.utf8ByteSize ≤ maxPathBytes) ∧
  (∀ p ∈ s.context.entries, p.2 < varintBound) ∧
  (encodeState s).size ≤ maxStateBytes

def Message.WireOk : Message → Prop
  | .hello _ _ _ => True
  | .digest _ => True
  | .state _ s => s.WireOk
  | .want hs => HashBatchOk hs
  | .noBlob hs => HashBatchOk hs
  | .have hs => HashBatchOk hs
  | .bye _ => True

/-! ## Encoders and total decoders

Decoders are total, run in time linear in the input (one tail-recursive pass, adjacent-pair
order checks, O(1) context lookup through an `Array` indexed by the dot's replica index), and
reject truncated, trailing, oversized and non-canonical input. -/

/-- Decode a state record (header included) and rebuild its invariants. -/
def decodeState (b : ByteArray) : Except DecodeError State :=
  sorry -- STAGE-1 PLACEHOLDER

def encodeMessage (m : Message) : ByteArray :=
  sorry -- STAGE-1 PLACEHOLDER

def decodeMessage (b : ByteArray) : Except DecodeError Message :=
  sorry -- STAGE-1 PLACEHOLDER

/-- Event envelope (host → Lean). The encoder exists for tests and for the round-trip theorem. -/
def encodeEvent (e : Event) : ByteArray :=
  sorry -- STAGE-1 PLACEHOLDER

def decodeEvent (b : ByteArray) : Except DecodeError Event :=
  sorry -- STAGE-1 PLACEHOLDER

/-- Effects envelope (Lean → host). The decoder exists for tests and the simulator. -/
def encodeEffects (effs : List Effect) : ByteArray :=
  sorry -- STAGE-1 PLACEHOLDER

def decodeEffects (b : ByteArray) : Except DecodeError (List Effect) :=
  sorry -- STAGE-1 PLACEHOLDER

end LeanSync
