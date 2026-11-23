import Std.Data.HashMap

/-!
Spike: a trivial `ByteArray → ByteArray` function exported to C, used to check that
compiled Lean runs under WebAssembly. It deliberately touches several parts of the
runtime: `ByteArray`, `Array`, `String` (UTF-8 decode/encode, formatting), `Nat`
bignums (well beyond 2^64), `Std.HashMap`, closures, and a `panic!`-free error path.

The output is a UTF-8 text report so that the JS side can print/compare it, followed by
the reversed input bytes.
-/

namespace WasmDemo

/-- Hex encoding of a byte array. -/
def hex (b : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut s := ""
  for x in b do
    s := s.push digits[(x / 16).toNat]!
    s := s.push digits[(x % 16).toNat]!
  return s

def reverseBytes (b : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity b.size
  for i in [0:b.size] do
    out := out.push b[b.size - 1 - i]!
  return out

/-- Byte histogram via `Std.HashMap`, rendered sorted by byte value. -/
def histogram (b : ByteArray) : String :=
  let m : Std.HashMap UInt8 Nat := b.foldl (fun m x => m.insert x (m.getD x 0 + 1)) {}
  let entries := m.toArray.qsort (fun a b => a.1 < b.1)
  ",".intercalate (entries.toList.map fun (k, v) => s!"{k}:{v}")

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- Bignum workout: product of (byte+1) over the first 256 input bytes, times 2^200, plus 40!. -/
def bigNum (b : ByteArray) : Nat :=
  (b.extract 0 256).foldl (fun acc x => acc * (x.toNat + 1)) 1 * 2 ^ 200 + factorial 40

/-- Literals between 2^31 and 2^63 are scalars on a 64-bit host but heap objects on
wasm32; this exercises how the 64-bit compiler's C treats them. -/
def midLiterals (n : Nat) : Nat := Id.run do
  let k := 5000000000          -- > 2^32
  let j := 3000000000          -- between 2^31 and 2^32
  let mut acc := #[]
  for i in [0:(min n 1000)+3] do
    acc := acc.push (k + i)
    acc := acc.push (j * i)
    acc := acc.push k
    acc := acc.push k            -- second owned use of the same literal
  return acc.foldl (· + ·) 0

/-- Platform-dependent facts. `hashOrder` is the *unsorted* iteration order of a HashMap
with String keys: if bucket selection depends on the width of `USize`, it differs between
a 64-bit native build and wasm32. -/
def usizeInfo : String :=
  let m : Std.HashMap String Nat := (List.range 12).foldl (fun m i => m.insert s!"k{i}" i) {}
  let order := m.toList.map (·.2)
  s!"numBits={System.Platform.numBits} usizeMax={USize.size - 1} hashOrder={order}"

/-- Non-tail recursion, to probe the wasm stack limit. -/
def depth : Nat → Nat
  | 0 => 0
  | n + 1 => depth n + 1

/-- Probes selected by the input (spike only): `!panic` triggers a Lean panic (out-of-bounds
`get!`), `!deep N` recurses N frames deep without tail calls. -/
def probe (s : String) : Option String :=
  if s == "!panic" then
    some s!"panic-probe result={(#[1, 2, 3] : Array Nat)[7]!}"
  else if s.startsWith "!deep " then
    let n := (s.drop 6).toNat!
    some s!"deep-probe result={depth n}"
  else none

def process (input : ByteArray) : ByteArray :=
  match (String.fromUTF8? input).bind probe with
  | some r => r.toUTF8
  | none =>
  let text := match String.fromUTF8? input with
    | some s => s!"utf8 len={s.length} upper={s.toUpper.quote}"
    | none => "not-utf8"
  let report := String.intercalate "\n" [
    s!"bytes={input.size}",
    text,
    s!"hist={histogram input}",
    s!"big={bigNum input}",
    s!"mid={midLiterals input.size}",
    s!"rev={hex (reverseBytes input)}",
    usizeInfo
  ]
  report.toUTF8 ++ "\n".toUTF8 ++ reverseBytes input

/-- The C-visible entry point. Takes ownership of `input`, returns a fresh `ByteArray`. -/
@[export lean_wasm_demo_process]
def processExport (input : ByteArray) : ByteArray := process input

end WasmDemo

/-- Native entry point, used to produce the reference output the wasm build is compared against.
Reads the input bytes from the file named by the first argument, writes the result to stdout. -/
def main (args : List String) : IO Unit := do
  let some path := args.head? | throw <| IO.userError "usage: wasm-demo-native <file>"
  let input ← IO.FS.readBinFile path
  (← IO.getStdout).write (WasmDemo.process input)
