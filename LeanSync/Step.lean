import LeanSync.Wire

/-!
# The step function and the wasm boundary

Executable module (imports `Init` only).

STAGE 1: signatures only. Bodies marked `STAGE-1 PLACEHOLDER` are `sorry` and will be written in
stage 2; none may remain at the end.
-/

namespace LeanSync

open LeanCrdt

/-- The protocol: one event in, the new machine and the effects out, in the order the host must
carry them out. Pure, total, deterministic. -/
def step (m : Machine) (ev : Event) : Machine × List Effect :=
  sorry -- STAGE-1 PLACEHOLDER

/-- Run a sequence of events; returns the final machine and the effects of each step. -/
def run (m : Machine) (evs : List Event) : Machine × List (List Effect) :=
  let r := evs.foldl (fun (acc : Machine × List (List Effect)) ev =>
    let (m', effs) := step acc.1 ev
    (m', effs :: acc.2)) (m, [])
  (r.1, r.2.reverse)

/-- The single boundary function: an encoded event in, the encoded effect list out. A malformed
envelope yields `[notify (badEvent e)]` and leaves the machine unchanged. -/
def process (m : Machine) (input : ByteArray) : Machine × ByteArray :=
  match decodeEvent input with
  | .ok ev => let (m', effs) := step m ev; (m', encodeEffects effs)
  | .error e => (m, encodeEffects [.notify (.badEvent e)])

/-- The machine lives here between calls (single-threaded wasm: one call at a time). -/
initialize machineRef : IO.Ref Machine ← IO.mkRef .uninit

/-- Exported entry point for the C shim (`ByteArray → IO ByteArray`; the shim unwraps the IO
result). The only impure code in the library: read the machine, step, write it back. -/
@[export lean_sync_process]
def processIO (input : ByteArray) : IO ByteArray := do
  let m ← machineRef.get
  machineRef.set .uninit          -- drop our reference so `step` can update `m` in place
  let (m', out) := process m input
  machineRef.set m'
  return out

end LeanSync
