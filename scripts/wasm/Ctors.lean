import Lean
open Lean

/-- Print, as one JSON object, the constructor names of the LeanSync types that cross the
host boundary. The JS codec test (test/unit/codec.test.mjs) checks its own tables against this
list, so a constructor added in Lean fails the JS tests until the JS codec handles it.
usage: lake env lean --run scripts/wasm/Ctors.lean -/
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `LeanSync.Envelope }] {} (loadExts := false)
  let types := [`LeanSync.Event, `LeanSync.LocalOp, `LeanSync.Query, `LeanSync.Effect, `LeanSync.Notice,
    `LeanSync.Reply, `LeanSync.PendingStatus, `LeanSync.PeerStatus, `LeanSync.CloseReason, `LeanSync.DecodeError]
  let mut parts : Array String := #[]
  for t in types do
    match env.find? t with
    | some (.inductInfo i) =>
      let names := i.ctors.map (fun c => s!"\"{c.componentsRev.head!}\"")
      parts := parts.push s!"\"{t.componentsRev.head!}\": [{", ".intercalate names}]"
    | _ => throw (IO.userError s!"{t} is not an inductive type")
  IO.println ("{" ++ ", ".intercalate parts.toList ++ "}")
