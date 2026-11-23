import Lean
open Lean

/-- Print the transitive import closure of the given modules, one per line,
in import order (dependencies before dependents). -/
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules (args.toArray.map fun m => { module := m.toName }) {} (loadExts := false)
  for m in env.header.moduleNames do
    IO.println m
