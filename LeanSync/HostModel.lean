import LeanSync.Step

/-!
# What the host can carry out

A model of the host's knowledge, built only from the events it has given Lean and the effects it
has already executed. An effect is *executable* when the host can carry it out in that view: a
send or close goes to a connection that is open as far as Lean has been told, a persist is not
issued while another is unacknowledged, a blob is served only if the host has reported it
present, and every message and persisted state is well formed for the wire (`WireOk`, which
includes the size limits), so that the receiving peer, and the host itself, can decode it.

Used by the theorem `effects_executable` and checked on every step by the simulator.
The definitions here are real (not placeholders).
-/

namespace LeanSync

open LeanCrdt

structure HostView where
  /-- Connections the host has reported and neither the host nor Lean has closed. -/
  peers : List PeerId := []
  /-- Tag of the persist the host is executing, if any. -/
  pendingPersist : Option Nat := none
  /-- Blobs the host has reported (or implied, by a local put) present and not reported lost. -/
  blobs : List Hash := []

namespace HostView

def addBlobs (v : HostView) (hs : List Hash) : HostView :=
  { v with blobs := hs.foldl (fun acc h => if h ∈ acc then acc else h :: acc) v.blobs }

def onEvent (v : HostView) : Event → HostView
  | .init _ _ bs => v.addBlobs bs
  | .initFresh _ bs => v.addBlobs bs
  | .connected p => if p ∈ v.peers then v else { v with peers := p :: v.peers }
  | .disconnected p => { v with peers := v.peers.filter (· ≠ p) }
  | .localOp (.putMany items) => v.addBlobs (items.map (·.hash))
  | .localOp (.resolve _ h) => v.addBlobs [h]
  | .persisted t _ => if v.pendingPersist = some t then { v with pendingPersist := none } else v
  | .persistFailed t => if v.pendingPersist = some t then { v with pendingPersist := none } else v
  | .blobStored h _ => v.addBlobs [h]
  | .blobsStored hs => v.addBlobs hs
  | .blobLost h => { v with blobs := v.blobs.filter (· ≠ h) }
  | _ => v

/-- Carry out one effect, or `none` if the host could not. -/
def exec (v : HostView) : Effect → Option HostView
  | .send p m => if p ∈ v.peers ∧ checkMessage m = true then some v else none
  | .close p _ => if p ∈ v.peers then some { v with peers := v.peers.filter (· ≠ p) } else none
  | .persist t s =>
    if v.pendingPersist = none ∧ checkWire s = true
    then some { v with pendingPersist := some t } else none
  | .fetch p hs =>
    if p ∈ v.peers ∧ checkBatch hs = true then some v else none
  | .serveBlob p h => if p ∈ v.peers ∧ h ∈ v.blobs then some v else none
  | .notify _ => some v
  | .reply _ => some v

def execAll (v : HostView) : List Effect → Option HostView
  | [] => some v
  | e :: es => match v.exec e with
    | some v' => execAll v' es
    | none => none

end HostView

/-- Every effect of every step of the run is executable, in order, by a host that has seen
exactly the preceding events and effects. -/
def Executable (step : Machine → Event → Machine × List Effect) :
    HostView → Machine → List Event → Prop
  | _, _, [] => True
  | v, m, ev :: evs =>
    let v₁ := v.onEvent ev
    let r := step m ev
    match v₁.execAll r.2 with
    | some v₂ => Executable step v₂ r.1 evs
    | none => False

end LeanSync
