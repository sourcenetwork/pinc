import Vinc.Json
import Vinc.DtnForward

/-!
# Replay of the forwarder traces

The replay half of the trace validation of `Forwarder` (the Rust test `trace_dtn_forward`; the TLA+ half is
`TraceDtnForward.tla`). Every recorded call is replayed through the model functions the theorems are about
(`DtnForward.step`, `DtnForward.poll`) on the model forwarder of its run, and any difference exits with an error
naming the line:

* `new`: a fresh forwarder with the recorded capacities and policy.
* `step`: the input at its time; the error the code returned must be the model's.
* `poll`: the action the code returned must be the model's.
* after every `step` and `poll`: the copies held, the copies handed and every transfer timer of the code must be
  those of the model state (`ch`, `cd`, `tm`).
-/

namespace Vinc.TraceDtnForward
open Vinc.Json Vinc.DtnForward

/-- The replay state: the model forwarder of the current run. -/
structure W where
  f : Option F := none

instance : Inhabited W := ⟨{}⟩

/-- The tags of this replay (the field `t`). -/
def isTag (t : String) : Bool := t == "fw"

def parseInput (j : J) : Except String Input := do
  match ← strF j "k" with
  | "tick" => pure .tick
  | "hold" => pure (.hold (← natF j "id") (← natF j "dest") (← natF j "exp") (← natF j "copies"))
  | "up" => pure (.linkUp (← natF j "peer"))
  | "down" => pure (.linkDown (← natF j "peer"))
  | "ack" => pure (.acked (← natF j "peer") (← natF j "id"))
  | "forget" => pure (.forget (← natF j "id"))
  | k => throw s!"unknown input {k}"

def errName : Err → String
  | .ok => "ok" | .duplicate => "Duplicate" | .full => "Full" | .noCopies => "NoCopies" | .unknown => "Unknown"

/-- The model's reading of the observables, in the shape the trace records them. -/
def observe (f : F) (nIds nPeers : Nat) : List Nat × List Nat × List (List Nat) :=
  let ids := List.range nIds |>.map (· + 1)
  (ids.map fun i => (copiesHeld f i).getD 0,
   ids.map fun i => handed f i,
   ids.map fun i => (List.range nPeers).map fun p => ((timer f (p + 1) i).map (· + 1)).getD 0)

def checkSnap (j : J) (f : F) : Except String Unit := do
  let ch ← natList (← field j "ch")
  let cd ← natList (← field j "cd")
  let tmArr ← match (← field j "tm").arr? with | some a => pure a.toList | none => throw "tm"
  let tm ← tmArr.mapM natList
  let nPeers := (tm.headD []).length
  let (mch, mcd, mtm) := observe f ch.length nPeers
  check (mch == ch) s!"copies held: model {mch}, code {ch}"
  check (mcd == cd) s!"copies handed: model {mcd}, code {cd}"
  check (mtm == tm) s!"timers: model {mtm}, code {tm}"

def parseAct (j : J) : Except String Act := do
  match ← strF j "k" with
  | "none" => pure .none
  | "release" => pure (.release (← natF j "bundle"))
  | "send" => pure (.send (← natF j "peer") (← natF j "bundle") (← natF j "copies") (← boolF j "retr"))
  | k => throw s!"unknown action {k}"

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "e" with
  | "new" =>
    pure { f := some (F.new (← natF j "retry") (← natF j "max") (← natF j "now") (← natF j "b") (← natF j "l") (← natF j "tt")) }
  | "step" =>
    let some f := w.f | throw "step before new"
    let inp ← parseInput (← field j "in")
    let (f', e) := step f (← natF j "now") inp
    check (errName e == (← strF j "err")) s!"error: model {errName e}, code {← strF j "err"}"
    checkSnap j f'
    pure { f := some f' }
  | "poll" =>
    let some f := w.f | throw "poll before new"
    let (f', a) := poll f
    let rec_ ← parseAct (← field j "act")
    check (a == rec_) s!"action: model {repr a}, code {repr rec_}"
    checkSnap j f'
    pure { f := some f' }
  | e => throw s!"unknown forwarder event {e}"

end Vinc.TraceDtnForward
