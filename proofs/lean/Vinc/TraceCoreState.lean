import Vinc.Json
import Vinc.CoreStateThm

/-!
# Replay of the saved-state trace

The Lean half of the trace validation of the endpoint's saved state (`core_state.ndjson` and `core_state_wide.ndjson`,
written by the Rust test `trace_core_state`): every `cs` event is one call of the real `export_state` or
`restore_state` and is checked against the model of `Vinc.CoreState`, whose theorems are in `Vinc.CoreStateThm`.

A `restore` event carries the bytes the endpoint exported before (`pre`, read back as the tables it held), the input
(`in`), the time, whether the code accepted it, what it reported and the bytes exported after (`post`). The model must
read `pre` as a state that encodes to `pre`, accept exactly the inputs the code accepted (an accepted input must be
the encoding of the state it reads), report what the code reported, and its tables after the restore must encode to
`post`; a refused input must leave `pre` unchanged. An `export` event is accepted when the buffer holds the state
exactly when the code fitted it. It is the port of `proofs/tla/TraceCoreState.tla`, on the same events and with the
bounds of the test endpoint (3 ticket slots, 256 round trips, 256 prekey peers); this replay also reads the wide
file, with times and expiries up to 2^64 - 1.
-/

namespace Vinc.TraceCoreState
open Vinc.Json Vinc.DtnCodec Vinc.CoreState

def isTag (t : String) : Bool := t == "cs"

def toBytes (l : List Nat) : Bytes := l.map (Fin.ofNat 256)

/-- The bounds of the endpoint of the test. -/
def cfg : Cfg := ⟨3, 256, 256, false, false⟩

/-- The tables the endpoint held: what its own export reads as. -/
def held (pre : Bytes) : Option St :=
  match parse pre with
  | some p => if enc p == pre then some p else none
  | none => none

def replayEvent (j : J) : Except String Unit := do
  let op ← strF j "op"
  let pre := toBytes (← natList (← field j "pre"))
  let some p := held pre | throw "the exported state is not one the model reads back to the same bytes"
  match op with
  | "export" =>
    let cap ← natF j "cap"
    let ok ← boolF j "ok"
    check (ok == decide (pre.length ≤ cap)) s!"export into {cap} bytes: code {ok}, state of {pre.length} bytes"
  | "restore" =>
    let now ← natF j "now"
    let inp := toBytes (← natList (← field j "in"))
    let ok ← boolF j "ok"
    let res ← natList (← field j "res")
    let post := toBytes (← natList (← field j "post"))
    let r := restore cfg p inp now
    check ((r.2.isSome) == ok) s!"the model and the code disagree on accepting the input: code {ok}"
    check ((parse inp).isSome == ok) "parse and restore disagree"
    match parse inp with
    | some q => check (enc q == inp) "an accepted input is not the encoding of the state it reads"
    | none => pure ()
    match r.2 with
    | some (a, b, c) =>
      check (res == [a, b, c]) s!"the code reported {res}, the model {[a, b, c]}"
      check (enc r.1 == post) "the tables after the restore are not the exported bytes"
    | none =>
      check res.isEmpty "a refused input reports counts"
      check (post == pre) "a refused input changed the tables"
  | _ => throw s!"unknown op {op}"

end Vinc.TraceCoreState
