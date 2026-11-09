import Vinc.Json
import Vinc.TransportReasm

/-!
# Replay of the handshake fragment traces

The Lean half of the trace validation of the handshake fragment reassembly (`conn/reasm.rs`), the port of
`proofs/tla/TraceReasm.tla`. It reads the `txrs` events written by the Rust test `trace_reasm` and replays every
fragment through `Vinc.TransportReasm.add`: the runs and the message length the model computes must be the ones
recorded, and so must the length of the message handed over.
-/

namespace Vinc.TraceReasm
open Vinc.Json Vinc.TransportReasm

def isTag (t : String) : Bool := t == "txrs"

structure W where
  r : R := {}
  mx : Nat := 0
  nr : Nat := 0

def same (m : R) (j : J) (what : String) : Except String Unit := do
  let v ← field j "v"
  let rec' : R := { runs := ← pairList (← field v "runs"), total := ← natF v "total" }
  if m == rec' then pure () else throw s!"{what}: the model computes {repr m}, the code recorded {repr rec'}"

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    same {} j "init"
    pure { r := {}, mx := ← natF j "max", nr := ← natF j "nr" }
  | "add" =>
    let (out, r2) := add w.r w.mx w.nr (← natF j "total") (← natF j "off") (← natF j "len")
    check ((out.map (fun t => (t : Int))).getD (-1) == (← intF j "out")) "add: the result differs"
    same r2 j "add"
    pure { w with r := r2 }
  | op => throw s!"unknown reassembly op {op}"

end Vinc.TraceReasm
