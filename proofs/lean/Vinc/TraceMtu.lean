import Vinc.Json
import Vinc.TransportMtu

/-!
# Replay of the path MTU traces

The Lean half of the trace validation of path MTU discovery (`conn/mtu.rs`), the port of `proofs/tla/TraceMtu.tla`.
It reads the `txmt` events written by the Rust test `trace_mtu` and replays every call through the functions of
`Vinc.TransportMtu`: the state the model computes must be the state recorded (a time shown at most `2^31 - 1` in the
narrow runs, as the 32-bit checker saw it), and so must the size a call answers and whether the path dropped to the
minimum.
-/

namespace Vinc.TraceMtu
open Vinc.Json Vinc.TransportMtu

def isTag (t : String) : Bool := t == "txmt"

def top32 : Nat := 2 ^ 31 - 1

def optOf (v : Int) : Option Nat := if v < 0 then none else some v.toNat
def optF (j : J) (k : String) : Except String (Option Nat) := do pure (optOf (← intF j k))

def mOf (v : J) : Except String M := do
  let susp : Option (Nat × Nat) := match (← intList (← field v "susp")) with
    | [b, a] => if b < 0 then none else some (b.toNat, a.toNat)
    | _ => none
  pure { cur := ← natF v "cur", infl := ← optF v "infl", ptok := ← optF v "ptok", probed := ← boolF v "probed", jdone := ← boolF v "jdone",
         retry := ← natF v "retry", started := ← boolF v "started", lbig := ← optF v "lbig", backed := ← optF v "backed",
         pbig := ← optF v "pbig", susp }

/-- The model's state as the recorder shows it: in the narrow runs the times are clamped at `2^31 - 1`. -/
def clamp (w : Bool) (m : M) : M :=
  if w then m else { m with retry := min m.retry top32, susp := m.susp.map (fun (b, a) => (b, min a top32)) }

def same (w : Bool) (m : M) (j : J) (what : String) : Except String Unit := do
  let rec' ← mOf (← field j "v")
  if clamp w m == rec' then pure () else throw s!"{what}: the model computes {repr (clamp w m)}, the code recorded {repr rec'}"

def replayEvent (j : J) (m : M) : Except String M := do
  let w := decide (900 ≤ (← natF j "run"))
  let upd (m2 : M) (what : String) : Except String M := do same w m2 j what; pure m2
  match ← strF j "op" with
  | "init" => upd {} "init"
  | "start" => upd (start m) "start"
  | "big" => upd (setBig m (← optF j "lb") (← optF j "ba") (← optF j "pb")) "big"
  | "target" =>
    let r := target m (← boolF j "allowed") (← natF j "im") (← boolF j "ll") (← natF j "now")
    check ((r.map (fun n => (n : Int))).getD (-1) == (← intF j "r")) "target: the size due differs"
    upd m "target"
  | "sent" => upd (probeSent m (← natF j "size") (← natF j "pn")) "sent"
  | "raise" =>
    let (m2, r) := raise m (← natF j "size") (← natF j "pn")
    check ((r.map (fun n => (n : Int))).getD (-1) == (← intF j "r")) "raise: the answer differs"
    upd m2 "raise"
  | "echo" =>
    let (m2, r) := echo m (← natF j "size") (ceiling (← natF j "im"))
    check ((r.map (fun n => (n : Int))).getD (-1) == (← intF j "r")) "echo: the answer differs"
    upd m2 "echo"
  | "lost" => upd (probeLost m (← natF j "size") (← natF j "pn") (← natF j "now")) "lost"
  | "event" => upd (event m) "event"
  | "bh" => upd (blackHole m (← natF j "now") (← natF j "rtt")) "bh"
  | "bhc" =>
    let (m2, d) := blackHoleCheck m (← natF j "now")
    check (d == (← boolF j "r")) "bhc: the fallback differs"
    upd m2 "bhc"
  | op => throw s!"unknown path MTU op {op}"

end Vinc.TraceMtu
