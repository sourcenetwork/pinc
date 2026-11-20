import Pinc.Json
import Pinc.TransportMtu

/-!
# Replay of the path MTU traces

The Lean half of the trace validation of path MTU discovery (`conn/mtu.rs`), the port of `proofs/tla/TraceMtu.tla`.
It reads the `txmt` events written by the Rust test `trace_mtu` and replays every call through the functions of
`Pinc.TransportMtu`: the state the model computes must be the state recorded (a time shown at most `2^31 - 1` in the
narrow runs, as the 32-bit checker saw it), and so must the size a call answers, whether an outcome applied and
whether the path dropped to the minimum.
-/

namespace Pinc.TraceMtu
open Pinc.Json Pinc.TransportMtu

def isTag (t : String) : Bool := t == "txmt"

def top32 : Nat := 2 ^ 31 - 1

def optOf (v : Int) : Option Nat := if v < 0 then none else some v.toNat
def optF (j : J) (k : String) : Except String (Option Nat) := do pure (optOf (← intF j k))

/-- A probe in flight or kept by a flush arrives as `-1` or a `[size, pn]` pair. -/
def prF (j : J) (k : String) : Except String (Option (Nat × Nat)) := do
  match (← field j k) with
  | .neg _ => pure none
  | .num _ => throw s!"{k}: a lone size is no probe"
  | .arr a =>
    if a.size = 2 then
      match (a[0]!.int?, a[1]!.int?) with
      | (some s, some p) => if s < 0 ∨ p < 0 then throw s!"{k}: a negative probe" else pure (some (s.toNat, p.toNat))
      | _ => throw s!"{k}: a probe is two integers"
    else throw s!"{k}: a probe is two integers"
  | _ => throw s!"{k}: a probe is -1 or a pair"

def mOf (v : J) : Except String M := do
  let susp : Option (Nat × Nat) := match (← intList (← field v "susp")) with
    | [b, a] => if b < 0 then none else some (b.toNat, a.toNat)
    | _ => none
  pure { cur := ← natF v "cur", infl := ← prF v "infl", flushed := ← prF v "flushed", probed := ← boolF v "probed",
         jdone := ← boolF v "jdone", retry := ← natF v "retry", started := ← boolF v "started",
         lbig := ← optF v "lbig", backed := ← optF v "backed", pbig := ← optF v "pbig", susp }

/-- The model's state as the recorder shows it: in the narrow runs the times are clamped at `2^31 - 1`. -/
def clamp (w : Bool) (m : M) : M :=
  if w then m else { m with retry := min m.retry top32, susp := m.susp.map (fun (b, a) => (b, min a top32)) }

def same (w : Bool) (m : M) (j : J) (what : String) : Except String Unit := do
  let rec' ← mOf (← field j "v")
  if clamp w m == rec' then pure () else throw s!"{what}: the model computes {repr (clamp w m)}, the code recorded {repr rec'}"

/-- The size an op answered, as the recorder shows it: `-1` for none. -/
def riseF (j : J) : Except String Int := intF j "r"

def replayEvent (j : J) (m : M) : Except String M := do
  let w := decide (900 ≤ (← natF j "run"))
  let upd (m2 : M) (what : String) : Except String M := do same w m2 j what; pure m2
  let rise (r : Option Nat) : Except String Unit := do
    let want ← riseF j
    check (((r.map (fun n => (n : Int))).getD (-1)) == want) "the size that rose differs"
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
    let (m2, r) := raise m (← natF j "size")
    rise r
    upd m2 "raise"
  | "ack" =>
    let (m2, r) := acked m (← natF j "size") (← natF j "pn")
    let want ← riseF j
    -- `-2` for a refusal, `-1` for a flat acknowledgement, else the size that rose.
    let flat : Int :=
      r.map (fun r' => r'.map (fun n => (n : Int)) |>.getD (-1)) |>.getD (-2)
    check (flat == want) "the size that rose differs"
    upd m2 "ack"
  | "lost" =>
    let (m2, applied) := probeLost m (← natF j "size") (← natF j "pn") (← natF j "now")
    check (applied == (← boolF j "applied")) "lost: whether it applied differs"
    upd m2 "lost"
  | "flush" =>
    let (m2, applied) := flush m (← natF j "size") (← natF j "pn")
    check (applied == (← boolF j "applied")) "flush: whether it applied differs"
    upd m2 "flush"
  | "fack" =>
    let (m2, r) := flushedAcked m (← natF j "pn")
    rise r
    upd m2 "fack"
  | "event" => upd (event m) "event"
  | "bh" => upd (blackHole m (← natF j "now") (← natF j "rtt")) "bh"
  | "bhc" =>
    let (m2, d) := blackHoleCheck m (← natF j "now")
    check (d == (← boolF j "r")) "bhc: the fallback differs"
    upd m2 "bhc"
  | op => throw s!"unknown path MTU op {op}"

end Pinc.TraceMtu
