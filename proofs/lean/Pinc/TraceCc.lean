import Pinc.Json
import Pinc.TransportCc

/-!
# Replay of the congestion control traces

The Lean half of the trace validation of the congestion controller and the pacer (`recovery/cubic.rs`,
`round_exit.rs`, `delivery.rs`, `pacer.rs`), the port of `proofs/tla/TraceCc.tla`. It reads the `txcc` events written by
the Rust test `trace_cc` and replays every call through the functions of `Pinc.TransportCc`: the state the model
computes must be the state recorded, field by field, and so must the answers of a query. The wide file replays runs
with windows up to `2^40` and times and byte counts up to `u64::MAX`; the 32-bit checker reads the other.
-/

namespace Pinc.TraceCc
open Pinc.Json Pinc.TransportCc

def isTag (t : String) : Bool := t == "txcc"

structure W where
  c : Cc := {}
  p : Pacer := {}

def optOf (v : Int) : Option Nat := if v < 0 then none else some v.toNat
def optF (j : J) (k : String) : Except String (Option Nat) := do pure (optOf (← intF j k))

/-- The state a recorded view shows. -/
def ccOf (v : J) : Except String Cc := do
  pure { cwnd := ← natF v "cwnd", ssthresh := ← natF v "ss", wMax := ← natF v "wmax", wEst := ← natF v "west",
         kMs := ← natF v "k", epoch := ← optF v "epoch", recovery := ← optF v "rec", streak := ← natF v "streak",
         re := { roundEnd := ← natF v "rend", ref := ← optF v "ref", rmin := ← optF v "rmin", samples := ← natF v "samp" },
         probe := { start := ← optF v "pst", bytes := ← natF v "pby", rate := ← natF v "rate" },
         slack := ← natF v "slack" }

/-- The largest value of a 32-bit checker integer: a threshold not set or a release time past the end is recorded as it
in the narrow runs. -/
def top32 : Nat := 2 ^ 31 - 1

def same (w : Bool) (m : Cc) (j : J) (what : String) : Except String Unit := do
  let r ← ccOf (← field j "v")
  let m' := if w then m else { m with ssthresh := min m.ssthresh top32 }
  if m' == r then pure () else throw s!"{what}: the model computes {repr m'}, the code recorded {repr r}"

def samePacer (w : Bool) (m : Pacer) (j : J) (what : String) : Except String Unit := do
  let v ← field j "v"
  let r : Pacer := { tokens := ← natF v "tokens", next := ← natF v "next", start := ← natF v "start" }
  let m' := if w then m else { m with next := min m.next top32 }
  if m' == r then pure () else throw s!"{what}: the model computes {repr m'}, the code recorded {repr r}"

def replayEvent (j : J) (w : W) : Except String W := do
  let op ← strF j "op"
  let c := w.c
  let wide := decide (900 ≤ (← natF j "run"))
  let same := same wide
  let samePacer := samePacer wide
  match op with
  | "init" => same {} j "init"; pure {}
  | "rtt" => let c2 := c.onRtt (← natF j "s"); same c2 j "rtt"; pure { w with c := c2 }
  | "ack" =>
    let c2 := c.onAcked ⟨← natF j "now", ← natF j "acked", ← natF j "la", ← natF j "np", ← optF j "srtt", ← optF j "mn",
      ← natF j "mss"⟩
    same c2 j "ack"; pure { w with c := c2 }
  | "loss" =>
    let (c2, r) := c.onLoss (← natF j "now") (← natF j "newest") (← optF j "lat") (← optF j "mn")
    check (r == (← boolF j "r")) "loss: the answer differs"
    same c2 j "loss"; pure { w with c := c2 }
  | "newpath" => let c2 := c.newPath (← natF j "now") (← natF j "np"); same c2 j "newpath"; pure { w with c := c2 }
  | "restore" => let c2 := c.restore (← natF j "cw") (← natF j "ss"); same c2 j "restore"; pure { w with c := c2 }
  | "resume" => let c2 := c.resume (← optF j "mn"); same c2 j "resume"; pure { w with c := c2 }
  | "slack" => let c2 := c.setSlack (← natF j "b"); same c2 j "slack"; pure { w with c := c2 }
  | "gate" =>
    check (c.gateCap (← natF j "mn") == (← optF j "cap")) "gate: the cap differs"
    same c j "gate"; pure w
  | "psent" =>
    let p2 := w.p.onSent (← natF j "now") (← natF j "mtu") (← natF j "srtt") (← natF j "cw") (← boolF j "lim")
    samePacer p2 j "psent"; pure { w with p := p2 }
  | "prel" =>
    let now ← natF j "now"
    check ((if wide then w.p.nextRelease now else min (w.p.nextRelease now) top32) == (← natF j "r")) "prel: the release differs"
    samePacer w.p j "prel"; pure w
  | "end" => pure w
  | _ => throw s!"unknown congestion control op {op}"

end Pinc.TraceCc
