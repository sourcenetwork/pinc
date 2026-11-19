import Pinc.Json
import Pinc.TransportRx

/-!
# Replay of the received-packet traces

The Lean half of the trace validation of the received-packet tracker (`recovery/recv.rs`), the port of
`proofs/tla/TraceRx.tla`. It reads the `txrx` events written by the Rust test `trace_rx` and replays every call
through the functions of `Pinc.TransportRx`: the state the model computes must be the state recorded (a deadline
shown at most `2^31 - 1`, as the 32-bit checker saw it, except in the wide runs, which are recorded as they are),
and so must the outcome of a receive and the answers of a query.
-/

namespace Pinc.TraceRx
open Pinc.Json Pinc.TransportRx

def isTag (t : String) : Bool := t == "txrx"

/-- The state with its run; `wide` runs are recorded without the 32-bit clamp. -/
structure W where
  x : X := X.init 1
  wide : Bool := false

def top32 : Nat := 2 ^ 31 - 1

def optOf (v : Int) : Option Nat := if v < 0 then none else some v.toNat

def optF (j : J) (k : String) : Except String (Option Nat) := do
  pure (optOf (← intF j k))

def clampO (w : Bool) (o : Option Nat) : Option Nat := if w then o else o.map (min top32)

/-- The state a recorded view shows. -/
def xOf (cap : Nat) (v : J) : Except String X := do
  pure { items := ← pairList (← field v "items"), cap, floor := ← natF v "floor", pending := ← natF v "pending",
         due := ← optF v "due", every := ← optF v "every", mrtt := ← optF v "mrtt", sent := ← pairList (← field v "sent"),
         conf := ← pairList (← field v "conf"), cf := ← optF v "cf" }

def same (w : Bool) (m : X) (j : J) (what : String) : Except String Unit := do
  let rec' ← xOf m.cap (← field j "v")
  let m' := { m with due := clampO w m.due }
  if m' == rec' then pure () else throw s!"{what}: the model computes {repr m'}, the code recorded {repr rec'}"

def replayEvent (j : J) (st : W) : Except String W := do
  let op ← strF j "op"
  let run ← natF j "run"
  let wide := decide (900 ≤ run)
  let x := st.x
  let upd (m : X) (what : String) : Except String W := do
    same wide m j what
    pure { x := m, wide }
  match op with
  | "init" => upd (X.init (← natF j "cap")) "init"
  | "recv" =>
    let (out, y) := receive x ⟨← natF j "pn", ← natF j "now", ← boolF j "elic", ← natF j "bytes"⟩
    check (out == (← strF j "out")) s!"recv: the model answers {out}, the code {← strF j "out"}"
    upd y "recv"
  | "rtt" => upd (setMinRtt x (← optF j "m")) "rtt"
  | "every" => upd (setEvery x (← optF j "e")) "every"
  | "acksent" => upd (ackSent x (← natF j "apn") (← natF j "now")) "acksent"
  | "peer" => upd (peerAck x (← natF j "now") (← pairList (← field j "rgs"))) "peer"
  | "query" =>
    let now ← natF j "now"
    same wide x j "query"
    check (ackRanges x now == (← pairList (← field j "rgs"))) s!"query: the ranges to report differ: model {repr (ackRanges x now)}"
    check (clampO wide (ackDeadline x) == (← optF j "dl")) "query: the deadline differs"
    check ((x.pending != 0) == (← boolF j "pend")) "query: ack_pending differs"
    check (ackDue x now == (← boolF j "due")) "query: ack_due differs"
    check (largest x == (← optF j "lg")) "query: the largest differs"
    check (x.items.length == (← natF j "rc")) "query: the range count differs"
    match (← field j "has").arr? with
    | some a =>
      for e in a do
        match e.arr? with
        | some #[p, b] =>
          match p.nat?, b.bool? with
          | some p, some b => check (contains x p == b) s!"query: contains {p} differs"
          | _, _ => throw "bad probe"
        | _ => throw "bad probe"
    | none => throw "has is not an array"
    pure st
  | "end" => pure st
  | _ => throw s!"unknown tracker op {op}"

end Pinc.TraceRx
