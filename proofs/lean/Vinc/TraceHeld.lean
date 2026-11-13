import Vinc.Json
import Vinc.CoreQueue
import Vinc.CoreHeld

/-!
# Replay of the held ring traces

The Lean half of the trace validation of a session's held ring (`vinc-core` `slot.rs`, `Held`), the port of
`proofs/tla/TraceHeld.tla`. It reads the `coh` events written by the Rust test `trace_held` and replays every call
through `Vinc.CoreHeld.hpush`, `hpop` and the release of everything: the head, length, drop count and stall flag the
model computes must be the recorded ones, and so must the held events whenever the record carries them, and the
result of a pop. An event is recorded as `[kind, stream, error]`; the model's event has the error as `id`, the kind
and stream as `sess` (`stream * 8 + kind`), and is recoverable for the kinds readable, writable and open ready
(1, 2 and 6), as the code decides.
-/

namespace Vinc.TraceHeld
open Vinc.Json Vinc.CoreQueue Vinc.CoreHeld

def isTag (t : String) : Bool := t == "coh"

structure W where
  r : R := {}
  cap : Nat := 1

/-- The same ring with its cells in an array. -/
def flat (cap : Nat) (r : R) : R :=
  let a : Array (Option E) := ((List.range cap).map r.cells).toArray
  { r with cells := fun p => a.getD p none }

def evOf (j : J) : Except String E := do
  match ← natList j with
  | [kind, stream, error] =>
    pure { id := error, lossy := kind == 1 || kind == 2 || kind == 6, sess := stream * 8 + kind, closed := false }
  | _ => throw "an event has not three parts"

def evList (j : J) : Except String (List E) := do
  match j.arr? with
  | some a => a.toList.mapM evOf
  | none => throw "expected a list of events"

def same (cap : Nat) (r : R) (j : J) (what : String) : Except String Unit := do
  let v ← field j "v"
  check (r.head == (← natF v "head")) s!"{what}: the head differs"
  check (r.len == (← natF v "len")) s!"{what}: the length differs"
  check (r.dropped == (← natF v "dropped")) s!"{what}: the drop count differs"
  check (hstalled cap r == (← boolF v "stalled")) s!"{what}: the stall flag differs"
  if (← boolF v "full") then
    let q ← evList (← field v "q")
    check (view r cap == q.map some) s!"{what}: the held events differ"

/-- The release of everything: pops until the ring is empty. -/
def clearAll (cap : Nat) : Nat → R → R
  | 0, r => r
  | n + 1, r => clearAll cap n (hpop cap r).2

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    let cap ← natF j "n"
    let r : R := {}
    same cap r j "init"
    pure { r, cap }
  | "push" =>
    let r2 := flat w.cap (hpush w.cap (← evOf (← field j "ev")) w.r)
    same w.cap r2 j "push"
    pure { w with r := r2 }
  | "pop" =>
    let (out, r2) := hpop w.cap w.r
    let want ← match (← field j "out").arr? with
      | some a => if a.isEmpty then pure none else some <$> evOf (← field j "out")
      | none => throw "expected the event popped"
    check (out == want) "pop: another event is given out"
    let r3 := flat w.cap r2
    same w.cap r3 j "pop"
    pure { w with r := r3 }
  | "clear" =>
    let r2 := flat w.cap (clearAll w.cap w.r.len w.r)
    same w.cap r2 j "clear"
    pure { w with r := r2 }
  | "end" =>
    same w.cap w.r j "end"
    pure w
  | op => throw s!"unknown held ring op {op}"

end Vinc.TraceHeld
