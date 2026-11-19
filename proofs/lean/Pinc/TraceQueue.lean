import Pinc.Json
import Pinc.CoreQueue
import Pinc.CoreQueueRun

/-!
# Replay of the event queue traces

The Lean half of the trace validation of the endpoint's event queue (`pinc-core` `queue.rs`), the port of
`proofs/tla/TraceQueue.tla`. It reads the `coq` events written by the Rust test `trace_queue` and replays every call
through `Pinc.CoreQueue.push`, `pop`, `purge` and `pushAll` (a burst): the head, length, recoverable count, counters
and stall flag the model computes must be the recorded ones, and so must the queued events whenever the record
carries them, and the result of a pop. After a burst from a ring that is not stalled, of at most the headroom of
unrecoverable events, `lost` must be what it was.

The model's cells are a function that every call wraps in a further update; the replay rebuilds it as an array after
every call (`flat`), which changes no cell the ring reads.
-/

namespace Pinc.TraceQueue
open Pinc.Json Pinc.CoreQueue

def isTag (t : String) : Bool := t == "coq"

structure W where
  r : R := {}
  cap : Nat := 1
  h : Nat := 0

/-- The same ring with its cells in an array. -/
def flat (cap : Nat) (r : R) : R :=
  let a : Array (Option E) := ((List.range cap).map r.cells).toArray
  { r with cells := fun p => a.getD p none }

/-- A recorded event: `[id, lossy, session, closed]`. -/
def evOf (j : J) : Except String E := do
  match j.arr? with
  | some a =>
    match a.toList with
    | [i, l, s, c] =>
      match i.nat?, l.bool?, s.nat?, c.bool? with
      | some id, some lossy, some sess, some closed => pure { id, lossy, sess, closed }
      | _, _, _, _ => throw "an event is not a number, a flag, a number and a flag"
    | _ => throw "an event has not four parts"
  | none => throw "expected an event"

def evList (j : J) : Except String (List E) := do
  match j.arr? with
  | some a => a.toList.mapM evOf
  | none => throw "expected a list of events"

def same (cap h : Nat) (r : R) (j : J) (what : String) : Except String Unit := do
  let v ← field j "v"
  check (r.head == (← natF v "head")) s!"{what}: the head differs"
  check (r.len == (← natF v "len")) s!"{what}: the length differs"
  check (r.ll == (← natF v "ll")) s!"{what}: the recoverable count differs"
  check (r.dropped == (← natF v "dropped")) s!"{what}: the drop count differs"
  check (r.lost == (← natF v "lost")) s!"{what}: the loss count differs"
  check (stalled cap h r == (← boolF v "stalled")) s!"{what}: the stall flag differs"
  if (← boolF v "full") then
    let q ← evList (← field v "q")
    check (view r cap == q.map some) s!"{what}: the queued events differ"

/-- How many of the events cannot be recovered. -/
def unrecIn (evs : List E) : Nat := nU evs

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    let cap ← natF j "cap"
    let h ← natF j "h"
    let r : R := {}
    same cap h r j "init"
    pure { r, cap, h }
  | "push" =>
    let r2 := flat w.cap (push w.cap (← evOf (← field j "ev")) w.r)
    same w.cap w.h r2 j "push"
    pure { w with r := r2 }
  | "burst" =>
    let evs ← evList (← field j "evs")
    check (!stalled w.cap w.h w.r) "burst: the ring was stalled"
    check (decide (unrecIn evs ≤ w.h)) "burst: more unrecoverable events than the headroom"
    let r2 := flat w.cap (pushAll w.cap evs w.r)
    check (r2.lost == w.r.lost) "burst: an event was lost"
    same w.cap w.h r2 j "burst"
    pure { w with r := r2 }
  | "pop" =>
    let (out, r2) := pop w.cap w.r
    let want ← match (← field j "out").arr? with
      | some a => if a.isEmpty then pure none else some <$> evOf (← field j "out")
      | none => throw "expected the event popped"
    check (out == want) "pop: another event is given out"
    let r3 := flat w.cap r2
    same w.cap w.h r3 j "pop"
    pure { w with r := r3 }
  | "purge" =>
    let r2 := flat w.cap (purge w.cap (← natF j "s") w.r)
    same w.cap w.h r2 j "purge"
    pure { w with r := r2 }
  | "end" =>
    same w.cap w.h w.r j "end"
    pure w
  | op => throw s!"unknown event queue op {op}"

end Pinc.TraceQueue
