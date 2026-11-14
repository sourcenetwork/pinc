import Vinc.Json
import Vinc.CoreExtIn

/-!
# Replay of the extension ring traces

The Lean half of the trace validation of the ring of extension frames held for the application (`vinc-core`
`ext_in.rs`), the port of `proofs/tla/TraceExtIn.tla`. It reads the `cox` events written by the Rust test
`trace_ext_in` and replays every call through `Vinc.CoreExtIn.eput` and `etake`: the result the model computes must be
the one the code returned (for a put: kept or not, and how many frames the ring gave up for it), and the head, the
length and the frames held (session, type, length and the first byte of the body, oldest first) must be the recorded
ones after every call. The model's frame carries the first byte in `id`.
-/

namespace Vinc.TraceExtIn
open Vinc.Json Vinc.CoreExtIn

def isTag (t : String) : Bool := t == "cox"

structure W where
  x : X := {}
  cap : Nat := 1
  mx : Nat := 0

/-- A frame as the test records it: session, type, length, first byte. -/
def frameOf (j : J) : Except String F := do
  match ← natList j with
  | [s, t, l, g] => pure { id := g, sess := s, ty := t, len := l }
  | _ => throw "a frame has not four parts"

def recOf (f : F) : List Nat := [f.sess, f.ty, f.len, f.id]

def same (x : X) (j : J) (what : String) : Except String Unit := do
  let v ← field j "v"
  check (x.head == (← natF v "head")) s!"{what}: the head differs"
  check (x.q.length == (← natF v "len")) s!"{what}: the length differs"
  let q ← match (← field v "q").arr? with
    | some a => a.toList.mapM natList
    | none => throw "expected the frames held"
  check (x.q.map recOf == q) s!"{what}: the frames held differ"

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    let w' : W := { x := {}, cap := ← natF j "n", mx := ← natF j "mx" }
    same w'.x j "init"
    pure w'
  | "put" =>
    let f ← frameOf (← field j "f")
    let (g, x2) := eput w.cap w.mx w.x f
    check (g.isSome == (← boolF j "ok")) "put: another result"
    check (g.getD 0 == (← natF j "gave")) "put: another number of frames given up"
    same x2 j "put"
    pure { w with x := x2 }
  | "take" =>
    let oc ← natF j "oc"
    let (res, x2) := etake w.cap oc w.x
    match res with
    | .none =>
      check ((← strF j "res") == "none") "take: the ring is not empty"
    | .err l =>
      check ((← strF j "res") == "err") "take: the frame fits the buffer"
      check (l == (← natF j "need")) "take: another length"
    | .ok f =>
      check ((← strF j "res") == "ok") "take: the frame does not fit the buffer"
      check (recOf f == (← natList (← field j "out"))) "take: another frame is given out"
    same x2 j "take"
    pure { w with x := x2 }
  | op => throw s!"unknown extension ring op {op}"

end Vinc.TraceExtIn
