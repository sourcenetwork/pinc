import Vinc.Json
import Vinc.CoreReach

/-!
# Replay of the reach ring traces

The Lean half of the trace validation of the ring of `REACH_OUT` bodies (`vinc-core` `reach.rs`), the port of
`proofs/tla/TraceReach.tla`. It reads the `cor` events written by the Rust test `trace_reach` and replays every
call through `Vinc.CoreReach.rput` and `rget`: the body a get returns must be the recorded one (its length and
first byte), and the pointer `next` and the four places (session, body length and first byte, or nothing) must be
the recorded ones after every call. The model's cell carries the first byte in `id`.
-/

namespace Vinc.TraceReach
open Vinc.Json Vinc.CoreReach

def isTag (t : String) : Bool := t == "cor"

structure W where
  r : R := {}
  n : Nat := 1
  mx : Nat := 0

/-- A place as the test records it: `[]` for empty, else `[session, length, first byte]`. -/
def recCell : Option C → List Nat
  | none => []
  | some c => [c.sess, c.len, c.id]

def same (r : R) (j : J) (what : String) : Except String Unit := do
  let v ← field j "v"
  check (r.next == (← natF v "next")) s!"{what}: the pointer differs"
  let cells ← match (← field v "cells").arr? with
    | some a => a.toList.mapM natList
    | none => throw "expected the places"
  check (r.cells.map recCell == cells) s!"{what}: the places differ"

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    let n ← natF j "n"
    let w' : W := { r := { cells := List.replicate n none, next := 0 }, n, mx := ← natF j "mx" }
    same w'.r j "init"
    pure w'
  | "put" =>
    match ← natList (← field j "c") with
    | [s, l, g] =>
      let r2 := rput w.n w.mx w.r { sess := s, id := g, len := l }
      same r2 j "put"
      pure { w with r := r2 }
    | _ => throw "a body has not three parts"
  | "get" =>
    let want ← natList (← field j "out")
    let got := match rget (← natF j "s") w.r.cells with
      | some c => [c.len, c.id]
      | none => []
    check (got == want) "get: another body"
    same w.r j "get"
    pure w
  | op => throw s!"unknown reach ring op {op}"

end Vinc.TraceReach
