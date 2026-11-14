import Vinc.Json
import Vinc.CoreReach

/-!
# Replay of the reach ring traces

The Lean half of the trace validation of the ring of `REACH_OUT` bodies (`vinc-core` `reach.rs`), the port of
`proofs/tla/TraceReach.tla`. It reads the `cor` events written by the Rust test `trace_reach` and replays every
call through `Vinc.CoreReach.rput` and `rget`: the number of bodies a put returned as lost and the body a get returns
(its length and first byte) must be the recorded ones, and so must the four places (session, body length and first
byte, or nothing) after every call. The stamps and the put counter are not recorded; the replay carries them from the
empty ring at the start of each run. The model's cell carries the first byte in `id`.
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
  let cells ← match (← field v "cells").arr? with
    | some a => a.toList.mapM natList
    | none => throw "expected the places"
  check (r.cells.map recCell == cells) s!"{what}: the places differ"

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    let n ← natF j "n"
    let w' : W := { r := { cells := List.replicate n none, clock := 0 }, n, mx := ← natF j "mx" }
    same w'.r j "init"
    pure w'
  | "put" =>
    match ← natList (← field j "c") with
    | [s, l, g] =>
      let (lost, r2) := rput w.mx w.r { sess := s, id := g, len := l }
      check (lost == (← natF j "lost")) "put: another number of bodies lost"
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
