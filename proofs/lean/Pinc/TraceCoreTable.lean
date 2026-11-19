import Pinc.Json
import Pinc.CoreTable

/-!
# Replay of the connection-id table traces

The Lean half of the trace validation of the endpoint's connection-id table (`pinc-core` `table.rs`), the port of
`proofs/tla/TraceCoreTable.tla`. It reads the `cota` events written by the Rust test `trace_core_table` and replays
every call through `Pinc.CoreTable.insert`, `insertRoom`, `insertDup`, `remove`, `removePair`, `touch`, `find` and
`matchesOf`: the result the model computes must be the recorded one, and the entries from the oldest to the newest and
the length after the call must be the recorded ones. The bucket function is the one the events show, key by key (the
code's hash is not modelled: the theorems hold for every bucket function); it must stay the same function of the key
within a run. The array positions the events also show are checked by the TLA+ trace check, whose model has the
array; this model has none.
-/

namespace Pinc.TraceCoreTable
open Pinc.Json Pinc.CoreTable

def isTag (t : String) : Bool := t == "cota"

structure W where
  n : Nat := 0
  t : T := T.new
  bks : List (Nat × Nat) := []

def W.bk (w : W) (k : Nat) : Nat := match w.bks.find? (fun p => p.1 == k) with
  | some p => p.2
  | none => 0

/-- The recorded entries as pairs. -/
def pairs (j : J) : Except String (List (Nat × Nat)) := pairList j

def same (w : W) (j : J) (what : String) : Except String Unit := do
  let v ← field j "v"
  let order ← pairs (← field v "order")
  let len ← natF v "len"
  check (iter w.t == order) s!"{what}: the model computes the entries {repr (iter w.t)}, the code recorded {repr order}"
  check (w.t.len == len) s!"{what}: the model computes the length {w.t.len}, the code recorded {len}"
  check (w.t.len ≤ w.n) s!"{what}: the table holds more than its capacity"

def optPair (j : J) : Except String (Option (Nat × Nat)) := do
  match ← natList j with
  | [] => pure none
  | [a, b] => pure (some (a, b))
  | _ => throw "expected no entry or a pair"

def optNat (j : J) : Except String (Option Nat) := do
  match ← natList j with
  | [] => pure none
  | [a] => pure (some a)
  | _ => throw "expected no value or one"

def replayEvent (j : J) (w : W) : Except String W := do
  let op ← strF j "op"
  if op == "init" then
    let w2 : W := { n := ← natF j "n", t := T.new, bks := [] }
    same w2 j "init"
    return w2
  if op == "clear" then
    let w2 := { w with t := T.new }
    same w2 j "clear"
    return w2
  let k ← natF j "k"
  let b ← natF j "b"
  -- the bucket function so far, with the key of this call; it must agree with what was seen
  let w : W := match w.bks.find? (fun p => p.1 == k) with
    | some _ => w
    | none => { w with bks := (k, b) :: w.bks }
  check (w.bk k == b) "the bucket of a key changed within a run"
  check (b < w.n) "a bucket outside the table"
  let bk := w.bk
  let w2 ← match op with
    | "insert" =>
      let (t2, ev) := insert bk w.n w.t k (← natF j "x")
      check (ev == (← optPair (← field j "out"))) "insert: another entry evicted"
      pure { w with t := t2 }
    | "room" =>
      let (t2, ok) := insertRoom bk w.n w.t k (← natF j "x")
      check (ok == (← boolF j "ok")) "insert_room: the result differs"
      pure { w with t := t2 }
    | "dup" =>
      let (t2, ok) := insertDup bk w.n w.t k (← natF j "x")
      check (ok == (← boolF j "ok")) "insert_dup: the result differs"
      pure { w with t := t2 }
    | "remove" =>
      let (t2, r) := remove bk w.t k
      check (r == (← optNat (← field j "out"))) "remove: another value removed"
      pure { w with t := t2 }
    | "rempair" =>
      let (t2, ok) := removePair bk w.t k (← natF j "x")
      check (ok == (← boolF j "ok")) "remove_pair: the result differs"
      pure { w with t := t2 }
    | "touch" => pure { w with t := touch bk w.t k }
    | "get" =>
      check (((find bk w.t k).map (·.v)) == (← optNat (← field j "out"))) "get: another value"
      pure w
    | "matches" =>
      let (out, c) := matchesOf bk w.t k (← natF j "m")
      check (out == (← natList (← field j "out"))) "matches: other values, or in another order"
      check (c == out.length) "matches: the count is not the number of values"
      pure w
    | _ => throw s!"unknown table op {op}"
  same w2 j op
  return w2

end Pinc.TraceCoreTable
