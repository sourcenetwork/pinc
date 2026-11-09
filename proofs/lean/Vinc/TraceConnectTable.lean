import Vinc.Json
import Vinc.ConnectTable

/-!
# Replay of the table trace

The replay half of the trace validation of `Table` and `Cache` (the Rust test `trace_connect_table`, the TLA+ half is
`TraceConnectTable.tla`). The buckets the real code computed are read first (`tbk`), then every recorded call is
replayed through the Lean functions of `ConnectTable.lean` (`insert`, `remove`, `retainOdd`, `cachePut`, `cacheGet`)
and the entries in slot order must equal the recorded ones.
-/

namespace Vinc.TraceConnectTable
open Vinc.Json Vinc.ConnectTable

structure W where
  n : Nat := 1
  bks : List (Nat × Nat) := []
  t : T := T.new 1
  c : List Slot := Cache.new 1

instance : Inhabited W := ⟨{}⟩

def W.bk (w : W) (k : Nat) : Nat := ((w.bks.find? (·.1 == k)).map (·.2)).getD 0

def replayEvent (j : J) (w : W) : Except String W := do
  match (← strF j "t") with
  | "tbnew" => let n ← natF j "n"; pure { n := n, bks := [], t := T.new n, c := w.c }
  | "knew" => let n ← natF j "n"; pure { n := n, bks := [], t := w.t, c := Cache.new n }
  | "tbk" => pure { w with bks := (← natF j "k", ← natF j "b") :: w.bks }
  | "tins" =>
    let (t, r) := insert w.n w.bk w.t (← natF j "k") (← natF j "v")
    match ← strF j "res", r with
    | "ok", .ok old => check (old == (← natF j "old")) s!"insert: old value {old}, code {← natF j "old"}"
    | "full", .full => pure ()
    | _, _ => throw "insert: the code and the model disagree on full"
    pure { w with t := t }
  | "trem" =>
    let (t, r) := remove w.n w.bk w.t (← natF j "k")
    match ← boolF j "found", r with
    | true, some v => check (v == (← natF j "v")) "remove: a different value"
    | false, none => pure ()
    | _, _ => throw "remove: the code and the model disagree on presence"
    pure { w with t := t }
  | "tret" =>
    let (t, vis) := retainOdd w.n w.bk w.t
    let rec_ ← natList (← field j "vis")
    check (vis.eraseDups.mergeSort == rec_.mergeSort) s!"retain visited {vis.eraseDups}, code {rec_}"
    pure { w with t := t }
  | "tslots" =>
    let mine := (entries w.t).map fun x => [x.k, x.v]
    let theirs ← (← field j "s").arr?.map (·.toList) |>.elim (throw "s") (fun l => l.mapM natList)
    check (mine == theirs) s!"entries in slot order: model {mine}, code {theirs}"
    pure w
  | "kput" => pure { w with c := cachePut w.c w.bk (← natF j "k") (← natF j "v") }
  | "kget" =>
    let r := cacheGet w.c w.bk (← natF j "k")
    match ← boolF j "hit", r with
    | true, some v => check (v == (← natF j "v")) "cache get: a different value"
    | false, none => pure ()
    | _, _ => throw "cache get: the code and the model disagree on a hit"
    pure w
  | t => throw s!"unknown table event {t}"

/-- The tags this module replays. -/
def isTag (t : String) : Bool := ["tbnew", "knew", "tbk", "tins", "trem", "tret", "tslots", "kput", "kget"].contains t

end Vinc.TraceConnectTable
