import Pinc.Json
import Pinc.CoreHeap

/-!
# Replay of the deadline heap traces

The Lean half of the trace validation of the endpoint's deadline heap (`pinc-core` `heap.rs`), the port of
`proofs/tla/TraceHeap.tla`. It reads the `cohp` events written by the Rust test `trace_heap` and replays every call
through `Pinc.CoreHeap.set`: the heap array, the position index and the stored deadlines the model computes must be the
ones recorded, and so must the answers of `peek` and `deadline`. The file `heap_wide.ndjson`, with deadlines up to
`u64::MAX` and ids up to `usize::MAX`, is replayed here only.
-/

namespace Pinc.TraceHeap
open Pinc.Json Pinc.CoreHeap

def isTag (t : String) : Bool := t == "cohp"

structure W where
  s : S := init 0

/-- The heap as recorded: the array up to its length, then the position (`-1` for none) and the stored deadline of
each id. -/
def same (m : S) (j : J) (what : String) : Except String Unit := do
  let v ← field j "v"
  let heap ← natList (← field v "heap")
  let pos ← intList (← field v "pos")
  let dl ← natList (← field v "at")
  let len ← natF v "len"
  let ids := List.range m.n
  let mpos : List Int := ids.map fun id => match m.pos id with
    | none => -1
    | some p => (p : Int)
  let mheap := (List.range m.len).map m.heap
  let mdl := ids.map m.dl
  check (len == m.len && heap == mheap) s!"{what}: the model's heap is {repr mheap}, the code recorded {repr heap}"
  check (pos == mpos) s!"{what}: the model's positions are {repr mpos}, the code recorded {repr pos}"
  check (dl == mdl) s!"{what}: the model's deadlines are {repr mdl}, the code recorded {repr dl}"

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    let s := init (← natF j "n")
    same s j "init"
    pure { s }
  | "set" =>
    let id ← natF j "id"
    let has ← boolF j "has"
    let at' ← natF j "at"
    let t : Option Nat := if has then some at' else none
    let r := set w.s id t
    same r j "set"
    let pk : List Nat := match peek r with
      | none => []
      | some (t, i) => [t, i]
    check (pk == (← natList (← field j "pk"))) "set: peek differs"
    let dl : List Nat := if id < r.n && (r.pos id).isSome then [r.dl id] else []
    check (dl == (← natList (← field j "dl"))) "set: deadline differs"
    pure { s := r }
  | op => throw s!"unknown deadline-heap op {op}"

end Pinc.TraceHeap
