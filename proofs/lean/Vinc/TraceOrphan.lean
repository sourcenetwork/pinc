import Vinc.Json
import Vinc.CoreOrphan

/-!
# Replay of the held first-flight fragment traces

The Lean half of the trace validation of the endpoint's table of held fragments (`vinc-core` `orphan.rs`), the port
of `proofs/tla/TraceOrphan.tla`. It reads the `coor` events written by the Rust test `trace_orphan` and replays
every call through `Vinc.CoreOrphan.hold`, `take` and `expire`: the entries and counters the model computes must be
the ones recorded, and so must the result of the call. The file `orphan_wide.ndjson`, with times up to `u64::MAX`,
is replayed here only.
-/

namespace Vinc.TraceOrphan
open Vinc.Json Vinc.CoreOrphan

def isTag (t : String) : Bool := t == "coor"

structure W where
  o : O := {}
  max : Nat := 0
  life : Nat := 0

def keyOf (j : J) : Except String Key := do
  match ← natList j with
  | [d, total, r] => pure (d, total, r)
  | _ => throw "expected a message of three numbers"

/-- A recorded entry: `[]` for a free one, else `[at, ord, [id, total, from], loc, len, tag]`. -/
def slotOf (j : J) : Except String (Option H) := do
  match j.arr? with
  | some a =>
    match a.toList with
    | [] => pure none
    | [t, ord, key, loc, len, tag] =>
      match t.nat?, ord.nat?, loc.nat?, len.nat?, tag.nat? with
      | some t, some ord, some loc, some len, some tag => pure (some { t, ord, key := ← keyOf key, loc, len, tag })
      | _, _, _, _, _ => throw "an entry is not made of numbers"
    | _ => throw "an entry has not six parts"
  | none => throw "expected an entry"

def same (m : O) (j : J) (what : String) : Except String Unit := do
  let v ← field j "v"
  let slots ← match (← field v "slots").arr? with
    | some a => a.toList.mapM slotOf
    | none => throw "expected the entries"
  let rec' : O := { slots, order := ← natF v "order", held := ← natF v "held", replayed := ← natF v "replayed",
                    expired := ← natF v "expired", evicted := ← natF v "evicted" }
  if m == rec' then pure () else throw s!"{what}: the model computes {repr m}, the code recorded {repr rec'}"

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "op" with
  | "init" =>
    let o := init (← natF j "n")
    same o j "init"
    pure { o, max := ← natF j "max", life := ← natF j "life" }
  | "hold" =>
    let (ok, o2) := hold w.max w.life (← natF j "now") (← keyOf (← field j "key")) (← natF j "loc") (← natF j "len")
      (← natF j "tag") w.o
    check (ok == (← boolF j "ok")) "hold: the result differs"
    same o2 j "hold"
    pure { w with o := o2 }
  | "take" =>
    let (out, o2) := take w.life (← natF j "now") (← keyOf (← field j "key")) w.o
    let got : List Nat := match out with
      | none => []
      | some h => [h.loc, h.len, h.tag]
    check (got == (← natList (← field j "out"))) "take: another datagram is given out"
    same o2 j "take"
    pure { w with o := o2 }
  | "expire" =>
    let o2 := expire w.life (← natF j "now") w.o
    same o2 j "expire"
    pure { w with o := o2 }
  | op => throw s!"unknown held-fragment op {op}"

end Vinc.TraceOrphan
