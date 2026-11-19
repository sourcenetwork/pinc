import Pinc.Json
import Pinc.ConnectPackThm

/-!
# Replay of the batch builder trace

The replay half of the trace validation of `BatchBuilder` (the Rust test `trace_connect_pack`, the TLA+ half is
`TraceConnectPack.tla`). Every recorded offer is replayed through `offer` and every close through `kind`, `record` and
`headFits`, the functions the theorems of `ConnectPackThm.lean` are about; any difference exits with an error naming
the line: the answer and its error, the number of frames held, the kind of record, its length and the lengths of the
frames it holds. The bytes of a frame are not recorded (the model only reads their number), so the replay offers
zeros of the right number.
-/

namespace Pinc.TraceConnectPack
open Pinc.Json Pinc.ConnPack

structure W where
  c : Cfg := ⟨0, 0, 0, 0⟩
  st : St := ⟨[]⟩

instance : Inhabited W := ⟨{}⟩

/-- The code of an encoder error by its name. -/
def errCode : String → Nat
  | "packet" => 1
  | "alias" => 2
  | _ => 0

def resName : Res → String × String
  | .added => ("added", "")
  | .refused => ("refused", "")
  | .noroom => ("err", "noroom")
  | .small => ("err", "small")
  | .bad e => ("err", if e = 1 then "packet" else if e = 2 then "alias" else "")

def kindName : Kind → String
  | .none => "none"
  | .single => "single"
  | .batch => "batch"

def replayEvent (j : J) (w : W) : Except String W := do
  match (← strF j "t") with
  | "bbnew" =>
    pure { c := ⟨← natF j "f", ← natF j "b", ← natF j "head", ← natF j "cap"⟩, st := ⟨[]⟩ }
  | "bboffer" =>
    let f : Cand := ⟨List.replicate (← natF j "n") 0, ← boolF j "long", ← boolF j "isbatch", ← boolF j "bad",
      errCode (← strF j "err")⟩
    let (r, st) := offer w.c w.st f
    let (res, e) := resName r
    check (res == (← strF j "res") && e == (← strF j "e"))
      s!"offer: model {res} {e}, code {← strF j "res"} {← strF j "e"}"
    check (st.count == (← natF j "cnt")) s!"offer: model holds {st.count} frames, code {← natF j "cnt"}"
    pure { w with st := st }
  | "bbfin" =>
    check (kindName (kind w.st) == (← strF j "kind")) s!"finish: model {kindName (kind w.st)}, code {← strF j "kind"}"
    check (headFits w.c w.st) "finish: the header does not fit the room kept for it"
    check ((record w.st).length == (← natF j "len")) s!"finish: model record of {(record w.st).length} bytes, code {← natF j "len"}"
    check (w.st.ps.map List.length == (← natList (← field j "lens"))) "finish: the lengths of the frames differ"
    pure { w with st := ⟨[]⟩ }
  | t => throw s!"unknown batch builder event {t}"

/-- The tags this module replays. -/
def isTag (t : String) : Bool := ["bbnew", "bboffer", "bbfin"].contains t

end Pinc.TraceConnectPack
