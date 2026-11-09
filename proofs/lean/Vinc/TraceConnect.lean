import Vinc.Json
import Vinc.ConnectRelay

/-!
# Replay of the relay trace

The replay half of the trace validation of the relay (the Rust test `trace_connect`, the TLA+ half is
`TraceConnect.tla`). Every recorded call is replayed through the Lean relay model of `ConnectRelay.lean` (times
multiplied by `10^9`) and any difference exits with an error naming the line: the answer, or an effect (a frame, a
close, a wake-up or a trace transition) that is not the one the model emits at that place.
-/

namespace Vinc.TraceConnect
open Vinc.Json Vinc.ConnectRelay

structure W where
  cf : CF := {}
  r : RS := RS.new {}

instance : Inhabited W := ⟨{}⟩

def toV (j : J) : Except String V :=
  match j.str?, j.nat? with
  | some s, _ => pure (.s s)
  | _, some n => pure (.n n)
  | _, _ => throw "an effect field is neither a string nor a number"

def toList (j : J) : Except String (List V) :=
  match j.arr? with
  | some a => a.toList.mapM toV
  | none => throw "expected an array"

def toEf (j : J) : Except String Ef :=
  match j.arr? with
  | some a => a.toList.mapM toList
  | none => throw "expected an array of effects"

def showV : V → String
  | .s x => x
  | .n x => toString x

def showEf (e : Ef) : String := String.intercalate " | " (e.map fun l => String.intercalate "," (l.map showV))

def step (j : J) (w : W) (o : Out) : Except String W := do
  let res ← strF j "res"
  let ef ← toEf (← field j "out")
  check (o.res == res) s!"answer: model {o.res}, code {res}"
  check (o.ef == ef) s!"effects: model [{showEf o.ef}], code [{showEf ef}]"
  pure { w with r := o.r }

def replayEvent (j : J) (w : W) : Except String W := do
  let now := (← (natF j "now" <|> pure 0)) * sec
  match (← strF j "t") with
  | "rnew" =>
    let me ← natF j "me"
    let c ← natF j "c"
    let r ← natF j "r"
    let mn ← natF j "mn"
    let mbb ← natF j "mb"
    let bytes ← natF j "bytes"
    let window ← natF j "window"
    let sess ← natF j "sess"
    let age ← natF j "age"
    let cf : CF := ⟨me, c, r, mn, mbb, bytes, window * sec, sess * sec, age * sec⟩
    pure { cf := cf, r := RS.new cf }
  | "rbk" => pure { w with r := { w.r with bk := aput w.r.bk (← natF j "n") (← natF j "b") } }
  | "radd" =>
    let (r, ok) := addPeer w.r (← natF j "p")
    check (ok == ((← strF j "res") == "ok")) "add_peer: the code and the model disagree on a full set"
    pure { w with r := r }
  | "rrem" => pure { w with r := removePeer w.r (← natF j "p") }
  | "ropen" => step j w (carrierOpened w.cf w.r now (← natF j "n"))
  | "rclose" => step j w (carrierClosed w.cf w.r now (← natF j "n") (← natF j "sid"))
  | "rframe" => step j w (carrierFrame w.cf w.r now (← natF j "n") (← natF j "sid") (← toList (← field j "f")))
  | "rpeer" => step j w (peerFrame w.cf w.r now (← natF j "from") (← toList (← field j "f")))
  | "rudph" => step j w (udpHeard w.cf w.r (← natF j "n") ((← natF j "at") * sec))
  | "rudpg" => pure { w with r := udpGone w.r (← natF j "n") }
  | "rspu" => step j w (spu w.cf w.r now (← natF j "m") (← natF j "dst") (← natF j "flag") (← natF j "len"))
  | "rret" => step j w (memberReturned w.cf w.r now (← natF j "n"))
  | "rtime" => step j w (timeout w.cf w.r now)
  | t => throw s!"unknown relay event {t}"

/-- The tags this module replays. -/
def isTag (t : String) : Bool :=
  ["rnew", "rbk", "radd", "rrem", "ropen", "rclose", "rframe", "rpeer", "rudph", "rudpg", "rspu", "rret", "rtime"].contains t

end Vinc.TraceConnect
