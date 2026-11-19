import Pinc.Json
import Pinc.ConnectRecords

/-!
# Replay of the record store trace

The replay half of the trace validation of the relay's record store (the Rust test `trace_connect_records`, the TLA+
half is `TraceConnectRecords.tla`). Every recorded call is replayed through the Lean functions the theorems of
`ConnectRecordsThm.lean` are about (times multiplied by `10^9`) and any difference exits with an error naming the
line: the answer, an effect (a frame to a peer relay or a trace transition) that is not the one the model emits at
that place, a lookup answer, the store afterwards (for each node: sequence number, home, tag, length and receive
time) or a counter.
-/

namespace Pinc.TraceConnectRecords
open Pinc.Json Pinc.ConnectRecords
open Pinc.ConnectRelay (V Ef)

structure W where
  cf : Cf := ⟨1, 1, 0⟩
  st : St := St.new ⟨1, 1, 0⟩

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

/-- The store as the trace shows it: node, sequence number, home, tag, length, receive time in seconds. -/
def stRows (st : St) : List (List Nat) :=
  st.ents.map fun e => [e.r.node, e.r.seq, e.r.home, e.r.tag, e.r.len, e.rcv / sec]

def recOf (j : J) : Except String Rec := do
  pure ⟨← natF j "rn", ← natF j "rs", ← natF j "rh", ← natF j "rt", ← natF j "rl", (← natF j "rok") == 1⟩

def seen (j : J) (st : St) : Except String Unit := do
  let rows ← (← field j "st").arr?.elim (throw "st: expected an array") (fun a => a.toList.mapM natList)
  check (rows.length == st.ents.length && rows.all (stRows st).contains)
    s!"store: model {stRows st}, code {rows}"
  let cn ← natList (← field j "cn")
  check (cn == [st.records, st.lookups, st.rejected]) s!"counters: model {[st.records, st.lookups, st.rejected]}, code {cn}"

def step (j : J) (w : W) (o : Out) : Except String W := do
  let res ← strF j "res"
  let ef ← toEf (← field j "out")
  check (o.res == res) s!"answer: model {o.res}, code {res}"
  check (o.ef == ef) s!"effects: model [{showEf o.ef}], code [{showEf ef}]"
  seen j o.st
  pure { w with st := o.st }

def replayEvent (j : J) (w : W) : Except String W := do
  match (← strF j "t") with
  | "qnew" =>
    let cf : Cf := ⟨← natF j "r", ← natF j "p", ← natF j "me"⟩
    pure { cf := cf, st := St.new cf }
  | "qadd" =>
    let (st, ok) := addPeer w.st (← natF j "p")
    check (ok == ((← strF j "res") == "ok")) "add_peer: the code and the model disagree on a full set"
    pure { w with st := st }
  | "qrem" => pure { w with st := removePeer w.st (← natF j "p") }
  | "qpub" => step j w (publish w.cf w.st ((← natF j "now") * sec) (← natF j "n") (← recOf j))
  | "qrep" => step j w (replica w.cf w.st ((← natF j "now") * sec) (← recOf j))
  | "qrst" => step j w (restore w.cf w.st ((← natF j "at") * sec) (← recOf j))
  | "qown" => step j w (setOwn w.cf w.st ((← natF j "now") * sec) (← recOf j))
  | "qtime" => step j w (timeout w.cf w.st ((← natF j "now") * sec))
  | "qlook" =>
    let peer ← natF j "peer"
    let now := (← natF j "now") * sec
    let (st, ef, ans) := answer w.st now peer
    check (ans == (← strF j "ans")) s!"lookup answer: model {ans}, code {← strF j "ans"}"
    check (ef == (← toEf (← field j "out"))) s!"lookup effects: model [{showEf ef}]"
    if ans == "record" then
      match lookup w.st now peer with
      | some r =>
        check (r.seq == (← natF j "as") && r.tag == (← natF j "at") && r.len == (← natF j "al"))
          "lookup: a different record than the model's"
      | none => throw "lookup: the model has no record"
    seen j st
    pure { w with st := st }
  | "qsync" =>
    let (ok, ef) := syncRecord w.cf w.st (← natF j "to") (← natF j "node")
    check (ok == ((← strF j "res") == "ok")) "sync_record: the code and the model disagree"
    check (ef == (← toEf (← field j "out"))) s!"sync_record effects: model [{showEf ef}]"
    seen j w.st
    pure w
  | t => throw s!"unknown record event {t}"

/-- The tags this module replays. -/
def isTag (t : String) : Bool :=
  ["qnew", "qadd", "qrem", "qpub", "qrep", "qrst", "qown", "qtime", "qlook", "qsync"].contains t

end Pinc.TraceConnectRecords
