import Pinc.Json
import Pinc.DtnScenario

/-!
# Replay of the scenario traces

The replay half of the trace validation of the delay-tolerant scenarios (the Rust test `trace_dtn_scenario`; the TLA+
half is `TraceDtnScenario.tla`). The recorded events of four nodes that run the real forwarder, custody book and
ledger are replayed through `Pinc.DtnScenario.exec`, the system model the theorems of `DtnScenarioAcct`,
`DtnScenarioChain` and `DtnScenarioTime` are about. For every event the recorded outcome (the action a poll returned,
what a delivery did, what an ack did) must be the model's, and after every event the observables of every node read
back from the code (copies held and handed, whether the book holds the bundle, the ledger's bytes and length, the
class of the bundle's item, the length of the book and the timer of each peer) must be those of the model.
-/

namespace Pinc.TraceDtnScenario
open Pinc.Json Pinc.DtnScenario

/-- The replay state: the model system of the current run. -/
structure W where
  s : Option Sys := none

instance : Inhabited W := ⟨{}⟩

/-- The tags of this replay (the field `t`). -/
def isTag (t : String) : Bool := t == "sc"

/-- The world of the test: four nodes, four copies, expiry 30, retry 2, three sends, ledgers of 3 slots and 3 bytes
(node 3 has none), books of 2, the ranked offer policy. -/
def world : Cfg :=
  { ids := [1, 2, 3, 4], src := 1, dest := 4, copies := 4, exp := 30, retry := 2, maxSends := 3, fb := 1, fl := 3,
    ft := 3, fd := 2, lbud := 3, lslots := 3, bslots := 2, tight := 3, pb := 2, ranked := true }

/-- Keep the node function flat: a replay of thousands of events must not stack one closure per event. -/
def compact (s : Sys) : Sys :=
  let arr := s.cfg.ids.toArray.map s.nodes
  { s with nodes := fun m =>
      match s.cfg.ids.idxOf? m with
      | some i => arr[i]?.getD (Node.empty s.cfg m)
      | none => Node.empty s.cfg m }

/-- What the model says an observer reads from node `n`. -/
def observe (s : Sys) (n : Nat) : List Int :=
  let x := s.nodes n
  let cls : Nat := match x.L.get (DtnStore.bkey bid) with
    | none => 0
    | some e => if e.cls == .custody then 1 else 2
  (([(DtnForward.copiesHeld x.f bid).getD 0, DtnForward.handed x.f bid,
   (if DtnStore.holds x.B bid then 1 else 0), x.L.used, x.L.entries.length, cls, (DtnStore.recs x.B).length] : List Nat).map
    Int.ofNat)
  ++ (((s.cfg.ids.filter (· != n)).map fun p => ((DtnForward.timer x.f p bid).map (Int.ofNat ·)).getD (-1)))

def readInts (j : J) : Except String (List Int) := do
  match j.arr? with
  | some a => a.toList.mapM fun v => match v.int? with | some i => pure i | none => throw "not an integer"
  | none => throw "not an array"

/-- Check the recorded observables of every node against the model. -/
def checkObs (j : J) (s : Sys) : Except String Unit := do
  let some ns := (← field j "ns").arr? | throw "ns is not an array"
  check (ns.size == s.cfg.ids.length) "ns has the wrong length"
  for k in [0:ns.size] do
    let n := k + 1
    let some node := ns[k]? | throw "ns"
    let some parts := node.arr? | throw "node observables"
    let head ← (parts.toList.take 7).mapM fun v => match v.int? with | some i => pure i | none => throw "not an integer"
    let tm ← match parts[7]? with | some a => readInts a | none => throw "timers missing"
    let rec_ := head ++ tm
    let mod := observe s n
    check (rec_ == mod) s!"node {n}: model {mod}, code {rec_}"

def findMsg (s : Sys) (id : Nat) : Except String Msg :=
  match s.msgs.find? (·.id == id) with
  | some m => pure m
  | none => throw s!"no message {id} in the network"

def replayEvent (j : J) (w : W) : Except String W := do
  let e ← strF j "e"
  if e == "new" then
    let s := compact (Sys.init world)
    checkObs j s
    return { s := some s }
  let some s := w.s | throw "event before new"
  let next ← match e with
    | "contact" =>
      pure (exec s (.contact (← natF j "a") (← natF j "b") (← boolF j "up")))
    | "tick" => pure (exec s .tick)
    | "poll" =>
      let n ← natF j "n"
      let a := (DtnForward.poll (s.nodes n).f).2
      match ← strF j "a" with
      | "none" => check (a == .none) s!"poll {n}: model {repr a}, code none"
      | "release" => check (match a with | .release _ => true | _ => false) s!"poll {n}: model {repr a}, code release"
      | "send" =>
        let want : DtnForward.Act := .send (← natF j "p") bid (← natF j "c") (← boolF j "r")
        check (a == want) s!"poll {n}: model {repr a}, code {repr want}"
        check (s.seq == (← natF j "mid")) s!"poll {n}: message id {s.seq} against {← natF j "mid"}"
      | k => throw s!"unknown action {k}"
      let s' := exec s (.poll n)
      if (← strF j "a") == "send" then
        match s'.msgs with
        | .bun _ _ _ _ _ off :: _ => check (off == (← natF j "off")) s!"poll {n}: offer id {off} against {← natF j "off"}"
        | _ => throw s!"poll {n}: a send made no bundle message"
      pure s'
    | "bun" =>
      let m ← findMsg s (← natF j "m")
      let (r, c, fresh) ← match m with
        | .bun _ _ r c fr _ => pure (r, c, fr)
        | .ack .. => throw "a bundle event on an ack"
      let from_ := match m with | .bun _ f .. => f | .ack .. => 0
      let outcome :=
        if r == s.cfg.dest then "dest" else
        let x := s.nodes r
        match (DtnStore.accept x.B x.L bid 1 s.cfg.exp from_ s.t).err with
        | some (.store .custodyRefused) => "refused"
        | some .capacity => "capacity"
        | some _ => "other"
        | none =>
          if (DtnForward.step x.f s.t (.hold bid s.cfg.dest s.cfg.exp c)).2 == .ok then "held" else "holdrefused"
      check (outcome == (← strF j "o")) s!"delivery of {← natF j "m"}: model {outcome}, code {← strF j "o"}"
      if outcome != "refused" && outcome != "capacity" && outcome != "other" then
        check (s.seq == (← natF j "aid")) s!"ack id {s.seq} against {← natF j "aid"}"
      let _ := fresh
      pure (exec s (.bun m))
    | "ack" =>
      let m ← findMsg s (← natF j "m")
      let (c, p, off) ← match m with
        | .ack _ c p off => pure (c, p, off)
        | .bun .. => throw "an ack event on a bundle"
      let x := s.nodes p
      let o := match (DtnStore.onAck x.B x.L bid c off true).err with
        | none => "ok" | some .unknown => "unknown" | some .notOffered => "notoffered"
        | some .storeUnknown => "storeunknown" | some _ => "other"
      check (o == (← strF j "o")) s!"ack {← natF j "m"}: model {o}, code {← strF j "o"}"
      pure (exec s (.ack m))
    | "lose" => pure (exec s (.lose (← findMsg s (← natF j "m"))))
    | "press" => pure (exec s (.press (← natF j "n") (← natF j "k")))
    | "bad" => pure (exec s .bad)
    | e => throw s!"unknown scenario event {e}"
  let next := compact next
  checkObs j next
  pure { s := some next }

end Pinc.TraceDtnScenario
