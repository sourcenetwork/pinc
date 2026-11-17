import Vinc.Json
import Vinc.BroadcastNode

/-!
# Replay of the broadcast traces

The Lean half of the trace validation of `vinc-broadcast` (the Rust test `trace_broadcast`, the TLA+ half is
`TraceBroadcast.tla`). Every input the message path acts on is replayed through the operators the node theorems are
about (`OnMsg`, `OnHave`, `OnTimer`, `AcpAnswer` of `Vinc.BroadcastNode`) on the model state of the node it was given
to; the trace records, the delivered ids and the PACK count must be those the code reported, and any difference
exits with an error naming the line. A message presented in a frame is judged by the oracle of the `sign` lines
exactly as in the TLA+ trace spec: it verifies only if the origin signed that topic, id, body, timestamp and flag.
-/

namespace Vinc.BroadcastTrace
open Vinc.Json Vinc.BroadcastNode

/-- The constants of the four nodes of the trace test (node 0 is the hub); the same as `TraceBroadcast.cfg`. -/
def paramsOf (n : Nat) : Params where
  ttl := 4800000
  seenCap := 8192
  logRing := 5879
  logCap := 2048
  logWin := 960000
  fholdMax := 256
  heldMax := 64
  checksMax := 256
  acpCap := 240000
  acpMax := 4096
  floorWait := 120000
  oldSlack := 16000
  me := n
  isHub := n == 0
  revoked := [99]
  heldDedup := true
  heldFullKeepsUnseen := true
  topicFull := false
  ackAfterStore := true
  gather := true
  evictGuard := true

/-- A signature the oracle knows: the signature id and the statement it covers. -/
structure Sig where
  sig : Nat
  org : Nat
  tid : Nat
  mid : Nat
  bid : Nat
  ts : Nat
  isb : Bool
  deriving BEq

/-- The replay state: the node states (set by `start`) and the oracle. -/
structure W where
  nodes : Array Node := #[]
  orc : List Sig := []

instance : Inhabited W := ⟨{}⟩

/-- The projection of a record the code reports: the fields the Rust trace carries. -/
def proj : TraceRec → TraceRec
  | .delivered mid _ _ _ => .delivered mid 0 0 .cache
  | .acpAsked id _ => .acpAsked id 0
  | .acpAnswered id a _ => .acpAnswered id a 0
  | r => r

def whyOf : String → Except String Why
  | "TopicsFull" => pure .topicsFull
  | "SeenFull" => pure .seenFull
  | "Old" => pure .old
  | "HeldFull" => pure .heldFull
  | "BadHead" => pure .badHead
  | "Duplicate" => pure .duplicate
  | "IdTaken" => pure .idTaken
  | "Revoked" => pure .revoked
  | "BadSignature" => pure .badSignature
  | "LogFull" => pure .logFull
  | s => throw s!"unknown rejection {s}"

def holdOf : String → Except String HoldWhy
  | "Acp" => pure .acp
  | "Floor" => pure .floor
  | s => throw s!"unknown hold reason {s}"

/-- A recorded trace record, in the projection. -/
def parseRec (j : J) : Except String TraceRec := do
  match ← strF j "k" with
  | "Stored" => pure (.stored (← natF j "mid") (← boolF j "fanned"))
  | "Rejected" => pure (.rejected (← natF j "mid") (← whyOf (← strF j "why")))
  | "Delivered" => pure (.delivered (← natF j "mid") 0 0 .cache)
  | "Held" => pure (.held (← natF j "mid") (← holdOf (← strF j "why")))
  | "AcpAsked" => pure (.acpAsked (← natF j "id") 0)
  | "AcpAnswered" => pure (.acpAnswered (← natF j "id") (← boolF j "allow") 0)
  | "Repaired" => pure (.repaired (← natF j "mid"))
  | "FloorDone" => pure (.floorDone (← boolF j "used"))
  | k => throw s!"unknown record {k}"

def parseOuts (j : J) : Except String (List TraceRec) := do
  match (← field j "out").arr? with
  | some a => a.toList.mapM parseRec
  | none => throw "out is not an array"

def frameOf : Nat → Except String Frame
  | 5 => pure .pub
  | 7 => pure .msg
  | 15 => pure .fan
  | 16 => pure .fanp
  | 17 => pure .other
  | n => throw s!"unknown frame type {n}"

def node (w : W) (n : Nat) : Except String Node :=
  match w.nodes[n]? with
  | some x => pure x
  | none => throw s!"node {n} was not started"

def setNode (w : W) (n : Nat) (x : Node) : W := {w with nodes := w.nodes.set! n x}

/-- The oracle's verdict on the message the frame presents. -/
def verified (w : W) (j : J) : Except String Bool := do
  let s : Sig := ⟨← natF j "sig", ← natF j "org", ← natF j "tid", ← natF j "mid", ← natF j "bid", ← natF j "ts",
    ← boolF j "isb"⟩
  pure (w.orc.contains s)

/-- Compare the result of an operator with the recorded records, and take the new node. -/
def finish (w : W) (j : J) (n : Nat) (r : Res) (what : String) : Except String W := do
  let outs ← parseOuts j
  check (r.outs.map proj == outs) s!"{what}: records differ: model {repr (r.outs.map proj)}, code {repr outs}"
  pure (setNode w n r.n)

/-- Replay one event. -/
def replayEvent (j : J) (w : W) : Except String W := do
  let op ← strF j "op"
  match op with
  | "start" =>
    let n ← natF j "n"
    let nd := {NodeInit (paramsOf n) (← natF j "at") with sub := false}
    let nodes := if n < w.nodes.size then w.nodes.set! n nd else w.nodes.push nd
    pure {w with nodes := nodes}
  | "sub" =>
    let n ← natF j "n"
    pure (setNode w n {(← node w n) with sub := true})
  | "sign" =>
    pure {w with orc := ⟨← natF j "sig", ← natF j "org", ← natF j "tid", ← natF j "mid", ← natF j "bid",
      ← natF j "ts", ← boolF j "isb"⟩ :: w.orc}
  | "frame" =>
    let n ← natF j "n"
    let hd ← boolF j "hd"
    let ok ← verified w j
    let big ← boolF j "big"
    let kind : MsgKind := if !hd then .badhead else if big then .big else if !ok then .badsig else .good
    let m : Msg := ⟨← natF j "mid", ← natF j "org", ← natF j "ts", kind, ← natF j "sz", (← natF j "bid", ← boolF j "isb")⟩
    let at_ ← natF j "at"
    let r := OnMsg (paramsOf n) (← node w n) at_ at_ (← frameOf (← natF j "ft")) (← boolF j "boot") m
    check (r.ack == (← natF j "ack")) s!"frame: PACK count differs: model {r.ack}"
    finish w j n r "frame"
  | "have" =>
    let n ← natF j "n"
    let ids ← natList (← field j "ids")
    finish w j n (OnHave (paramsOf n) (← node w n) (← natF j "at") (← boolF j "boot") ids) "have"
  | "timer" =>
    let n ← natF j "n"
    finish w j n (OnTimer (paramsOf n) (← node w n) (← natF j "at")) "timer"
  | "acp" =>
    let n ← natF j "n"
    finish w j n (AcpAnswer (paramsOf n) (← node w n) (← natF j "at") (← natF j "id") (← boolF j "allow")) "acp"
  | s => throw s!"unknown broadcast event {s}"

end Vinc.BroadcastTrace
