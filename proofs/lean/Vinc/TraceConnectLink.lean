import Vinc.Json
import Vinc.ConnectLink

/-!
# Replay of the client carrier trace

The replay half of the trace validation of the client carrier state machine (the Rust test `trace_connect_link`; the
TLA+ half is `TraceConnectLink.tla`). Every recorded call of the real `Link` is replayed through the Lean functions of
`ConnectLink.lean`: the answer and the link and shared state read back after the call must be the ones the model
computes. Times are recorded in microseconds and are nanoseconds here.
-/

namespace Vinc.TraceConnectLink
open Vinc.Json Vinc.ConnectLink

/-- The model state of a run: the link and the shared state. -/
structure W where
  l : Link := {}
  s : Shared := {}

instance : Inhabited W := ⟨{}⟩

def isTag (t : String) : Bool := t == "lknew" || t == "lkset" || t == "lk"

def us (j : J) (k : String) : Except String Nat := do pure ((← natF j k) * 1000)

def optUs (j : J) (k : String) : Except String (Option Nat) := do
  let v ← intF j k
  pure (if v < 0 then none else some (v.toNat * 1000))

def stateOf : String → Except String State
  | "down" => pure .down
  | "dialing" => pure .dialing
  | "open" => pure .open_
  | s => throw s!"unknown state {s}"

def linkOf (j : J) : Except String Link := do
  pure { st := ← stateOf (← strF j "st"), retry := ← us j "retry", at_ := ← us j "at", ds := ← us j "ds",
         chk := ← us j "chk", ride := ← boolF j "ride", gap := ← us j "gap", lrx := ← us j "lrx",
         hlt := ← us j "hlt", defer := ← boolF j "defer", was := ← boolF j "was" }

def sharedOf (j : J) : Except String Shared := do
  pure { phone := ← boolF j "phone", kfail := ← optUs j "kfail", lhi := ← us j "lhi", klearn := ← boolF j "klearn",
         kiv := ← us j "kiv", restarted := ← boolF j "restarted", du := ← optUs j "du" }

def ctxOf (j : J) : Except String Ctx := do
  pure { home := ← boolF j "home", rtt := ← us j "rtt", udp := ← boolF j "udp", rides := ← boolF j "rides",
         queued := ← boolF j "queued" }

def actStr : Option Act → String
  | none => "none"
  | some .dial => "dial"
  | some .close => "close"
  | some .ping => "ping"
  | some .check => "check"

def pulseStr : Pulse → String
  | .closed => "closed"
  | .waiting => "waiting"
  | .ping => "ping"

def sameState (call : String) (w : W) (l : Link) (s : Shared) (j : J) : Except String W := do
  check (decide (l = (← linkOf (← field j "L")))) s!"{call}: different link"
  check (decide (s = (← sharedOf (← field j "S")))) s!"{call}: different shared state"
  pure { l := l, s := s }

def replayEvent (j : J) (w : W) : Except String W := do
  match ← strF j "t" with
  | "lknew" => pure { l := {}, s := ← sharedOf (← field j "S") }
  | "lkset" => pure { w with s := ← sharedOf (← field j "S") }
  | "lk" =>
    let now ← us j "now"
    let c ← ctxOf (← field j "ctx")
    let call ← strF j "c"
    let res ← field j "res"
    let resS (e : String) : Except String Unit :=
      check (res.str? == some e) s!"{call}: the answer is {repr res.str?}, the model says {e}"
    match call with
    | "want_dial" =>
      let (a, l, s) := wantDial w.l w.s now c
      resS (actStr a)
      sameState call w l s j
    | "opened" =>
      let (was, l) := opened w.l now
      check (res.bool? == some was) "opened: different answer"
      sameState call w l w.s j
    | "closed" => resS "none"; sameState call w (closed w.l now) w.s j
    | "heard" => resS "none"; sameState call w (heard w.l now) w.s j
    | "wrote" => resS "none"; sameState call w (wrote w.l now) w.s j
    | "pulse" =>
      let (p, l) := pulse w.l now c
      resS (pulseStr p)
      sameState call w l w.s j
    | "reset" =>
      let (_, l) := reset w.l now
      resS "close"
      sameState call w l w.s j
    | "before_send" =>
      let (a, l) := beforeSend w.l w.s now c
      resS (actStr a)
      sameState call w l w.s j
    | "check" =>
      let (a, l) := startCheck w.l now c (← boolF j "ridden")
      resS (actStr a)
      sameState call w l w.s j
    | "tick" =>
      let (a, l, s) := tick w.l w.s now c
      resS (actStr a)
      sameState call w l s j
    | "deadline" =>
      let d := match nextDeadline w.l w.s now c with | some d => ((d + 999) / 1000 : Nat) | none => 0
      match nextDeadline w.l w.s now c, res.nat?, res.int? with
      | some _, some r, _ => check (r == d) s!"deadline: {r}, the model says {d}"
      | none, _, some r => check (r == -1) "deadline: the model has none"
      | _, _, _ => throw "deadline: different answer"
      sameState call w w.l w.s j
    | t => throw s!"unknown link call {t}"
  | t => throw s!"unknown link event {t}"

end Vinc.TraceConnectLink
