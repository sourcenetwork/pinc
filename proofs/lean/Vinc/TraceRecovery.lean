import Vinc.Json
import Vinc.TransportRecovery

/-!
# Replay of the loss recovery traces

The Lean half of the trace validation of loss recovery (`recovery/engine.rs`, `ack.rs`, `loss.rs`, `pto.rs`,
`sent.rs`, `rtt.rs`, `tail.rs`), the port of `proofs/tla/TraceRecovery.tla`. It reads the `rc` and `tr` events
written by the Rust test `trace_recovery` and replays every call through the functions of
`Vinc.TransportRecovery`: the state the model computes must be the state recorded (the loss timer and the next
timer shown at most `2^31 - 1`, as the 32-bit checker saw them), and so must the events (the path each acknowledgement
and loss names is the one its packet left on), the summary, the error and the ping of the call. The constants are those
of the test: nanoseconds, a ring of 6, 8 paths, 200 ghosts, 32 late sends; the saturation value is `u64::MAX`.
-/

namespace Vinc.TraceRecovery
open Vinc.Json Vinc.TransportRecovery

def params : P := { n := 6, ms := 1000000, sec := 1000000000, mp := 8, top := 2 ^ 64 - 1, maxg := 200, laten := 32 }

/-- The largest value of a 32-bit checker integer. -/
def top32 : Nat := 2 ^ 31 - 1

def optNat (j : J) (k : String) : Except String (Option Nat) := do
  let v ← intF j k
  pure (if v < 0 then none else some v.toNat)

def optOf (v : Int) : Option Nat := if v < 0 then none else some v.toNat

def boolList (j : J) : Except String (List Bool) := do
  match j.arr? with
  | none => throw "not an array"
  | some a => a.toList.mapM (fun x => match x.bool? with | some b => pure b | none => throw "not a bool")

def stOf (n : Nat) : Except String St :=
  match n with | 0 => pure .fl | 1 => pure .lost | 2 => pure .done | _ => throw "bad slot state"

def slotOf (j : J) : Except String Slot := do
  pure { pn := ← natF j "pn", time := ← natF j "time", size := ← natF j "size", path := ← natF j "path",
         rep := ← boolF j "rep", probe := ← boolF j "probe", fr := ← boolList (← field j "fr"),
         st := ← stOf (← natF j "st"), lostAt := ← natF j "at" }

def reoOf (j : J) : Except String (Nat × Option Nat) := do
  match j.arr? with
  | some #[a, b] =>
    match a.nat?, b.int? with
    | some e, some s => pure (e, optOf s)
    | _, _ => throw "bad reorder cell"
  | _ => throw "bad reorder cell"

/-- The state a recorded view shows. -/
def rOf (v : J) : Except String R := do
  let ring ← match (← field v "ring").arr? with
    | some a => a.toList.mapM slotOf
    | none => throw "ring is not an array"
  let rt ← field v "rtt"
  let reo ← match (← field v "reo").arr? with
    | some a => a.toList.mapM reoOf
    | none => throw "reo is not an array"
  pure { ring, ls := ← optNat v "ls", la := ← optNat v "la", sent := ← natF v "sent", acked := ← natF v "acked",
         lost := ← natF v "lost", inf := ← natF v "inf", infp := ← natF v "infp", lt := ← optNat v "lt",
         pc := ← natF v "pc", lp := ← natF v "lp", asleep := ← boolF v "asleep", down := ← boolF v "down",
         hrd := ← natF v "hrd", clock := ← natF v "clock", tgr := ← natF v "tgr", lrtt := ← natF v "lrtt",
         rtt := { lat := ← optNat rt "lat", sm := ← natF rt "sm", var := ← natF rt "var", mn := ← optNat rt "mn",
                  has := ← boolF rt "has" },
         rel := ← boolList (← field v "rel"), prtt := ← natList (← field v "prtt"), act := ← natF v "act",
         flip := ← optNat v "flip", late := ← pairList (← field v "late"), saved := ← optNat v "saved", reo,
         gs := ← natF v "gs", lat := ← natF v "lat" }

/-- The model's state as the 32-bit checker records the loss timer. -/
def clampR (r : R) : R :=
  { r with lt := r.lt.map (min top32),
           -- the code shows the time of the loss only for a slot that is a ghost
           ring := r.ring.map (fun s => if s.st == .lost then s else { s with lostAt := 0 }) }

def evOf (j : J) : Except String Ev := do
  match j.arr? with
  | some #[k, pn, size, fr, f1, f2] | some #[k, pn, size, fr, f1, f2, _] =>
    match k.str?, pn.nat?, size.nat?, f1.bool?, f2.bool? with
    | some k, some pn, some size, some f1, some f2 => pure ⟨k, pn, size, ← boolList fr, f1, f2⟩
    | _, _, _, _, _ => throw "bad event"
  | _ => throw "bad event"

/-- The path an acknowledgement or a loss reports is the path its packet left on: the 7th field of the event names a
slot of the ring (before the call) with the packet's number. -/
def evPathOk (r : R) (j : J) : Except String Unit := do
  match j.arr? with
  | some #[k, pn, _, _, _, _, path] =>
    match k.str?, pn.nat?, path.nat? with
    | some k, some pn, some path =>
      if k == "acked" || k == "lost" then
        check (r.ring.any (fun s => s.pn == pn && s.path == path)) s!"{k} of packet {pn}: the path {path} is not the one it left on"
      else pure ()
    | _, _, _ => throw "bad event path"
  | some #[k, _, _, _, _, _] =>
    match k.str? with
    | some k => check (k != "acked" && k != "lost") s!"a {k} event without its path"
    | none => throw "bad event"
  | _ => throw "bad event"

def evPathsOk (r : R) (j : J) : Except String Unit := do
  match j.arr? with
  | some a => a.toList.forM (evPathOk r)
  | none => throw "evs is not an array"

def evsOf (j : J) : Except String (List Ev) := do
  match j.arr? with
  | some a => a.toList.mapM evOf
  | none => throw "evs is not an array"

def smOf (j : J) : Except String Sm := do
  match ← natList j with
  | [a, b, c, d, e] => pure ⟨a, b, c, d, e⟩
  | _ => throw "bad summary"

structure St' where
  r : R := R.init params
  t : Tail := Tail.new
  run : Nat := 0

/-- The recorded view equals the model's state, the next timer included. -/
def same (m : R) (v : J) (what : String) : Except String Unit := do
  let rec' ← rOf v
  if clampR m == rec' then pure () else throw s!"{what}: the model computes {repr (clampR m)}, the code recorded {repr rec'}"
  let nt ← optNat v "nt"
  if (nextTimeout params m).map (min top32) == nt then pure ()
  else throw s!"{what}: the next timer is {repr ((nextTimeout params m).map (min top32))}, the code recorded {repr nt}"

def checkRes (j : J) (x : Res) (what : String) (sum : Bool) : Except String Unit := do
  check (x.err == (← strF j "err")) s!"{what}: the model answers {x.err}, the code {← strF j "err"}"
  check (x.ev == (← evsOf (← field j "evs"))) s!"{what}: the events differ: model {repr x.ev}"
  if sum && x.err == "ok" then
    check (x.s == (← smOf (← field j "sum"))) s!"{what}: the summary differs: model {repr x.s}"

def replayEvent (j : J) (st : St') : Except String St' := do
  let t ← strF j "t"
  let op ← strF j "op"
  let p := params
  if t == "tr" then
    match op with
    | "init" => pure { st with t := Tail.new }
    | "pkt" =>
      let t2 := tailPacket st.t (← natF j "pn") (← boolF j "plain") (← boolF j "inel")
      check (t2.burst == (← natF j "burst") && t2.cand == (← optNat j "cand")) "tail: the packet step differs"
      pure { st with t := t2 }
    | "drain" =>
      let (t2, c) := tailDrain st.t
      check (c == (← optNat j "c")) "tail: the candidate differs"
      check (t2.burst == (← natF j "burst") && t2.cand == (← optNat j "cand")) "tail: the drain step differs"
      pure { st with t := t2 }
    | _ => throw s!"unknown tail op {op}"
  else
    let v ← field j "v"
    let r := st.r
    let upd (r2 : R) (what : String) : Except String St' := do
      same r2 v what
      pure { st with r := r2 }
    match op with
    | "init" =>
      same (R.init p) v "init"
      pure { st with r := R.init p, run := ← natF j "run" }
    | "end" => pure st
    | "send" =>
      let x := send p r ⟨← natF j "pn", ← natF j "time", ← natF j "size", ← natF j "path", ← boolF j "rep",
        ← boolF j "probe", ← boolList (← field j "fr")⟩
      check (x.err == (← strF j "err")) s!"send: the model answers {x.err}, the code {← strF j "err"}"
      upd x.r "send"
    | "untracked" =>
      let x := untracked r (← natF j "pn")
      check (x.err == (← strF j "err")) s!"untracked: the model answers {x.err}"
      upd x.r "untracked"
    | "ack" =>
      let x := ack p r (← natF j "now") (← pairList (← field j "rgs"))
      checkRes j x "ack" true
      evPathsOk r (← field j "evs")
      upd x.r "ack"
    | "timeout" =>
      let x := timeout p r (← natF j "now")
      check (x.ev == (← evsOf (← field j "evs"))) s!"timeout: the events differ: model {repr x.ev}"
      evPathsOk r (← field j "evs")
      check (x.s == (← smOf (← field j "sum"))) s!"timeout: the summary differs"
      check (x.ping == (← boolF j "ping")) "timeout: the ping differs"
      upd x.r "timeout"
    | "flush" =>
      let x := flush r (← natF j "now")
      check (x.ev == (← evsOf (← field j "evs"))) "flush: the events differ"
      evPathsOk r (← field j "evs")
      check (x.s == (← smOf (← field j "sum"))) "flush: the summary differs"
      upd x.r "flush"
    | "health" =>
      check (health p r (← natF j "now") == (← strF j "h")) "health differs"
      upd r "health"
    | "kind" =>
      let (r2, e) := setKind r p.mp (← natF j "path") (← boolF j "relay")
      check (e == (← strF j "err")) "kind: the error differs"
      upd r2 "kind"
    | "switch" =>
      let (r2, re, e) := switchPath r p.mp (← natF j "path")
      check (e == (← strF j "err") && re == (← boolF j "restarted")) "switch differs"
      upd r2 "switch"
    | "follow" =>
      let (r2, e) := followPath r p.mp (← natF j "path")
      check (e == (← strF j "err")) "follow: the error differs"
      upd r2 "follow"
    | "asleep" => upd { r with asleep := ← boolF j "b" } "asleep"
    | "down" => upd { r with down := ← boolF j "b" } "down"
    | "activity" => upd (activity r (← natF j "now")) "activity"
    | "seed" => upd { r with rtt := rttSeed p r.rtt (← natF j "x") } "seed"
    | "node" => upd { r with tgr := ← natF j "x" } "node"
    | "hs" => upd { r with lrtt := ← natF j "x" } "hs"
    | _ => throw s!"unknown recovery op {op}"

end Vinc.TraceRecovery
