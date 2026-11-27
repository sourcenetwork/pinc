import Pinc.Json
import Pinc.TransportTimers

/-!
# Replay of the timers traces

The Lean half of the trace validation of the timers and the closing state of the connection (`conn/timer.rs`,
`conn/life.rs`), the port of `proofs/tla/TraceTimers.tla`. It reads the `tmr` events written by the Rust test
`trace_timers` and replays every call of each connection through the functions of `Pinc.TransportTimers` with the
real constants (in microseconds): `poll_timeout` must be the minimum `poll` takes over the recorded component
deadlines; the state recorded after each call must be the one the model computes from the state the previous call
left, with the same lifecycle events and the same idle deadline; `poll_transmit` may write only what `canSend`
allows, and at most one CLOSE leaves each connection of a run. A `handle_timeout` call carries what the recovery
timer read for the close behind a live carrier (`pr`: the probe timeout, the path, the carrier, the probe timeouts in a
row, when the peer was last heard, the round trip) and whether the path was dead; the model decides from them. A
close the handshake's timer decided in the call (a handshake timeout, or a dialing side's session its peer never
confirmed) is read from the events it reported.
-/

namespace Pinc.TraceTimers
open Pinc.Json Pinc.TransportTimers

def isTag (t : String) : Bool := t == "tmr"

def optOf (v : Int) : Option Nat := if v < 0 then none else some v.toNat
def optF (j : J) (k : String) : Except String (Option Nat) := do pure (optOf (← intF j k))

def phOf : String → Except String Ph
  | "hs" => pure .hs
  | "conn" => pure .conn
  | "closing" => pure .closing
  | "closed" => pure .closed
  | p => throw s!"unknown phase {p}"

def evOf : String → Except String Ev
  | "local" => pure .local
  | "peer" => pure .peer
  | "viol" => pure .viol
  | "idle" => pure .idle
  | "dead" => pure .dead
  | "hs" => pure .hs
  | "unconf" => pure .unconf
  | "asleep" => pure .asleep
  | "awake" => pure .awake
  | "unanswered" => pure .unanswered
  | e => throw s!"unknown event {e}"

def sOf (v : J) : Except String S := do
  pure { ph := ← phOf (← strF v "ph"), close := ← optF v "close", keys := ← boolF v "keys", act := ← natF v "act",
         sent := ← natF v "sent", ka := ← optF v "ka", pa := ← optF v "pa", la := ← boolF v "la",
         stx := ← natF v "stx", wd := ← optF v "wd", ld := ← optF v "ld" }

def cOf (v : J) : Except String C := do
  pure { conf := ← boolF v "conf", hs := ← optF v "hs", rekey := ← optF v "rekey", recov := ← optF v "rec",
         ack := ← optF v "ack", amp := ← boolF v "amp", rr := ← boolF v "rr", kr := ← boolF v "kr", paced := ← optF v "paced", path := ← optF v "path",
         mtu := ← optF v "mtu" }

/-- What the recovery timer read at a `handle_timeout` call for the carrier rule. -/
def pOf (v : J) : Except String P := do
  pure { ping := ← boolF v "ping", relay := ← boolF v "relay", ch := ← optF v "ch", pto := ← natF v "pto",
         lh := ← natF v "lh", smp := ← boolF v "smp", sr := ← natF v "sr", nd := ← natF v "nd" }

def evsOf (j : J) : Except String (List Ev) := do
  match (← field j "ev").arr? with
  | some a => a.toList.mapM fun e => match e.str? with
    | some x => evOf x
    | none => throw "an event is not a string"
  | none => throw "ev is not an array"

/-- Per connection of the run: the state, and the CLOSE packets that left. -/
structure W where
  a : S := {}
  b : S := {}
  ca : Nat := 0
  cb : Nat := 0

def W.get (w : W) (n : String) : S × Nat := if n == "a" then (w.a, w.ca) else (w.b, w.cb)
def W.put (w : W) (n : String) (s : S) (c : Nat) : W :=
  if n == "a" then { w with a := s, ca := c } else { w with b := s, cb := c }

def k : K := kReal

/-- The state after the call must be the model's, with the same events and the same idle deadline. -/
def same (r : R) (j : J) (what : String) : Except String Unit := do
  let v ← field j "v"
  let rec' ← sOf v
  if r.s != rec' then throw s!"{what}: the model computes {repr r.s}, the code recorded {repr rec'}"
  let ev ← evsOf j
  if r.ev != ev then throw s!"{what}: the model reports {repr r.ev}, the code reported {repr ev}"
  check (idle k r.s == (← natF v "idle")) s!"{what}: the idle deadline differs"

def replayEvent (j : J) (w : W) : Except String W := do
  let n ← strF j "n"
  let (s, c) := w.get n
  let now ← natF j "now"
  let ev ← evsOf j
  let has (x : Ev) : Bool := ev.contains x
  let keep (x : S) (what : String) : Except String W := do
    same ⟨x, []⟩ j what
    pure (w.put n x c)
  let upd (r : R) (what : String) : Except String W := do
    same r j what
    pure (w.put n r.s c)
  match ← strF j "op" with
  | "init" =>
    check ev.isEmpty "init: events"
    let s0 ← sOf (← field j "v")
    same ⟨s0, []⟩ j "init"
    pure (w.put n s0 0)
  | "poll" =>
    let out ← intF j "out"
    let p := poll k s (← cOf (← field j "v"))
    check ((p.map (fun t => (t : Int))).getD (-1) == out)
      s!"poll: the model computes {repr p}, the code returned {out}"
    keep s "poll"
  | "timeout" =>
    let pj ← field j "pr"
    -- The handshake's timer runs before the recovery timer: an end it reported came first, and a dead path in the
    -- same call changed nothing.
    let dead ← boolF pj "dead"
    let cc : CC := if has .hs then .hs else if has .unconf then .unconf else if dead then .dead else .none
    upd (timeout k s now cc (← pOf pj)) "timeout"
  | "recv" =>
    upd (recv s now ((← strF j "res") == "ok") (has .asleep) (has .peer)) "recv"
  | "inject" =>
    check (isOpen s) "inject: on a connection that is not open"
    let err ← natF j "err"
    upd (if (← strF j "kind") == "bad" then bad s err else viol s now err) "inject"
  | "close" => upd (close s (← natF j "err")) "close"
  | "tx" =>
    let sent := decide (0 < (← natF j "len"))
    let stx ← natF (← field j "v") "stx"
    check (!sent || canSend s) "tx: the connection wrote what it may not"
    check (decide (stx ≤ s.stx) && (decide (s.stx ≤ stx) || sent)) "tx: the SLEEP count moved without a datagram"
    let c2 := c + if txClose s sent then 1 else 0
    check (decide (c2 ≤ 1)) "tx: a second CLOSE left"
    same ⟨tx s now sent stx, []⟩ j "tx"
    pure (w.put n (tx s now sent stx) c2)
  | "sleep" => keep (sleep s) "sleep"
  | "wake" => keep (wake k s now) "wake"
  | "link" => keep (link k s now (← boolF j "down")) "link"
  | "keepalive" => keep (keepalive s (← optF j "ka")) "keepalive"
  | "pulse" => keep (pulse s now (← boolF j "sent")) "pulse"
  | "app" =>
    check (!(← boolF j "ok") || isOpen s) "app: a closed connection took data"
    keep s "app"
  | op => throw s!"unknown timer op {op}"

end Pinc.TraceTimers
