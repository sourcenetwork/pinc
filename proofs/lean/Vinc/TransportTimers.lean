/-!
# The timers and the closing state: the model

A model of the timers and the closing state of the VINCER connection, `vinc-transport` `conn/timer.rs`
(`poll_timeout`, `handle_timeout`) and `conn/life.rs` (close, sleep, wake, the link outage, the idle deadline, the
three ends), with the parts of `conn/send.rs` and `conn/recv.rs` that touch them (the CLOSE packet, the last send,
SLEEP leaving, a packet heard, SLEEP and CLOSE applied), as `proofs/tla/TimersOps.tla` has it, over unbounded `Nat`.

The deadlines of the other components are inputs (`C`): their own rules are proved in their own models (loss recovery
in `TransportRecovery*`, the pacer in `TransportCc*`, the acknowledgement deadline in `TransportRx*`, the MTU timer in
`TransportMtu`). So are the decisions the components take inside a call: a close a component decides in
`handle_timeout` (`CC.dead` when recovery gives up, `CC.hs` when the handshake runs out of time), whether
`poll_transmit` wrote a datagram, and how many SLEEP frames are left after it. The close of a relay session behind a
live carrier (`dead_behind_live_carrier`, at a probe timeout) is decided here from its inputs (`P`). `Vinc.TraceTimers` replays the recorded
calls of a scripted pair of real connections through these functions; the theorems are in `Vinc.TransportTimersThm`.
-/

namespace Vinc.TransportTimers

/-- The phase: handshaking, connected, closing (its CLOSE still to leave), closed. -/
inductive Ph where
  | hs
  | conn
  | closing
  | closed
  deriving DecidableEq, Repr

/-- The constants: `IDLE_TIMEOUT`, `SLEEP_HOLD`, `WAKE_WAIT`, `LINK_DOWN_MAX`, `CARRIER_FRESH`, `INITIAL_RTT`. -/
structure K where
  idle : Nat
  hold : Nat
  wake : Nat
  ldm : Nat
  cf : Nat
  ir : Nat
  deriving Repr

/-- The real constants in microseconds, the unit of the traces: 75 s, 120 s, 800 ms, 30 s, 6 s, 333 ms. -/
def kReal : K :=
  { idle := 75000000, hold := 120000000, wake := 800000, ldm := 30000000, cf := 6000000, ir := 333000 }

/-- The lifecycle state. -/
structure S where
  ph : Ph := .hs
  /-- The code of the CLOSE to send, until it left. -/
  close : Option Nat := none
  /-- The 1-RTT sending keys are installed. -/
  keys : Bool := false
  /-- When the peer was last heard (or the connection last resumed). -/
  act : Nat := 0
  /-- When a datagram last left. -/
  sent : Nat := 0
  /-- The keepalive interval. -/
  ka : Option Nat := none
  /-- Since when the peer announced its sleep. -/
  pa : Option Nat := none
  /-- This endpoint sleeps. -/
  la : Bool := false
  /-- SLEEP frames still to send. -/
  stx : Nat := 0
  /-- When an unanswered WAKE is reported. -/
  wd : Option Nat := none
  /-- Since when the link is down. -/
  ld : Option Nat := none
  deriving DecidableEq, Repr

/-- The deadlines of the other components, as `poll_timeout` reads them. -/
structure C where
  /-- The handshake is confirmed (its retransmit deadline is then not read). -/
  conf : Bool
  hs : Option Nat
  rekey : Option Nat
  /-- Loss recovery: the loss time or the probe timeout. -/
  recov : Option Nat
  ack : Option Nat
  /-- The active path may still be sent 64 bytes (the acknowledgement deadline is read only then). -/
  amp : Bool
  paced : Option Nat
  path : Option Nat
  mtu : Option Nat
  deriving Repr

/-- What `handle_timeout` reads to decide a close behind a live carrier. -/
structure P where
  /-- A probe timeout fired in this call. -/
  ping : Bool
  /-- The active path is a relay path. -/
  relay : Bool
  /-- When the relay's carrier last heard anything. -/
  ch : Option Nat
  /-- Probe timeouts in a row. -/
  pto : Nat
  /-- When the peer was last heard. -/
  lh : Nat
  /-- The round trip has a sample. -/
  smp : Bool
  /-- The smoothed round trip. -/
  sr : Nat
  /-- The node's longest round trip (0 for none). -/
  nd : Nat
  deriving Repr

/-- What a call reports: the reasons of `Event::Closed`, and `PeerAsleep`, `PeerAwake`, `WakeUnanswered`. -/
inductive Ev where
  | local
  | peer
  | viol
  | idle
  | dead
  | hs
  | asleep
  | awake
  | unanswered
  deriving DecidableEq, Repr

/-- A close a component decides inside `handle_timeout`. -/
inductive CC where
  | none
  | dead
  | hs
  deriving DecidableEq, Repr

def isOpen (s : S) : Bool := s.ph == .hs || s.ph == .conn

/-- `idle_deadline`: 75 s after the peer was last heard, or 120 s after it announced its sleep. -/
def idle (k : K) (s : S) : Nat :=
  match s.pa with
  | some p => max (s.act + k.idle) (p + k.hold)
  | none => s.act + k.idle

/-- Nothing can leave: the link is down, or this endpoint sleeps and its SLEEP frames left. -/
def suspended (s : S) : Bool := s.ld.isSome || (s.la && s.stx == 0)
def linkEnd (k : K) (s : S) : Option Nat := s.ld.map (· + k.ldm)
def keepDue (s : S) : Option Nat := s.ka.map (s.sent + ·)

/-- `add` of `poll_timeout`: fold a deadline into the minimum. -/
def addD (t : Nat) : Option Nat → Nat
  | some x => min t x
  | none => t

/-- `poll_timeout`, step for step. -/
def poll (k : K) (s : S) (c : C) : Option Nat :=
  match s.ph with
  | .closed => none
  | .closing => some 0
  | _ =>
    if suspended s then
      let t := addD (addD (idle k s) (linkEnd k s)) s.wd
      some (if s.ld.isSome then addD t c.recov else t)
    else
      let t1 := if !c.conf then addD (idle k s) c.hs else idle k s
      let t2 := addD (addD t1 c.rekey) c.recov
      let t3 := if c.amp then addD t2 c.ack else t2
      let t4 := addD (addD (addD (addD t3 c.paced) c.path) s.wd) (linkEnd k s)
      some (if s.ph == .conn then addD (addD t4 (keepDue s)) c.mtu else t4)

/-- The state after a call and what it reported. -/
structure R where
  s : S
  ev : List Ev
  deriving DecidableEq, Repr

/-- The round trip `dead_behind_live_carrier` reads: the smoothed one, or before a sample the larger of
`INITIAL_RTT` and twice the node's longest round trip. -/
def rtt (k : K) (p : P) : Nat := if p.smp then p.sr else max k.ir (2 * p.nd)

/-- `dead_behind_live_carrier`: the active path is a relay path, its carrier was heard within `CARRIER_FRESH`, 4 probe
timeouts fired in a row and nothing was heard for 4 round trips (differences saturate, as in the code). -/
def carrier (k : K) (now : Nat) (p : P) : Bool :=
  p.relay && (match p.ch with | some h => decide (now - h < k.cf) | none => false) && decide (4 ≤ p.pto)
    && decide (4 * rtt k p ≤ now - p.lh)

def silent (s : S) : S := { s with ph := .closed, close := none }

/-- `begin_close`: one CLOSE is to leave if the connection was established with sending keys; otherwise it is over
at once. -/
def beginClose (s : S) (err : Nat) (why : Ev) : R :=
  if isOpen s then
    { s := { s with close := some err, ph := if s.ph == .conn && s.keys then .closing else .closed }, ev := [why] }
  else { s := s, ev := [] }

/-- The handshake timer of `handle_timeout`: the handshake may run out of time while handshaking. -/
def hsStep (s : S) (cc : CC) : R := if cc == .hs && s.ph == .hs then ⟨silent s, [.hs]⟩ else ⟨s, []⟩

/-- The end of a link outage that lasted its bound. -/
def linkStep (k : K) (s : S) (now : Nat) : S :=
  match s.ld with
  | some d => if d + k.ldm ≤ now then { s with ld := none } else s
  | none => s

/-- The recovery timer: recovery may give up (`silent_close` does nothing once closed). -/
def deadStep (r : R) (cc : CC) : R := if cc == .dead && r.s.ph != .closed then ⟨silent r.s, r.ev ++ [.dead]⟩ else r

/-- The recovery timer at a probe timeout behind a live carrier: unless the path is dead (`cc = .dead`, handled by
`deadStep`), the connection begins a close with a CLOSE, error 0, reason `PathDead` (a no-op once it ended). -/
def carrierStep (k : K) (r : R) (now : Nat) (p : P) (cc : CC) : R :=
  if cc != .dead && p.ping && carrier k now p then
    let b := beginClose r.s 0 .dead
    ⟨b.s, r.ev ++ b.ev⟩
  else r

/-- The recovery timer of `handle_timeout`: recovery may give up, and otherwise the carrier rule may close. -/
def recStep (k : K) (r : R) (now : Nat) (p : P) (cc : CC) : R := carrierStep k (deadStep r cc) now p cc

/-- The wake wait: run out, it is reported. -/
def wakeStep (r : R) (now : Nat) : R :=
  match r.s.wd with
  | some w => if w ≤ now then ⟨{ r.s with wd := none }, r.ev ++ [.unanswered]⟩ else r
  | none => r

/-- `handle_timeout`: a closing connection ends; past the idle deadline the connection ends silently and nothing else
runs; otherwise the handshake timer (it may end a handshaking connection), the end of a link outage, the recovery
timer (it may give up, or close behind a live carrier) and the wake wait, in this order. -/
def timeout (k : K) (s : S) (now : Nat) (cc : CC) (p : P) : R :=
  match s.ph with
  | .closed => ⟨s, []⟩
  | .closing => ⟨{ s with ph := .closed }, []⟩
  | _ =>
    if idle k s ≤ now then ⟨silent s, [.idle]⟩
    else
      let h := hsStep s cc
      wakeStep (recStep k ⟨linkStep k h.s now, h.ev⟩ now p cc) now

/-- A datagram reached `handle_datagram`: `heard` (a packet authenticated and was new), and of its frames a SLEEP
and a CLOSE were applied. A closed or closing connection refuses it. -/
def recv (s : S) (now : Nat) (heard sleep close : Bool) : R :=
  if !isOpen s || !heard then ⟨s, []⟩
  else
    let s1 := { s with act := now, wd := none, pa := if sleep then some now else none }
    let e1 := if sleep then [Ev.asleep] else []
    if close then ⟨silent s1, e1 ++ [.peer]⟩
    else ⟨s1, e1 ++ (if s.pa.isSome && !sleep then [.awake] else [])⟩

/-- Frames that do not decode: a violation before anything is heard. -/
def bad (s : S) (err : Nat) : R := beginClose s err .viol
/-- A frame that breaks a rule: the packet was heard, the peer's sleep ended, then the violation. (A closed or
closing connection refuses the datagram before its frames are read.) -/
def viol (s : S) (now err : Nat) : R :=
  if isOpen s then beginClose { s with act := now, wd := none, pa := none } err .viol else ⟨s, []⟩
def close (s : S) (err : Nat) : R := beginClose s err .local

/-- What `poll_transmit` may write: nothing once closed, only the CLOSE while closing, nothing while suspended. -/
def canSend (s : S) : Bool :=
  match s.ph with
  | .closed => false
  | .closing => s.close.isSome
  | _ => !suspended s

/-- One `poll_transmit` call: `sent` says whether it wrote a datagram, `stx` is the SLEEP count after it. -/
def tx (s : S) (now : Nat) (sent : Bool) (stx : Nat) : S :=
  match s.ph with
  | .closed => s
  | .closing =>
    if s.close.isNone then { s with ph := .closed }
    else if sent then { s with ph := .closed, close := none, sent := now } else s
  | _ => if suspended s then s else { s with sent := if sent then now else s.sent, stx := stx }

/-- Whether the call wrote the CLOSE. -/
def txClose (s : S) (sent : Bool) : Bool := s.ph == .closing && s.close.isSome && sent

def resume (k : K) (s : S) (now : Nat) (susp : Bool) : S :=
  { s with wd := if susp then some (now + k.wake) else s.wd, act := now }
def sleep (s : S) : S := if s.ph == .conn && !s.la then { s with la := true, stx := 2 } else s
def wake (k : K) (s : S) (now : Nat) : S :=
  if s.ph == .conn && s.la then resume k { s with la := false } now true else s
/-- `set_link_down`; a handshaking connection only tells its handshake about a return. -/
def link (k : K) (s : S) (now : Nat) (down : Bool) : S :=
  if s.ph != .conn then s
  else if down then { s with ld := some (s.ld.getD now) }
  else if s.ld.isSome then resume k { s with ld := none } now false
  else s
def keepalive (s : S) (ka : Option Nat) : S := { s with ka := ka }
def pulse (s : S) (now : Nat) (sent : Bool) : S := { s with act := now, sent := if sent then now else s.sent }
/-- The handshake established the session (`Event::Connected`). -/
def est (s : S) (now : Nat) : S := if s.ph == .hs then { s with ph := .conn, keys := true, act := now } else s

/-- The calls that move the lifecycle state, with the decisions of the other components they carry. -/
inductive Op where
  | timeout (now : Nat) (cc : CC) (p : P)
  | recv (now : Nat) (heard sleep close : Bool)
  | bad (err : Nat)
  | viol (now err : Nat)
  | close (err : Nat)
  | tx (now : Nat) (sent : Bool) (stx : Nat)
  | sleep
  | wake (now : Nat)
  | link (now : Nat) (down : Bool)
  | keepalive (ka : Option Nat)
  | pulse (now : Nat) (sent : Bool)
  | est (now : Nat)

/-- One call: the new state, what it reported, and whether the CLOSE left. `poll_transmit` writes only what
`canSend` allows. -/
def step (k : K) (s : S) : Op → R × Bool
  | .timeout now cc p => (timeout k s now cc p, false)
  | .recv now h sl cl => (recv s now h sl cl, false)
  | .bad err => (bad s err, false)
  | .viol now err => (viol s now err, false)
  | .close err => (close s err, false)
  | .tx now sent stx => (⟨tx s now (sent && canSend s) stx, []⟩, txClose s (sent && canSend s))
  | .sleep => (⟨sleep s, []⟩, false)
  | .wake now => (⟨wake k s now, []⟩, false)
  | .link now down => (⟨link k s now down, []⟩, false)
  | .keepalive ka => (⟨keepalive s ka, []⟩, false)
  | .pulse now sent => (⟨pulse s now sent, []⟩, false)
  | .est now => (⟨est s now, []⟩, false)

/-- A run of calls: the final state and how many CLOSE packets left. -/
def run (k : K) : S → List Op → S × Nat
  | s, [] => (s, 0)
  | s, op :: ops =>
    let st := step k s op
    let rest := run k st.1.s ops
    (rest.1, rest.2 + if st.2 then 1 else 0)

end Vinc.TransportTimers
