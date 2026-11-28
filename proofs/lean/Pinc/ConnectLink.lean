import Pinc.Json

/-!
# The client carrier state machine

`client/link.rs` of `pinc-connect`, step for step: the timing state machine of one carrier to one relay (dial, retry,
watchdog, keepalive, check, lease and restart defer), as functions from a link, the node-wide shared state and a
clock reading to the new link, the new shared state and what the host must do. Times are nanoseconds as `Nat`; the
`u64` operations of the code are `saturating_sub` (`satSub`), `saturating_add` and `saturating_mul`, none of which
overflows below `2^63`, the range the proofs and the traces use, so plain `Nat` arithmetic is the code's.

Theorems (`ConnectLinkThm.lean`): the retry wait is 1 s or 2 s, `Open` is reached only by `opened`, `lease_hi` never
rises, the learned keepalive interval is at least 15 s and at most half of an earlier one, a dial past the watchdog is
closed, a clock reading before the next deadline does nothing (`tick_before_deadline`), a tick that does nothing
leaves the next deadline in the future (`tick_none_future`), the tick at the deadline acts (`tick_at_deadline_acts`),
a failed unridden check at an idle gap of 15 s or more
teaches the lease, a send onto a carrier idle both ways for the lease resets it, and the restart defer.
-/

namespace Pinc.ConnectLink

def sec : Nat := 1000000000

/-- `link::rule`. -/
def retryMin : Nat := sec
def retryMax : Nat := 2 * sec
def dialWaitMin : Nat := 8 * sec
def dialWaitRtts : Nat := 8
def dialCap : Nat := 30 * sec
def homeKeep : Nat := 30 * sec
def relayKeep : Nat := 65 * sec
def keepMemory : Nat := 600 * sec
def checkMin : Nat := 3 * sec
def checkRtts : Nat := 3
def keepFloor : Nat := 15 * sec
def leaseFloor : Nat := 15 * sec
def deferNs : Nat := 600000000

/-- `u64::saturating_sub`. -/
def satSub (a b : Nat) : Nat := a - b

/-- `dial_wait`: `max(8 s, 8 x rtt)`, at most 30 s. -/
def dialWait (rtt : Nat) : Nat :=
  let w := rtt * dialWaitRtts
  let w := if w > dialWaitMin then w else dialWaitMin
  if w > dialCap then dialCap else w

/-- `check_wait`: `max(3 s, 3 x rtt)`. -/
def checkWait (rtt : Nat) : Nat :=
  let w := rtt * checkRtts
  if w > checkMin then w else checkMin

/-- `lease_keep`: `max(15 s, min(7/8 x hi, (15 s + hi) / 2))`. -/
def leaseKeep (hi : Nat) : Nat :=
  let a := hi * 7 / 8
  let b := (leaseFloor + hi) / 2
  let m := if a < b then a else b
  if m > leaseFloor then m else leaseFloor

inductive State where
  | down
  | dialing
  | open_
  deriving DecidableEq, Repr

/-- What every carrier of the node shares (`Shared`); `kfail` and `du` are `none` when unset. -/
structure Shared where
  phone : Bool := false
  kfail : Option Nat := none
  lhi : Nat := 0
  klearn : Bool := false
  kiv : Nat := 0
  restarted : Bool := false
  du : Option Nat := none
  deriving DecidableEq, Repr

/-- What the node tells a link on every call (`Ctx`). -/
structure Ctx where
  home : Bool
  rtt : Nat
  udp : Bool
  rides : Bool
  queued : Bool
  deriving DecidableEq, Repr

/-- One carrier's timing state (`Link`). -/
structure Link where
  st : State := .down
  retry : Nat := retryMin
  at_ : Nat := 0
  ds : Nat := 0
  chk : Nat := 0
  ride : Bool := false
  gap : Nat := 0
  lrx : Nat := 0
  hlt : Nat := 0
  defer : Bool := false
  was : Bool := false
  deriving DecidableEq, Repr

/-- What the host must do (`Act`). -/
inductive Act where
  | dial
  | close
  | ping
  | check
  deriving DecidableEq, Repr

def Link.isOpen (l : Link) : Bool := l.st == .open_

/-- A frame to send during the restart defer cancels the wait. -/
def cancelDefer (l : Link) (s : Shared) (now : Nat) (c : Ctx) : Link :=
  if s.restarted ∧ c.queued ∧ l.defer then { l with defer := false, at_ := min l.at_ now } else l

/-- The restart defer holds the home carrier's dial at `now`: nothing is queued and its end is still ahead. `du` is
fixed when the shared state is built, at the start of the node; `none` reads as an end of 0, already past. -/
abbrev deferring (s : Shared) (now : Nat) (c : Ctx) : Prop :=
  s.restarted = true ∧ c.queued = false ∧ c.home = true ∧ now < s.du.getD 0

/-- `Link::dial_at`: the retry time, held back to the end of the defer, brought forward to `now` by a frame queued
during it. -/
def dialAt (l : Link) (s : Shared) (now : Nat) (c : Ctx) : Nat :=
  if deferring s now c then max l.at_ (s.du.getD 0)
  else if s.restarted ∧ c.queued ∧ l.defer then min l.at_ now else l.at_

/-- The dial itself: when the carrier is wanted and its time has come (`dial_at` of the link after `cancelDefer` is its
retry time). -/
def dialOrWait (l1 : Link) (s1 : Shared) (now : Nat) (c : Ctx) : Option Act × Link × Shared :=
  if l1.at_ ≤ now ∧ (c.queued ∨ c.home) then (some .dial, { l1 with st := .dialing, ds := now }, s1)
  else (none, l1, s1)

/-- `Link::want_dial`. -/
def wantDial (l : Link) (s : Shared) (now : Nat) (c : Ctx) : Option Act × Link × Shared :=
  if l.st ≠ .down then (none, l, s)
  else if deferring s now c then (none, { l with at_ := dialAt l s now c, defer := true }, s)
  else dialOrWait (cancelDefer l s now c) s now c

/-- `Link::opened`: whether the carrier was open before. -/
def opened (l : Link) (now : Nat) : Bool × Link :=
  (l.was, { l with st := .open_, retry := retryMin, chk := 0, ride := false, lrx := now, hlt := now, was := true })

/-- `Link::closed`. -/
def closed (l : Link) (now : Nat) : Link :=
  { l with st := .down, at_ := now + l.retry, retry := min (l.retry * 2) retryMax, chk := 0 }

def heard (l : Link) (now : Nat) : Link := { l with lrx := now, chk := 0 }
def wrote (l : Link) (now : Nat) : Link := { l with hlt := now }

/-- `Link::reset`. -/
def reset (l : Link) (now : Nat) : Act × Link := (.close, { l with st := .down, at_ := now, chk := 0, lrx := now })

/-- `Link::check`. -/
def startCheck (l : Link) (now : Nat) (c : Ctx) (ridden : Bool) : Option Act × Link :=
  if ¬ l.isOpen ∨ l.chk ≠ 0 then (none, l)
  else
    let l1 := { l with chk := now + checkWait c.rtt, ride := ridden }
    if ridden then (none, l1) else (some .ping, { l1 with gap := satSub now l.hlt })

/-- `Link::before_send` (STALE_SEND). -/
def beforeSend (l : Link) (s : Shared) (now : Nat) (c : Ctx) : Option Act × Link :=
  if l.isOpen ∧ s.lhi ≠ 0 ∧ ¬ c.udp ∧ satSub now l.hlt ≥ s.lhi ∧ satSub now l.lrx ≥ s.lhi then
    let r := reset l now
    (some r.1, r.2)
  else (none, l)

inductive Pulse where
  | closed
  | waiting
  | ping
  deriving DecidableEq, Repr

/-- `Link::pulse` (CARRIER_PULSE). -/
def pulse (l : Link) (now : Nat) (c : Ctx) : Pulse × Link :=
  if ¬ l.isOpen then (.closed, l)
  else
    let k := startCheck l now c false
    ((if k.1.isSome then .ping else .waiting), k.2)

/-- A silent death is remembered at `now`: up to and including `keepMemory` after it. -/
def recent (s : Shared) (now : Nat) : Bool :=
  match s.kfail with
  | some t => decide (satSub now t ≤ keepMemory)
  | none => false

/-- The keepalive interval while a silent death is remembered (`r`) or not. -/
def keepOf (s : Shared) (c : Ctx) (r : Bool) : Nat :=
  let base := if c.home && (s.phone || r) then homeKeep else relayKeep
  if s.kiv = 0 then base else min base s.kiv

/-- `Link::keep_after`. -/
def keepAfter (s : Shared) (now : Nat) (c : Ctx) : Nat := keepOf s c (recent s now)

/-- `Link::keep_due`: the last heard time plus the interval that holds at that instant. -/
def keepDue (l : Link) (s : Shared) (now : Nat) (c : Ctx) : Nat :=
  l.lrx + keepAfter s (max (l.lrx + keepAfter s now c) now) c

/-- `Link::tick_open`. -/
def tickOpen (l : Link) (s : Shared) (now : Nat) (c : Ctx) : Option Act × Link × Shared :=
  let lease := s.lhi ≠ 0 ∧ ¬ c.udp
  if l.chk ≠ 0 ∧ now ≥ l.chk then
    if l.ride then
      let r := startCheck { l with chk := 0 } now c false
      (r.1, r.2, s)
    else
      let s1 := { s with kfail := some now }
      let s2 :=
        if s1.klearn then
          let silence := satSub now l.lrx
          let seen := if s1.kiv = 0 then silence else min s1.kiv silence
          { s1 with kiv := max (seen / 2) keepFloor }
        else s1
      let s3 :=
        if ¬ c.udp ∧ l.gap ≥ leaseFloor then { s2 with lhi := if s2.lhi = 0 then l.gap else min s2.lhi l.gap } else s2
      let r := reset l now
      (some r.1, r.2, s3)
  else if l.chk ≠ 0 then (none, l, s)
  else if lease ∧ (c.home ∨ c.rides) ∧ satSub now l.hlt ≥ leaseKeep s.lhi then
    let r := startCheck l now c false
    (r.1, r.2, s)
  else if (c.home ∨ c.rides) ∧ now ≥ keepDue l s now c then (some .check, l, s)
  else (none, l, s)

/-- `Link::tick`. -/
def tick (l : Link) (s : Shared) (now : Nat) (c : Ctx) : Option Act × Link × Shared :=
  match l.st with
  | .dialing =>
    if satSub now l.ds > dialWait c.rtt then (some .close, { l with st := .down, at_ := now }, s) else (none, l, s)
  | .down => wantDial l s now c
  | .open_ => tickOpen l s now c

/-- `Link::next_deadline`. -/
def nextDeadline (l : Link) (s : Shared) (now : Nat) (c : Ctx) : Option Nat :=
  match l.st with
  | .dialing => some (l.ds + dialWait c.rtt + 1)
  | .down =>
    if c.queued ∨ c.home then some (dialAt l s now c) else none
  | .open_ =>
    if l.chk ≠ 0 then some l.chk
    else if ¬ (c.home ∨ c.rides) then none
    else
      let silent := keepDue l s now c
      if s.lhi ≠ 0 ∧ ¬ c.udp then some (min (l.hlt + leaseKeep s.lhi) silent) else some silent

end Pinc.ConnectLink
