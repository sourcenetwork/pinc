/-!
# Congestion control and pacing: the model

A model of `vinc-transport` `recovery/cubic.rs`, `round_exit.rs`, `delivery.rs` and `pacer.rs`, call for call, over
unbounded `Nat` with the saturation of the `u64` the code computes in (`sat`). `Vinc.TraceCc` replays the recorded
calls of the real code through these functions; the theorems are in `Vinc.TransportCcThm`.

The cubic term is computed in `Int` (it can be negative before the origin) and floored toward negative infinity, as
the code does.
-/

namespace Vinc.TransportCc

def u64max : Nat := 2 ^ 64 - 1
/-- Narrowing to `u64`, saturating. -/
def sat (v : Nat) : Nat := min v u64max
def satAdd (a b : Nat) : Nat := sat (a + b)
def satMul (a b : Nat) : Nat := sat (a * b)

def ms : Nat := 1000000
def sec : Nat := 1000000000
def initialCwnd : Nat := 44000
def minCwnd : Nat := 2400
def maxCwnd : Nat := 2 ^ 40
def betaSmallLim : Nat := 48000
def minMss : Nat := 1200
def maxMss : Nat := 65535
def gateFast : Nat := 256 * 1024
def gateMid : Nat := 44000
def fastRtt : Nat := 2 * ms
def slowRtt : Nat := 250 * ms
def maxTms : Nat := 2 ^ 30
def initialRtt : Nat := 333 * ms
def u32max : Nat := 2 ^ 32 - 1
def burst : Nat := 10

/-- The integer cube root: the largest `r` below `2^43` with `r^3 <= n`, found bit by bit as the code does. -/
def icbrt (n : Nat) : Nat :=
  (List.range 43).reverse.foldl (fun root bit => if (root ||| (1 <<< bit)) ^ 3 ≤ n then root ||| (1 <<< bit) else root) 0

/-- The slow-start exit detector (`round_exit.rs`). -/
structure Re where
  roundEnd : Nat := 0
  ref : Option Nat := none
  rmin : Option Nat := none
  samples : Nat := 0
  deriving BEq, Repr

def Re.onSample (r : Re) (s : Nat) : Re :=
  { r with rmin := some (match r.rmin with | some m => min m s | none => s), samples := min (r.samples + 1) u32max }

def Re.onAck (r : Re) (largestAcked nextPn cwnd : Nat) : Re × Bool :=
  let r1 := if r.roundEnd ≤ largestAcked then
      { r with ref := (if 8 ≤ r.samples then r.rmin.or r.ref else r.ref), rmin := none, samples := 0, roundEnd := nextPn }
    else r
  let ex := match r1.ref, r1.rmin with
    | some rf, some m =>
      decide (8 ≤ r1.samples) && decide (19200 ≤ cwnd) &&
        decide (satAdd rf (max (4 * ms) (min (rf / 8) (16 * ms))) < m)
    | _, _ => false
  (r1, ex)

/-- The delivery-rate probe (`delivery.rs`). -/
structure Probe where
  start : Option Nat := none
  bytes : Nat := 0
  rate : Nat := 0
  deriving BEq, Repr

def Probe.onAcked (p : Probe) (now bytes minRtt : Nat) : Probe :=
  let start := p.start.getD now
  let b := satAdd p.bytes bytes
  let elapsed := now - start
  if elapsed == 0 || decide (elapsed < minRtt) then { p with start := some start, bytes := b }
  else { start := some now, bytes := 0, rate := max (sat (b * sec / elapsed)) (p.rate - p.rate / 8) }

/-- The controller (`cubic.rs`). -/
structure Cc where
  cwnd : Nat := initialCwnd
  ssthresh : Nat := u64max
  wMax : Nat := 0
  wEst : Nat := 0
  kMs : Nat := 0
  epoch : Option Nat := none
  recovery : Option Nat := none
  streak : Nat := 0
  re : Re := {}
  probe : Probe := {}
  slack : Nat := gateMid
  deriving BEq, Repr

/-- What one acknowledgement tells the controller. -/
structure Ack where
  now : Nat
  acked : Nat
  largestAcked : Nat
  nextPn : Nat
  srtt : Option Nat
  minRtt : Option Nat
  mss : Nat

/-- `W_max + 4 mss d^3 / 1e10`, floored, capped at `maxCwnd`. -/
def cubicTarget (wMax kMs mss tMs : Nat) : Int :=
  let d : Int := (tMs : Int) - ((min kMs maxTms : Nat) : Int)
  let delta : Int := Int.fdiv (4 * (mss : Int) * d * d * d) 10000000000
  min ((wMax : Int) + delta) (maxCwnd : Int)

/-- The window after the cubic step: grown toward the target by the share of the acknowledged bytes. -/
def caCw1 (cwnd : Nat) (target : Int) (acked mss : Nat) : Nat :=
  if (cwnd : Int) < target then
    min (satAdd cwnd (sat (max 1 ((target - cwnd).toNat * mss / cwnd * acked / mss)))) maxCwnd
  else cwnd

/-- The Reno estimate after the acknowledgement. -/
def caWe (west mss acked cw1 : Nat) : Nat := min (satAdd west (sat (53 * mss * acked / (100 * cw1)))) maxCwnd

/-- Slow start: every acknowledged byte, and the exit detector. -/
def Cc.growSS (c : Cc) (acked largestAcked nextPn : Nat) : Cc :=
  let cw := min (satAdd c.cwnd acked) maxCwnd
  let r := c.re.onAck largestAcked nextPn cw
  { c with cwnd := cw, re := r.1, ssthresh := if r.2 then cw else c.ssthresh }

/-- The start of a growth epoch: its time, the origin of the cubic curve and the Reno estimate it starts from. -/
def caSt (c : Cc) (now mss : Nat) : Nat × Nat × Nat :=
  match c.epoch with
  | some e => (e, c.kMs, c.wEst)
  | none => (now, (if c.cwnd < c.wMax then icbrt ((c.wMax - c.cwnd) * 1000000000 / (mss * 4) * 10) else 0), c.cwnd)

/-- The controller after the step: the higher of the cubic window and the Reno estimate. -/
def Cc.caFinish (c : Cc) (ep k we cw1 : Nat) : Cc :=
  { c with epoch := some ep, kMs := k, wEst := we, cwnd := if cw1 < we then we else cw1 }

/-- Congestion avoidance: the cubic curve and the Reno estimate; the higher of the two. -/
def Cc.growCA (c : Cc) (now acked mss0 srtt : Nat) : Cc :=
  let mss := max minMss (min mss0 maxMss)
  let st := caSt c now mss
  let tMs := min (satAdd (now - st.1) srtt / ms) maxTms
  let cw1 := caCw1 c.cwnd (cubicTarget c.wMax st.2.1 mss tMs) acked mss
  c.caFinish st.1 st.2.1 (caWe st.2.2 mss acked cw1) cw1

def Cc.grow (c : Cc) (now acked largestAcked nextPn mss0 srtt : Nat) : Cc :=
  if c.cwnd < c.ssthresh then c.growSS acked largestAcked nextPn else c.growCA now acked mss0 srtt

/-- `gate_cap` for a path whose minimum round trip is `m`. -/
def Cc.gateCap (c : Cc) (m : Nat) : Option Nat :=
  if c.probe.rate == 0 then none
  else
    let bdp := sat (c.probe.rate * m / sec)
    let sf : Nat × Nat := if m < fastRtt then (gateFast, initialCwnd) else if slowRtt ≤ m then (0, minCwnd) else (c.slack, initialCwnd)
    some (min (max (satAdd (satMul bdp 2) sf.1) sf.2) maxCwnd)

def Cc.applyGate (c : Cc) (m : Nat) : Cc :=
  match c.gateCap m with
  | some cap => if cap < c.cwnd then { c with cwnd := cap, ssthresh := min c.ssthresh cap } else c
  | none => c

def Cc.onRtt (c : Cc) (s : Nat) : Cc := { c with re := c.re.onSample s }

/-- The delivery-rate probe takes the acknowledged bytes. -/
def Cc.feed (c : Cc) (a : Ack) : Cc :=
  { c with probe := match a.minRtt with
      | some m => if 0 < m then c.probe.onAcked a.now a.acked m else c.probe
      | none => c.probe }

/-- The last reduction is older than four smoothed round trips and a streak is running. -/
def decayCond (c : Cc) (now srtt : Nat) : Bool :=
  c.streak != 0 && (match c.recovery with | some r => decide (satMul 4 srtt < now - r) | none => false)

/-- The filter streak decays once the last reduction is older than four smoothed round trips. -/
def Cc.decay (c : Cc) (now srtt : Nat) : Cc := if decayCond c now srtt then { c with streak := 0 } else c

def Cc.onAcked (c : Cc) (a : Ack) : Cc :=
  let srtt := a.srtt.getD initialRtt
  let c3 := ((c.feed a).decay a.now srtt).grow a.now a.acked a.largestAcked a.nextPn a.mss srtt
  match a.minRtt with
  | some m => if fastRtt ≤ m ∧ m < slowRtt then c3 else c3.applyGate m
  | none => c3

def Cc.resume (c : Cc) (m : Option Nat) : Cc :=
  match m with
  | some m => c.applyGate m
  | none => c

/-- A loss with no queueing delay (the latest round trip within `min + max(4 ms, min / 8)`) and a streak below 4. -/
def isFiltered (c : Cc) (latest mn : Option Nat) : Bool :=
  match latest, mn with
  | some l, some m => decide (l ≤ satAdd m (max (4 * ms) (m / 8))) && decide (c.streak < 4)
  | _, _ => false

/-- The filtered reduction: 0.9 of the window, slow start is not left. -/
def Cc.lossFiltered (c : Cc) (now : Nat) : Cc :=
  let cw := max (c.cwnd * 9 / 10) minCwnd
  if c.ssthresh != u64max then
    { c with recovery := some now, streak := c.streak + 1, cwnd := cw, ssthresh := min c.ssthresh cw, wEst := min c.wEst cw }
  else { c with recovery := some now, streak := c.streak + 1, cwnd := cw }

/-- The regular reduction: 0.7 of the window (0.85 below 48,000 bytes), slow start ends. -/
def Cc.lossRegular (c : Cc) (now : Nat) : Cc :=
  let cw := max (c.cwnd * (if c.cwnd < betaSmallLim then 85 else 7) / (if c.cwnd < betaSmallLim then 100 else 10)) minCwnd
  { c with recovery := some now, streak := 0, wMax := c.cwnd, cwnd := cw, ssthresh := cw, epoch := none, wEst := cw }

/-- A loss of a packet sent before the last reduction belongs to that episode. -/
def inEpisode (c : Cc) (newest : Nat) : Bool := match c.recovery with | some r => decide (newest ≤ r) | none => false

/-- `on_loss`: the controller and whether the window was reduced. -/
def Cc.onLoss (c : Cc) (now newest : Nat) (latest mn : Option Nat) : Cc × Bool :=
  if inEpisode c newest then (c, false)
  else if isFiltered c latest mn then (c.lossFiltered now, true)
  else (c.lossRegular now, true)

def Cc.newPath (c : Cc) (now nextPn : Nat) : Cc :=
  { c with cwnd := initialCwnd, ssthresh := u64max, epoch := none, re := { roundEnd := nextPn }, streak := 0,
           recovery := match c.recovery with | none => some now | some r => if r < now then some now else some r }

def Cc.restore (c : Cc) (cw ss : Nat) : Cc :=
  if c.cwnd < cw then
    let cw' := min cw maxCwnd
    { c with cwnd := cw', ssthresh := max c.ssthresh ss, wEst := max c.wEst cw' }
  else c

def Cc.setSlack (c : Cc) (b : Nat) : Cc := { c with slack := min b maxCwnd }

/-! ### The pacer (`pacer.rs`) -/

structure Pacer where
  tokens : Nat := burst
  next : Nat := 0
  /-- When the first packet of the burst being counted left. -/
  start : Nat := 0
  deriving BEq, Repr

def Pacer.nextRelease (p : Pacer) (now : Nat) : Nat := if now < p.next then p.next else now

/-- The gap between two packets of a burst's pause. -/
def gap (mtu srtt cwnd : Nat) : Nat := sat (min mtu maxMss * srtt * 4 / (5 * max cwnd 1))

/-- The pause after a burst: ten gaps. -/
def span (mtu srtt cwnd : Nat) : Nat := satMul (gap mtu srtt cwnd) burst

/-- The start of the burst a packet at `now` belongs to: `now` for the first packet of a burst. -/
def Pacer.startAt (p : Pacer) (now : Nat) : Nat := if p.tokens = burst then now else p.start

/-- The burst took at least its pause and the window does not limit the sender: it has waited already. -/
def Pacer.slow (p : Pacer) (now mtu srtt cwnd : Nat) (limited : Bool) : Bool :=
  !limited && decide (span mtu srtt cwnd ≤ now - p.startAt now)

/-- `on_sent`: a packet out of the burst takes a token; the last one refills the burst and sets the release, ten
gaps after it, or one tick after it for a sender that was slow. The release only moves forward. -/
def Pacer.onSent (p : Pacer) (now mtu srtt cwnd : Nat) (limited : Bool) : Pacer :=
  if 1 < p.tokens then { p with tokens := p.tokens - 1, start := p.startAt now }
  else { tokens := burst,
         next := max p.next (satAdd now (if p.slow now mtu srtt cwnd limited then 1 else span mtu srtt cwnd)),
         start := p.startAt now }

end Vinc.TransportCc
