/-!
# Received packets: the model

A model of `vinc-transport` `recovery/recv.rs` (`ReceivedPackets`), operation for operation as
`proofs/tla/RxOps.tla` has them, over unbounded `Nat` packet numbers and times. A time the code computes in `u64`
saturates at `top` (`u64::MAX`); the replay of the recorded runs uses the same value and compares what the 32-bit
checker saw through the clamp at `2^31 - 1`. `Vinc.TraceRx` replays the recorded calls of the real code through these
functions; the theorems are in `Vinc.TransportRxThm` and `Vinc.TransportRxAck`.

The sorted position of the code (`partition_point`) is the split of the list at the first range that does not end
below the number: `split`.
-/

namespace Vinc.TransportRx

/-- A range `[start, end)`. -/
abbrev Iv := Nat × Nat

/-- The state of one tracker. `cap` is the const generic `RANGES`. -/
structure X where
  items : List Iv
  cap : Nat
  floor : Nat := 0
  pending : Nat := 0
  due : Option Nat := none
  every : Option Nat := none
  mrtt : Option Nat := none
  sent : List Iv := []
  conf : List Iv := []
  cf : Option Nat := none
  deriving BEq, Repr

def top : Nat := 2 ^ 64 - 1
def ms : Nat := 1000000
def sec : Nat := 1000000000
def maxpn : Nat := 2 ^ 62 - 1
def u32max : Nat := 2 ^ 32 - 1
/-- Acknowledgement-carrying packets remembered. -/
def sentn : Nat := 48
/-- Confirmations queued. -/
def confn : Nat := 32
/-- The most ranges one acknowledgement reports. -/
def maxack : Nat := 32
def hold : Nat := 2 * sec

def sadd (a b : Nat) : Nat := min (a + b) top

/-- `max_ack_delay`. -/
def delay (m : Option Nat) : Nat :=
  match m with
  | some v => if 250 * ms ≤ v then max (25 * ms) (min (250 * ms) (v / 8)) else 25 * ms
  | none => 25 * ms

def isLong (m : Option Nat) : Bool :=
  match m with
  | some v => decide (250 * ms ≤ v)
  | none => false

/-- The largest packet number received. -/
def largest (x : X) : Option Nat := x.items.getLast?.map (fun iv => iv.2 - 1)

/-- The ranges that end below `pn` (the partition point) and the rest. -/
def split (pn : Nat) : List Iv → List Iv × List Iv
  | [] => ([], [])
  | iv :: t => if iv.2 < pn then ((iv :: (split pn t).1), (split pn t).2) else ([], iv :: t)

def contains (x : X) (pn : Nat) : Bool := decide (pn < x.floor) || x.items.any (fun iv => decide (iv.1 ≤ pn ∧ pn < iv.2))

/-- `push_new`: a fresh one-number range between `a` and `b`; when full the lowest range is forgotten. -/
def pushNew (x : X) (a b : List Iv) (pn : Nat) : Bool × X :=
  if a.length + b.length = x.cap then
    match a, b with
    | [], [] => (false, x)
    | [], (ls, _) :: _ => (false, { x with floor := max x.floor ls })
    | (_, le) :: a', _ => (true, { x with floor := max x.floor le, items := a' ++ (pn, pn + 1) :: b })
  else (true, { x with items := a ++ (pn, pn + 1) :: b })

/-- `insert` once the list is split at the partition point into `a` (ranges ending below `pn`) and `b`. -/
def insertAB (x : X) (pn : Nat) (a b : List Iv) : Bool × X :=
  match b with
  | [] => pushNew x a b pn
  | (s, e) :: b' =>
    if s ≤ pn ∧ pn < e then (false, x)
    else if e = pn then
      match b' with
      | (ns, ne) :: b'' =>
        if ns = pn + 1 then (true, { x with items := a ++ (s, ne) :: b'' })
        else (true, { x with items := a ++ (s, pn + 1) :: (ns, ne) :: b'' })
      | [] => (true, { x with items := a ++ [(s, pn + 1)] })
    else if s = pn + 1 then (true, { x with items := a ++ (pn, e) :: b' })
    else pushNew x a b pn

/-- `insert`: false when `pn` is a duplicate or too old to track. -/
def insert (x : X) (pn : Nat) : Bool × X :=
  if pn < x.floor then (false, x) else insertAB x pn (split pn x.items).1 (split pn x.items).2

/-- The deadline after an ack-eliciting packet: now when the rule fires, else the earlier of the old deadline and
`due2`, the packet's time plus the delay. -/
def dueNext (fire : Bool) (now due2 : Nat) (od : Option Nat) : Nat :=
  if fire then now else match od with | none => due2 | some d0 => if due2 < d0 then due2 else d0

/-- One received packet: the number, the time, whether it needs an acknowledgement, the stream bytes. -/
structure Rx where
  pn : Nat
  now : Nat
  elic : Bool
  bytes : Nat

/-- `on_packet_received`: the outcome and the new state. -/
def receive (x : X) (p : Rx) : String × X :=
  if maxpn < p.pn then ("PacketNumberOutOfRange", x)
  else
    let expected := match largest x with | some l => l + 1 | none => 0
    let r := insert x p.pn
    let y := r.2
    if !r.1 then ("Duplicate", y)
    else if !p.elic then ("New", y)
    else
      let gap := p.pn != expected
      let pend := min (y.pending + 1) u32max
      let bulk := decide (1000 ≤ p.bytes) && (match largest y with | some l => decide (2 ≤ l) | none => false)
      let e0 := match y.every with | some e => e | none => if bulk then 3 else 2
      let ev := if isLong y.mrtt then max e0 4 else e0
      let due2 := sadd p.now (delay y.mrtt)
      ("New", { y with pending := pend, due := some (dueNext (decide (ev ≤ pend) || gap) p.now due2 y.due) })

def setMinRtt (x : X) (m : Option Nat) : X := { x with mrtt := m }
def setEvery (x : X) (e : Option Nat) : X := { x with every := e.map (max 1) }

def ackDeadline (x : X) : Option Nat := if x.pending == 0 then none else x.due
def ackDue (x : X) (now : Nat) : Bool := match ackDeadline x with | some d => decide (d ≤ now) | none => false

/-- The larger of two optional numbers, none being the smallest. -/
def omax : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => some (max a b)

def maxOf (l : List Iv) (m : Option Nat) : Option Nat := l.foldl (fun a c => omax a (some c.2)) m

/-- The confirmations at least 2 s old, oldest first. -/
def aged (c : List Iv) (now : Nat) : List Iv := c.takeWhile (fun e => decide (sadd e.1 hold ≤ now))

def floorAt (x : X) (now : Nat) : Option Nat := maxOf (aged x.conf now) x.cf

/-- `ack_ranges`: largest first, as inclusive pairs. -/
def ackRanges (x : X) (now : Nat) : List Iv :=
  let n := x.items.length
  let only := match floorAt x now with
    | some f => decide (1 < n) && (match x.items[n - 2]? with | some iv => decide (iv.2 - 1 < f) | none => false)
    | none => false
  let take := if only then 1 else maxack
  (x.items.reverse.take take).map (fun iv => (iv.1, iv.2 - 1))

/-- `on_ack_sent`. -/
def ackSent (x : X) (apn now : Nat) : X :=
  match largest x with
  | none => x
  | some lg =>
    let ag := aged x.conf now
    let s0 := if x.sent.length == sentn then x.sent.drop 1 else x.sent
    { x with pending := 0, due := none, cf := maxOf ag x.cf, conf := x.conf.drop ag.length, sent := s0 ++ [(apn, lg)] }

/-- `on_peer_ack` with the acknowledged inclusive ranges. -/
def peerAck (x : X) (now : Nat) (rgs : List Iv) : X :=
  match (rgs.map (·.2)).foldl (fun a b => some (match a with | some a => max a b | none => b)) none with
  | none => x
  | some lg =>
    let hits := x.sent.filter (fun e => decide (e.1 ≤ lg) && rgs.any (fun r => decide (r.1 ≤ e.1 ∧ e.1 ≤ r.2)))
    match hits.map (·.2) |>.foldl (fun a b => some (match a with | some a => max a b | none => b)) none with
    | none => x
    | some best =>
      { x with sent := x.sent.filter (fun e => decide (lg < e.1)),
               conf := if x.conf.length < confn then x.conf ++ [(now, best)] else x.conf }

def X.init (cap : Nat) : X := { items := [], cap }

end Vinc.TransportRx
