import Vinc.MembershipInc
import Vinc.MembershipCodec

/-!
# The membership machine: types, constants, tables, host and outputs

The model of `crates/vinc-membership` (`node.rs`, `consts.rs`, `event.rs`, `session.rs`): the state of one
`Membership` node, the host it talks to, and what a call into it produces. The step functions are in
`MembershipModelView.lean` (`view.rs`), `MembershipModelHub.lean` (`hub.rs`) and `MembershipModelNode.lean`
(`timers.rs`, `input.rs`, `node.rs`).

Conventions:

* A `BTreeMap` / `BTreeSet` of the code is a list sorted by key without duplicates (`AMap`, `ASet`); iteration order is
  key order. A cursor loop (`next_key`) is the fold over the keys the table holds when the loop starts (`forKeys`):
  every loop of the code visits keys in increasing order and its body changes the iterated table at the visited key
  only (a removal or an update of the entry in hand), so no key appears or disappears ahead of the cursor. The replay
  of the real traces checks this on every loop that ran.
* A node id is a `Nat` (the code compares ids by equality and order only).
* A `u64` is a `Nat`. `saturating_add` is `satAdd`, `saturating_sub` is natural subtraction, plain `+` and `*` are
  `Nat` operations: the model is exact below `2^64`, which every instant of a host's monotonic clock is for 584
  years.
* The incarnation and the address tag are those of `Vinc.MemInc`. The host's store (`Local`) is part of the call's
  environment and is read from it at the start of each call.
* The proofs treat a call as `N → N`: every effect on the host (frames sent, broadcast layer calls, closes, the store)
  is appended to the node's output lists, in order.
-/

set_option linter.unusedVariables false

namespace Vinc.Membership
open Vinc.MemInc

/-! ## Constants (`consts.rs`), in nanoseconds -/

def S : Nat := 1000000000
def MS : Nat := 1000000
def U64MAX : Nat := 2 ^ 64 - 1
def LEASE : Nat := 80 * S
def RENEW : Nat := 25 * S
def HUB_STALE : Nat := 75 * S
def PULSE_FRESH : Nat := 67 * S
def QUIET : Nat := 10 * S
def RECHECK_GAP : Nat := 5 * S
def WAKE_GAP : Nat := 2 * S
def SLEEP_WIN : Nat := 10 * S
def PROBE_WAIT_MIN : Nat := 250 * MS
def CONFIRM : Nat := S
def SLOW_TICK : Nat := 5 * S
def NODE_TICK : Nat := 500 * MS
def HUB_TICK : Nat := S
def ACK_WAIT : Nat := 6 * S
def HS_GRACE : Nat := 30 * S
def RTT_QUIET : Nat := 4000
def HEAL_SILENCE : Nat := 60 * S
def HYST_ABS : Nat := 20 * MS
def RTT_SAMPLE_MAX : Nat := 5 * S
def MAX_TABLE : Nat := 4096
def MAX_HUBS : Nat := 64
def QUEUE_CAP : Nat := 8192
def FLOOR_MAX : Nat := 4096
def SNAP_CHUNK : Nat := 64
def MAX_PROBES : Nat := 4
def MAX_FRAMES_PER_CALL : Nat := 512
def LEAVE_CODE : Nat := 0x4C
def RTT_UNKNOWN : Nat := 2 ^ 40
def U32MAX : Nat := 2 ^ 32 - 1

def satAdd (a b : Nat) : Nat := min (a + b) U64MAX

/-! ## Sorted tables -/

/-- A `BTreeMap`: a list sorted by key. -/
abbrev AMap (α : Type) := List (Nat × α)
/-- A `BTreeSet`. -/
abbrev ASet := List (Nat × Unit)

namespace AMap
variable {α : Type}

def get? (m : AMap α) (k : Nat) : Option α := (m.find? (fun p => p.1 == k)).map (·.2)
def has (m : AMap α) (k : Nat) : Bool := m.any (fun p => p.1 == k)
def keys (m : AMap α) : List Nat := m.map (·.1)
def len (m : AMap α) : Nat := m.length

def insert : AMap α → Nat → α → AMap α
  | [], k, v => [(k, v)]
  | (a, b) :: r, k, v => if k < a then (k, v) :: (a, b) :: r else if k == a then (k, v) :: r else (a, b) :: insert r k v

def erase (m : AMap α) (k : Nat) : AMap α := m.filter (fun p => p.1 != k)

/-- Update the value at `k`, if present. -/
def modify (m : AMap α) (k : Nat) (f : α → α) : AMap α := m.map (fun p => if p.1 == k then (p.1, f p.2) else p)

/-- `next_key`: the first key strictly after `after` (the first key when none). -/
def nextKey (m : AMap α) (after : Option Nat) : Option Nat :=
  (m.find? (fun p => match after with | none => true | some a => a < p.1)).map (·.1)
end AMap

/-- The time of an entry of `hello_at` or `hsent`: a cleared entry stays in the table as `None`. -/
def AMap.timeAt (m : AMap (Option Nat)) (k : Nat) : Option Nat := (m.get? k).getD none

/-- Clear the entry at `k` of `hello_at` or `hsent`, if present (`*v = None`): the entry stays. -/
def AMap.unset (m : AMap (Option Nat)) (k : Nat) : AMap (Option Nat) := m.modify k (fun _ => none)

namespace ASet
def has (s : ASet) (k : Nat) : Bool := AMap.has s k
def ins (s : ASet) (k : Nat) : ASet := AMap.insert s k ()
def del (s : ASet) (k : Nat) : ASet := AMap.erase s k
def keys (s : ASet) : List Nat := AMap.keys s
def len (s : ASet) : Nat := s.length
end ASet

/-! ## Records, frames, proofs -/

structure Rec where
  inc : Nat
  ver : Nat
  th : List Nat
  deriving DecidableEq, Repr

abbrev Alive := Vinc.MemCodec.Alive

/-- The evidence of a DOWN: how long the sender heard nothing, and its probes `(age_ms, path)`. -/
structure Proof where
  sil : Nat
  probes : List (Nat × Nat)
  deriving DecidableEq, Repr

def Proof.independent (p : Proof) : Bool := p.probes.any fun a => p.probes.any fun b => a.2 != b.2
def Proof.oldest (p : Proof) : Nat := p.probes.foldl (fun m a => max m a.1) 0

/-- A hub stream frame with node ids as `Nat`. -/
inductive NFrame where
  | hello (rc : Rec) (snap homed : Bool)
  | ack
  | delta (m : Nat) (rc : Rec) (a : Alive)
  | snap (part more : Bool) (es : List (Nat × Rec))
  | probe
  | down (m inc : Nat) (pf : Proof)
  | other (ty : Nat) (topic rest : List Nat)
  deriving DecidableEq, Repr

def NFrame.ty : NFrame → Nat
  | .hello .. => 1
  | .ack => 2
  | .delta .. => 3
  | .snap .. => 4
  | .probe => 12
  | .down .. => 13
  | .other t _ _ => t

/-! ## Events and traces (`event.rs`) -/

inductive Ev where
  | joined (m : Nat) | down (m : Nat) | left (m : Nat) | revoked (m : Nat) | addr (m : Nat)
  | stack (m v : Nat) | view (epoch n : Nat) | lost (n : Nat)
  deriving DecidableEq, Repr

/-- The refusal reasons of a DOWN, in enum order. -/
inductive Refusal where
  | notApplicable | unknown | leaseFresh | carrierOpen | notIndependent | badProof
  deriving DecidableEq, Repr

def Refusal.toNat : Refusal → Nat
  | .notApplicable => 0 | .unknown => 1 | .leaseFresh => 2 | .carrierOpen => 3 | .notIndependent => 4 | .badProof => 5

/-- Why a member left the view, in enum order. -/
inductive Removal where
  | reported | left | leaseExpired | revoked
  deriving DecidableEq, Repr

def Removal.toNat : Removal → Nat
  | .reported => 0 | .left => 1 | .leaseExpired => 2 | .revoked => 3

inductive Tr where
  | started (inc : Nat) | incarnation (inc : Nat) | frameIn (peer ty : Nat) | frameOut (peer ty : Nat)
  | badFrame (peer : Nat) | attached (m : Nat) | pulse (m : Nat) | leaseExpired (m : Nat) | carrierGone (m : Nat)
  | probeSent (m path : Nat) | noIndependentPath (m : Nat) | confirmed (m : Nat) | leaveSeen (m : Nat)
  | downSent (m : Nat) | downAccepted (m : Nat) | downRefused (m why : Nat) | carrierReturned (m : Nat) (restored : Bool)
  | selfDelta (hub : Nat) | snapApplied (hub entries : Nat) (more : Bool) | absent (m : Nat) | removed (m why : Nat)
  | deferred (m : Nat) | quiet (cause : Nat) | hubStale (hub : Nat) | primary (hub : Nat) | helloSuppressed (hub : Nat)
  | sealFailed | lost (n : Nat)
  deriving DecidableEq, Repr

/-! ## The host -/

structure Evid where
  rx : Nat
  srtt : Nat
  pto : Nat
  inf : Nat
  direct : Bool
  deriving DecidableEq, Repr

inductive Car where
  | unknown
  | open_
  | gone (since : Nat) (sleep : Option Nat)
  deriving DecidableEq, Repr

/-- The host as a call finds it: transport evidence, carriers, the peers a send reaches, the local node. -/
structure Env where
  ev : AMap Evid
  car : AMap Car
  acc : ASet
  ver : Nat
  tk : Nat
  refl : Bool
  loc : Local
  /-- The body the broadcast layer writes in a FLOOR frame for a member. -/
  floorBody : Nat → List Nat
  /-- `give_up(peer)` for the peers the host lists; any other peer has the default `HEAL_SILENCE`. -/
  gu : AMap Nat

/-- `Session::give_up`: how long silence on the path to `p` lasts before the transport gives the path up. -/
def Env.giveUp (e : Env) (p : Nat) : Nat := (e.gu.get? p).getD HEAL_SILENCE
def Env.evidence (e : Env) (p : Nat) : Option Evid := e.ev.get? p
def Env.carrier (e : Env) (m : Nat) : Car := (e.car.get? m).getD .unknown
/-- `address_hash(moves)` of the host. -/
def Env.hash (e : Env) (m : Nat) : List Nat := [e.tk, m, 0, 0, 0, 0, 0, 7]

inductive Route where
  | session | direct | via (x : Nat)
  deriving DecidableEq, Repr

inductive Bc where
  | frame (from_ ty : Nat) (topic rest : List Nat)
  | hold (m : Nat) | restore (m : Nat) | release (m : Nat) | resub (hub : Nat)
  | primary (old : Option Nat) (new : Nat)
  deriving DecidableEq, Repr

inductive CloseR where
  | noack | stale | leave | revoked
  deriving DecidableEq, Repr

/-- A `Session::send`: peer, route, frame, whether a session took it. -/
abbrev Sent := Nat × Route × NFrame × Bool

/-! ## The state -/

structure Lease where
  rc : Rec
  renewed : Nat
  deriving DecidableEq, Repr

structure CopyEntry where
  rc : Rec
  round : Nat
  absentSince : Option Nat
  deriving DecidableEq, Repr

structure HubCopy where
  entries : AMap CopyEntry
  round : Nat
  open_ : Bool

structure ViewEntry where
  rc : Rec
  deriving DecidableEq, Repr

structure Susp where
  since : Nat
  probeA : Nat
  probeB : Option (Nat × Nat)
  wait : Nat
  deriving DecidableEq, Repr

/-- One `Membership` node with the effects of the current call appended. -/
structure N where
  me : Nat
  isHub : Bool
  boot : List Nat
  born : Nat
  leaving : Bool
  inc : Inc
  tag : Tag
  ver : Nat
  th : List Nat
  sent : Option (Nat × List Nat)
  sealFailed : Bool
  maxFrame : Nat
  up : AMap Nat
  heard : AMap Nat
  revoked : ASet
  hv : AMap HubCopy
  members : AMap ViewEntry
  epoch : Nat
  hrtt : AMap Nat
  hsent : AMap (Option Nat)
  helloAt : AMap (Option Nat)
  primary : Option Nat
  homeOk : Option Nat
  homeSeen : Bool
  recheck : ASet
  quietUntil : Nat
  regrace : Bool
  goneVer : AMap (Nat × List Nat)
  left : ASet
  nextRenew : Nat
  nextTick : Option Nat
  nextSlow : Nat
  own : Rec
  roster : AMap Lease
  attached : ASet
  homed : ASet
  susp : AMap Susp
  downed : AMap (Lease × Nat)
  nextConf : Option Nat
  events : List Ev
  lostEvents : Nat
  tracing : Bool
  traces : List Tr
  lostTraces : Nat
  -- effects of the calls since they were last taken
  loc : Local
  outSent : List Sent
  outBc : List Bc
  outClose : List (Nat × CloseR)

/-! ## Outputs, tracing, sending -/

def N.emit (n : N) (e : Ev) : N :=
  if QUEUE_CAP ≤ n.events.length then { n with lostEvents := n.lostEvents + 1 } else { n with events := n.events ++ [e] }

def N.trace (n : N) (t : Tr) : N :=
  if !n.tracing then n
  else if QUEUE_CAP ≤ n.traces.length then { n with lostTraces := n.lostTraces + 1 } else { n with traces := n.traces ++ [t] }

/-- Everything `poll_event` returns until it is empty: the loss count first. -/
def N.drainEvents (n : N) : List Ev := (if 0 < n.lostEvents then [Ev.lost n.lostEvents] else []) ++ n.events
def N.drainTraces (n : N) : List Tr := (if 0 < n.lostTraces then [Tr.lost n.lostTraces] else []) ++ n.traces

/-- The queues emptied, as after a full drain. -/
def N.drained (n : N) : N := { n with events := [], lostEvents := 0, traces := [], lostTraces := 0 }

/-- Empty the effect lists (the start of a call as the recorder sees it). -/
def N.clearOut (n : N) : N := { n with outSent := [], outBc := [], outClose := [] }

def N.bc (n : N) (b : Bc) : N := { n with outBc := n.outBc ++ [b] }
def N.close (n : N) (p : Nat) (r : CloseR) : N := { n with outClose := n.outClose ++ [(p, r)] }

def N.isBoot (n : N) (x : Nat) : Bool := n.boot.contains x

/-- Whether hub `x` is alive: this node itself, or a session that received a frame within `HUB_STALE`. -/
def N.hubUp (n : N) (now x : Nat) : Bool :=
  x == n.me || (n.up.has x && (match n.heard.get? x with | some t => decide (now - t < HUB_STALE) | none => false))

/-- `tx_buf`: nothing to a revoked peer or to the node itself; otherwise the frame is traced and handed to the host.
(The frame always encodes: `MembershipCodecBuf.lean`.) Returns whether a session took it. -/
def N.tx (e : Env) (n : N) (peer : Nat) (route : Route) (f : NFrame) : N × Bool :=
  if n.revoked.has peer || peer == n.me then (n, false)
  else
    let n := n.trace (.frameOut peer f.ty)
    let ok := e.acc.has peer
    ({ n with outSent := n.outSent ++ [(peer, route, f, ok)] }, ok)

def N.deltaTo (e : Env) (n : N) (peer m : Nat) (rc : Rec) (a : Alive) : N :=
  (N.tx e n peer .session (.delta m rc a)).1

/-- `begin_quiet`. -/
def N.beginQuiet (n : N) (now cause : Nat) : N :=
  ({ n with quietUntil := satAdd now QUIET, regrace := false }).trace (.quiet cause)

/-- Visit the keys in increasing order (a cursor loop of the code). -/
def forKeys (ks : List Nat) (f : Nat → N → N) (n : N) : N := ks.foldl (fun n k => f k n) n

end Vinc.Membership
