import Vinc.Json
import Vinc.ConnectLink
import Vinc.ConnectRecord

/-!
# The client rules of connectivity

The small state machines and decision functions of `vinc-connect/src/client`, step for step, in nanoseconds as
`Nat` (the `u64` operations of the code are `saturating_*`, none of which overflows below `2^63`):

* `punch.rs`: `probe_gaps` and the punch timer `Puncher`;
* `tunnel.rs`: `hub_ok`, `decide`, `thin_splice` and the splice tables `Splices`;
* `dial.rs`: `direct_first`, `select` and the pending dials `Pending`;
* `lookup.rs`: the lookup table `Lookups` and `verify`;
* `netcheck.rs`: `classify` and the probe state `Netcheck`.

Node ids and addresses are small numbers here: the rules compare them for equality and nothing else (the one
exception is the shared address range of `classify`, which reads the octets). The tables are lists of fixed length,
as the arrays of the code.
-/

namespace Vinc.ConnectClient
open Vinc.ConnectLink (sec satSub)

/-! ## Punching -/

def probeBase : Nat := 33300000
def probeCap : Nat := 2 * sec
def upgradeInterval : Nat := 60 * sec
def goodLatency : Nat := 10000000
def firstDelay : Nat := 1000000
def activeKeep : Nat := 20 * sec

def gapsFrom : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, g => g :: gapsFrom n (min (g * 2) probeCap)

/-- `probe_gaps`: the gaps between the nine probes of a path whose smoothed round trip is `srtt`. -/
def probeGaps (srtt : Nat) : List Nat := gapsFrom 9 (max probeBase (srtt / 8))

structure View where
  appIdle : Nat
  direct : Bool
  rtt : Nat
  quietUntil : Nat
  deriving DecidableEq, Repr

inductive PStep where
  | punch
  | wait
  deriving DecidableEq, Repr

/-- The punch timer; `0` is off. -/
structure Puncher where
  at_ : Nat := 0
  deriving DecidableEq, Repr

def Puncher.established (_p : Puncher) (now : Nat) : Puncher := ⟨now + firstDelay⟩
def Puncher.arm (_p : Puncher) (at_ : Nat) : Puncher := ⟨at_⟩

/-- `Puncher::due`. -/
def Puncher.due (p : Puncher) (now : Nat) (v : View) : PStep × Puncher :=
  if p.at_ = 0 ∨ now < p.at_ then (.wait, p)
  else if now < v.quietUntil ∧ v.direct then (.wait, ⟨v.quietUntil + 1⟩)
  else if v.appIdle ≥ activeKeep then (.wait, ⟨now + upgradeInterval⟩)
  else (.punch, ⟨if v.direct ∧ v.rtt ≠ 0 ∧ v.rtt ≤ goodLatency then 0 else now + upgradeInterval⟩)

/-! ## The hub tunnel -/

def tunnelStale : Nat := 15 * sec
def hubTunnelFresh : Nat := 20 * sec
def splLive : Nat := 30 * sec
def thinSpliceFresh : Nat := 2 * sec
def thinSplicePto : Nat := 2
def spliceSpan : Nat := 4 * sec

def hubOk (validated : Bool) (heard now : Nat) : Bool := validated && decide (satSub now heard < hubTunnelFresh)

inductive Via where
  | carrier
  | tunnel
  | both
  deriving DecidableEq, Repr

structure Rides where
  pto : Nat
  handshaking : Bool
  hsTries : Nat
  thin : Bool
  deriving DecidableEq, Repr

/-- `tunnel::decide`. -/
def decide' (carrierOpen : Bool) (silentFor : Nat) (session : Option Rides) (tunnel : Bool) : Via :=
  if ¬ tunnel then .carrier
  else if ¬ carrierOpen then .tunnel
  else if silentFor > tunnelStale then .both
  else match session with
    | some s =>
      let loss := s.pto ≥ (if s.thin then 2 else 1)
      let hs := s.handshaking ∧ (s.hsTries ≥ 2 ∨ ¬ s.thin)
      if loss ∨ hs then .both else .carrier
    | none => .carrier

structure Thin where
  thin : Bool
  established : Bool
  spliceAge : Option Nat
  rtt : Nat
  carrierFresh : Bool
  tunnelTook : Bool
  pto : Nat
  deriving DecidableEq, Repr

/-- `thin_splice` (THIN_SPLICE). -/
def thinSplice (t : Thin) : Bool :=
  if ¬ (t.thin ∧ t.established ∧ t.tunnelTook ∧ ¬ t.carrierFresh ∧ t.pto < thinSplicePto) then false
  else
    let span := if t.rtt * 2 > spliceSpan then t.rtt * 2 else spliceSpan
    match t.spliceAge with
    | some a => decide (a < span)
    | none => false

/-- The splice tables for `P` peers and `R` relays: the peers that reach us by splice (peer, relay, time), the next
slot to overwrite, and the hubs that spliced lately (time, address). -/
structure Splices where
  peers : List (Option (Nat × Nat × Nat))
  next : Nat
  live : List (Option (Nat × Nat))
  deriving DecidableEq, Repr

def Splices.new (p r : Nat) : Splices := ⟨List.replicate p none, 0, List.replicate r none⟩

/-- `Splices::seen`. -/
def Splices.seen (t : Splices) (now relay peer frm : Nat) : Splices :=
  let live := if relay < t.live.length then t.live.set relay (some (now, frm)) else t.live
  let slot := match t.peers.findIdx? (fun s => match s with | some (p, _, _) => p == peer | none => false) with
    | some i => i
    | none => t.next
  let peers := if slot < t.peers.length then t.peers.set slot (some (peer, relay, now)) else t.peers
  let next := if slot == t.next then (t.next + 1) % (max t.peers.length 1) else t.next
  ⟨peers, next, live⟩

/-- `Splices::age`. -/
def Splices.age (t : Splices) (now relay peer : Nat) : Option Nat :=
  match t.peers.find? (fun s => match s with | some (p, r, _) => p == peer && r == relay | none => false) with
  | some (some (_, _, at_)) => some (satSub now at_)
  | _ => none

/-- `Splices::live` (SPLICE_LIVE). -/
def Splices.liveAt (t : Splices) (now relay rtt : Nat) : Option Nat :=
  match t.live.getD relay none with
  | some (at_, a) =>
    let span := if rtt * 2 > splLive then rtt * 2 else splLive
    if satSub now at_ < span then some a else none
  | none => none

/-! ## Dialing -/

def lateStart : Nat := 10 * sec
def tgSlow : Nat := 250000000
def rlyOnce : Nat := 30 * sec
def rlyOnceMin : Nat := 4 * sec

/-- `direct_first` (HUB_DIRECT_FIRST). -/
def directFirst (firstTry isHub : Bool) (firstDialAt started : Nat) : Bool :=
  firstTry && isHub && decide (satSub firstDialAt started > lateStart)

inductive Cand where
  | udp (a : Nat)
  | relay (r : Nat)
  deriving DecidableEq, Repr

structure RelayView where
  live : Bool
  gen : Nat
  deriving DecidableEq, Repr

structure Try where
  now : Nat
  dialer : Bool
  tries : Nat
  linkRtt : Nat
  noRtt : Bool
  hs0 : Bool
  lastRelay : Option (Nat × Nat × Nat)
  deriving DecidableEq, Repr

/-- Whether a try keeps a candidate (the first 16 are looked at). -/
def keepCand (t : Try) (relay : Nat → Option RelayView) : Cand → Bool
  | .udp _ => !(t.hs0 && t.dialer)
  | .relay r =>
    !(t.dialer && decide (t.linkRtt ≥ tgSlow) &&
      (match relay r with
       | some v => v.live &&
         (match t.lastRelay with
          | some (lr, g, at_) =>
            lr == r && g == v.gen && decide (satSub t.now at_ < min rlyOnce (max rlyOnceMin (t.linkRtt * 3)))
          | none => false)
       | none => false))

/-- `select`: the candidates this try is sent on (at most `cap`), and the relay and generation that now carry the
flight. -/
def select (cands : List Cand) (t : Try) (relay : Nat → Option RelayView) (cap : Nat) :
    List Cand × Option (Nat × Nat) :=
  let kept := (cands.take 16).filter (keepCand t relay)
  let n := kept.length
  let slow := t.linkRtt ≥ tgSlow
  let thin := t.dialer ∧ n > 1 ∧ (slow ∨ (t.tries ≥ 2 ∧ t.noRtt))
  let picked := if thin then (kept.drop (t.tries % n)).take 1 else kept
  let out := picked.take cap
  let carried := out.foldl (fun acc c => match c with
    | .relay r => some (r, (relay r).elim 0 (·.gen))
    | .udp _ => acc) none
  (out, carried)

/-- The pending dials: up to `N` peers (a peer and the sessions that wait for its address, `H` each). -/
structure Pending where
  items : List (Option (Nat × List (Option Nat)))
  h : Nat
  deriving DecidableEq, Repr

def Pending.new (n h : Nat) : Pending := ⟨List.replicate n none, h⟩

def Pending.contains (p : Pending) (peer : Nat) : Bool :=
  p.items.any fun e => match e with | some (q, _) => q == peer | none => false

def Pending.peers (p : Pending) : List Nat := p.items.filterMap fun e => e.map (·.1)

/-- `Pending::add`. -/
def Pending.add (p : Pending) (peer session : Nat) : Bool × Pending :=
  let at_ := p.items.findIdx? fun e => match e with | some (q, _) => q == peer | none => false
  let slot := match at_ with
    | some i => some i
    | none => p.items.findIdx? fun e => Option.isNone e
  match slot with
  | none => (false, p)
  | some i =>
    let (q, ws) := (p.items.getD i none).getD (peer, List.replicate p.h none)
    if ws.contains (some session) then (true, { p with items := p.items.set i (some (q, ws)) })
    else match ws.findIdx? (fun w => Option.isNone w) with
      | some j => (true, { p with items := p.items.set i (some (q, ws.set j (some session))) })
      | none => (false, { p with items := p.items.set i (some (q, ws)) })

/-- `Pending::take`: the sessions that waited for `peer`. -/
def Pending.take (p : Pending) (peer : Nat) : List (Option Nat) × Pending :=
  match p.items.findIdx? (fun e => match e with | some (q, _) => q == peer | none => false) with
  | some i => ((p.items.getD i none).elim (List.replicate p.h none) (·.2), { p with items := p.items.set i none })
  | none => (List.replicate p.h none, p)

/-- `Pending::prune` (DIAL_PRUNE): keep the sessions in handshake; the peers left with none are dropped. -/
def Pending.prune (p : Pending) (inHs : Nat → Bool) : List Nat × Pending :=
  let step := fun (acc : List Nat × List (Option (Nat × List (Option Nat)))) (e : Option (Nat × List (Option Nat))) =>
    match e with
    | none => (acc.1, acc.2 ++ [none])
    | some (q, ws) =>
      let ws' := ws.map fun w => match w with | some t => if inHs t then some t else none | none => none
      if ws'.all (fun w => Option.isNone w) then (acc.1 ++ [q], acc.2 ++ [none]) else (acc.1, acc.2 ++ [some (q, ws')])
  let r := p.items.foldl step ([], [])
  (r.1, { p with items := r.2 })

/-! ## Lookups -/

def lookupRetry : Nat := 300000000
def carrierWait : Nat := 2 * sec
def thinWaitMax : Nat := 8 * sec

structure Item where
  peer : Nat
  at_ : Nat
  tried : Bool
  carrierOnly : Bool
  again : Bool
  wait : Nat
  deriving DecidableEq, Repr

inductive Ask where
  | skip
  | udp (others : Bool)
  | carrier
  | later
  deriving DecidableEq, Repr

structure Lookups where
  items : List (Option Item)
  deriving DecidableEq, Repr

def Lookups.new (n : Nat) : Lookups := ⟨List.replicate n none⟩

def Lookups.len (t : Lookups) : Nat := (t.items.filter Option.isSome).length
def Lookups.contains (t : Lookups) (peer : Nat) : Bool :=
  t.items.any fun e => match e with | some i => i.peer == peer | none => false

/-- `Lookups::ask`; `thin` is the node's round trip when the node is thin and `0` otherwise. -/
def Lookups.ask (t : Lookups) (now peer : Nat) (udpAny carrierOpen : Bool) (thin : Nat) : Ask × Lookups :=
  let slot := match t.items.findIdx? (fun e => match e with | some i => i.peer == peer | none => false) with
    | some i => some i
    | none => t.items.findIdx? fun e => Option.isNone e
  match slot with
  | none => (.skip, t)
  | some at_ =>
    let cur := t.items.getD at_ none
    let item := cur.getD ⟨peer, 0, false, false, false, lookupRetry⟩
    if cur.isSome ∧ ¬ item.again ∧ now < item.at_ + item.wait then (.skip, t)
    else
      let retry := item.tried
      let item := { item with again := false, tried := true, at_ := now,
                              wait := max lookupRetry (min thinWaitMax (2 * thin)) }
      let byCarrier := ¬ udpAny ∨ item.carrierOnly
      let (out, item) :=
        if byCarrier then
          let item := { item with at_ := now + (carrierWait - lookupRetry) }
          if carrierOpen then (Ask.carrier, item)
          else if retry then (Ask.later, item)
          else (Ask.udp false, { item with at_ := now })
        else (Ask.udp retry, item)
      (out, ⟨t.items.set at_ (some item)⟩)

def Lookups.answered (t : Lookups) (peer : Nat) : Lookups :=
  ⟨t.items.map fun e => match e with | some i => if i.peer == peer then none else e | none => none⟩

def Lookups.tooLarge (t : Lookups) (peer : Nat) : Lookups :=
  ⟨t.items.map fun e => match e with
    | some i => if i.peer == peer then some { i with carrierOnly := true, again := true } else e
    | none => none⟩

def Lookups.clear (t : Lookups) : Lookups := ⟨t.items.map fun _ => none⟩

def Lookups.due (t : Lookups) (now : Nat) : List Nat :=
  t.items.filterMap fun e => match e with
    | some i => if now > i.at_ + i.wait then some i.peer else none
    | none => none

def Lookups.nextDeadline (t : Lookups) : Option Nat :=
  (t.items.filterMap fun e => e.map fun i => i.at_ + i.wait + 1).min?

/-! ## Netcheck -/

def homeTries : Nat := 3
def missLimit : Nat := 3

inductive HomeStep where
  | done
  | again
  | fallback (r : Nat)
  deriving DecidableEq, Repr

/-- The probe state for `R` relays. -/
structure Netcheck where
  probes : List (Option (List Nat × Nat))
  rtt : List Nat
  refl : List (Option Nat)
  home : Option Nat
  missed : List Nat
  tries : Nat
  firstProbe : Option Nat
  deriving DecidableEq, Repr

def Netcheck.new (r : Nat) : Netcheck :=
  ⟨List.replicate r none, List.replicate r 0, List.replicate r none, none, List.replicate r 0, 0, none⟩

def Netcheck.unhealthy (n : Netcheck) (i : Nat) : Bool := decide (n.missed.getD i 0 ≥ missLimit)

def Netcheck.failed (n : Netcheck) (i : Nat) : Netcheck :=
  if i < n.missed.length then { n with missed := n.missed.set i (min 255 (n.missed.getD i 0 + 1)) } else n

def Netcheck.healthy (n : Netcheck) (i : Nat) : Netcheck :=
  if i < n.missed.length then { n with missed := n.missed.set i 0 } else n

/-- `Netcheck::probe_sent`. -/
def Netcheck.probeSent (n : Netcheck) (now relay : Nat) (nonce : List Nat) (udpWorks : Bool) : Netcheck :=
  let n := if udpWorks ∧ (n.probes.getD relay none).isSome then n.failed relay else n
  if relay < n.probes.length then
    { n with probes := n.probes.set relay (some (nonce, now)), firstProbe := some (n.firstProbe.getD now) }
  else n

/-- The first index of the lowest value among `idx` (`min_by_key`). -/
def argMin (idx : List Nat) (key : Nat → Nat) : Option Nat :=
  idx.foldl (fun acc i => match acc with
    | none => some i
    | some b => if key i < key b then some i else some b) none

/-- `Netcheck::answered`: the round trip when the nonce matched an outstanding probe. -/
def Netcheck.answered (n : Netcheck) (now relay : Nat) (nonce : List Nat) (addr : Nat) : Option Nat × Netcheck :=
  match n.probes.getD relay none with
  | some (nc, sent) =>
    if nc ≠ nonce then (none, n)
    else
      let rtt := satSub now sent
      let n1 := { n with probes := n.probes.set relay none, missed := n.missed.set relay 0,
                         rtt := n.rtt.set relay rtt, refl := n.refl.set relay (some addr) }
      let cands := (List.range n.probes.length).filter fun i => (n1.refl.getD i none).isSome && !n1.unhealthy i
      let best := argMin cands fun i => n1.rtt.getD i 0
      let n2 := match best with
        | some b =>
          if (n1.home != some b) && (match n1.home with
              | none => true
              | some h => n1.unhealthy h || decide (n1.rtt.getD b 0 < n1.rtt.getD h 0)) then { n1 with home := some b }
          else n1
        | none => n1
      (some rtt, n2)
  | none => (none, n)

/-- `Netcheck::failover`: move the home away from an unhealthy relay, only to one known to work: a probe answered since
it last failed (lowest round trip first), else an `open` carrier (next by table position). `usable` says which relays
are configured. With no such relay the home stays. -/
def Netcheck.failover (n : Netcheck) (usable isOpen : Nat → Bool) : Option Nat × Netcheck :=
  match n.home with
  | none => (none, n)
  | some home =>
    if ¬ n.unhealthy home then (none, n)
    else
      let rn := n.probes.length
      let measured := argMin ((List.range rn).filter fun i =>
        i != home && usable i && n.missed.getD i 0 == 0 && (n.refl.getD i none).isSome) fun i => n.rtt.getD i 0
      let next := match measured with
        | some m => some m
        | none => ((List.range' 1 (rn - 1)).map fun k => (home + k) % rn).find? fun i => usable i && isOpen i && !n.unhealthy i
      match next with
      | some x => (some x, { n with home := some x })
      | none => (none, n)

/-- `Netcheck::rtt`. -/
def Netcheck.rttOf (n : Netcheck) (i : Nat) : Option Nat :=
  if (n.refl.getD i none).isSome then n.rtt[i]? else none

def Netcheck.bestRtt (n : Netcheck) : Nat :=
  (((List.range n.probes.length).filter fun i => (n.refl.getD i none).isSome).map fun i => n.rtt.getD i 0).min?.getD 0

def Netcheck.restart (n : Netcheck) : Netcheck :=
  { n with probes := n.probes.map fun _ => none, refl := n.refl.map fun _ => none, firstProbe := none, tries := 0 }

/-- `Netcheck::home_missing`. -/
def Netcheck.homeMissing (n : Netcheck) (first : Option Nat) : HomeStep × Netcheck :=
  if n.home.isSome then (.done, n)
  else
    let n := { n with tries := min 255 (n.tries + 1) }
    match first with
    | some f => if n.tries ≥ homeTries then (.fallback f, { n with home := some f }) else (.again, n)
    | none => (.again, n)

/-- An address: the octets of the ip and the port. -/
abbrev Addr := List Nat × Nat

/-- `is_shared`: an IPv4 address in 100.64.0.0/10. -/
def isShared (ip : List Nat) : Bool :=
  match ip with
  | [a, b, _, _] => a == 100 && decide (64 ≤ b ∧ b < 128)
  | _ => false

structure Observed where
  local_ : List Addr
  reflexive : List Addr
  mapped : List Addr
  udpHeard : Bool
  sinceProbe : Nat
  watchdog : Nat

/-- `classify`: the reachability class (1 public, 2 port mapped, 3 behind NAT, 4 carrier-grade NAT, 5 UDP blocked). -/
def classify (o : Observed) : Option Nat :=
  match o.reflexive with
  | [] => if ¬ o.udpHeard ∧ o.sinceProbe ≥ o.watchdog then some 5 else none
  | first :: _ =>
    if o.reflexive.any (fun r => o.local_.contains r) then some 1
    else if o.reflexive.any (fun r => o.mapped.contains r) then some 2
    else if o.reflexive.any (fun r => isShared r.1) ∨ o.reflexive.any (fun r => r != first) then some 4
    else some 3

/-- What a lookup answer is (`DnsAnswer`). -/
inductive Answer where
  | absent
  | record (bytes : List Nat)
  | tooLarge

/-- The tag of a verified lookup answer: `none` for no record, the record's fields, or the refusal. -/
inductive Verified where
  | none
  | found (home : List Nat) (reach : Nat) (seq : Nat) (addrs : List (List Nat))
  | refused (tag : String)
  deriving DecidableEq, Repr

/-- `lookup::verify`: `sigOk` is whether the record's signature verifies for its key and the key belongs to its node
id (the identity module's check, an oracle here). -/
def verify (peer : List Nat) (a : Answer) (sigOk : Bool) (tagOf : Vinc.ConnCodec.CErr → String) : Verified :=
  match a with
  | .absent => .none
  | .tooLarge => .refused "toolarge"
  | .record bytes =>
    match Vinc.ConnCodec.Rec.parse bytes with
    | .error e => .refused (tagOf e)
    | .ok r =>
      if ¬ sigOk then .refused "rec:sig"
      else if r.node ≠ peer then .refused "wrongnode"
      else .found r.home r.reach r.seq r.addrs

end Vinc.ConnectClient
