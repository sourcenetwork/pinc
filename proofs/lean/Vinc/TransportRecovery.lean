/-!
# Loss recovery: the model

A model of `vinc-transport` `recovery/engine.rs`, `ack.rs`, `loss.rs`, `pto.rs`, `sent.rs`, `rtt.rs` and `tail.rs`,
operation for operation as `proofs/tla/RecoveryOps.tla` has them, over unbounded `Nat` times and sizes. A time or a
product that the code computes in `u64` saturates at `P.top` (`u64::MAX` for the theorems; the replay of the recorded
runs uses the same value and compares what the 32-bit checker saw through the same clamp). `Vinc.TraceRecovery`
replays the recorded calls of the real code through these functions; the theorems about them are in
`Vinc.TransportRecoveryThm`.

A path slot has a generation, and a packet records the generation of its slot when it is sent: the round trip of the
newest acknowledged packet is kept for its path only when that occupant is still in the slot (`nwPath`; a path leaving
the slot is `forgetPath`), by occupant and not by clock. The reorder state of a slot is kept when another path takes it.

A slot of the sent ring is in flight, declared lost (a ghost) or done. The congestion controller and the
pacer are not part of the state; recovery only tells them what happened (see `RecoveryOps.tla`).
-/

namespace Vinc.TransportRecovery

/-- The constants: ring slots, a millisecond and a second in the unit of time, paths, the saturation value, the
ghost cap and the late-send table. -/
structure P where
  n : Nat
  ms : Nat
  sec : Nat
  mp : Nat
  top : Nat
  maxg : Nat
  laten : Nat

def P.irtt (p : P) : Nat := 333 * p.ms
def P.ad (p : P) : Nat := 25 * p.ms
def P.long (p : P) : Nat := 250 * p.ms
def P.oldx (p : P) : Nat := 50 * p.ms
def P.relayMin (p : P) : Nat := 3 * p.sec / 2
def P.gret (p : P) : Nat := 2 * p.sec
def P.gscan (p : P) : Nat := 25 * p.ms
def P.lateSample (p : P) : Nat := 4 * p.sec
def P.ptoCap (p : P) : Nat := 2 * p.sec
def P.slowSrtt (p : P) : Nat := 4 * p.long
def P.giveUp (p : P) : Nat := 20 * p.sec

def sat (p : P) (x : Nat) : Nat := min x p.top
def sadd (p : P) (a b : Nat) : Nat := sat p (a + b)
def smul (p : P) (a b : Nat) : Nat := sat p (a * b)

/-- Replace the element at `i` by `f` of it. -/
def upd {α : Type} : List α → Nat → (α → α) → List α
  | [], _, _ => []
  | x :: xs, 0, f => f x :: xs
  | x :: xs, i + 1, f => x :: upd xs i f

/-- The state of a slot of the sent ring: in flight, declared lost (a ghost) or done. -/
inductive St where
  | fl
  | lost
  | done
  deriving DecidableEq, Repr, Inhabited

structure Slot where
  pn : Nat
  time : Nat
  size : Nat
  path : Nat
  rep : Bool
  probe : Bool
  fr : List Bool
  st : St
  lostAt : Nat
  /-- The generation of the path's slot when the packet was sent: the occupant that sent it. -/
  occ : Nat
  deriving DecidableEq, Repr, Inhabited

structure Rtt where
  lat : Option Nat
  sm : Nat
  var : Nat
  mn : Option Nat
  has : Bool
  deriving DecidableEq, Repr, Inhabited

structure R where
  ring : List Slot
  ls : Option Nat
  la : Option Nat
  sent : Nat
  acked : Nat
  lost : Nat
  inf : Nat
  infp : Nat
  lt : Option Nat
  pc : Nat
  lp : Nat
  asleep : Bool
  down : Bool
  hrd : Nat
  clock : Nat
  tgr : Nat
  lrtt : Nat
  rtt : Rtt
  rel : List Bool
  prtt : List Nat
  act : Nat
  flip : Option Nat
  /-- The generation of each path slot: a path that takes the slot after another left it is the next one. -/
  gen : List Nat
  late : List (Nat × Nat)
  saved : Option Nat
  reo : List (Nat × Option Nat)
  gs : Nat
  lat : Nat
  deriving DecidableEq, Repr, Inhabited

def R.init (p : P) : R :=
  { ring := [], ls := none, la := none, sent := 0, acked := 0, lost := 0, inf := 0, infp := 0, lt := none, pc := 0,
    lp := 0, asleep := false, down := false, hrd := 0, clock := 0, tgr := 0, lrtt := 0,
    rtt := { lat := none, sm := p.irtt, var := p.irtt / 2, mn := none, has := false },
    rel := List.replicate p.mp false, prtt := List.replicate p.mp 0, act := 0, flip := none,
    gen := List.replicate p.mp 0, late := [], saved := none,
    reo := List.replicate p.mp (0, none), gs := 0, lat := 0 }

/-- An event the engine reports: `kind` is `acked`, `late` or `lost`; `f1` and `f2` are probe and repair for an
acknowledgement, requeue and probe for a loss. -/
structure Ev where
  k : String
  pn : Nat
  size : Nat
  fr : List Bool
  f1 : Bool
  f2 : Bool
  deriving DecidableEq, Repr, Inhabited

structure Sm where
  ap : Nat := 0
  ab : Nat := 0
  lap : Nat := 0
  lp : Nat := 0
  lb : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The result of a call: the state, the events, the summary, the error and whether a ping is asked for. -/
structure Res where
  r : R
  ev : List Ev
  s : Sm
  err : String
  ping : Bool

def omax : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => some (max a b)

def omin (a : Nat) : Option Nat → Nat
  | none => a
  | some b => min a b

/-! ### The round-trip estimate -/

def rttUpdate (p : P) (e : Rtt) (x : Nat) : Rtt :=
  let e1 := { e with lat := some x, mn := some (match e.mn with | none => x | some m => min m x) }
  if !e.has then { e1 with has := true, sm := x, var := x / 2 }
  else
    let diff := (e.sm - x) + (x - e.sm)
    { e1 with var := sat p ((3 * e.var + diff) / 4), sm := sat p ((7 * e.sm + x) / 8) }

def rttSeed (p : P) (e : Rtt) (x : Nat) : Rtt :=
  if e.has then e else { e with has := true, sm := max x p.ms, var := max x p.ms / 2 }

def isLongRtt (p : P) (mn : Option Nat) : Bool := match mn with | none => false | some m => decide (m ≥ p.long)

/-! ### The sent ring -/

def trim (p : P) (now : Nat) : List Slot → List Slot
  | [] => []
  | h :: t =>
    if h.st == .done || (h.st == .lost && decide (sadd p h.lostAt p.gret < now)) then trim p now t else h :: t

def hasRoom (p : P) (ring : List Slot) : Bool :=
  decide (ring.length < p.n) || (match ring with | [] => false | h :: _ => h.st != .fl)

/-- The ring after the push, or `none` when the ring is full of packets in flight. -/
def push (p : P) (ring : List Slot) (sl : Slot) : Option (List Slot) :=
  if ring.length = p.n then
    match ring with
    | [] => some [sl]
    | h :: t => if h.st == .fl then none else some (t ++ [sl])
  else some (ring ++ [sl])

def lowerBound (ring : List Slot) (pn : Nat) : Nat := (ring.filter (fun s => decide (s.pn < pn))).length
def ghosts (ring : List Slot) : Nat := (ring.filter (fun s => s.st == .lost)).length
def hasGhost (ring : List Slot) : Bool := ring.any (fun s => s.st == .lost)

def lim : Nat → List Slot → List Slot
  | _, [] => []
  | 0, l => l
  | ex + 1, s :: t => if s.st == .lost then { s with st := .done } :: lim ex t else s :: lim (ex + 1) t

def limitGhosts (p : P) (ring : List Slot) : List Slot := lim (ghosts ring - p.maxg) ring

def firstIFFrom : List Slot → Nat → Option Nat
  | [], _ => none
  | s :: t, i => if s.st == .fl then some i else firstIFFrom t (i + 1)

/-- The index of the oldest packet in flight. -/
def firstIF (ring : List Slot) : Option Nat := firstIFFrom ring 0

def newestIFTime (ring : List Slot) : Option Nat :=
  (ring.filter (fun s => s.st == .fl)).getLast?.map (·.time)

def isRelay (r : R) (path : Nat) : Bool := path < r.rel.length && r.rel.getD path false

/-! ### The reorder lens -/

def reoHold (p : P) (r : R) : Nat := max (smul p p.sec 2) (smul p r.rtt.sm 16)

def reoExtent (p : P) (r : R) (path now : Nat) : Option Nat :=
  match r.reo.getD path (0, none) with
  | (ext, some seen) => if now - seen < reoHold p r then some ext else none
  | (_, none) => none

def noteOvertaken (p : P) (r : R) (now pn time path : Nat) : R :=
  match r.la with
  | none => r
  | some prev =>
    if sadd p pn 3 > prev || path != r.act || isRelay r path then r
    else
      let spread := r.lat - time
      let kept := (reoExtent p r path now).getD 0
      { r with reo := r.reo.set path (max kept spread, some now) }

/-! ### Late sends -/

def lateInsert (p : P) (ls : List (Nat × Nat)) (pn time : Nat) : List (Nat × Nat) :=
  let base :=
    if ls.length = p.laten then
      match ls.map (·.1) |>.min? with
      | some m =>
        match ls.findIdx? (fun e => e.1 == m) with
        | some i => ls.take i ++ ls.drop (i + 1)
        | none => ls
      | none => ls
    else ls
  base ++ [(pn, time)]

def lateTime (ls : List (Nat × Nat)) (pn : Nat) : Option Nat := (ls.find? (fun e => e.1 == pn)).map (·.2)
def lateTake (ls : List (Nat × Nat)) (pn : Nat) : List (Nat × Nat) :=
  match ls.findIdx? (fun e => e.1 == pn) with
  | some i => ls.take i ++ ls.drop (i + 1)
  | none => ls

/-! ### Losing a packet -/

structure Y where
  r : R
  ev : List Ev
  s : Sm
  nl : Option Nat

def loseAt (p : P) (y : Y) (i now : Nat) : Y :=
  match y.r.ring[i]? with
  | none => y
  | some sl =>
    let counts := !sl.rep && !sl.probe
    let ghost := counts && sl.fr.any id
    let r1 := { y.r with
      ring := upd y.r.ring i (fun s => { s with st := if ghost then .lost else .done, lostAt := if ghost then now else s.lostAt }),
      inf := y.r.inf - sl.size, lost := y.r.lost + sl.size, infp := y.r.infp - 1,
      late := if counts then lateInsert p y.r.late sl.pn sl.time else y.r.late }
    { r := r1, ev := y.ev ++ [⟨"lost", sl.pn, sl.size, sl.fr, counts, sl.probe⟩],
      s := { y.s with lp := y.s.lp + 1, lb := y.s.lb + sl.size },
      nl := if counts then omax y.nl (some sl.time) else y.nl }

def settle (p : P) (y : Y) : Y :=
  if y.s.lp > 0 then { y with r := { y.r with ring := limitGhosts p y.r.ring } } else y

/-! ### Loss detection -/

def lossRtt (p : P) (r : R) : Nat := if r.rtt.has then max (r.rtt.lat.getD 0) r.rtt.sm else p.irtt
def lossDelay (p : P) (r : R) : Nat := max (sat p (lossRtt p r * 9 / 8)) p.ms

/-- The verdict on one packet in flight: lost by the count rule, and the age threshold. -/
def verdict (p : P) (r : R) (sl : Slot) (largest now : Nat) : Bool × Nat :=
  let rtt := lossRtt p r
  let delay := lossDelay p r
  let pa := sl.path
  if pa != r.act then
    let widest := max rtt (r.prtt.getD pa 0)
    let d2 := sadd p (smul p widest 4) p.oldx
    (false, if isRelay r pa then max d2 p.relayMin else d2)
  else if isRelay r pa && (match r.flip with | some f => decide (sl.time ≤ f) | none => false) then
    (false, max (sadd p (smul p rtt 4) p.oldx) p.relayMin)
  else if isRelay r pa then
    (false, sadd p (max (smul p rtt 2) delay) p.oldx)
  else match reoExtent p r pa now with
    | some e => (false, min (max delay (sadd p rtt (smul p e 2))) (smul p rtt 4))
    | none => (decide (largest ≥ sadd p sl.pn 3), delay)

def detectLoop (p : P) (now largest : Nat) : Nat → Nat → Y → Y
  | 0, _, y => y
  | k + 1, i, y =>
    match y.r.ring[i]? with
    | none => y
    | some sl =>
      if sl.pn > largest then y
      else if sl.st != .fl then detectLoop p now largest k (i + 1) y
      else
        let v := verdict p y.r sl largest now
        let due := sadd p sl.time v.2
        if !(v.1 || decide (now ≥ due)) then
          detectLoop p now largest k (i + 1) { y with r := { y.r with lt := some (omin due y.r.lt) } }
        else detectLoop p now largest k (i + 1) (loseAt p y i now)

def detect (p : P) (y : Y) (now largest : Nat) : Y :=
  settle p (detectLoop p now largest y.r.ring.length 0 { y with r := { y.r with lt := none } })

/-! ### The probe timer -/

def node (r : R) : Nat := max r.tgr r.lrtt
def ptoSeed (p : P) (r : R) : Nat := max p.irtt (smul p (node r) 2)
def ptoSrtt (p : P) (r : R) : Nat := if r.rtt.has then r.rtt.sm else ptoSeed p r
def ptoSlow (p : P) (r : R) : Bool := isLongRtt p r.rtt.mn || decide (ptoSrtt p r ≥ p.slowSrtt)
def ptoWide (p : P) (r : R) : Nat := max p.ptoCap (smul p (ptoSrtt p r) 2)
def ptoDur (p : P) (r : R) : Nat :=
  let srtt := ptoSrtt p r
  let var := if r.rtt.has then r.rtt.var else ptoSeed p r / 2
  let base := sadd p (sadd p srtt (max (smul p var 4) p.ms)) p.ad
  let shifted := min (smul p base (2 ^ min r.pc 6)) (smul p (ptoWide p r) 4)
  min shifted (if ptoSlow p r then ptoWide p r else p.ptoCap)

def ptoDeadline (p : P) (r : R) : Option Nat :=
  (newestIFTime r.ring).map (fun nw => sadd p (max nw r.lp) (ptoDur p r))

def nextTimeout (p : P) (r : R) : Option Nat :=
  match r.lt, ptoDeadline p r with
  | some a, some b => some (min a b)
  | a, b => a.or b

def isThin (p : P) (r : R) : Bool :=
  if !r.rtt.has then true else decide (max (max (node r) (r.rtt.mn.getD 0)) (r.rtt.sm / 2) ≥ p.long)

def health (p : P) (r : R) (now : Nat) : String :=
  let slow := isLongRtt p r.rtt.mn || isThin p r
  let srtt := if r.rtt.has then r.rtt.sm else 0
  let need := max (if slow then p.giveUp else 0) (smul p srtt 8)
  if r.pc ≥ 10 && decide (now - r.hrd ≥ need) then "Dead" else if r.pc ≥ 3 then "Degraded" else "Healthy"

def declareOldest (p : P) (y : Y) (now : Nat) : Y :=
  match firstIF y.r.ring with
  | none => y
  | some i =>
    match y.r.ring[i]? with
    | none => y
    | some sl =>
      let y1 := if y.r.pc == 1 then { y with r := { y.r with saved := some sl.pn } } else y
      settle p (loseAt p y1 i now)

def res (r : R) (ev : List Ev) (s : Sm) (err : String) (ping : Bool) : Res := ⟨r, ev, s, err, ping⟩

/-- The loss timer of a timeout call: loss detection if its time came. -/
def timeoutLoss (p : P) (r0 : R) (now : Nat) : Y :=
  let y0 : Y := ⟨r0, [], {}, none⟩
  match r0.lt, r0.la with
  | some t, some la => if now ≥ t then detect p y0 now la else y0
  | _, _ => y0

def timeout (p : P) (r : R) (now : Nat) : Res :=
  let r0 := { r with clock := max r.clock now }
  let y1 := timeoutLoss p r0 now
  let r1 := y1.r
  match ptoDeadline p r1 with
  | none => res r1 y1.ev y1.s "ok" false
  | some d =>
    if now < d then res r1 y1.ev y1.s "ok" false
    else if r1.asleep then res { r1 with lp := now } y1.ev y1.s "ok" false
    else
      let r2 := { r1 with pc := if r1.down then r1.pc else r1.pc + 1, lp := now }
      if health p r2 now == "Dead" then res r2 y1.ev y1.s "ok" false
      else
        let y3 := declareOldest p { y1 with r := r2 } now
        res y3.r y3.ev y3.s "ok" true

/-! ### Flushing the flight -/

def flushLoop (now : Nat) : Nat → Nat → Y → Y
  | 0, _, y => y
  | k + 1, i, y =>
    match y.r.ring[i]? with
    | none => y
    | some sl =>
      if sl.st != .fl then flushLoop now k (i + 1) y
      else
        let r1 := { y.r with ring := upd y.r.ring i (fun s => { s with st := .lost, lostAt := now }),
                             inf := y.r.inf - sl.size, lost := y.r.lost + sl.size, infp := y.r.infp - 1 }
        flushLoop now k (i + 1)
          ⟨r1, y.ev ++ [⟨"lost", sl.pn, sl.size, sl.fr, !sl.rep && !sl.probe, sl.probe⟩],
           { y.s with lp := y.s.lp + 1, lb := y.s.lb + sl.size }, none⟩

def flush (r : R) (now : Nat) : Res :=
  let y := flushLoop now r.ring.length 0 ⟨{ r with clock := max r.clock now }, [], {}, none⟩
  res { y.r with lt := none, pc := 0, lp := 0, saved := none } y.ev y.s "ok" false

/-! ### Sending -/

structure Pkt where
  pn : Nat
  time : Nat
  size : Nat
  path : Nat
  rep : Bool
  probe : Bool
  fr : List Bool

def send (p : P) (r : R) (k : Pkt) : Res :=
  if r.ls.any (fun l => decide (k.pn ≤ l)) then res r [] {} "PacketNumberNotIncreasing" false
  else if k.path ≥ p.mp then res r [] {} "PathOutOfRange" false
  else
    let r1 := { r with clock := max r.clock k.time, ring := trim p k.time r.ring }
    match push p r1.ring ⟨k.pn, k.time, k.size, k.path, k.rep, k.probe, k.fr, .fl, 0, r1.gen.getD k.path 0⟩ with
    | none => res r1 [] {} "RingFull" false
    | some ring =>
      res { r1 with ring, ls := some k.pn, sent := r1.sent + k.size, inf := r1.inf + k.size, infp := r1.infp + 1 }
        [] {} "ok" false

def untracked (r : R) (pn : Nat) : Res :=
  if r.ls.any (fun l => decide (pn ≤ l)) then res r [] {} "PacketNumberNotIncreasing" false
  else res { r with ls := some pn } [] {} "ok" false

/-! ### Acknowledgements -/

structure X where
  r : R
  ev : List Ev
  s : Sm
  fl : Option Nat
  nw : Option (Nat × Nat × Nat)
  gh : Bool
  err : String

/-- The path whose round trip a newest acknowledged packet may set: its own when the path in that slot is still the
occupant that sent the packet, and an index past the table (which `List.set` leaves alone) when another path has taken
the slot since. The bound is the occupant, not a time, so it holds for a boundary kept as a packet number too. -/
def nwPath (r : R) (sl : Slot) : Nat := if sl.occ == r.gen.getD sl.path 0 then sl.path else r.prtt.length

def ackRing (p : P) (now b : Nat) : Nat → Nat → X → X
  | 0, _, x => x
  | k + 1, i, x =>
    match x.r.ring[i]? with
    | none => x
    | some sl =>
      if sl.pn > b then x
      else if sl.st == .done then ackRing p now b k (i + 1) x
      else if sl.st == .lost && !x.gh then ackRing p now b k (i + 1) x
      else if sl.st == .lost && decide (now - sl.lostAt > p.gret) then
        ackRing p now b k (i + 1) { x with r := { x.r with ring := upd x.r.ring i (fun s => { s with st := .done }) } }
      else
        let late := sl.st == .lost
        let r1 := noteOvertaken p { x.r with ring := upd x.r.ring i (fun s => { s with st := .done }) } now sl.pn sl.time sl.path
        if late then
          ackRing p now b k (i + 1)
            { x with r := { r1 with lost := r1.lost - sl.size, acked := r1.acked + sl.size },
                     s := { x.s with lap := x.s.lap + 1 },
                     ev := x.ev ++ [⟨"late", sl.pn, 0, sl.fr.filter id, false, false⟩] }
        else
          ackRing p now b k (i + 1)
            { x with r := { r1 with inf := r1.inf - sl.size, acked := r1.acked + sl.size, infp := r1.infp - 1 },
                     s := { x.s with ap := x.s.ap + 1, ab := x.s.ab + sl.size },
                     ev := x.ev ++ [⟨"acked", sl.pn, sl.size, sl.fr, sl.probe, sl.rep⟩],
                     nw := match x.nw with
                       | none => some (sl.pn, sl.time, nwPath x.r sl)
                       | some n => if sl.pn > n.1 then some (sl.pn, sl.time, nwPath x.r sl) else x.nw }

/-- One acknowledged range `[a, b]` with no error: its largest number is noted, a saved window it covers is restored,
the packets inside are acknowledged. -/
def ackRange1 (p : P) (now a b : Nat) (x : X) : X :=
  let x1 : X := { x with fl := omax x.fl (some b),
                         r := { x.r with saved := match x.r.saved with
                                                  | some s => if a ≤ s && s ≤ b then none else x.r.saved
                                                  | none => none } }
  ackRing p now b x1.r.ring.length (lowerBound x1.r.ring a) x1

def ackRanges (p : P) (now : Nat) : List (Nat × Nat) → X → X
  | [], x => x
  | (a, b) :: t, x =>
    if x.err != "ok" then x
    else if a > b then { x with err := "InvalidAckRange" }
    else if x.r.ls.all (fun l => decide (b > l)) then { x with err := "AckOfUnsentPacket" }
    else ackRanges p now t (ackRange1 p now a b x)

/-- The state a call of `ack` starts from: the clock, and the ghost look when it is due. -/
def ackStart (p : P) (r : R) (now : Nat) : R × Bool :=
  let r0 := { r with clock := max r.clock now }
  let gh := decide (now - r0.gs ≥ p.gscan) && hasGhost r0.ring
  (if gh then { r0 with gs := now } else r0, gh)

/-- The late-send table and the round-trip seed of an acknowledgement whose largest number is `fl`: the state and
the newest acknowledged packet (a late send can stand in for it when the estimate is empty). -/
def ackSeed (p : P) (x : X) (now fl : Nat) : R × Option (Nat × Nat × Nat) :=
  let r2 := { x.r with hrd := max x.r.hrd now, la := omax x.r.la (some fl) }
  let lst := lateTime r2.late fl
  let r3 := { r2 with late := lateTake r2.late fl }
  let seeded := lst.isSome && (match x.nw with | none => true | some n => n.1 != fl) && !r3.rtt.has
  (if seeded then { r3 with pc := 0 } else r3,
   if seeded then some (fl, max (lst.getD 0) (now - p.lateSample), r3.act) else x.nw)

/-- The round-trip sample, when the newest acknowledged packet is the acknowledgement's largest. -/
def ackSample (p : P) (r4 : R) (npn ntime npath now fl : Nat) : R :=
  let e2 := rttUpdate p r4.rtt (now - ntime)
  if npn == fl then
    { r4 with lat := ntime, rtt := e2, tgr := max e2.sm (r4.tgr - r4.tgr / 32), prtt := r4.prtt.set npath e2.sm }
  else r4

def ackFinish (p : P) (x : X) (now fl : Nat) : Res :=
  match (ackSeed p x now fl).2 with
  | none => res { (ackSeed p x now fl).1 with ring := trim p now (ackSeed p x now fl).1.ring } x.ev x.s "ok" false
  | some (npn, ntime, npath) =>
    let y := detect p ⟨{ ackSample p (ackSeed p x now fl).1 npn ntime npath now fl with pc := 0 }, x.ev, x.s, none⟩ now fl
    res { y.r with ring := trim p now y.r.ring } y.ev y.s "ok" false

def ack (p : P) (r : R) (now : Nat) (rgs : List (Nat × Nat)) : Res :=
  let x := ackRanges p now rgs ⟨(ackStart p r now).1, [], {}, none, none, (ackStart p r now).2, "ok"⟩
  if x.err != "ok" then res x.r x.ev x.s x.err false
  else match x.fl with
  | none => res { x.r with hrd := max x.r.hrd now } x.ev x.s "ok" false
  | some fl => ackFinish p x now fl

/-! ### Configuration calls -/

def switchPath (r : R) (mp path : Nat) : R × Bool × String :=
  if path ≥ mp then (r, false, "PathOutOfRange")
  else if path == r.act then (r, false, "ok")
  else if isRelay r r.act && isRelay r path then ({ r with act := path }, false, "ok")
  else ({ r with act := path, flip := some r.clock }, true, "ok")

def followPath (r : R) (mp path : Nat) : R × String :=
  if path ≥ mp then (r, "PathOutOfRange")
  else if path != r.act then ({ r with act := path, flip := some r.clock }, "ok")
  else (r, "ok")

/-- The path in slot `path` goes and another takes the slot: its round trip is cleared and a packet sent before is
stale (`nwPath`). The reorder state of the slot is kept. -/
def forgetPath (r : R) (mp path : Nat) : R × String :=
  if path ≥ mp then (r, "PathOutOfRange")
  else ({ r with prtt := r.prtt.set path 0, gen := r.gen.set path (r.gen.getD path 0 + 1) }, "ok")

def setKind (r : R) (mp path : Nat) (relay : Bool) : R × String :=
  if path ≥ mp then (r, "PathOutOfRange") else ({ r with rel := r.rel.set path relay }, "ok")

def activity (r : R) (now : Nat) : R := { r with hrd := max r.hrd now, clock := max r.clock now }

/-! ### Tail repair -/

structure Tail where
  burst : Nat
  cand : Option Nat
  deriving DecidableEq, Repr

def Tail.new : Tail := ⟨0, none⟩

def tailPacket (t : Tail) (pn : Nat) (plain inel : Bool) : Tail :=
  let b2 := if inel then 2 else min (t.burst + 1) 2
  if b2 > 1 then ⟨b2, none⟩ else ⟨b2, if plain then some pn else t.cand⟩

def tailDrain (t : Tail) : Tail × Option Nat := (Tail.new, t.cand)

end Vinc.TransportRecovery
