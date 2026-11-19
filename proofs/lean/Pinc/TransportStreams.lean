/-!
# The stream table: the receive and credit path

A model of `pinc-transport` `stream/table.rs`, `recv.rs`, `flow.rs`, `ranges.rs` and `pool.rs`, operation for
operation as `proofs/tla/StreamsOps.tla` has them (the same operators, with unbounded `Nat` offsets and arbitrary
sizes in `P`: the chunk size `ch`, the ring `ring`, the stored-range cap `rr`, the slots `n`, the pool `b` in
chunks). `Pinc.TraceStreams` replays the recorded calls of the real code through these functions; the theorems
about them are in `Pinc.TransportStreamsGrant`, `Pinc.TransportStreamsFlow`, `Pinc.TransportStreamsLocal` and
`Pinc.TransportStreamsAdmit`.

A slot's `held` is the ascending list of chunk numbers its ring holds, `rs` the ascending stored ranges. The
pool use of the streams is the number of chunks their rings hold; `ext` is what everything else holds (send
buffers, datagram queues, the early-data buffer), charged to the same pool.
-/

namespace Pinc.TransportStreams

/-- The constants of a table: `CH`, `RING`, `RR`, slots, peer-stream cap, pool chunks, initial and ceiling window,
the cap of streams this side opens, and whether a deferred grant is retried after a
release of pool chunks (the code does). -/
structure P where
  ch : Nat
  ring : Nat
  rr : Nat
  n : Nat
  maxrem : Nat
  b : Nat
  swc : Nat
  mswc : Nat
  pm : Nat
  maxoff : Nat
  retry : Bool
  /-- The chunks of a window the ledger counts while the stream has carried no data, and keeps for each stream inside
  the credit (`FIRST_CHARGE`, 4 in the code). -/
  firstk : Nat

def P.half (p : P) : Nat := p.b * p.ch / 2 / p.ch * p.ch
/-- The ceiling of a stream window: the configured one, `(C - 1)` chunks, and half the pool. -/
def P.maxStream (p : P) : Nat := min p.mswc (min ((p.ring - 1) * p.ch) p.half)
/-- The initial window. -/
def P.sw (p : P) : Nat := min p.swc p.maxStream
/-- The initial window in whole chunks. -/
def P.winC (p : P) : Nat := (p.sw + p.ch - 1) / p.ch * p.ch
/-- What the ledger counts for a stream that has carried no data, and keeps for each stream inside the credit: its
initial window, or `firstk` chunks, whichever is less. -/
def P.firstW (p : P) : Nat := min p.winC (p.firstk * p.ch)
/-- Half of `f` windows, but three stay free, and one at least when one fits (`admit_fit`). -/
def admitFit (f : Nat) : Nat := max (min (f - 3) (f / 2)) (min f 1)
/-- The live peer streams the table admits: at most half the slots, so the rest stay free for its own streams. -/
def P.capLive (p : P) : Nat := min p.maxrem (max (p.n / 2) 1)
/-- The stream credit the handshake gives the peer (`Streams::admit_cap` on an empty table). -/
def P.adv0 (p : P) : Nat := min p.capLive (admitFit (p.b * p.ch / p.firstW))

structure Slot where
  id : Option Nat
  open_ : Bool
  held : List Nat
  rs : List (Nat × Nat)
  read : Nat
  hi : Nat
  contig : Nat
  fin : Option Nat
  limit : Nat
  size : Nat
  pend : Bool
  defer : Bool
  rst : Option Nat
  obs : Bool
  sdone : Bool
  srst : Nat
  /-- The stop request of the receive half: 0 none, 1 pending, 2 sent, 3 acknowledged. -/
  stop : Nat
  qcode : Option Nat
  scode : Option Nat
  /-- The stream counts against its opener's limit (`Slot::counted`). Not on the wire: the trace replay carries it. -/
  cnt : Bool
  /-- The send half's end has left and no lost range is queued: the part of `Send::flushed` that `sdone` and `srst`
  do not show. Not on the wire either. -/
  sfl : Bool
  /-- For a stream we opened, how many we had opened in all, itself included (`Slot::ordinal`): its data waits until
  the peer's limit covers it. 0 for a stream the peer opened. -/
  ord : Nat
  /-- This stream's delivery meter (`Recv::meter`): the epoch start, the bytes read in it, the last rate. -/
  ms : Option Nat
  mb : Nat
  mr : Nat
  deriving DecidableEq, Repr, Inhabited

def Slot.new : Slot :=
  { id := none, open_ := false, held := [], rs := [], read := 0, hi := 0, contig := 0, fin := none, limit := 0,
    size := 0, pend := false, defer := false, rst := none, obs := false, sdone := true, srst := 0, stop := 0, qcode := none, scode := none,
    cnt := false, sfl := false, ord := 0, ms := none, mb := 0, mr := 0 }

structure Tab where
  slots : List Slot
  rn : Nat × Nat
  lo : Nat × Nat
  rl : Nat
  ll : Nat
  ext : Nat
  /-- The limit on the streams we may open in all, as the peer last said. -/
  adlim : Nat
  /-- The limit on the streams the peer may open in all, as last advertised. -/
  adv : Nat
  /-- The streams admitted when `adv` was set. -/
  adat : Nat
  /-- A `MAX_STREAMS` frame is waiting to be sent. -/
  adpend : Bool
  /-- Opens may pass `adlim`, which the peer has not stated yet (`Admit::early`, an optimistic dial). -/
  early : Bool
  deriving DecidableEq, Repr, Inhabited

def Tab.init (p : P) : Tab :=
  { slots := List.replicate p.n Slot.new, rn := (0, 0), lo := (0, 0), rl := 0, ll := 0,
    ext := 0, adlim := p.pm, adv := p.adv0, adat := 0, adpend := false,
    early := false }

/-! ### Identifiers -/
def isUni (id : Nat) : Bool := id / 2 % 2 == 1
def isLocal (id : Nat) : Bool := id % 2 == 1
def cls (id : Nat) : Nat := if isUni id then 1 else 0
def idx (id : Nat) : Nat := id / 4
def cget (c : Nat × Nat) (k : Nat) : Nat := if k == 0 then c.1 else c.2
def cset (c : Nat × Nat) (k v : Nat) : Nat × Nat := if k == 0 then (v, c.2) else (c.1, v)

/-! ### The range set (`ranges.rs`) -/
def insertR (rr : Nat) (rs : List (Nat × Nat)) (s e : Nat) : Option (List (Nat × Nat)) :=
  if s ≥ e then some rs
  else
    let fr := (rs.filter (fun iv => iv.2 < s)).length
    let to := (rs.filter (fun iv => iv.1 ≤ e)).length
    let merged := if fr < to then (min (rs.getD fr (0, 0)).1 s, max (rs.getD (to - 1) (0, 0)).2 e) else (s, e)
    if rs.length - (to - fr) + 1 > rr then none else some (rs.take fr ++ [merged] ++ rs.drop to)

def overlaps (rs : List (Nat × Nat)) (lo e : Nat) : Bool := rs.any (fun iv => iv.1 < e && iv.2 > lo)
def first0 (rs : List (Nat × Nat)) : Nat :=
  match rs with
  | (0, e) :: _ => e
  | _ => 0

/-! ### The receive half -/
/-- 0 open, 1 finished, 2 reset. -/
def Slot.status (r : Slot) : Nat :=
  if r.rst.isSome then 2 else if r.fin == some r.read then 1 else 0
def Slot.readable (r : Slot) : Nat := if r.rst.isSome then 0 else r.contig - r.read
def Slot.recvDone (r : Slot) : Bool := !r.open_ || (r.obs && r.status != 0)
def Slot.sendDone (r : Slot) : Bool := r.sdone || r.srst == 3

def Slot.reach (r : Slot) (l : Nat) : Nat := match r.fin with | none => l | some f => min f l

/-- `pool_demand`: the pool bytes credit up to `l` may still claim. -/
def poolDemand (p : P) (r : Slot) (l : Nat) : Nat :=
  if !r.open_ || r.reach l ≤ r.read then 0
  else ((r.reach l - 1) / p.ch - r.read / p.ch + 1 - r.held.length) * p.ch

/-- How far into a window the ledger counts it: the first `firstk` chunks while the stream has carried no data, the
whole window from its first byte on. -/
def Slot.chargeTo (p : P) (r : Slot) (l : Nat) : Nat := if r.hi = 0 then min l (p.firstk * p.ch) else l

/-- `charged_demand`: the pool bytes credit up to `l` may claim, as the ledger counts them. -/
def Slot.demandTo (p : P) (r : Slot) (l : Nat) : Nat := poolDemand p r (r.chargeTo p l)

def Slot.unreceived (p : P) (r : Slot) : Nat := r.demandTo p r.limit

/-- `due`: the limit the window is due to move to, once an eighth of it was freed. -/
def Slot.due (p : P) (r : Slot) : Option Nat :=
  if !r.open_ then none
  else
    let cap := match r.fin with | none => p.maxoff | some f => f
    let cand := min (r.read + r.size) cap
    if cand > r.limit && cand ≥ r.limit + r.size / 8 then some cand else none

/-! ### The pool -/
def heldTotal (T : Tab) : Nat := (T.slots.map (·.held.length)).sum
def used (T : Tab) : Nat := heldTotal T + T.ext
def availC (p : P) (T : Tab) : Nat := p.b - used T
def avail (p : P) (T : Tab) : Nat := availC p T * p.ch
def gu (p : P) (T : Tab) : Nat := (T.slots.map (·.unreceived p)).sum
/-- `Streams::consume`'s window target: twice the rate the stream's own reader drained per round trip, never below
the initial window nor above the ceiling. -/
def windowTarget (p : P) (rate : Nat) : Nat := min (max (rate * 2) p.sw) p.maxStream
/-- The peer streams admitted in all. -/
def admitted (T : Tab) : Nat := T.rn.1 + T.rn.2
/-- The streams the peer may still open inside the credit it was given. -/
def creditLeft (T : Tab) : Nat := T.adv - admitted T
/-- The pool bytes kept for them. -/
def resv (p : P) (T : Tab) : Nat := creditLeft T * p.firstW

def setSlot (T : Tab) (i : Nat) (r : Slot) : Tab := { T with slots := T.slots.set i r }
def findSlot (T : Tab) (id : Nat) : Option Nat := T.slots.findIdx? (·.id == some id)
def firstFree (T : Tab) : Option Nat := T.slots.findIdx? (·.id == none)
def Slot.hot (r : Slot) : Bool := (r.pend && r.open_) || r.srst == 1 || r.stop == 1
/-- The slot may give a control frame now: it has one, and the limit `lim` covers its ordinal (`Streams::refresh`;
#432: a stream opened past the peer's limit holds its control frames as it holds its data). -/
def Slot.ctlDue (lim : Nat) (r : Slot) : Bool := r.hot && decide (r.ord ≤ lim)
def anyDefer (T : Tab) : Bool := T.slots.any (·.defer)

/-! ### The window grant (`Streams::grant`) -/
/-- The slot with its window size raised to the target. -/
def Slot.grown (r : Slot) (tgt : Nat) : Slot := { r with size := max r.size tgt }

/-- The window moved to `c`, the update queued. -/
def Slot.raised (r : Slot) (c : Nat) : Slot := { r with limit := c, pend := true, defer := false }
/-- The grant marked deferred, or not. -/
def Slot.parked (r : Slot) (d : Bool) : Slot := { r with defer := d }

/-- The new slot of one grant step, given the credit sum `g`, the bytes the pool has left `a` and the window target. -/
def grantSlot (p : P) (tgt g a : Nat) (r : Slot) : Slot :=
  match (r.grown tgt).due p with
  | none => (r.grown tgt).parked false
  | some c =>
    if g - r.unreceived p + (r.grown tgt).demandTo p c ≤ a
    then (r.grown tgt).raised c
    else (r.grown tgt).parked true

def grantOne (p : P) (first : Nat) (T : Tab) (i : Nat) : Tab :=
  let r := T.slots.getD i Slot.new
  -- the window size moved when its own reader consumed; a grant only moves the limit (target 0 leaves the size)
  if !r.open_ || !(i == first || r.defer) then T else setSlot T i (grantSlot p 0 (gu p T + resv p T) (avail p T) r)

def grantRun (p : P) (T : Tab) (first : Nat) : Tab := (List.range p.n).foldl (grantOne p first) T
/-- `Streams::admit_room`: how many more peer streams could be admitted now. -/
def freeSlots (T : Tab) : Nat := (T.slots.filter (·.id == none)).length
def admitRoom (p : P) (T : Tab) : Nat :=
  min (min (p.capLive - T.rl) (freeSlots T)) (admitFit ((avail p T - gu p T) / p.firstW))

/-- `Streams::refresh_admit`: queue a raise of the credit when the room grew by an eighth of the credit last given, or at
once when the opener used all of it. -/
def refreshAdmit (p : P) (T : Tab) : Tab :=
  let now := admitted T + admitRoom p T
  if now > T.adv && (decide (T.adv ≤ admitted T) || decide (now - T.adv ≥ max ((T.adv - T.adat) / 8) 1))
  then { T with adv := now, adat := admitted T, adpend := true } else T

def regrant (p : P) (T : Tab) : Tab :=
  let T1 := refreshAdmit p T
  if p.retry && anyDefer T1 then grantRun p T1 p.n else T1

/-! ### Slots -/
def freeSlot (T : Tab) (i : Nat) : Tab :=
  let r := T.slots.getD i Slot.new
  let T1 := setSlot T i Slot.new
  match r.id with
  | none => T1
  | some id => if isLocal id then { T1 with ll := T1.ll - 1 } else if r.cnt then { T1 with rl := T1.rl - 1 } else T1

/-- `Send::flushed`: everything the send half will send has left and nothing waits to be sent again. -/
def Slot.flushed (r : Slot) : Bool := r.sdone || r.srst ≥ 2 || r.sfl

/-- `Streams::release_limit`: a peer stream stops counting against the peer's limit once what it sent is whole and read
and our answer has left; its slot is kept until both halves are done. -/
def releaseLimit (T : Tab) (i : Nat) : Tab :=
  let r := T.slots.getD i Slot.new
  match r.id with
  | none => T
  | some id =>
    if isLocal id || !r.cnt || !r.recvDone || !r.flushed then T
    else { setSlot T i { r with cnt := false } with rl := T.rl - 1 }

def settle (p : P) (T : Tab) (i : Nat) : Tab :=
  let r := T.slots.getD i Slot.new
  regrant p (if r.recvDone && r.sendDone then freeSlot T i else releaseLimit T i)

def allocSlot (p : P) (T : Tab) (id : Nat) : Tab :=
  match firstFree T with
  | none => T
  | some i =>
    let lcl := isLocal id
    let recvOn := !isUni id || !lcl
    let sendOn := !isUni id || lcl
    let r := { Slot.new with id := some id, open_ := recvOn, limit := if recvOn then p.sw else 0,
                             size := if recvOn then p.sw else 0, sdone := !sendOn, cnt := true,
                             ord := if lcl then T.lo.1 + T.lo.2 + 1 else 0 }
    let T1 := setSlot T i r
    if lcl then { T1 with ll := T1.ll + 1 } else { T1 with rl := T1.rl + 1 }

/-! ### Admission of peer streams -/
/-- `Streams::windows_fit`: the first charges of `count` new streams fit beside the credit granted. The one test for a
peer stream beyond the credit and for a local one. -/
def windowsFit (p : P) (T : Tab) (count : Nat) : Bool :=
  gu p T + count * p.firstW ≤ avail p T

/-- `Streams::admits`: under the cap and with slots; inside the credit with no pool test (the new streams take no
chunk, and the credit kept their first charges), beyond it with their first charges fitting. -/
def admits (p : P) (T : Tab) (c next count : Nat) : Bool :=
  let free := (T.slots.filter (·.id == none)).length
  T.rl + count ≤ p.maxrem && free ≥ count &&
    (decide (admitted T + count ≤ T.adv) || windowsFit p T (max count (creditLeft T)))

/-- `Locate`: the table, the slot found (if any) and the error ("ok" when none). A peer stream that does not fit is
held back: "Exhausted" and the table unchanged. -/
def locate (p : P) (T : Tab) (id : Nat) : Tab × Option Nat × String :=
  let c := cls id
  let ix := idx id
  let next := cget T.rn c
  if isLocal id then
    if ix ≥ cget T.lo c then (T, none, "StreamState") else (T, findSlot T id, "ok")
  else if ix < next then (T, findSlot T id, "ok")
  else if ix ≥ next + p.maxrem then (T, none, "StreamLimit")
  else if !admits p T c next (ix - next + 1) then (T, none, "Exhausted")
  else
    let T2 := (List.range (ix - next + 1)).foldl (fun T k => allocSlot p T ((next + k) * 4 + id % 4)) T
    let T3 := { T2 with rn := cset T2.rn c (ix + 1) }
    (T3, findSlot T3 id, "ok")

/-! ### on_data -/
/-- `Recv::store`: the slot and the error ("ok" when none). -/
def storeStep (p : P) (T : Tab) (r : Slot) (off len : Nat) (diff : Bool) : Slot × String :=
  let e := off + len
  let lo := max off r.read
  let first := lo / p.ch
  let last := (e - 1) / p.ch
  let missing := ((List.range (last + 1 - first)).map (first + ·)).filter (fun k => !r.held.contains k)
  if lo ≥ e then (r, "ok")
  else if last - r.read / p.ch ≥ p.ring then (r, "FlowControl")
  else if lo < r.hi && diff && overlaps r.rs lo e then (r, "Conflict")
  else if missing.length > availC p T then (r, "Exhausted")
  else match insertR p.rr r.rs lo e with
    | none => (r, "Fragmented")
    | some rs' =>
      ({ r with held := r.held.filter (· < first) ++ (List.range (last + 1 - first)).map (first + ·) ++
                        r.held.filter (· > last),
                rs := rs', contig := first0 rs' }, "ok")

def onData (p : P) (T : Tab) (r : Slot) (off len : Nat) (fin diff : Bool) : Slot × String :=
  let e := off + len
  let store := storeStep p T r off len diff
  let done := { store.1 with hi := max store.1.hi e, fin := if fin then some e else store.1.fin }
  if e > p.maxoff then (r, "FlowControl")
  else if r.fin.any (fun f => e > f || (fin && e != f)) then (r, "FinalSize")
  else if r.fin.isNone && fin && e < r.hi then (r, "FinalSize")
  else if e > r.limit then (r, "FlowControl")
  else if r.rst.isNone && store.2 != "ok" then (r, store.2)
  else if r.rst.isNone then (done, "ok")
  else ({ r with hi := max r.hi e, fin := if fin then some e else r.fin }, "ok")

def frame (p : P) (T : Tab) (id off len : Nat) (fin diff : Bool) : Tab × String :=
  let (T1, i, err) := locate p T id
  match i with
  | none => (T1, err)
  | some i =>
    if err != "ok" then (T1, err)
    else
      let (r, e2) := onData p T1 (T1.slots.getD i Slot.new) off len fin diff
      (settle p (setSlot T1 i r) i, e2)

/-! ### on_reset -/
def onReset (p : P) (r : Slot) (code fs : Nat) : Slot × String :=
  if fs > p.maxoff || r.fin.any (· != fs) || fs < r.hi then (r, "FinalSize")
  else if fs > r.limit then (r, "FlowControl")
  else if r.rst.isSome then (r, "ok")
  else ({ r with hi := fs, fin := some fs, rst := some code, read := fs, contig := fs, held := [], rs := [] }, "ok")

def reset (p : P) (T : Tab) (id code fs : Nat) : Tab × String :=
  let (T1, i, err) := locate p T id
  match i with
  | none => (T1, err)
  | some i =>
    if err != "ok" then (T1, err)
    else
      let (r, e2) := onReset p (T1.slots.getD i Slot.new) code fs
      (settle p (setSlot T1 i r) i, e2)

/-! ### consume -/
def meterStep (ms : Option Nat) (mb mr n now srtt : Nat) : Option Nat × Nat × Nat :=
  let st := ms.getD now
  let by_ := mb + n
  let el := if now ≥ st then now - st else 0
  if srtt > 0 && el ≥ srtt then (some now, 0, by_ * srtt / el) else (some st, by_, mr)

def consume (p : P) (T : Tab) (id n now srtt : Nat) : Tab × String :=
  match findSlot T id with
  | none => (T, "UnknownStream")
  | some i =>
    let r := T.slots.getD i Slot.new
    if n > r.readable then (T, "InvalidConsume")
    else
      let nr := r.read + n
      let cut := r.fin == some nr
      -- the stream's own meter takes the bytes read, and its window grows toward twice the rate it measures
      let (ms, mb, mr) := meterStep r.ms r.mb r.mr n now srtt
      let r1 := { r with read := nr,
                         held := if cut then [] else r.held.filter (fun k => !(r.read / p.ch ≤ k && k < nr / p.ch)),
                         rs := if cut then [] else r.rs,
                         ms := ms, mb := mb, mr := mr,
                         size := max r.size (windowTarget p mr) }
      let r2 := { r1 with obs := r1.obs || r1.status != 0 }
      (settle p (grantRun p (setSlot T i r2) i) i, "ok")

/-! ### Control frames -/
/-- `pending_control` with the test `due` of the slots that may give a frame: the table, the kind ("none", "reset",
"stop", "msd"), the stream and the number: the limit of an msd, the error code of a reset or a stop. A raise of the
stream credit goes first; then the first slot `due` lets go gives one: its stream reset first, then its stop request,
then its limit. -/
def pendingBy (due : Slot → Bool) (T : Tab) : Tab × String × Nat × Nat :=
  if T.adpend then ({ T with adpend := false }, "msts", 0, T.adv) else
  match T.slots.findIdx? due with
  | none => (T, "none", 0, 0)
  | some i =>
    let r := T.slots.getD i Slot.new
    let id := r.id.getD 0
    if r.srst == 1 then (setSlot T i { r with srst := 2 }, "reset", id, r.scode.getD 0)
    else if r.stop == 1 then (setSlot T i { r with stop := 2 }, "stop", id, r.qcode.getD 0)
    else (setSlot T i { r with pend := false }, "msd", id, r.limit)

/-- `pending_control`: the first slot with a frame to send whose ordinal the limit covers gives one (`Slot.ctlDue`). -/
def pending (T : Tab) : Tab × String × Nat × Nat := pendingBy (Slot.ctlDue T.adlim) T

/-- A lost `MAX_STREAMS` frame is sent again unless a later limit superseded it. -/
def ctlLostMsts (T : Tab) (l : Nat) : Tab := if l ≥ T.adv then { T with adpend := true } else T

/-- A `MAX_STREAMS` frame arrived: the limit on the streams we may open only grows. -/
def recvMaxStreams (T : Tab) (l : Nat) : Tab := { T with adlim := max T.adlim l }

/-- `Streams::set_early`: opens may pass the limit (`on`), or no longer. -/
def setEarly (T : Tab) (on : Bool) : Tab := { T with early := on }

/-- The establishment of an optimistic dial: the peer's record raises the limit, then early opens end. -/
def establish (T : Tab) (l : Nat) : Tab := setEarly (recvMaxStreams T l) false

/-- `Streams::refresh`: the data and the control frames of slot `i` may leave once the limit covers its ordinal
(always, for a peer stream). -/
def canSend (T : Tab) (i : Nat) : Bool := decide ((T.slots.getD i Slot.new).ord ≤ T.adlim)

def ctlLostMsd (T : Tab) (id mx : Nat) : Tab :=
  match findSlot T id with
  | none => T
  | some i =>
    let r := T.slots.getD i Slot.new
    if mx ≥ r.limit then setSlot T i { r with pend := true } else T

def ctlLostReset (T : Tab) (id : Nat) : Tab :=
  match findSlot T id with
  | none => T
  | some i =>
    let r := T.slots.getD i Slot.new
    if r.srst == 2 then setSlot T i { r with srst := 1 } else T

def ctlAckedReset (p : P) (T : Tab) (id : Nat) : Tab :=
  match findSlot T id with
  | none => T
  | some i =>
    let r := T.slots.getD i Slot.new
    let acked := r.srst == 1 || r.srst == 2
    settle p (setSlot T i { r with srst := if acked then 3 else r.srst, scode := if acked then none else r.scode }) i

/-- A lost stop request is sent again unless the sender ended the stream meanwhile. -/
def ctlLostStop (T : Tab) (id : Nat) : Tab :=
  match findSlot T id with
  | none => T
  | some i =>
    let r := T.slots.getD i Slot.new
    if r.stop == 2 && r.rst.isNone && r.fin.isNone then setSlot T i { r with stop := 1 } else T

def ctlAckedStop (T : Tab) (id : Nat) : Tab :=
  match findSlot T id with
  | none => T
  | some i =>
    let r := T.slots.getD i Slot.new
    if r.stop == 1 || r.stop == 2 then setSlot T i { r with stop := 3, qcode := none } else T

/-! ### The send half, as far as the receive side sees it -/
def openLocal (p : P) (T : Tab) : Tab :=
  if (!T.early && decide (T.lo.1 + T.lo.2 ≥ T.adlim)) || (firstFree T).isNone || decide (freeSlots T ≤ creditLeft T)
      || !windowsFit p T (creditLeft T + 1) then T
  else { allocSlot p T (T.lo.1 * 4 + 1) with lo := (T.lo.1 + 1, T.lo.2) }

def Slot.sendOpen (r : Slot) : Bool := !(r.id.any (fun id => isUni id && !isLocal id))

/-- A stream frame left on slot `i` (`pick.rs`): the send half's end has gone with nothing queued again (`f`), or not
yet, or a lost range waits to be sent again (`!f`); then `release_limit`. Only a send half that can still send a stream
frame is touched. -/
def sendOut (T : Tab) (i : Nat) (f : Bool) : Tab :=
  let r := T.slots.getD i Slot.new
  if r.id.isNone || !r.sendOpen || r.sdone || r.srst != 0 || !canSend T i then T
  else releaseLimit (setSlot T i { r with sfl := f }) i

def appReset (p : P) (T : Tab) (id code ext2 : Nat) : Tab :=
  match findSlot T id with
  | none => T
  | some i =>
    let r := T.slots.getD i Slot.new
    let T1 := if r.sendOpen && r.srst == 0 && !r.sdone
              then { setSlot T i { r with srst := 1, scode := some code } with ext := ext2 } else T
    settle p T1 i

/-- `Streams::stop_sending`: queue a stop request once; nothing if the sender already ended the stream. -/
def stopReq (T : Tab) (id code : Nat) : Tab × String :=
  match findSlot T id with
  | none => (T, "UnknownStream")
  | some i =>
    let r := T.slots.getD i Slot.new
    if !r.open_ then (T, "StreamState")
    else if r.rst.isNone && r.fin.isNone && r.stop == 0 then (setSlot T i { r with stop := 1, qcode := some code }, "ok")
    else (T, "ok")

/-- `Streams::on_stop_sending`: the table, the error and whether this call reset the send half with `code`. -/
def onStop (p : P) (T : Tab) (id code ext2 : Nat) : Tab × String × Bool :=
  if isUni id && !isLocal id then (T, "StreamState", false)
  else
    let (T1, i, err) := locate p T id
    if err != "ok" then (T1, err, false)
    else
      match i with
      | none => (T1, "ok", false)
      | some i =>
        let r := T1.slots.getD i Slot.new
        let fresh := r.sendOpen && r.srst == 0 && !r.sdone
        let T2 := if fresh then { setSlot T1 i { r with srst := 1, scode := some code } with ext := ext2 } else T1
        (settle p T2 i, "ok", fresh)

def finish (p : P) (T : Tab) (id ext2 : Nat) (done : Bool) : Tab :=
  match findSlot T id with
  | none => T
  | some i =>
    let r := T.slots.getD i Slot.new
    settle p { setSlot T i { r with sdone := r.sdone || (done && r.srst == 0) } with ext := ext2 } i

def extTo (p : P) (T : Tab) (ext2 : Nat) : Tab :=
  if ext2 > T.ext && ext2 - T.ext > availC p T then T
  else if ext2 ≥ T.ext then { T with ext := ext2 }
  else regrant p { T with ext := ext2 }

def closeAll (p : P) (T : Tab) (ext2 : Nat) : Tab :=
  { T with slots := (Tab.init p).slots, rl := 0, ll := 0, ext := ext2 }

end Pinc.TransportStreams
