import Vinc.Ranges

/-!
# The time rules of the value fetch

The functions of `crates/vinc-values/src/fetch/{recv,stall}.rs` that decide with a clock, written step for step on
natural numbers with the saturating operations of `u64`:

* HEAD_HOLD: `groupVerified` (capture of the first granule, immediate announcement of the later ones), `holdWhy` and
  `holdCheck` (the release causes), `checkDone` (the forced release and `Complete`).
* STALL_REDIAL: `arrival` (ARK_PACE), `byteLive` (BYTE_LIVE), `stallRtt` (STALL_RTT), `stallLive` (STALL_LIVE),
  `stallStep` (the first block of `on_timeout`), `pollTimeout`.
* The whole of `on_timeout` (`onTimeout`: the stall block, the head block, the steal re-check, the deadline, the
  retries, in the order of the code) and `startFetch` (the failure reasons of `Fetch::start`).

`Fs` holds exactly the fields of `Fetch` these functions read or write, and the `log` of the trace records and
application events they emit, oldest first (`Ev`). The session (the assigned sessions' round trips and liveness) and
the store are the environment: `Sess` lists, and the verified set as the interval list of `Vinc.Ranges`.

Units: times are nanoseconds, sizes bytes. A byte offset or length is a plain natural (the code adds them without
saturation; they are bounded by the value length). Every time arithmetic that the code saturates is `sadd`, `smul`
or a truncated subtraction (`u64::saturating_sub` is `Nat.sub`), so a theorem here holds for every `u64` input.

Theorems: `Vinc/ValuesTimeHold.lean` (property 4), `ValuesTimeStall.lean` (property 8, the deadline, the failure
reasons); the replay of the recorded traces: `ValuesTimeTrace.lean`.
-/

set_option linter.unusedVariables false

namespace Vinc.ValuesTime
open Vinc.Ranges

/-! ## The constants of `knobs.rs` -/

abbrev NS : Nat := 1000000000
abbrev MS : Nat := 1000000
/-- `u64::MAX`, 2^64 - 1. -/
abbrev U64Max : Nat := 18446744073709551615
abbrev GROUP : Nat := 16384
abbrev HOLD_B : Nat := 98304
abbrev HOLD_NV : Nat := 40
abbrev HOLD_MAX : Nat := 2 * NS
abbrev STALL_WAIT : Nat := 4 * NS
abbrev STALL_CAP : Nat := 16 * NS
abbrev ARK_PACE_CAP : Nat := 40 * NS
abbrev BYTE_GAP_CAP : Nat := 60 * NS
abbrev STALL_RTT : Nat := 4
abbrev STALL_RTT_CAP : Nat := 60 * NS
abbrev SLOW_RTT : Nat := 250 * MS
abbrev LIVE_CAP : Nat := 90 * NS
abbrev ASSUMED_RTT : Nat := NS
abbrev STEAL_IDLE : Nat := 2 * NS
abbrev REDIAL_DELAY : Nat := NS
abbrev OPEN_RETRY : Nat := 200 * MS
abbrev RESTREAM_DELAY : Nat := 500 * MS

/-- Unfold the constants of `knobs.rs` to numerals (for `omega`). -/
macro "ucs" : tactic => `(tactic| (try simp only [NS, MS, U64Max, GROUP, HOLD_B, HOLD_NV, HOLD_MAX, STALL_WAIT, STALL_CAP,
  ARK_PACE_CAP, BYTE_GAP_CAP, STALL_RTT, STALL_RTT_CAP, SLOW_RTT, LIVE_CAP, ASSUMED_RTT, STEAL_IDLE, REDIAL_DELAY,
  OPEN_RETRY, RESTREAM_DELAY] at *))

/-- `a.saturating_add(b)`. -/
def sadd (a b : Nat) : Nat := min (a + b) U64Max

/-- `a.saturating_mul(k)`. -/
def smul (a k : Nat) : Nat := min (a * k) U64Max

/-! ## The state and what the machine tells -/

/-- The first granule, verified and stored, not yet announced (`fetch::Head`). -/
structure Head where
  off : Nat
  len : Nat
  t0 : Nat
  deriving DecidableEq, Repr

/-- `trace::Release`. -/
inductive Cause where
  | buffered | tail | granules | timeout | done
  deriving DecidableEq, Repr

/-- `trace::FailReason`. -/
inductive Fail where
  | noProvider | lied | deadline | store | badRoot
  deriving DecidableEq, Repr

/-- The trace records and events of the time rules, in the order the code emits them. -/
inductive Ev where
  | verified (off len : Nat)
  | held (off : Nat)
  | released (off : Nat) (why : Cause)
  | readable (off len : Nat)
  | complete
  | failed (r : Fail)
  | redial (wait next : Nat)
  deriving DecidableEq, Repr

/-- What the session answers about an assigned provider (`PeerInfo`). -/
structure PeerInfo where
  rtt : Option Nat
  pto : Bool
  lastRx : Nat
  deriving DecidableEq, Repr

/-- An assigned provider as the stall rules see it: whether the fetch holds a session, and its `peer_info`. -/
structure Sess where
  conn : Bool
  info : Option PeerInfo
  deriving DecidableEq, Repr

/-- The fields of `Fetch` the time rules read or write. `want` is the aligned wanted ranges as intervals,
`store` the verified set, `trusted` the providers not yet evicted. -/
structure Fs where
  running : Bool
  sw : Nat
  lastp : Nat
  lastb : Nat
  treq : Nat
  tw : Nat
  rt : Option Nat
  head : Option Head
  rel : Bool
  nv : Nat
  deadline : Option Nat
  o0 : Nat
  striped : Bool
  trusted : Nat
  want : List Interval
  store : List Interval
  log : List Ev

/-- The state right after `Fetch::start` accepted the spec (`Fetch::new` plus the fields `start` sets). -/
def Fs.init (o0 : Nat) (want store : List Interval) (deadline : Option Nat) (striped : Bool) (trusted : Nat) : Fs :=
  { running := true, sw := STALL_WAIT, lastp := 0, lastb := 0, treq := 0, tw := 0, rt := none, head := none
    rel := false, nv := 0, deadline, o0, striped, trusted, want, store, log := [] }

/-- Append emitted records. -/
def Fs.emit (s : Fs) (es : List Ev) : Fs := { s with log := s.log ++ es }

/-- `want.missing(store).is_empty()`. -/
def Fs.wantedDone (s : Fs) : Bool := s.want.all (containsRange s.store)

/-- `want.total()`. -/
def Fs.tot (s : Fs) : Nat := coveredLen s.want

/-- The end of the wanted ranges in delivery order: the end of the last range of the list (`want.last().end()`). -/
def Fs.wend (s : Fs) : Nat := (s.want.getLast?.map (·.2)).getD 0

/-- The run of verified bytes that starts at `e`: `verified_from(e).filter(start <= e).map_or(0, end - e)`, where
`verified_from` is the first interval that ends after `e` (`store::verified_after`). -/
def bufOf (st : List Interval) (e : Nat) : Nat :=
  match st.find? (fun iv => decide (e < iv.2)) with
  | some iv => if iv.1 ≤ e then iv.2 - e else 0
  | none => 0

/-! ## HEAD_HOLD (`recv.rs`) -/

/-- The cause of the release of the held granule `h` at `now`, if any: `force`, else the first that holds of the
buffer, the tail, the granule count, the timeout (`hold_check`). -/
def holdWhy (s : Fs) (h : Head) (now : Nat) (force : Option Cause) : Option Cause :=
  match force with
  | some c => some c
  | none =>
    if HOLD_B ≤ bufOf s.store (h.off + h.len) then some .buffered
    else if s.wend ≤ h.off + h.len + bufOf s.store (h.off + h.len) then some .tail
    else if HOLD_NV ≤ s.nv then some .granules
    else if sadd h.t0 HOLD_MAX ≤ now then some .timeout
    else none

/-- `hold_check`: release the held granule if a cause holds: the `Released` trace, then the `Readable` event. -/
def holdCheck (s : Fs) (now : Nat) (force : Option Cause) : Fs :=
  match s.head with
  | none => s
  | some h =>
    match holdWhy s h now force with
    | none => s
    | some c => Fs.emit { s with head := none, rel := true } [.released h.off c, .readable h.off h.len]

/-- `check_done`: hold check, then, if nothing wanted is missing, the forced release and `Complete`. -/
def checkDone (s : Fs) (now : Nat) : Fs :=
  let s := if s.head.isSome then holdCheck s now none else s
  if s.wantedDone then
    let s := if s.head.isSome then holdCheck s now (some .done) else s
    Fs.emit { s with running := false } [.complete]
  else s

/-- `group_verified` for a group whose bytes are already written and committed: the `Verified` record, the capture
of the first granule or the immediate announcement of a later one, the hold check, the completion check. -/
def groupVerified (s : Fs) (now off len : Nat) : Fs :=
  let s := Fs.emit s [.verified off len]
  let s :=
    if !s.rel && off ≤ s.o0 && s.o0 < off + len then
      let t0 := match s.head with
        | some h => h.t0
        | none => now
      Fs.emit { s with head := some ⟨off, len, t0⟩, nv := 0 } [.held off]
    else
      let s := Fs.emit s [.readable off len]
      if s.head.isSome then holdCheck { s with nv := s.nv + 1 } now none else s
  checkDone s now

/-- A group another stream already stored (the race of two streams on one group) is neither written nor announced
again: only its `Verified` record and the completion check run. -/
def dupStep (s : Fs) (now off len : Nat) : Fs := checkDone (Fs.emit s [.verified off len]) now

/-- `store_group` then `group_verified`: commit `[off, off + len)` to the store, then announce; a group the store
already holds is a `dupStep`. -/
def verifyStep (s : Fs) (now off len : Nat) : Fs :=
  if containsRange s.store (off, off + len) then dupStep s now off len
  else groupVerified { s with store := insertVec s.store (off, off + len) } now off len

/-- A terminal failure: the fetch is done and the reason is the one event. -/
def failWith (s : Fs) (r : Fail) : Fs := Fs.emit { s with running := false } [.failed r]

/-! ## STALL_REDIAL (`recv.rs`, `stall.rs`) -/

/-- `arrival` (ARK_PACE): the stall timer follows the pace of completed frames. -/
def arrival (s : Fs) (now : Nat) : Fs :=
  if s.lastp ≠ 0 ∧ s.sw < smul (now - s.lastp) 3 then
    { s with sw := min ARK_PACE_CAP (smul (now - s.lastp) 3), lastp := now }
  else { s with lastp := now }

/-- BYTE_LIVE in `on_readable`: bytes arriving count as progress; the wait follows the burst gaps and the first-byte
delay. -/
def byteLive (s : Fs) (now : Nat) : Fs :=
  if s.lastb ≠ 0 then { s with sw := max s.sw (min BYTE_GAP_CAP (smul (now - s.lastb) 3)), lastb := now }
  else if s.treq ≠ 0 then { s with sw := max s.sw (min BYTE_GAP_CAP (smul (now - s.treq) 2)), lastb := now }
  else { s with lastb := now }

/-- STALL_RTT: at least four round trips of the slowest assigned session, capped. -/
def stallRtt (ss : List Sess) : Nat :=
  let r := ((ss.filterMap (fun p => p.info.bind (·.rtt))).filter (· ≠ 0)).foldl max 0
  min (smul r STALL_RTT) STALL_RTT_CAP

/-- The round trip `stall_live` uses for a session: its sample, or the assumed one when it has none. -/
def rttOf (i : PeerInfo) : Nat :=
  match i.rtt with
  | some r => if r ≠ 0 then r else ASSUMED_RTT
  | none => ASSUMED_RTT

/-- One assigned session in the loop of `stall_live`; `none` is the early `return 0`. -/
def liveStep (now lastp : Nat) (d : Option Nat) (p : Sess) : Option Nat :=
  match d with
  | none => none
  | some d =>
    match (if p.conn then p.info else none) with
    | none => none
    | some i =>
      let r := rttOf i
      if r < SLOW_RTT ∨ i.pto ∨ max (2 * NS) (smul r 2) < now - i.lastRx ∨ LIVE_CAP < now - lastp then none
      else some (max (max d (smul r 2)) STALL_WAIT)

/-- STALL_LIVE: 0, or the extra wait of a fetch whose every assigned session is slow but still receiving. -/
def stallLive (now lastp : Nat) (ss : List Sess) : Nat :=
  ((ss.foldl (liveStep now lastp) (some 0))).getD 0

/-- `stall_redial`: the wait is spent, the wait doubles up to STALL_CAP; the sessions are dropped and dialled again
(the environment). -/
def redial (s : Fs) (now : Nat) : Fs :=
  Fs.emit { s with lastp := now, sw := min (smul s.sw 2) STALL_CAP } [.redial s.sw (min (smul s.sw 2) STALL_CAP)]

/-- The later of the last verified granule and the first request. -/
def lastProg (s : Fs) : Nat := max s.lastp s.treq

/-- `stall_base`: the moment the stall wait counts from, the later of the last granule, the last stream bytes and the
first request (the timer runs once a request was sent). -/
def stallBase (s : Fs) : Nat := max (max s.lastp s.lastb) s.treq

/-- The first block of `on_timeout`. -/
def stallStep (s : Fs) (now : Nat) (ss : List Sess) : Fs :=
  if s.treq ≠ 0 ∧ sadd (stallBase s) s.sw ≤ now then
    if s.sw < stallRtt ss ∧ now < sadd (lastProg s) (stallRtt ss) then { s with sw := stallRtt ss }
    else if stallLive now (lastProg s) ss ≠ 0 then { s with sw := sadd (now - lastProg s) (stallLive now (lastProg s) ss) }
    else redial s now
  else s

/-- The timers `poll_timeout` takes the minimum of: the stall timer once a request was sent, the hold timer, the steal
re-check, the deadline plus one, the retries. -/
def pollList (s : Fs) : List Nat :=
  (if s.treq ≠ 0 then [sadd (stallBase s) s.sw] else []) ++
    (s.head.map (fun h => sadd h.t0 HOLD_MAX)).toList ++ (if s.tw ≠ 0 then [s.tw] else []) ++
    (s.deadline.map (fun d => sadd d 1)).toList ++ s.rt.toList

/-- `poll_timeout`: the next time `on_timeout` has something to do; `none` when the fetch is done or arms nothing. -/
def pollTimeout (s : Fs) : Option Nat := if s.running then (pollList s).min? else none

/-- Whether `now` is past the deadline. -/
def Fs.late (s : Fs) (now : Nat) : Bool :=
  match s.deadline with
  | some d => decide (d < now)
  | none => false

/-- The stall block of `on_timeout`; past the deadline the call only winds the fetch down, so it is skipped. -/
def lateStall (s : Fs) (now : Nat) (ss : List Sess) : Fs := if s.late now then s else stallStep s now ss

/-- The head block: hold check, completion check. -/
def headBlock (s : Fs) (now : Nat) : Fs := if s.head.isSome then checkDone (holdCheck s now none) now else s

/-- The steal re-check: the timer is spent (and armed again when the top-ups found nothing to steal). -/
def stealBlock (s : Fs) (now : Nat) (late rearm : Bool) : Fs :=
  if !late && s.striped && s.tw ≠ 0 && s.tw ≤ now then { s with tw := if rearm then now + STEAL_IDLE / 2 else 0 }
  else s

/-- The due retries: their timer is spent (and armed again when a request could not be opened). -/
def retryBlock (s : Fs) (now : Nat) (rt' : Option Nat) : Fs :=
  match s.rt with
  | some t => if t ≤ now then { s with rt := rt' } else s
  | none => s

/-- `on_timeout` at `now`, in the order of the code: the stall block, the head block, the steal re-check, the
deadline, the retries. `ss` are the assigned sessions at the call, `rearm` whether the re-check armed the steal timer
again, `rt'` the retry timer after the due retries were sent. -/
def onTimeout (s : Fs) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat) : Fs :=
  if s.running then
    let s1 := headBlock (lateStall s now ss) now
    if s1.running then
      let s2 := stealBlock s1 now (s.late now) rearm
      if s.late now then failWith s2 .deadline else retryBlock s2 now rt'
    else s1
  else s

/-! ## Inputs and runs -/

/-- The inputs that reach the time rules. A `frame` is one completed frame of a request stream (`b`: the bytes that
completed it arrived in this call), matched with the group `g` or skipped as already stored. -/
inductive Inp where
  | bytes (now : Nat)
  | frame (now : Nat) (b : Bool) (g : Option (Nat × Nat))
  | frameStoreFail (now : Nat) (b : Bool)
  | ahead (now off len : Nat)
  | aheadStoreFail (now : Nat)
  | evict (now : Nat) (b : Bool)
  | streamEnd (now : Nat)
  | arm (tw : Nat) (rt : Option Nat) (treq : Nat)
  | timeout (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat)

/-- One input; a fetch that is not running ignores every input (`on_event`, `on_timeout`). -/
def step (s : Fs) (i : Inp) : Fs :=
  if s.running then
    match i with
    | .bytes now => byteLive s now
    | .frame now b g =>
      let s := arrival (if b then byteLive s now else s) now
      match g with
      | none => s
      | some (o, l) => verifyStep s now o l
    | .frameStoreFail now b => failWith (arrival (if b then byteLive s now else s) now) .store
    | .ahead now o l => verifyStep s now o l
    | .aheadStoreFail now => failWith s .store
    | .evict now b =>
      let s := if b then byteLive s now else s
      if s.trusted ≤ 1 then failWith { s with trusted := 0 } .lied else { s with trusted := s.trusted - 1 }
    | .streamEnd now => checkDone s now
    | .arm tw rt treq => { s with tw, rt, treq }
    | .timeout now ss rearm rt' => onTimeout s now ss rearm rt'
  else s

/-- A group that no earlier verification overlapped: nonempty and disjoint from every group verified before. -/
def Fresh (s : Fs) (off len : Nat) : Prop :=
  0 < len ∧ ∀ o l, Ev.verified o l ∈ s.log → o + l ≤ off ∨ off + len ≤ o

/-- A group fed to the receive path must be nonempty and, against every group verified before, either disjoint or
the same group (two streams may carry one group), and a group the store holds must have been verified by this fetch
(the skip of stored frames in `Rx` decides this before the bytes are hashed). -/
def GroupOk (s : Fs) (off len : Nat) : Prop :=
  0 < len ∧ (∀ o l, Ev.verified o l ∈ s.log → o + l ≤ off ∨ off + len ≤ o ∨ (o = off ∧ l = len)) ∧
    (containsRange s.store (off, off + len) = true → Ev.verified off len ∈ s.log)

/-- The inputs the environment may give in state `s`. -/
def Valid (s : Fs) : Inp → Prop
  | .frame _ _ (some (o, l)) => GroupOk s o l
  | .ahead _ o l => GroupOk s o l
  | _ => True

/-- The states reachable from `s0` by valid inputs. -/
inductive Reach (s0 : Fs) : Fs → Prop where
  | init : Reach s0 s0
  | step {s : Fs} (i : Inp) : Reach s0 s → Valid s i → Reach s0 (step s i)

/-! ## The start of a fetch (`Fetch::start`) -/

/-- The outcome of `start` for a spec with `n` providers whose wanted bytes are `want`, over a store: the check order
of the code (bad root, nothing missing, no provider). -/
def startFetch (length : Nat) (emptyRoot : Bool) (n : Nat) (want store : List Interval) : Option Ev :=
  if length = 0 ∧ !emptyRoot then some (.failed .badRoot)
  else if want.all (containsRange store) then some .complete
  else if n = 0 then some (.failed .noProvider)
  else none

end Vinc.ValuesTime
