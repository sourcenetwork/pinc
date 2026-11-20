/-!
# The node's own record and address discovery

The client side of `pinc-connect` as total functions over unbounded `Nat`, step for step the operators of
`proofs/tla/ConnectOwnOps.tla`: `Connectivity::{set_local, set_hints, probe_all, candidates, tick}`, the QADR arm of
`handle_udp` with `Netcheck::{probe_sent, answered, reflexive_into, restart}`, and `publish`, `start_jobs`,
`record_job` and the record arm of `sign_response` (`client/signing.rs`, `client/timers.rs`), and
`Connectivity::restore_record_seq`. The theorems are in `ConnectOwnThm.lean`; the trace replay is
`TraceConnectOwn.lean`.

An address is a natural, a relay is its position in the configuration (0-based here), `udp[k]` its configured UDP
address (0: it takes none), a nonce is a natural (an `Option`: the code's nonce `[0; 8]` is as good as any). The home
relay and the reachability class are inputs of `record_job` (`client/conn.rs` computes them: `ConnectClient.lean`).
Time is in nanoseconds, as in the code; `wall` is the wall clock of the last tick that had one, in milliseconds, and
`last` the sequence number of the last record built (`last_seq`, raised by `restore_record_seq`).

Seams, stated: the signature is the host's (a job is signed or it fails: `signed` takes the outcome); the carrier is a
Boolean, whether `frame_to` could send the record; sleep notices and beacons share the one signing slot in the code
and are left out (they only delay a record job: `start` does nothing while a job is outstanding); the node holds no
port mapping (`set_mapped`: a mapped address a relay vouches for would lead the list, `mapped.rs`, tests only).
-/

namespace Pinc.ConnectOwn

/-- `RECORD_REPUBLISH_NS` and `HOME_RETRY_NS`; `u64::MAX`. -/
def repub : Nat := 1800 * 1000000000
def retry : Nat := 2 * 1000000000
def uMax : Nat := 2 ^ 64 - 1

/-- `saturating_add` on `u64`. -/
def sadd (a b : Nat) : Nat := min (a + b) uMax

structure Cf where
  cap : Nat
  udp : List Nat

/-- The record job: what `record_job` writes (the signature is the host's). -/
structure Rec where
  seq : Nat
  home : Nat
  reach : Nat
  addrs : List Nat
  hints : List Nat
  deriving DecidableEq, Repr

structure St where
  probe : List (Option Nat)
  refl : List (Option Nat)
  loc : List Nat := []
  wall : Option Nat := none
  /-- `last_seq`, the number of the last record built (0 before the first) -/
  last : Nat := 0
  hints : List Nat := []
  /-- `next_publish` -/
  np : Nat := 0
  /-- `sign.record`, the record is wanted -/
  want : Bool := false
  /-- the record job outstanding, if the signing slot holds one -/
  job : Option Rec := none
  /-- the record last handed to the home carrier -/
  sent : Option Rec := none

def St.new (cf : Cf) : St := { probe := cf.udp.map fun _ => none, refl := cf.udp.map fun _ => none }

/-- `set_local`: the first `cap` addresses. -/
def setLocal (cf : Cf) (s : St) (addrs : List Nat) : St := { s with loc := addrs.take cf.cap }

/-- `probe_all`: a probe with a fresh nonce to every relay that takes UDP (`ns[k]` is the nonce of the probe that was
queued for relay `k`, none if none was). -/
def probeAll (cf : Cf) (s : St) (ns : List (Option Nat)) : St :=
  { s with probe := (List.range cf.udp.length).map fun k =>
      if cf.udp.getD k 0 ≠ 0 then
        (match ns.getD k none with
         | some n => some n
         | none => s.probe.getD k none)
      else s.probe.getD k none }

/-- The position of the first `x` in a list. -/
def firstIdx (x : Nat) : List Nat → Option Nat
  | [] => none
  | y :: l => if y = x then some 0 else (firstIdx x l).map (· + 1)

/-- `relay_by_udp`: the first relay whose configured UDP address is `from` (addresses are nonzero). -/
def relayAt (cf : Cf) (from_ : Nat) : Option Nat :=
  if from_ = 0 then none else firstIdx from_ cf.udp

/-- `handle_udp` for a QADR from `from_` with nonce `n` reporting `a`, and `Netcheck::answered`: taken only when the
sender is a configured relay address and the nonce is that of the relay's outstanding probe. -/
def observe (cf : Cf) (s : St) (from_ n a : Nat) : St × Bool :=
  match relayAt cf from_ with
  | none => (s, false)
  | some k =>
    if s.probe[k]? = some (some n) then
      ({ s with probe := s.probe.set k none, refl := s.refl.set k (some a) }, true)
    else (s, false)

/-- `Netcheck::restart` (`link_changed`). -/
def restart (s : St) : St :=
  { s with probe := s.probe.map fun _ => none, refl := s.refl.map fun _ => none }

/-- One step of the loops of `Netcheck::reflexive_into` and `Connectivity::candidates`: an address is written when
there is room and it is not listed yet. -/
def addNew (cap : Nat) (acc : List Nat) (a : Nat) : List Nat :=
  if acc.length < cap ∧ a ∉ acc then acc ++ [a] else acc

/-- `Netcheck::reflexive_into`: the distinct reflexive addresses in relay order (an address that several relays report
is listed once, at the first of them), as many as fit. -/
def reflList (cf : Cf) (s : St) : List Nat := (s.refl.filterMap id).foldl (addNew cf.cap) []

/-- `Connectivity::candidates`: the reflexive addresses first, then the local ones not yet there, up to `cap`. -/
def cands (cf : Cf) (s : St) : List Nat := s.loc.foldl (addNew cf.cap) (reflList cf s)

/-- `tick`: the wall clock is taken when it is given one. -/
def tick (s : St) (w : Option Nat) : St :=
  match w with
  | some x => { s with wall := some x }
  | none => s

/-- The number of a record built at the wall clock `w` after the one numbered `last`: the clock, or one above the last
when the clock did not move past it (`wall_ms.max(last_seq.saturating_add(1))`). -/
def nextSeq (w last : Nat) : Nat := max w (sadd last 1)

/-- `record_job`, called with the wall clock of the last tick: the record that is signed (none without a home, a
class or a wall clock). -/
def recordJob (cf : Cf) (s : St) (home cls : Option Nat) : Option Rec :=
  match home, cls, s.wall with
  | some h, some c, some w => some ⟨nextSeq w s.last, h, c, cands cf s, s.hints⟩
  | _, _, _ => none

/-- `restore_record_seq`: the last number is raised to `n`, never lowered. -/
def restoreSeq (s : St) (n : Nat) : St := { s with last := max s.last n }

/-- `set_hints` (the length check is the code's `MAX_HINT_LEN`; a refused call changes nothing): the hints and the
record wanted. -/
def setHints (s : St) (h : List Nat) : St := { s with hints := h, want := true }

/-- `publish`: ask for the record when it is due and the home carrier is open. -/
def publish (s : St) (now : Nat) (canPublish : Bool) : St :=
  if s.np = 0 ∨ s.np = uMax ∨ now < s.np ∨ s.want ∨ s.job.isSome then s
  else if canPublish then { s with want := true, np := uMax } else s

/-- The class or home changed, a carrier opened (`next_publish = now`). -/
def changed (s : St) (now : Nat) : St := { s with np := now }

/-- `start_jobs` for a record: nothing while a job is outstanding or before the first wall clock; a wanted record
starts a job and its number becomes the last one, or, when it cannot (no home or class), waits a retry period. -/
def start (cf : Cf) (s : St) (now : Nat) (home cls : Option Nat) : St :=
  if s.job.isSome then s
  else match s.wall with
    | none => s
    | some _ =>
      if s.want then
        match recordJob cf s home cls with
        | some j => { s with want := false, job := some j, last := j.seq }
        | none => { s with want := false, np := sadd now retry }
      else s

/-- The next publish once a record was handed to the carrier: the republish 1800 s on when nothing armed it while
the job was out (`np` is `0` or `uMax`, the code's `None`), else the deadline a change or a retry wrote then, which
wins (`complete`, the code fix K10 on top of K1's `Option`). -/
def afterSent (np now : Nat) : Nat := if np = 0 ∨ np = uMax then sadd now repub else np

theorem afterSent_disarmed {np : Nat} (now : Nat) (h : np = 0 ∨ np = uMax) : afterSent np now = sadd now repub := by
  unfold afterSent; exact if_pos h

theorem afterSent_kept {np : Nat} (now : Nat) (h0 : np ≠ 0) (hm : np ≠ uMax) : afterSent np now = np := by
  unfold afterSent; exact if_neg (fun h => h.elim h0 hm)

/-- `sign_response` for the record job: `ok` is a signature of the right length that `finish` accepted, `sent` that
`frame_to` put the record on the home carrier. A change made while the job was out is kept (`afterSent`). -/
def signed (s : St) (now : Nat) (ok sent : Bool) : St :=
  match s.job with
  | none => s
  | some j =>
    if ok then
      if sent then { s with job := none, sent := some j, np := afterSent s.np now }
      else { s with job := none, np := now }
    else { s with job := none, np := sadd now retry }

inductive Op
  | setLocal (a : List Nat)
  | probe (ns : List (Option Nat))
  | answer (from_ n a : Nat)
  | restart
  | tick (w : Option Nat)
  | hints (h : List Nat)
  | publish (now : Nat) (can : Bool)
  | changed (now : Nat)
  | start (now : Nat) (home cls : Option Nat)
  | signed (now : Nat) (ok sent : Bool)
  | restore (n : Nat)

def step (cf : Cf) (s : St) : Op → St
  | .setLocal a => setLocal cf s a
  | .probe ns => probeAll cf s ns
  | .answer f n a => (observe cf s f n a).1
  | .restart => restart s
  | .tick w => tick s w
  | .hints h => setHints s h
  | .publish now c => publish s now c
  | .changed now => changed s now
  | .start now h c => start cf s now h c
  | .signed now ok sent => signed s now ok sent
  | .restore n => restoreSeq s n

def run (cf : Cf) (s : St) (ops : List Op) : St := ops.foldl (step cf) s

end Pinc.ConnectOwn
