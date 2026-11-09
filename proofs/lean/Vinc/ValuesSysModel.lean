/-!
# The multi-provider value fetch as a system

The Lean counterpart of `proofs/tla/ValuesSys.tla` and `ValuesSysCore.tla`: the state machine of `vinc-values`
`fetch/{mod,sched,recv,rx,wt,stall}.rs` at the granularity of whole groups, driven by an adversary (any provider in
`Cfg.liars` may send any frame, the network delivers in any order). Hashing is symbolic and collision free, as in
`RangeVerifier.tla`: a frame has a `Kind`, and a group hashes to the root exactly when its data is genuine.

What is modelled exactly (every constructor of `Step` is an action of the TLA+ model):

* the store: a group is written (`wr`) and then committed (`ver`) in two steps, so a restart can fall between them;
  a refusal of either ends the fetch with `Store`;
* the events: `Readable` of a verified group, the held first granule (HEAD_HOLD), `Complete`, `Failed(reason)`, and
  the final event, which is emitted once and after which nothing is emitted;
* the liars: a provider whose frame fails verification in the order parse (`evict`) leaves the candidates, loses its
  share to the queue, and when no candidate is left the fetch fails with `EveryProviderLied`;
* the in-order parse and the write-through path (`accept`, `acceptAhead`): a group enters the store only when its
  frame verifies against the root, from a provider that is still a candidate, for a group that was requested;
* the deadline, the restart (the committed set survives, a new fetch starts from it) and the start (BadRoot, Complete
  when nothing is missing, NoProvider, else the work goes to the queue).

What is abstracted, as the brief asks: the scheduling (top-up, steal, request, dial, retry, stall redial, timers) is
the single constructor `plumb`: any change of the scheduling fields (`queue`, `asg`, `reqd`, `rx`...) that keeps what
`sched.rs` guarantees (`PlumbOk`: whole groups, never a verified group requested, the missing work stays queued or
assigned, nobody but the candidates holds work). The queue arithmetic is `ValuesSched`, the timing is `ValuesTime`;
the TLC model `ValuesSys.tla` keeps the triggers and the order of the scheduling steps exactly and checks the
progress of the whole machine (two stuck states of the code were found there and fixed).

Sets of groups are `Nat → Bool`.
-/

namespace Vinc.ValuesSys
open Classical

/-- A set of groups. -/
abbrev GSet := Nat → Bool

/-- The set with `g` added. -/
def ins (a : GSet) (g : Nat) : GSet := fun x => a x || decide (x = g)

/-- `a \ b`. -/
def dif (a b : GSet) : GSet := fun x => a x && !b x

/-- `a ⊆ b`. -/
def Sub (a b : GSet) : Prop := ∀ g, a g = true → b g = true

/-- The empty set. -/
def emp : GSet := fun _ => false

/-- What a store holds for a group. -/
inductive Wr where
  | none | good | junk
  deriving DecidableEq

/-- The frames the adversary can send for a group. `band`: genuine data with a wrong in-band proof or header. -/
inductive Kind where
  | good | band | junk
  deriving DecidableEq

/-- Whether the group hashes to the root: collision freedom says this is exactly genuine data. -/
def Kind.verifies : Kind → Bool
  | .good => true
  | .band => true
  | .junk => false

/-- The bytes a frame carries. -/
def Kind.content : Kind → Wr
  | .good => .good
  | .band => .good
  | .junk => .junk

/-- Collision freedom: the data of a frame that hashes to the root is the true data. -/
theorem Kind.verifies_genuine (k : Kind) (h : k.verifies = true) : k.content = .good := by
  cases k <;> simp_all [Kind.verifies, Kind.content]

/-- The final events. -/
inductive Final where
  | complete | deadline | everyProviderLied | noProvider | store | badRoot
  deriving DecidableEq

inductive Run where
  | idle | running | done
  deriving DecidableEq

/-- The scenario: the constants of the TLA+ model. -/
structure Cfg where
  /-- The number of groups of the value. -/
  g : Nat
  /-- The wanted groups. -/
  want : GSet
  /-- The group that holds the first requested byte. -/
  head0 : Nat
  /-- The groups the store has verified at the start. -/
  initVer : GSet
  /-- The providers the fetch names (at most four). -/
  listed : Nat → Bool
  /-- The value has length 0. -/
  empty : Bool
  /-- The root is the hash of the empty value. -/
  rootOk : Bool
  /-- The providers that may send bad frames. -/
  liars : Nat → Bool
  /-- The store may refuse a write or a commit. -/
  storeFail : Bool
  /-- The deadline in ticks, if any. -/
  deadline : Option Nat

/-- A verified group on its way into the store: `committing` once written. -/
structure Pd where
  g : Nat
  c : Wr
  committing : Bool

structure St where
  run : Run
  fin : Option Final
  nfin : Nat
  late : Nat
  /-- Readable events per group (capped). -/
  ann : Nat → Nat
  /-- What the store holds. -/
  wr : Nat → Wr
  /-- The committed (verified) groups. -/
  ver : GSet
  /-- The committed groups when the fetch started. -/
  ver0 : GSet
  /-- The groups asked for since the start. -/
  reqd : GSet
  /-- The providers that sent a bad frame. -/
  lied : Nat → Bool
  /-- The held first granule. -/
  hd : Option Nat
  rel : Bool
  inP : Nat → Bool
  inA : Nat → Bool
  asg : Nat → GSet
  queue : GSet
  now : Nat
  pd : Option Pd
  rs : Nat

/-- The state before the first fetch: the store holds `initVer`. -/
def init (c : Cfg) (rs : Nat) : St where
  run := .idle
  fin := none
  nfin := 0
  late := 0
  ann := fun _ => 0
  wr := fun g => if c.initVer g then .good else .none
  ver := c.initVer
  ver0 := c.initVer
  reqd := emp
  lied := fun _ => false
  hd := none
  rel := false
  inP := fun _ => false
  inA := fun _ => false
  asg := fun _ => emp
  queue := emp
  now := 0
  pd := none
  rs := rs

/-- The final event: once, and an event emitted after it is counted in `late`. -/
def finish (s : St) (f : Final) : St :=
  { s with run := .done, fin := some f, nfin := s.nfin + 1, late := s.late + (if s.run = .done then 1 else 0),
           pd := none }

/-- A `Readable` event for `g`. -/
def readable (s : St) (g : Nat) : St :=
  { s with ann := fun x => if x = g then min 2 (s.ann g + 1) else s.ann x,
           late := s.late + (if s.run = .done then 1 else 0) }

/-- The held first granule is announced. -/
def releaseHd (s : St) : St :=
  match s.hd with
  | none => s
  | some g => { readable s g with hd := none, rel := true }

/-- The candidate `p` leaves, with its share; it never holds work again (`sched.rs` evict, first part). -/
def evict1 (s : St) (p : Nat) : St :=
  { s with inP := fun q => if q = p then false else s.inP q,
           inA := fun q => if q = p then false else s.inA q,
           asg := fun q => if q = p then emp else s.asg q,
           lied := fun q => if q = p then true else s.lied q }

/-- When nobody holds a share any more the candidates all do. -/
noncomputable def evict2 (s : St) (p : Nat) : St :=
  if (∀ q, (evict1 s p).inA q = false) then { evict1 s p with inA := (evict1 s p).inP } else evict1 s p

/-- The books after an eviction: the missing share of `p` is back in the queue. -/
noncomputable def evictBooks (s : St) (p : Nat) : St :=
  { evict2 s p with queue := fun x => (evict2 s p).queue x || dif (s.asg p) s.ver x }

/-- The eviction of the liar `p` (`sched.rs` evict): with no candidate left the fetch fails. -/
noncomputable def evictSt (s : St) (p : Nat) : St :=
  if (∀ q, (evict2 s p).inA q = false) then finish (evict2 s p) .everyProviderLied else evictBooks s p

/-- What `plumb` may do: the scheduling step of the machine. It leaves the store, the events and the candidates
alone; asks only for missing wanted groups; keeps every missing wanted group queued or assigned to a provider that
holds a share; gives work only to such providers; and never hands a verified group to two owners. -/
structure PlumbOk (c : Cfg) (s : St) (q : GSet) (a : Nat → GSet) (r : GSet) : Prop where
  asks : ∀ g, r g = true → s.reqd g = true ∨ (c.want g = true ∧ s.ver g = false)
  grows : ∀ g, s.reqd g = true → r g = true
  conserved : ∀ g, c.want g = true → s.ver g = false → q g = true ∨ ∃ p, s.inA p = true ∧ a p g = true
  holders : ∀ p, s.inA p = false → a p = emp ∨ (∀ g, a p g = true → s.ver g = true)

/-- The commit of a verified group: the first granule is held back, any other group is announced. -/
def commitSt (c : Cfg) (s : St) (g : Nat) : St :=
  if (({ s with ver := ins s.ver g, pd := none } : St).rel = false ∧ g = c.head0) then
    { { s with ver := ins s.ver g, pd := none } with hd := some g }
  else readable { s with ver := ins s.ver g, pd := none } g

/-- One step of the system. -/
inductive Step (c : Cfg) : St → St → Prop where
  /-- Start with a wrong root for the empty value. -/
  | startBadRoot (s : St) :
      s.run = .idle → c.empty = true → c.rootOk = false →
      Step c s (finish { s with run := .running, ver0 := s.ver, reqd := emp, inP := c.listed } .badRoot)
  /-- Start with nothing missing. -/
  | startComplete (s : St) :
      s.run = .idle → ¬ (c.empty = true ∧ c.rootOk = false) → (∀ g, c.want g = true → s.ver g = true) →
      Step c s (finish { s with run := .running, ver0 := s.ver, reqd := emp, inP := c.listed } .complete)
  /-- Start with no provider named. -/
  | startNoProvider (s : St) :
      s.run = .idle → ¬ (c.empty = true ∧ c.rootOk = false) → (∃ g, c.want g = true ∧ s.ver g = false) →
      (∀ p, c.listed p = false) →
      Step c s (finish { s with run := .running, ver0 := s.ver, reqd := emp, inP := c.listed } .noProvider)
  /-- Start: the missing work goes to the queue, the named providers are the candidates and hold a share. -/
  | begin (s : St) :
      s.run = .idle → ¬ (c.empty = true ∧ c.rootOk = false) → (∃ g, c.want g = true ∧ s.ver g = false) →
      (∃ p, c.listed p = true) →
      Step c s { s with run := .running, ver0 := s.ver, reqd := emp, inP := c.listed, inA := c.listed,
                        queue := dif c.want s.ver, asg := fun _ => emp }
  /-- Scheduling (abstracted, see `PlumbOk`). -/
  | plumb (s : St) (q : GSet) (a : Nat → GSet) (r : GSet) :
      s.run = .running → s.pd = none → PlumbOk c s q a r → Step c s { s with queue := q, asg := a, reqd := r }
  /-- The in-order parse of a frame whose data verifies, for a group not stored yet: write it. -/
  | accept (s : St) (p g : Nat) (k : Kind) :
      s.run = .running → s.pd = none → s.inP p = true → s.reqd g = true → c.want g = true →
      s.ver g = false → k.verifies = true →
      Step c s { s with pd := some { g := g, c := k.content, committing := false } }
  /-- The in-order parse of a frame for a group the store already has: skipped, not stored again. -/
  | skip (s : St) (p g : Nat) :
      s.run = .running → s.pd = none → s.inP p = true → s.reqd g = true → s.ver g = true → Step c s s
  /-- Write-through: an out-of-order frame with a covering good range proof verifies, and is written at once. -/
  | acceptAhead (s : St) (p g : Nat) (k : Kind) :
      s.run = .running → s.pd = none → s.inP p = true → s.reqd g = true → c.want g = true →
      s.ver g = false → k.verifies = true →
      Step c s { s with pd := some { g := g, c := k.content, committing := false } }
  /-- A provider sends a bad frame in the order parse (a failed hash, a wrong header, bytes after the last range). -/
  | evict (s : St) (p : Nat) :
      s.run = .running → s.pd = none → s.inP p = true → c.liars p = true → Step c s (evictSt s p)
  /-- `write_at`. -/
  | write (s : St) (d : Pd) :
      s.run = .running → s.pd = some d → d.committing = false →
      Step c s { s with wr := fun x => if x = d.g then d.c else s.wr x, pd := some { d with committing := true } }
  /-- `write_at` refused. -/
  | writeRefused (s : St) (d : Pd) :
      s.run = .running → s.pd = some d → d.committing = false → c.storeFail = true →
      Step c s (finish s .store)
  /-- `commit`: the group is verified; the first granule is held, any other is announced. -/
  | commit (s : St) (d : Pd) :
      s.run = .running → s.pd = some d → d.committing = true → Step c s (commitSt c s d.g)
  /-- `commit` refused. -/
  | commitRefused (s : St) (d : Pd) :
      s.run = .running → s.pd = some d → d.committing = true → c.storeFail = true →
      Step c s (finish s .store)
  /-- HEAD_HOLD: the first granule is announced. -/
  | release (s : St) :
      s.run = .running → s.pd = none → (∃ g, s.hd = some g) → Step c s (releaseHd s)
  /-- `check_done`: nothing wanted is missing. -/
  | check (s : St) :
      s.run = .running → s.pd = none → (∀ g, c.want g = true → s.ver g = true) →
      Step c s (finish (releaseHd s) .complete)
  /-- Time passes. -/
  | tick (s : St) :
      s.run = .running → s.pd = none → Step c s { s with now := s.now + 1 }
  /-- The deadline passed. -/
  | deadlineFire (s : St) (d : Nat) :
      s.run = .running → s.pd = none → c.deadline = some d → d < s.now → Step c s (finish s .deadline)
  /-- The process restarts: the committed set and the bytes written survive, a new fetch can start. -/
  | restart (s : St) :
      s.run ≠ .idle → 0 < s.rs →
      Step c s { (init c (s.rs - 1)) with wr := s.wr, ver := s.ver, ver0 := s.ver }

/-- The behaviours: everything reachable from the initial state. -/
inductive Reach (c : Cfg) (rs : Nat) : St → Prop where
  | init : Reach c rs (init c rs)
  | step (s s' : St) : Reach c rs s → Step c s s' → Reach c rs s'

end Vinc.ValuesSys
