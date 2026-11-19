/-!
# The event queue: the model

A model of `pinc-core` `queue.rs` (`EventRing`), as `proofs/tla/QueueOps.tla` has it, over unbounded `Nat`: the
bounded ring of events waiting for the host. The ring is modelled as the code has it, a function from places to
events with a head and a length, so that the shift an eviction makes and the compaction a purge makes are the code's
own loops (the code's split of the places into a base and four rows of `K` is an addressing of `0 .. CAP - 1`, see
`Pinc.CoreQueueThm.place_inj`). An event is its place in the order of pushes (`id`), whether the application can
recover it by reading state (`lossy`), the session it names (`sess`, 0 for none) and whether it is that session's
`Closed`. `Pinc.TraceQueue` replays the recorded calls of the real code through these functions; the theorems are in
`Pinc.CoreQueueThm`.
-/

namespace Pinc.CoreQueue

structure E where
  id : Nat
  lossy : Bool
  sess : Nat
  closed : Bool
  deriving BEq, DecidableEq, Repr

abbrev Cells := Nat → Option E

/-- The ring: the cells, the place of the oldest event, how many are queued, how many of them are recoverable,
and the two counters. -/
structure R where
  cells : Cells := fun _ => none
  head : Nat := 0
  len : Nat := 0
  ll : Nat := 0
  dropped : Nat := 0
  lost : Nat := 0

def setC (c : Cells) (p : Nat) (v : Option E) : Cells := fun q => if q = p then v else c q

/-- The place of the `i`th queued event, counting from the oldest. -/
def at' (r : R) (cap i : Nat) : Nat := (r.head + i) % cap

def get (r : R) (cap i : Nat) : Option E := r.cells (at' r cap i)

def isLossy : Option E → Bool
  | some e => e.lossy
  | none => false

/-- The queued events, oldest first, as the cells hold them. -/
def view (r : R) (cap : Nat) : List (Option E) := (List.range r.len).map (get r cap)

/-- The place, counting from the oldest, of the oldest recoverable event. -/
def victim (r : R) (cap : Nat) : Option Nat := (List.range r.len).find? (fun i => isLossy (get r cap i))

/-- The shift of the eviction loop `for i in (0..victim).rev() { place i + 1 <- place i }`. -/
def shift (c : Cells) (head cap : Nat) : Nat → Cells
  | 0 => c
  | k + 1 => shift (setC c ((head + k + 1) % cap) (c ((head + k) % cap))) head cap k

/-- What that loop leaves, place by place (`Pinc.CoreQueueThm.shiftC_eq_shift` proves it for any size): the places
`1 .. v` counting from the head take the event of the place before, the others keep theirs. The eviction uses this
form, so that a long run of calls does not pile up a chain of updates (`proofs/tla/QueueOps.tla` has both and checks
them equal). -/
def shiftC (c : Cells) (head cap v : Nat) : Cells := fun p =>
  let j := (p + cap - head % cap) % cap
  if 1 ≤ j ∧ j ≤ v then c ((head + (j - 1)) % cap) else c p

def append (cap : Nat) (ev : E) (r : R) : R :=
  { r with
    cells := setC r.cells ((r.head + r.len) % cap) (some ev)
    len := r.len + 1
    ll := r.ll + (if ev.lossy then 1 else 0) }

/-- A full queue gives up one event: the oldest recoverable one, else (counted as lost) the oldest. -/
def evict (cap : Nat) (r : R) : R :=
  let v0 := victim r cap
  let v := v0.getD 0
  { r with
    cells := shiftC r.cells r.head cap v
    head := (r.head + 1) % cap
    len := r.len - 1
    ll := if isLossy (get r cap v) then r.ll - 1 else r.ll
    lost := r.lost + (if v0.isNone then 1 else 0) }

/-- `push`: a full queue counts a drop; it drops the new event if that is recoverable, else gives up one queued. -/
def push (cap : Nat) (ev : E) (r : R) : R :=
  if r.len = cap then
    let r1 := { r with dropped := r.dropped + 1 }
    if ev.lossy then r1 else append cap ev (evict cap r1)
  else append cap ev r

def pop (cap : Nat) (r : R) : Option E × R :=
  if r.len = 0 then (none, r)
  else
    let e := r.cells r.head
    (e, { r with
      cells := setC r.cells r.head none
      head := (r.head + 1) % cap
      len := r.len - 1
      ll := r.ll - (if isLossy e then 1 else 0) })

/-- What `purge` drops: the events that name the session, but its `Closed`. -/
def stale (s : Nat) (e : E) : Bool := e.sess == s && !e.closed

/-- The compaction loop of `purge`: event `i` is taken out of its place and, if it stays, written at place `kept`. -/
def purgeGo (cap head s : Nat) : Nat → Nat → Cells → Nat → Nat → Cells × Nat × Nat
  | 0, _, c, kept, ll => (c, kept, ll)
  | n + 1, i, c, kept, ll =>
    match c ((head + i) % cap) with
    | none => purgeGo cap head s n (i + 1) c kept ll
    | some ev =>
      let c1 := setC c ((head + i) % cap) none
      if stale s ev then purgeGo cap head s n (i + 1) c1 kept (ll - (if ev.lossy then 1 else 0))
      else purgeGo cap head s n (i + 1) (setC c1 ((head + kept) % cap) (some ev)) (kept + 1) ll

def purge (cap s : Nat) (r : R) : R :=
  let (c, kept, ll) := purgeGo cap r.head s r.len 0 r.cells 0 r.ll
  { r with cells := c, len := kept, ll }

/-- The queue holds, beside the headroom, no more unrecoverable events than it has places. -/
def stalled (cap h : Nat) (r : R) : Bool := decide (r.len - r.ll + h > cap)

/-- The places of the event queue for a table of `k` sessions. -/
def eventQueue (k : Nat) : Nat := 4 * k + 1024

/-- The places kept free of unrecoverable events. -/
def eventHeadroom (k : Nat) : Nat := 2 * k + 64

end Pinc.CoreQueue
