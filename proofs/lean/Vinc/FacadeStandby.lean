/-!
# The facade's standby slab: the model

A model of `crates/vinc/src/standby.rs` (`Standby`), as `proofs/tla/StandbyOps.tla` has it, over unbounded `Nat`:
the slab of tickets of the facade futures that wait, and the queue of those waiting for the driving role. A ticket is
a slot and the slot's generation; a slot keeps the waker of the future that holds it, whether it is queued, and
whether a future holds it; the queue holds tickets. `alloc` takes the slot on top of the free stack (the head of
`free`, the last element of the code's `Vec`) or pushes a new one; `arm` keeps a waker and, unless the slot is
queued, queues the ticket at the back, first dropping the stale entries (`compact`) when the queue holds twice as
many entries as the slab has slots; `notify` takes and wakes one ticket's waker; `baton` pops the queue up to the
first entry whose ticket is live and armed and wakes it, dropping stale entries and unqueuing the slots of live ones;
`notifyAll` wakes every live armed slot in slot order; `release` ends the slot's life, unqueues it, moves its
generation on (`wrapping_add` on a `u32`: modulo `2^32`) and pushes it on the free stack, leaving the ticket's entry
in the queue, stale, except that the release that brings the slot's generation round (from `2^32 - 1` to 0) drops
every stale entry (`wrapQueue`, the fix of #419). Every call that wakes returns the wakers woken, in order. `alloc`
names a new slot by the slab's length, as the code does while it has fewer than `2^32` slots.

Beside the slab, `Op.order` keeps the documented order of the baton: the tickets waiting for the role in the order
they were queued (`orderWoken` is what that order says the baton wakes). `Op.revives` is an `alloc` that hands out a
ticket a stale entry of the queue still names, which the drop at the wrap rules out (`exec_norevive`).

`Vinc.TraceFacadeStandby` replays the recorded calls of the real code through these functions; the theorems are in
`Vinc.FacadeStandbyThm` (the slab) and `Vinc.FacadeStandbyOrder` (the queue and the baton's order), and
`Vinc.FacadeTurn` runs them inside the drive's turn.
-/

namespace Vinc.FacadeStandby

/-- The number of generations: the code's `u32` wraps. -/
def GENS : Nat := 4294967296

structure Slot where
  gen : Nat
  waker : Option Nat
  queued : Bool
  live : Bool
  deriving DecidableEq, Repr

structure Ticket where
  idx : Nat
  gen : Nat
  deriving DecidableEq, Repr

structure S where
  slots : List Slot := []
  /-- The free stack, top first. -/
  free : List Nat := []
  /-- The queue of tickets, front first. -/
  queue : List Ticket := []
  deriving DecidableEq, Repr

def newSlot : Slot := ⟨0, none, false, true⟩

/-- The slot a ticket names among `slots`, if it is live and has the ticket's generation (`Standby::slot`). -/
def slotAt (slots : List Slot) (t : Ticket) : Option Slot :=
  match slots[t.idx]? with
  | some sl => if sl.live = true ∧ sl.gen = t.gen then some sl else none
  | none => none

def slotOf (s : S) (t : Ticket) : Option Slot := slotAt s.slots t

/-- The ticket names a live slot of its generation. -/
def valid (slots : List Slot) (t : Ticket) : Bool := (slotAt slots t).isSome

/-- The waker kept for a live ticket. -/
def wakerAt (slots : List Slot) (t : Ticket) : Option Nat := (slotAt slots t).bind Slot.waker

def alloc (s : S) : Ticket × S :=
  match s.free with
  | i :: rest =>
    match s.slots[i]? with
    | some sl => (⟨i, sl.gen⟩, { s with free := rest, slots := s.slots.set i { sl with live := true } })
    | none => (⟨s.slots.length, 0⟩, { s with free := rest, slots := s.slots ++ [newSlot] })
  | [] => (⟨s.slots.length, 0⟩, { s with slots := s.slots ++ [newSlot] })

/-- The queue `arm` appends to: the live entries only (`drop_stale`) when it holds twice as many entries as the slab
has slots. -/
def compact (s : S) : List Ticket :=
  if 2 * s.slots.length ≤ s.queue.length then s.queue.filter (valid s.slots) else s.queue

def arm (t : Ticket) (w : Nat) (s : S) : S :=
  match slotOf s t with
  | none => s
  | some sl =>
    if sl.queued then { s with slots := s.slots.set t.idx { sl with waker := some w } }
    else { s with slots := s.slots.set t.idx { sl with waker := some w, queued := true }, queue := compact s ++ [t] }

def notify (t : Ticket) (s : S) : List Nat × S :=
  match slotOf s t with
  | none => ([], s)
  | some sl =>
    match sl.waker with
    | none => ([], s)
    | some w => ([w], { s with slots := s.slots.set t.idx { sl with waker := none } })

/-- The loop of `baton` over the queue: a stale entry is dropped; the slot of a live one is no longer queued, and the
first live one with a waker gives it up and is woken, and the loop ends. Returns the wakers woken, the slots and what
is left of the queue. -/
def batonGo (slots : List Slot) : List Ticket → List Nat × List Slot × List Ticket
  | [] => ([], slots, [])
  | t :: rest =>
    match slotAt slots t with
    | none => batonGo slots rest
    | some sl =>
      match sl.waker with
      | some w => ([w], slots.set t.idx { sl with queued := false, waker := none }, rest)
      | none => batonGo (slots.set t.idx { sl with queued := false }) rest

def baton (s : S) : List Nat × S :=
  match batonGo s.slots s.queue with
  | (w, slots, q) => (w, { s with slots := slots, queue := q })

/-- The waker a slot gives up to `notify_all`. -/
def armedW (sl : Slot) : Option Nat := if sl.live then sl.waker else none

def notifyAll (s : S) : List Nat × S :=
  (s.slots.filterMap armedW,
   { s with slots := s.slots.map fun sl => if sl.live then { sl with waker := none } else sl })

/-- The queue a release of a slot of generation `g` leaves, with `slots` the slots after it: the live entries only
(`drop_stale`) when the release brings the generation round (`g` is `u32::MAX`), the queue as it was otherwise. -/
def wrapQueue (g : Nat) (slots : List Slot) (q : List Ticket) : List Ticket :=
  if g + 1 = GENS then q.filter (valid slots) else q

def release (t : Ticket) (s : S) : S :=
  match slotOf s t with
  | none => s
  | some sl =>
    { s with slots := s.slots.set t.idx
               { sl with live := false, gen := (sl.gen + 1) % GENS, waker := none, queued := false },
             free := t.idx :: s.free,
             queue := wrapQueue sl.gen (s.slots.set t.idx
               { sl with live := false, gen := (sl.gen + 1) % GENS, waker := none, queued := false }) s.queue }

/-- The calls, for runs of them. -/
inductive Op where
  | alloc
  | arm (t : Ticket) (w : Nat)
  | notify (t : Ticket)
  | baton
  | notifyAll
  | release (t : Ticket)
  deriving DecidableEq, Repr

def Op.run : Op → S → S
  | .alloc, s => (FacadeStandby.alloc s).2
  | .arm t w, s => FacadeStandby.arm t w s
  | .notify t, s => (FacadeStandby.notify t s).2
  | .baton, s => (FacadeStandby.baton s).2
  | .notifyAll, s => (FacadeStandby.notifyAll s).2
  | .release t, s => FacadeStandby.release t s

def exec : List Op → S → S
  | [], s => s
  | o :: os, s => exec os (o.run s)

def liveCount (s : S) : Nat := (s.slots.filter (·.live)).length

/-! ## The documented order -/

/-- What the documented order `o` says the baton wakes: the waker of its first ticket that is live and armed. -/
def orderWoken (slots : List Slot) : List Ticket → List Nat
  | [] => []
  | t :: rest =>
    match wakerAt slots t with
    | some w => [w]
    | none => orderWoken slots rest

/-- The order after the baton: the tickets after the first one that is live and armed (none, when no ticket is). -/
def orderAfter (slots : List Slot) : List Ticket → List Ticket
  | [] => []
  | t :: rest => if (wakerAt slots t).isSome then rest else orderAfter slots rest

/-- The documented order through a call: `arm` appends a live ticket that is not in it, `release` takes its ticket
out, and the baton offers the role to the first ticket that is armed, which leaves the order with every ticket before
it. -/
def Op.order : Op → S → List Ticket → List Ticket
  | .arm t _, s, o => if valid s.slots t = true ∧ t ∉ o then o ++ [t] else o
  | .baton, s, o => orderAfter s.slots o
  | .release t, s, o => if valid s.slots t = true then o.filter (fun u => decide (u ≠ t)) else o
  | _, _, o => o

/-- A run with the documented order beside the slab. -/
def execO : List Op → S → List Ticket → S × List Ticket
  | [], s, o => (s, o)
  | op :: os, s, o => execO os (op.run s) (op.order s o)

/-- An `alloc` that hands out a ticket an entry of the queue still names: that stale entry names a live slot again. -/
def Op.revives : Op → S → Prop
  | .alloc, s => (FacadeStandby.alloc s).1 ∈ s.queue
  | _, _ => False

/-- No call of the run revives a stale entry. -/
def NoRevive : List Op → S → Prop
  | [], _ => True
  | o :: os, s => ¬o.revives s ∧ NoRevive os (o.run s)

end Vinc.FacadeStandby
