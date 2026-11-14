/-!
# The facade's standby slab: the model

A model of `crates/vinc/src/standby.rs` (`Standby`), as `proofs/tla/StandbyOps.tla` has it, over unbounded `Nat`:
the slab of tickets of the facade futures that wait, and the queue of those waiting for the driving role. A ticket is
a slot and the slot's generation; a slot keeps the waker of the future that holds it, whether it is queued, and
whether a future holds it. `alloc` takes the slot on top of the free stack (the head of `free`, the last element of
the code's `Vec`) or pushes a new one; `arm` keeps a waker and queues the slot unless it is queued; `notify` takes
and wakes one ticket's waker; `baton` pops the queue up to the first slot that is live and armed and wakes it;
`notifyAll` wakes every live armed slot in slot order; `release` ends the slot's life, moves its generation on
(`wrapping_add` on a `u32`: modulo `2^32`) and pushes it on the free stack, leaving the queue as it is. Every call
that wakes returns the wakers woken, in order. `alloc` names a new slot by the slab's length, as the code does while
it has fewer than `2^32` slots.

`Vinc.TraceFacadeStandby` replays the recorded calls of the real code through these functions; the theorems are in
`Vinc.FacadeStandbyThm`, and `Vinc.FacadeTurn` runs them inside the drive's turn.
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
  /-- The queue, front first. -/
  queue : List Nat := []
  deriving DecidableEq, Repr

def newSlot : Slot := ⟨0, none, false, true⟩

/-- The slot a ticket names, if it is live and has the ticket's generation (`Standby::slot`). -/
def slotOf (s : S) (t : Ticket) : Option Slot :=
  match s.slots[t.idx]? with
  | some sl => if sl.live = true ∧ sl.gen = t.gen then some sl else none
  | none => none

def alloc (s : S) : Ticket × S :=
  match s.free with
  | i :: rest =>
    match s.slots[i]? with
    | some sl => (⟨i, sl.gen⟩, { s with free := rest, slots := s.slots.set i { sl with live := true } })
    | none => (⟨s.slots.length, 0⟩, { s with free := rest, slots := s.slots ++ [newSlot] })
  | [] => (⟨s.slots.length, 0⟩, { s with slots := s.slots ++ [newSlot] })

def arm (t : Ticket) (w : Nat) (s : S) : S :=
  match slotOf s t with
  | none => s
  | some sl =>
    if sl.queued then { s with slots := s.slots.set t.idx { sl with waker := some w } }
    else { s with slots := s.slots.set t.idx { sl with waker := some w, queued := true }, queue := s.queue ++ [t.idx] }

def notify (t : Ticket) (s : S) : List Nat × S :=
  match slotOf s t with
  | none => ([], s)
  | some sl =>
    match sl.waker with
    | none => ([], s)
    | some w => ([w], { s with slots := s.slots.set t.idx { sl with waker := none } })

/-- The loop of `baton` over the queue: each slot popped is no longer queued; the first live one with a waker gives
it up and is woken, and the loop ends. Returns the wakers woken, the slots and what is left of the queue. -/
def batonGo (slots : List Slot) : List Nat → List Nat × List Slot × List Nat
  | [] => ([], slots, [])
  | i :: rest =>
    match slots[i]? with
    | none => batonGo slots rest
    | some sl =>
      match sl.live, sl.waker with
      | true, some w => ([w], slots.set i { sl with queued := false, waker := none }, rest)
      | _, _ => batonGo (slots.set i { sl with queued := false }) rest

def baton (s : S) : List Nat × S :=
  match batonGo s.slots s.queue with
  | (w, slots, q) => (w, { s with slots := slots, queue := q })

/-- The waker a slot gives up to `notify_all`. -/
def armedW (sl : Slot) : Option Nat := if sl.live then sl.waker else none

def notifyAll (s : S) : List Nat × S :=
  (s.slots.filterMap armedW,
   { s with slots := s.slots.map fun sl => if sl.live then { sl with waker := none } else sl })

def release (t : Ticket) (s : S) : S :=
  match slotOf s t with
  | none => s
  | some sl =>
    { s with slots := s.slots.set t.idx { sl with live := false, gen := (sl.gen + 1) % GENS, waker := none },
             free := t.idx :: s.free }

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

end Vinc.FacadeStandby
