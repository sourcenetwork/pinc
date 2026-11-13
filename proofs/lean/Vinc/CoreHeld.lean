import Vinc.CoreQueue

/-!
# The held ring of a session: the model

A model of `vinc-core` `slot.rs` (`Held`), as `proofs/tla/HeldOps.tla` has it, over unbounded `Nat`: the application
events of a session waiting for its access check. It is a ring of the queue's own kind (the cells, head and length
and the loop that closes the gap an eviction leaves are those of `Vinc.CoreQueue`, which proves them), with two
differences from the event queue: a recoverable event that repeats one held (the same kind and stream, which is the
event's `sess` here) merges into it and is not held again, and a full ring with nothing recoverable in it refuses
the new event and counts it, where the event queue gives up its oldest. `E.id` is the place in the order of pushes,
`E.lossy` whether the application can recover the event, `E.sess` its kind and stream together; `E.closed` is
unused. The count `ll` of recoverable events is a ghost of the model: the code scans for them instead.
`Vinc.TraceHeld` replays the recorded calls of the real code through these functions; the theorems are in
`Vinc.CoreHeldThm`.
-/

namespace Vinc.CoreHeld
open Vinc.CoreQueue

/-- Whether a recoverable `ev` repeats a held event (the same kind and stream). -/
def merges (cap : Nat) (ev : E) (r : R) : Bool :=
  ev.lossy && (List.range r.len).any fun i =>
    match get r cap i with
    | some x => x.sess == ev.sess
    | none => false

/-- The ring holds nothing it may drop and has no room. -/
def hstalled (cap : Nat) (r : R) : Bool := r.len == cap && (victim r cap).isNone

/-- `push`: a repeat of a recoverable event merges; a full ring gives up its oldest recoverable event, or, holding
none, refuses the new event; both count a drop. -/
def hpush (cap : Nat) (ev : E) (r : R) : R :=
  if merges cap ev r then r
  else if r.len = cap then
    match victim r cap with
    | none => { r with dropped := r.dropped + 1 }
    | some _ => append cap ev (evict cap { r with dropped := r.dropped + 1 })
  else append cap ev r

def hpop (cap : Nat) (r : R) : Option E × R := pop cap r

end Vinc.CoreHeld
