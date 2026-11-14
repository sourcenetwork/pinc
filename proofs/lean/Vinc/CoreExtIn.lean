/-!
# The ring of extension frames held for the application: the model

A model of `vinc-core` `ext_in.rs` (`ExtRing`), as `proofs/tla/ExtInOps.tla` has it, over unbounded `Nat`: the
extension frames received for the application, in a ring of `cap` places (`EXT_SLOTS = 8`) read oldest first. The
ring is its head and the frames in order (`q`, from the head on); the code keeps them in an array and takes both
ends modulo `cap`, which `head` tracks. A frame is its place in the order of puts (`id`), its session and type and
the length of its body (the body is carried, not looked at). `mx` is `EXT_BODY_MAX = 1200`.

`eput`: a body longer than `mx` is refused and nothing changes (`put` returns `None`); otherwise a full ring drops
its oldest frame (the head moves on) and the frame is appended, and `put` returns `Some` of how many frames the ring
gave up for it, 1 when it was full, else 0. The endpoint adds that, or 1 for a refused body, to its count of
extension frames lost (`unwrap_or(1)`). `etake`: the oldest frame, nothing for an
empty ring, or, when the oldest frame is longer than the buffer `oc`, its length with the frame left held.
`Vinc.TraceExtIn` replays the recorded calls of the real code through these functions; the theorems are in
`Vinc.CoreExtInThm`.
-/

namespace Vinc.CoreExtIn

structure F where
  id : Nat
  sess : Nat
  ty : Nat
  len : Nat
  deriving DecidableEq, Repr

structure X where
  head : Nat := 0
  q : List F := []
  deriving Repr

def eput (cap mx : Nat) (x : X) (f : F) : Option Nat × X :=
  if f.len > mx then (none, x)
  else
    let x1 : X := if x.q.length = cap then { head := (x.head + 1) % cap, q := x.q.tail } else x
    (some (if x.q.length = cap then 1 else 0), { head := x1.head, q := x1.q ++ [f] })

inductive Res where
  | none
  | err (n : Nat)
  | ok (f : F)
  deriving DecidableEq, Repr

def etake (cap oc : Nat) (x : X) : Res × X :=
  match x.q with
  | [] => (.none, x)
  | f :: t => if f.len > oc then (.err f.len, x) else (.ok f, { head := (x.head + 1) % cap, q := t })

end Vinc.CoreExtIn
