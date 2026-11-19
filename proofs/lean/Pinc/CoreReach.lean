/-!
# The ring of `REACH_OUT` bodies: the model

A model of `pinc-core` `reach.rs` (`ReachRing`), as `proofs/tla/ReachOps.tla` has it, over unbounded `Nat`: the
bodies received from peers, in `n` places (`REACH_SLOTS = 4`), each holding a session with its body and the stamp of
its put, or nothing, and the ring's put counter `clock`. A body (`B`) is its session, its place in the order of puts
(`id`) and its length (the body is carried, not looked at); a place (`C`) adds the stamp. `mx` is
`REACH_BODY_MAX = 153`.

`rput`: the counter moves on by one for every put, a refused one too. A body longer than `mx` changes nothing else
and is lost: `rput` returns 1. Otherwise the place is that of the session if it is held (`pos`, the first place whose
session it is), else the first empty place (`free`), else the place of the smallest stamp (`minAt`, the first such
place: `min_by_key` over the stamps, an empty place counting 0, though it is only asked of a full ring); that place
gets the body with the counter as its stamp, and `rput` returns 1 when it overwrote another session's body (the place
of the smallest stamp), else 0. A ring of no places keeps nothing and returns 1, as the code. `rget` is the body of a
session, the first cell that has it. `Pinc.TraceReach` replays the recorded calls of the real code through these
functions; the theorems are in `Pinc.CoreReachThm`.
-/

namespace Pinc.CoreReach

structure B where
  sess : Nat
  id : Nat
  len : Nat
  deriving DecidableEq, Repr

structure C where
  sess : Nat
  id : Nat
  len : Nat
  stamp : Nat
  deriving DecidableEq, Repr

structure R where
  cells : List (Option C) := []
  clock : Nat := 0
  deriving Repr

/-- `Option::iter().position(|h| h.session == s)` over the places. -/
def pos (s : Nat) : List (Option C) → Option Nat
  | [] => none
  | c :: cs =>
    match c with
    | some c' => if c'.sess = s then some 0 else (pos s cs).map (· + 1)
    | none => (pos s cs).map (· + 1)

/-- `position(Option::is_none)`: the first empty place. -/
def free : List (Option C) → Option Nat
  | [] => none
  | none :: _ => some 0
  | some _ :: cs => (free cs).map (· + 1)

/-- The key `min_by_key` compares: the stamp, 0 for an empty place. -/
def key : Option C → Nat
  | none => 0
  | some c => c.stamp

/-- One place in front of the least of the places after it: it wins a tie, as the first of equals. -/
def minStep (c : Option C) : Option (Nat × Nat) → Option (Nat × Nat)
  | none => some (0, key c)
  | some (j, k) => if key c ≤ k then some (0, key c) else some (j + 1, k)

/-- `min_by_key`: the first place of the least key, with that key; `none` for no places. -/
def minAt : List (Option C) → Option (Nat × Nat)
  | [] => none
  | c :: cs => minStep c (minAt cs)

def cellAt (cells : List (Option C)) (i : Nat) : Option C := (cells[i]?).getD none

/-- The place a put writes, stamped with the counter after the put. -/
def newC (r : R) (b : B) : C := { sess := b.sess, id := b.id, len := b.len, stamp := r.clock + 1 }

/-- `put`: how many bodies were lost, and the ring after. -/
def rput (mx : Nat) (r : R) (b : B) : Nat × R :=
  if mx < b.len then (1, { r with clock := r.clock + 1 })
  else
    match pos b.sess r.cells with
    | some p => (0, { cells := r.cells.set p (some (newC r b)), clock := r.clock + 1 })
    | none =>
      match free r.cells with
      | some p => (0, { cells := r.cells.set p (some (newC r b)), clock := r.clock + 1 })
      | none =>
        match minAt r.cells with
        | some (p, _) => (1, { cells := r.cells.set p (some (newC r b)), clock := r.clock + 1 })
        | none => (1, { r with clock := r.clock + 1 })

/-- `get`: the first held cell that has the session. -/
def rget (s : Nat) (cells : List (Option C)) : Option C :=
  (cells.filterMap id).find? (fun h => h.sess == s)

def full (cells : List (Option C)) : Prop := ∀ i, i < cells.length → (cellAt cells i).isSome

/-- The places held. -/
def occ : List (Option C) → Nat
  | [] => 0
  | none :: cs => occ cs
  | some _ :: cs => occ cs + 1

end Pinc.CoreReach
