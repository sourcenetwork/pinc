/-!
# The ring of `REACH_OUT` bodies: the model

A model of `vinc-core` `reach.rs` (`ReachRing`), as `proofs/tla/ReachOps.tla` has it, over unbounded `Nat`: the
bodies received from peers, in `n` places (`REACH_SLOTS = 4`), each holding a session with its body or nothing,
and a pointer `next`, the place the next session that is not held takes. A cell is its session, the body's place
in the order of puts (`id`) and its length (the body is carried, not looked at). `mx` is `REACH_BODY_MAX = 153`.

`rput`: a body longer than `mx` changes nothing (the code returns without a trace); otherwise the place is that of
the session if it is held (`pos`, the first place whose session it is), else `next`; that place gets the cell; and
`next` moves on one, modulo `n`, when the place written was `next`, whether the session was held or not. Nothing
counts a body that is overwritten or refused; the code has no counter. `rget` is the body of a session, the first
cell that has it. `Vinc.TraceReach` replays the recorded calls of the real code through these functions; the
theorems are in `Vinc.CoreReachThm`.
-/

namespace Vinc.CoreReach

structure C where
  sess : Nat
  id : Nat
  len : Nat
  deriving DecidableEq, Repr

structure R where
  cells : List (Option C) := []
  next : Nat := 0
  deriving Repr

/-- `Option::iter().position(|h| h.session == s)` over the places. -/
def pos (s : Nat) : List (Option C) → Option Nat
  | [] => none
  | c :: cs =>
    match c with
    | some c' => if c'.sess = s then some 0 else (pos s cs).map (· + 1)
    | none => (pos s cs).map (· + 1)

def cellAt (cells : List (Option C)) (i : Nat) : Option C := (cells[i]?).getD none

def rput (n mx : Nat) (r : R) (c : C) : R :=
  if c.len > mx then r
  else
    let slot := (pos c.sess r.cells).getD r.next
    { cells := r.cells.set slot (some c), next := if slot = r.next then (r.next + 1) % n else r.next }

/-- `get`: the first held cell that has the session. -/
def rget (s : Nat) (cells : List (Option C)) : Option C :=
  (cells.filterMap id).find? (fun h => h.sess == s)

def full (cells : List (Option C)) : Prop := ∀ i, i < cells.length → (cellAt cells i).isSome

end Vinc.CoreReach
