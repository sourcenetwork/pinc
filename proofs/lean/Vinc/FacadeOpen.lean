import Vinc.Axioms

/-!
# The facade's queue of stream opens: who is served next

The story, in plain words. Futures that want a stream on a session, when the peer's places are all held, wait on a
list, oldest first. A future joins the list once, at the end. A future leaves the list when it takes a place or is
dropped, and the others keep their order. When a place frees, the endpoint wakes only the oldest; when the oldest
leaves, it wakes the next. A future that has never waited (no ticket yet) and finds anyone on the list queues behind
them.

What must never happen: the list holds a future twice; leaving reorders the others; the future woken after the
oldest leaves is anyone but the next oldest; a future that never waited goes ahead of one on the list.

The list is `Sess::waits` in `crates/vinc/src/engine.rs`, filtered to the open entries of one kind (`first_wait`);
`join` is `Core::add_wait`, `leave` is the retain in `Core::forget`, `ahead` is `Core::open_ahead`. The TLA+ model is
`proofs/tla/FacadeOpen.tla`. The old code's wake emptied the list (`wakeAll`): `wakeAll_bad` shows a newcomer then
goes first.

Main theorems: `join_nodup`, `leave_nodup`, `leave_sublist`, `leave_head_next`, `join_head`, `ahead_newcomer`,
`wakeAll_bad`.
-/

namespace Vinc.FacadeOpen

-- `add_wait`: a future already on the list stays where it is; a new one goes to the end.
def join (l : List Nat) (t : Nat) : List Nat := if t ∈ l then l else l ++ [t]

-- `forget`: the future leaves; every other keeps its place relative to the rest.
def leave (l : List Nat) (t : Nat) : List Nat := l.filter (fun x => x ≠ t)

-- `open_ahead`: someone is first on the list and it is not the caller (`none` for a future that never waited).
def ahead (l : List Nat) (caller : Option Nat) : Bool :=
  match l with
  | [] => false
  | h :: _ => caller != some h

-- Joining never puts a future on the list twice.
theorem join_nodup (l : List Nat) (t : Nat) (h : l.Nodup) : (join l t).Nodup := by
  unfold join
  split
  · exact h
  · rename_i hn
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact fun e => hn (e ▸ ha)

-- Leaving keeps the order of everyone else: the new list is the old one with some entries struck out.
theorem leave_sublist (l : List Nat) (t : Nat) : (leave l t).Sublist l :=
  List.filter_sublist

-- Leaving never puts a future on the list twice either.
theorem leave_nodup (l : List Nat) (t : Nat) (h : l.Nodup) : (leave l t).Nodup :=
  List.Nodup.sublist (leave_sublist l t) h

-- When the oldest leaves, the first on the list is the one that was second: the hand-off wakes the next oldest.
theorem leave_head_next (t : Nat) (r : List Nat) (h : (t :: r).Nodup) : (leave (t :: r) t).head? = r.head? := by
  have hr : t ∉ r := (List.nodup_cons.mp h).1
  have hl : leave (t :: r) t = r := by
    unfold leave
    rw [List.filter_cons_of_neg (by simp)]
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [ne_eq, decide_eq_true_eq]
    exact fun hxt => hr (hxt ▸ hx)
  rw [hl]

-- A future joining a list that is not empty never becomes its first: the oldest stays the oldest.
theorem join_head (l : List Nat) (t : Nat) (h : l ≠ []) : (join l t).head? = l.head? := by
  unfold join
  split
  · rfl
  · cases l with
    | nil => exact absurd rfl h
    | cons a r => rfl

-- A future that never waited finds anyone on the list ahead of it, so it queues instead of taking the place.
theorem ahead_newcomer (l : List Nat) (h : l ≠ []) : ahead l none = true := by
  cases l with
  | nil => exact absurd rfl h
  | cons a r => rfl

-- The first on the list is never ahead of itself, so the woken oldest takes the place when there is one.
theorem ahead_self (t : Nat) (r : List Nat) : ahead (t :: r) (some t) = false := by
  simp [ahead]

-- The old code: a freed place woke every waiting future and took them all off the list.
def wakeAll (_ : List Nat) : List Nat := []

-- With the old code, a future that waited is woken, and before it runs a newcomer finds nobody ahead of it.
theorem wakeAll_bad : ∃ l : List Nat, l ≠ [] ∧ ahead (wakeAll l) none = false :=
  ⟨[1], by simp, rfl⟩

end Vinc.FacadeOpen

#audit_axioms Vinc.FacadeOpen.join_nodup
#audit_axioms Vinc.FacadeOpen.leave_nodup
#audit_axioms Vinc.FacadeOpen.leave_sublist
#audit_axioms Vinc.FacadeOpen.leave_head_next
#audit_axioms Vinc.FacadeOpen.join_head
#audit_axioms Vinc.FacadeOpen.ahead_newcomer
#audit_axioms Vinc.FacadeOpen.ahead_self
#audit_axioms Vinc.FacadeOpen.wakeAll_bad
