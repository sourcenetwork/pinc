import Pinc.Axioms

/-!
# The spill arena of the range sets

The story: a stream keeps the ranges of bytes it has stored (or that were acknowledged, or declared lost) in a small
array inside the stream. When scattered losses leave more holes than that array holds, the set moves into one slot of
the endpoint's spill arena (`pinc-transport/src/stream/spill.rs`, `SpillArena`; `ranges.rs`, `RangeSet::edit`). The
arena is made once, with all its slots, when the endpoint is set up. A slot is taken from a list of returned slots, or
else from a cursor over the slots never used (`SpillArena::take`), and pushed back on that list when the set shrinks
or its stream ends (`SpillArena::give`). Each session may hold at most half of the slots (`SpillUse::take`).

What must never happen: one slot given to two range sets at once, a slot lost (neither held nor free), the arena
growing past the slots it was made with, a set writing past its slot, or one session taking every slot.

This file proves:
* `slot_fits`: a slot is `SLOT_RANGES` = 512 intervals of two 8-byte words, 8 KiB, and its words are `WORDS`;
* `take_inv`, `give_inv`: taking and returning a slot keep every slot made so far either free or held, exactly once;
* `take_fresh`: the slot taken is not one already held, so no two sets share a slot;
* `conserved`: the free slots and the held ones together are the slots made so far, never more than the arena has;
* `take_none`: the arena refuses only when every slot it has is held;
* `cap_share`: a session's share is at least one slot when the arena has any, and leaves the other sessions at least
  half of the slots.
-/

namespace Pinc.TransportRangesSpill

/-- The intervals one slot holds (`SLOT_RANGES`). -/
def slotRanges : Nat := 512
/-- The `u64` words of one slot: a start and an end per interval (`WORDS`). -/
def words : Nat := slotRanges * 2

/-- A slot is 512 intervals of 16 bytes: 1024 words of 8 bytes, 8 KiB, so a set of `slotRanges` intervals never writes
past its slot. -/
theorem slot_fits : slotRanges * 16 = 8192 ∧ words * 8 = 8192 := by decide

/-- The arena: the slots handed out so far by the cursor (`fresh`: slots `1..fresh`), the returned ones in the order
they come back out (`free`, its head first: `free_head`), and the ones range sets hold now (`held`, a ghost: the code
keeps only their count). -/
structure Arena where
  fresh : Nat
  free : List Nat
  held : List Nat

/-- The arena right after it is made: no slot handed out. -/
def Arena.new : Arena := ⟨0, [], []⟩

/-- `SpillArena::take`: the most recently returned slot, else the next one the cursor has, else nothing. -/
def take (n : Nat) (a : Arena) : Option (Nat × Arena) :=
  match a.free with
  | r :: rest => some (r, { a with free := rest, held := r :: a.held })
  | [] => if a.fresh < n then some (a.fresh + 1, { a with fresh := a.fresh + 1, held := (a.fresh + 1) :: a.held })
          else none

/-- `SpillArena::give`: the slot goes on top of the returned list. -/
def give (r : Nat) (a : Arena) : Arena := { a with free := r :: a.free, held := a.held.erase r }

/-- The arena is sound: the cursor never passes the slots made, and the free and held slots are the slots handed out so
far, each exactly once. -/
def Inv (n : Nat) (a : Arena) : Prop := a.fresh ≤ n ∧ (a.free ++ a.held).Perm (List.range' 1 a.fresh)

/-- The new arena is sound. -/
theorem new_inv (n : Nat) : Inv n Arena.new := ⟨Nat.zero_le _, List.Perm.refl _⟩

/-- Every slot handed out is free or held, exactly once: no slot is in two places. -/
theorem nodup_of_inv {n : Nat} {a : Arena} (h : Inv n a) : (a.free ++ a.held).Nodup :=
  h.2.nodup_iff.mpr List.nodup_range'

/-- The slots `1..k+1` are the slots `1..k`, then slot `k + 1`. -/
theorem range'_succ (k : Nat) : List.range' 1 (k + 1) = List.range' 1 k ++ [k + 1] := by
  rw [List.range'_concat]
  -- the last slot is `1 + 1 * k`, which is `k + 1`
  simp [Nat.add_comm]

/-- Taking a slot keeps the arena sound. -/
theorem take_inv {n r : Nat} {a a' : Arena} (h : Inv n a) (ht : take n a = some (r, a')) : Inv n a' := by
  unfold take at ht
  split at ht
  · -- a returned slot: it moves from the head of the free list to the held ones
    rename_i rest hfree
    cases ht
    refine ⟨h.1, ?_⟩
    have hp := h.2
    rw [hfree] at hp
    exact List.perm_middle.trans hp
  · split at ht
    · -- a fresh slot: the cursor moves one on, and its slot is held
      rename_i hfree hlt
      cases ht
      refine ⟨hlt, ?_⟩
      have hp := h.2
      rw [hfree, List.nil_append] at hp
      simp only [hfree, List.nil_append]
      rw [range'_succ]
      -- the new slot in front of the held ones is the held ones, then the new slot
      exact (List.perm_append_singleton _ _).symm.trans (hp.append_right _)
    · cases ht

/-- The slot taken is held by no range set yet: two sets never share a slot. -/
theorem take_fresh {n r : Nat} {a a' : Arena} (h : Inv n a) (ht : take n a = some (r, a')) : r ∉ a.held := by
  have hnd := nodup_of_inv h
  unfold take at ht
  split at ht
  · -- a returned slot is free, and a free slot is not held
    rename_i rest hfree
    cases ht
    rw [hfree] at hnd
    intro hm
    exact (List.nodup_append.mp hnd).2.2 r (by simp) r hm rfl
  · split at ht
    · -- a fresh slot is past every slot handed out so far, so nobody holds it
      rename_i hfree _
      cases ht
      intro hm
      have hp := h.2
      rw [hfree, List.nil_append] at hp
      have := hp.mem_iff.mp hm
      simp [List.mem_range'] at this
      omega
    · cases ht

/-- Returning a slot a range set holds keeps the arena sound. -/
theorem give_inv {n r : Nat} {a : Arena} (h : Inv n a) (hr : r ∈ a.held) : Inv n (give r a) := by
  refine ⟨h.1, ?_⟩
  -- `r` back on the free list is the same slots: `r` taken out of the held ones and put in front
  have hm : (r :: (a.free ++ a.held.erase r)).Perm (a.free ++ a.held) :=
    List.perm_middle.symm.trans (List.Perm.append_left _ (List.perm_cons_erase hr).symm)
  exact hm.trans h.2

/-- The free slots and the held ones are the slots handed out so far, and never more than the arena has. -/
theorem conserved {n : Nat} {a : Arena} (h : Inv n a) : a.free.length + a.held.length = a.fresh ∧ a.fresh ≤ n := by
  have := h.2.length_eq
  simp only [List.length_append, List.length_range'] at this
  exact ⟨this, h.1⟩

/-- The arena refuses only when the range sets hold every slot it has. -/
theorem take_none {n : Nat} {a : Arena} (h : Inv n a) (ht : take n a = none) : a.held.length = n := by
  unfold take at ht
  split at ht
  · cases ht
  · rename_i hfree
    split at ht
    · cases ht
    · -- no slot returned and the cursor at the end: every slot is held
      rename_i hge
      have hc := conserved h
      rw [hfree] at hc
      simp at hc
      omega

/-- `SpillUse::new`: a session's share, half of the slots rounded up. -/
def cap (n : Nat) : Nat := (n + 1) / 2

/-- A session may take at least one slot of an arena that has any, and leaves the others at least half of them. -/
theorem cap_share (n : Nat) : (0 < n → 1 ≤ cap n) ∧ cap n ≤ n ∧ n / 2 ≤ n - cap n := by
  unfold cap
  omega

end Pinc.TransportRangesSpill

#audit_axioms Pinc.TransportRangesSpill.slot_fits
#audit_axioms Pinc.TransportRangesSpill.take_inv
#audit_axioms Pinc.TransportRangesSpill.take_fresh
#audit_axioms Pinc.TransportRangesSpill.give_inv
#audit_axioms Pinc.TransportRangesSpill.conserved
#audit_axioms Pinc.TransportRangesSpill.take_none
#audit_axioms Pinc.TransportRangesSpill.cap_share
