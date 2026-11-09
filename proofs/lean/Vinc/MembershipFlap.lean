import Vinc.MembershipViewPrimary

/-!
# Primary hub switch: no flapping inside the hysteresis (property 10)

`reselect_switch_requires` says a member changes its primary from `cur` to `p` only when `cur` is not alive or
`rn + 20 ms < rc * 3 / 4`. Two switches in a row between two alive hubs, on the same round trips, would need that
inequality both ways. `reselect_no_flap` shows they cannot: after a switch from `cur` to `p`, `reselect` does not
switch back to `cur` while both hubs are alive and the round trips are unchanged, so the primary does not oscillate
between two hubs whose round trips are within the hysteresis of each other.
-/

set_option linter.unusedVariables false

namespace Vinc.Membership
open Vinc.MemInc

theorem OutOnly.hrtt {n n' : N} (h : OutOnly n n') : n'.hrtt = n.hrtt := by obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h; rfl

/-- What a switch leaves alone: the round trips, the sessions, the hearing, the node's identity and role. -/
def Fixed (n n' : N) : Prop := n'.hrtt = n.hrtt ∧ n'.up = n.up ∧ n'.heard = n.heard ∧ n'.me = n.me ∧ n'.isHub = n.isHub

theorem Fixed.refl (n : N) : Fixed n n := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem Fixed.of_out {n n' : N} (h : OutOnly n n') : Fixed n n' := ⟨h.hrtt, h.up, h.heard, h.me, h.isHub⟩
theorem Fixed.trans {a b c : N} (h1 : Fixed a b) (h2 : Fixed b c) : Fixed a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.trans h1.2.2.2.2⟩

theorem helloTo_fixed (e : Env) (n : N) (peer : Nat) (snap : Bool) : Fixed n (N.helloTo e n peer snap) :=
  Fixed.of_out (tx_out _ _ _ _ _)

theorem rsSwitch_fixed (e : Env) (n : N) (now p : Nat) : Fixed n (rsSwitch e n now p) := by
  unfold rsSwitch
  dsimp only
  refine Fixed.trans ?_ (Fixed.of_out (bc_out _ _))
  have h0 : Fixed n ({ n with primary := some p } : N) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have h1 := h0.trans (Fixed.of_out (trace_out ({ n with primary := some p } : N) (.primary p)))
  generalize (({ n with primary := some p } : N).trace (.primary p)) = n1 at h1 ⊢
  split
  · have h2 : Fixed n1 ({ n1 with homeOk := none } : N) := ⟨rfl, rfl, rfl, rfl, rfl⟩
    have h3 := h2.trans (helloTo_fixed e ({ n1 with homeOk := none } : N) p true)
    refine h1.trans (h3.trans ?_)
    generalize N.helloTo e ({ n1 with homeOk := none } : N) p true = n3
    split
    · split
      · exact helloTo_fixed e n3 _ false
      · exact Fixed.refl n3
    · exact Fixed.refl n3
  · exact h1.trans (Fixed.refl n1)

theorem reselect_fixed (e : Env) (n : N) (now : Nat) : Fixed n (N.reselect e n now) := by
  rw [reselect_eq]
  split
  · exact Fixed.refl n
  · split
    · exact Fixed.refl n
    · exact rsSwitch_fixed ..

theorem Fixed.hubUp {n n' : N} (h : Fixed n n') (now x : Nat) : n'.hubUp now x = n.hubUp now x := by
  obtain ⟨-, hup, hhe, hme, -⟩ := h
  unfold N.hubUp; rw [hme, hup, hhe]

/-- **No flapping.** After `reselect` switches the primary of a member from `cur` to `p`, a second `reselect` on the same
round trips does not switch back to `cur` while both hubs are alive: the two switches would need
`rn + 20 ms < rc * 3 / 4` and `rc + 20 ms < rn * 3 / 4` together. -/
theorem reselect_no_flap (e e' : Env) (n : N) (now cur p : Nat) (hnh : n.isHub = false) (hc : n.primary = some cur)
    (hp : (N.reselect e n now).primary = some p) (hne : p ≠ cur) (hcur : n.hubUp now cur = true)
    (hpu : n.hubUp now p = true) : (N.reselect e' (N.reselect e n now) now).primary ≠ some cur := by
  intro hback
  have hf := reselect_fixed e n now
  have h1 := reselect_switch_requires e n now cur p hnh hc hp hne
  have h2 := reselect_switch_requires e' (N.reselect e n now) now p cur (by rw [hf.2.2.2.2]; exact hnh) hp hback (Ne.symm hne)
  rw [hf.hubUp] at h2
  rw [hf.1] at h2
  rcases h1 with h1 | ⟨-, h1⟩
  · rw [hcur] at h1; cases h1
  · rcases h2 with h2 | ⟨-, h2⟩
    · rw [hpu] at h2; cases h2
    · simp only [HYST_ABS, U64MAX, RTT_UNKNOWN, MS] at h1 h2
      omega

end Vinc.Membership
