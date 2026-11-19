import Pinc.ValuesPlanTile
import Pinc.PartitionPoint

/-!
# `locate` inverts `frame`

`Plan::locate(at)` finds the range of a stream offset with `partition_point` over the range starts, then the
frame with the binary search of `frame_start`. This file proves the search correct and `locate` the inverse of
`frame` for every accepted plan and every offset:

* `bsGo_spec`: the binary search returns the largest index whose start is at most the offset, for any
  non-decreasing start function.
* `locate_frame`: if a frame of the plan holds the offset then `locate` returns exactly that frame.
* `locate_total`: every offset below the response length is held by a frame (so `locate` finds one), and
  `locate_end`: an offset at or past the length finds none.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesPlan
open Pinc.Layout Pinc.Encode

/-- The binary search of `locate`: `lo`, `hi` and `mid = lo + (hi - lo).div_ceil(2)`. -/
def bsGo (st : Nat → Nat) (at_ : Nat) (lo hi : Nat) : Nat :=
  if h : lo < hi then
    if st (lo + (hi - lo + 1) / 2) ≤ at_ then bsGo st at_ (lo + (hi - lo + 1) / 2) hi
    else bsGo st at_ lo (lo + (hi - lo + 1) / 2 - 1)
  else lo
termination_by hi - lo

/-- On a non-decreasing start function the search returns the last index whose start is at most the offset. -/
theorem bsGo_spec (st : Nat → Nat) (at_ H : Nat) (hm : ∀ i j, i ≤ j → j ≤ H → st i ≤ st j) :
    ∀ (n lo hi : Nat), hi - lo = n → lo ≤ hi → hi ≤ H → st lo ≤ at_ → (hi = H ∨ at_ < st (hi + 1)) →
      lo ≤ bsGo st at_ lo hi ∧ bsGo st at_ lo hi ≤ hi ∧ st (bsGo st at_ lo hi) ≤ at_ ∧
        (bsGo st at_ lo hi = H ∨ at_ < st (bsGo st at_ lo hi + 1)) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi hn hlo hhi hsl hb
    rw [bsGo]
    by_cases h : lo < hi
    · simp only [h, dite_true]
      by_cases hc : st (lo + (hi - lo + 1) / 2) ≤ at_
      · simp only [hc, ite_true]
        have := ih (hi - (lo + (hi - lo + 1) / 2)) (by omega) (lo + (hi - lo + 1) / 2) hi rfl (by omega) hhi hc hb
        omega
      · simp only [hc, ite_false]
        have := ih (lo + (hi - lo + 1) / 2 - 1 - lo) (by omega) lo (lo + (hi - lo + 1) / 2 - 1) rfl (by omega) (by omega) hsl
          (Or.inr (by rw [show lo + (hi - lo + 1) / 2 - 1 + 1 = lo + (hi - lo + 1) / 2 by omega]; exact Nat.lt_of_not_le hc))
        omega
    · simp only [h, dite_false]
      have hh : hi = lo := by omega
      subst hh
      exact ⟨Nat.le_refl _, Nat.le_refl _, hsl, hb.elim (fun h => Or.inl h) (fun h => Or.inr h)⟩

/-- `Plan::locate`. -/
def PlanM.locate (pl : PlanM) (at_ : Nat) : Option FrameM :=
  if pl.total ≤ at_ then none else
  match PP.partitionPoint (fun r : PR => decide (r.start ≤ at_)) pl.rs with
  | 0 => none
  | p + 1 =>
    match pl.rs[p]? with
    | none => none
    | some r =>
      (pl.frame p (bsGo (pl.frameStart r) at_ 0 (r.last - r.first - 1))).filter (fun f => decide (at_ < f.fend))

/-- Some range of a chain holds any offset below its end. -/
theorem RO_contains (len : Nat) : ∀ (rs : List PR) (s t at_ : Nat), RO len rs s t → s ≤ at_ → at_ < t →
    ∃ (i : Nat) (r : PR), rs[i]? = some r ∧ r.start ≤ at_ ∧ at_ < r.start + szr len r := by
  intro rs
  induction rs with
  | nil => intro s t a h h1 h2; simp only [RO] at h; omega
  | cons x rest ih =>
    intro s t a h h1 h2
    obtain ⟨_, _, h3, h4⟩ := h
    by_cases hx : a < s + szr len x
    · exact ⟨0, x, rfl, by omega, by omega⟩
    · obtain ⟨i, r, hr, c1, c2⟩ := ih _ _ a h4 (by omega) h2
      exact ⟨i + 1, r, hr, c1, c2⟩

theorem sumTo_find (f : Nat → Nat) (hf : ∀ j, 0 < f j) : ∀ m x, x < sumTo f m → ∃ k, k < m ∧ sumTo f k ≤ x ∧ x < sumTo f (k + 1) := by
  intro m
  induction m with
  | zero => intro x h; simp [sumTo] at h
  | succ m ih =>
    intro x h
    by_cases hx : x < sumTo f m
    · obtain ⟨k, hk, a, b⟩ := ih x hx
      exact ⟨k, by omega, a, b⟩
    · exact ⟨m, by omega, by omega, by simpa [sumTo] using h⟩

/-- Every offset below the response is held by a frame of the plan. -/
theorem locate_total {len : Nat} {pl : PlanM} (g : Good len pl) {at_ : Nat} (h : at_ < pl.total) :
    ∃ i r k f, pl.rs[i]? = some r ∧ k < r.last - r.first ∧ pl.frame i k = some f ∧ f.start ≤ at_ ∧ at_ < f.fend := by
  obtain ⟨_, htot, _⟩ := RO_index len pl.rs 0 pl.total g.ro
  obtain ⟨i, r, hr, c1, c2⟩ := RO_contains len pl.rs 0 pl.total at_ g.ro (by omega) h
  obtain ⟨h1, h2, _⟩ := g.range hr
  have hs : at_ - r.start < sumTo (fb len r.first) (r.last - r.first) := by
    have := frame_range_end g hr
    omega
  obtain ⟨k, hk, a, b⟩ := sumTo_find (fb len r.first) (fun j => by have := fb_pos len r.first j; unfold HDR at this; omega) _ _ hs
  obtain ⟨f, hf, _, _, _, s1, e1, _⟩ := frame_spec g hr hk
  exact ⟨i, r, k, f, hr, hk, hf, by omega, by omega⟩

/-- `locate` returns the frame that holds the offset. -/
theorem locate_frame {len : Nat} {pl : PlanM} (g : Good len pl) {at_ i k : Nat} {r : PR} {f : FrameM}
    (hr : pl.rs[i]? = some r) (hk : k < r.last - r.first) (hf : pl.frame i k = some f)
    (hs : f.start ≤ at_) (he : at_ < f.fend) : pl.locate at_ = some f := by
  obtain ⟨h1, h2, h3⟩ := g.range hr
  obtain ⟨f', hf', _, _, _, s1, e1, _⟩ := frame_spec g hr hk
  rw [hf] at hf'; cases hf'
  have htot := (frame_end_le_total g hr hk f hf).1
  have hlen : i < pl.rs.length :=
    Classical.byContradiction fun hc => by rw [List.getElem?_eq_none (by omega)] at hr; cases hr
  have hrs : pl.rs[i] = r := by rw [List.getElem?_eq_getElem hlen] at hr; exact Option.some.inj hr
  -- the partition point is i + 1
  have hPart : PP.FirstFalse (fun r : PR => decide (r.start ≤ at_)) pl.rs (i + 1) := by
    refine ⟨by omega, ?_, ?_⟩
    · intro j hj hji
      by_cases hje : j = i
      · subst hje; simp only [hrs, decide_eq_true_eq]; omega
      · have := RO_lt len pl.rs 0 pl.total g.ro j i pl.rs[j] r (by omega) (List.getElem?_eq_getElem hj) hr
        simp only [decide_eq_true_eq]; omega
    · intro j hj hij
      have := RO_lt len pl.rs 0 pl.total g.ro i j r pl.rs[j] (by omega) hr (List.getElem?_eq_getElem hj)
      have hrf := frame_range_end g hr
      have : sumTo (fb len r.first) (k + 1) ≤ sumTo (fb len r.first) (r.last - r.first) := sumTo_mono _ _ _ (by omega)
      simp only [decide_eq_false_iff_not, Nat.not_le]; omega
  have hpp := PP.partitionPoint_eq _ _ _ hPart
  -- the binary search lands on k
  have hmono : ∀ a b, a ≤ b → b ≤ r.last - r.first - 1 → pl.frameStart r a ≤ pl.frameStart r b := by
    intro a b hab hb
    rw [frameStart_eq g hr (by omega), frameStart_eq g hr (by omega)]
    have := sumTo_mono (fb len r.first) a b hab
    omega
  have hst0 : pl.frameStart r 0 ≤ at_ := by
    rw [frameStart_eq g hr (by omega)]; simp [sumTo]; omega
  have hsp := bsGo_spec (pl.frameStart r) at_ (r.last - r.first - 1) hmono _ 0 (r.last - r.first - 1) rfl (by omega)
    (Nat.le_refl _) hst0 (Or.inl rfl)
  have hk' : bsGo (pl.frameStart r) at_ 0 (r.last - r.first - 1) = k := by
    obtain ⟨c1, c2, c3, c4⟩ := hsp
    generalize bsGo (pl.frameStart r) at_ 0 (r.last - r.first - 1) = k' at c1 c2 c3 c4 ⊢
    have hk'm : k' < r.last - r.first := by omega
    rw [frameStart_eq g hr hk'm] at c3
    by_cases hlt : k' < k
    · rcases c4 with c4 | c4
      · omega
      · rw [frameStart_eq g hr (by omega)] at c4
        have := sumTo_mono (fb len r.first) (k' + 1) k (by omega)
        omega
    · by_cases hgt : k < k'
      · have := sumTo_mono (fb len r.first) (k + 1) k' (by omega)
        omega
      · omega
  unfold PlanM.locate
  rw [if_neg (by omega), hpp]
  simp only [hrs, hr, hk', hf, Option.filter, decide_eq_true_eq, he, ite_true]

/-- Every offset at or past the response length finds no frame. -/
theorem locate_end {pl : PlanM} (at_ : Nat) (h : pl.total ≤ at_) : pl.locate at_ = none := by
  unfold PlanM.locate; rw [if_pos h]

/-- Frames never share an offset: two frames that hold the same offset are the same frame. -/
theorem frame_unique {len : Nat} {pl : PlanM} (g : Good len pl) {at_ i k i' k' : Nat} {r r' : PR} {f f' : FrameM}
    (hr : pl.rs[i]? = some r) (hr' : pl.rs[i']? = some r') (hk : k < r.last - r.first) (hk' : k' < r'.last - r'.first)
    (hf : pl.frame i k = some f) (hf' : pl.frame i' k' = some f')
    (hs : f.start ≤ at_) (he : at_ < f.fend) (hs' : f'.start ≤ at_) (he' : at_ < f'.fend) : i = i' ∧ k = k' := by
  have a := locate_frame g hr hk hf hs he
  have b := locate_frame g hr' hk' hf' hs' he'
  have e : f = f' := Option.some.inj (a.symm.trans b)
  obtain ⟨f2, hf2, ra, ka, _⟩ := frame_spec g hr hk
  obtain ⟨f3, hf3, rb, kb, _⟩ := frame_spec g hr' hk'
  have e2 : f2 = f := Option.some.inj (hf2.symm.trans hf)
  have e3 : f3 = f' := Option.some.inj (hf3.symm.trans hf')
  subst e2 e3 e
  omega

end Pinc.ValuesPlan
