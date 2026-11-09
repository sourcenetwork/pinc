import Vinc.ValuesPlanGeom

/-!
# Frames tile the response

The frames of an accepted plan are laid back to back: within a range each frame ends where the next starts, the
last frame of a range ends where the next range starts (the last range, at the response length `total`), and the
first frame starts at 0. Frame starts strictly increase. No frame passes `total`, which is at most `2^62 - 1`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Vinc.ValuesPlan
open Vinc.Layout Vinc.Encode

theorem RO_ge (len : Nat) : ∀ (rs : List PR) (s t : Nat), RO len rs s t → ∀ r ∈ rs, s ≤ r.start := by
  intro rs
  induction rs with
  | nil => intro s t h r hr; simp at hr
  | cons x rest ih =>
    intro s t h r hr
    obtain ⟨_, _, h3, h4⟩ := h
    rcases List.mem_cons.1 hr with rfl | hr
    · omega
    · have := ih _ _ h4 r hr; omega

/-- Consecutive ranges abut, and every range ends by `t`. -/
theorem RO_next (len : Nat) : ∀ (rs : List PR) (s t : Nat), RO len rs s t → ∀ (i : Nat) (r : PR), rs[i]? = some r →
    ((∀ r', rs[i + 1]? = some r' → r'.start = r.start + szr len r) ∧
      (rs[i + 1]? = none → t = r.start + szr len r)) ∧ r.start + szr len r ≤ t := by
  intro rs
  induction rs with
  | nil => intro s t h i r hr; simp at hr
  | cons x rest ih =>
    intro s t h i r hr
    obtain ⟨h1, h2, h3, h4⟩ := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      cases rest with
      | nil =>
        simp only [RO] at h4
        refine ⟨⟨fun r' h => by simp at h, fun _ => by omega⟩, by omega⟩
      | cons y rest' =>
        obtain ⟨g1, g2, g3, g4⟩ := h4
        have := (RO_index len (y :: rest') _ t ⟨g1, g2, g3, g4⟩).2.1
        refine ⟨⟨fun r' h => ?_, fun h => by simp at h⟩, ?_⟩
        · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
          subst h; omega
        · simp only [List.map_cons, List.sum_cons] at this; omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at hr
      obtain ⟨⟨a, b⟩, c⟩ := ih _ _ h4 i r hr
      exact ⟨⟨fun r' h => a r' (by simpa using h), fun h => b (by simpa using h)⟩, c⟩

/-- Ranges are laid in order. -/
theorem RO_lt (len : Nat) : ∀ (rs : List PR) (s t : Nat), RO len rs s t → ∀ (i j : Nat) (r r' : PR), i < j →
    rs[i]? = some r → rs[j]? = some r' → r.start + szr len r ≤ r'.start := by
  intro rs
  induction rs with
  | nil => intro s t h i j r r' _ hr; simp at hr
  | cons x rest ih =>
    intro s t h i j r r' hij hr hr'
    obtain ⟨h1, h2, h3, h4⟩ := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.getElem?_cons_succ] at hr'
        have := RO_ge len rest _ t h4 r' (List.mem_of_getElem? hr')
        omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.getElem?_cons_succ] at hr hr'
        exact ih _ _ h4 i j r r' (by omega) hr hr'

/-- The range index of a frame start is within the range. -/
theorem frame_range_end {len : Nat} {pl : PlanM} (g : Good len pl) {i : Nat} {r : PR} (hr : pl.rs[i]? = some r) :
    r.start + sumTo (fb len r.first) (r.last - r.first) = r.start + szr len r := by
  obtain ⟨h1, h2, _⟩ := g.range hr
  unfold szr
  rw [refSize_sumTo len r.first r.last h1 h2]

theorem frame_none {len : Nat} {pl : PlanM} (g : Good len pl) (i k : Nat)
    (h : ¬ ∃ r, pl.rs[i]? = some r ∧ k < r.last - r.first) : pl.frame i k = none := by
  unfold PlanM.frame
  cases hr : pl.rs[i]? with
  | none => rfl
  | some r =>
    have : ¬ k < r.last - r.first := fun hk => h ⟨r, hr, hk⟩
    simp only [show ¬ r.first + k < r.last by omega, ite_false]

/-- The lengths of a frame fit the `u32` of `Frame`. -/
theorem frame_u32 {len : Nat} {pl : PlanM} (g : Good len pl) {i k : Nat} {r : PR} (hr : pl.rs[i]? = some r)
    (hk : k < r.last - r.first) :
    pendLen (groups len lg) r.first k * PARL < 2 ^ 32 ∧ groupSize len lg (r.first + k) < 2 ^ 32 := by
  have hn := groups_le len lg g.hlen
  constructor
  · have h1 : pendLen (groups len lg) r.first k ≤ hh (groups len lg) := by
      unfold pendLen
      by_cases h0 : k = 0
      · simp only [h0, ite_true]; exact chain_length_le _ _ _ _ _ (Nat.sub_zero _)
      · simp only [h0, ite_false]
        exact Nat.le_trans (List.length_filter_le _ _) (chain_length_le _ _ _ _ _ (Nat.sub_zero _))
    have h2 : hh (groups len lg) ≤ 54 := by
      unfold hh
      by_cases hc : groups len lg ≤ 1
      · simp [hc]
      · simp only [hc, ite_false]
        have : Nat.log2 (groups len lg - 1) < 54 := by
          rw [Nat.log2_lt (by omega)]
          omega
        omega
    unfold PARL; omega
  · have := groupSize_le_len len lg (r.first + k) g.hlen
    have : groupLen lg = 16384 := by decide
    omega

/-- The frames of one range follow one another. -/
theorem frame_end_start {len : Nat} {pl : PlanM} (g : Good len pl) {i k : Nat} {r : PR} (hr : pl.rs[i]? = some r)
    (hk : k + 1 < r.last - r.first) :
    ∃ f f', pl.frame i k = some f ∧ pl.frame i (k + 1) = some f' ∧ f.fend = f'.start ∧ f.start < f.fend := by
  obtain ⟨f, hf, _, _, _, s1, e1, _⟩ := frame_spec g hr (show k < r.last - r.first by omega)
  obtain ⟨f', hf', _, _, _, s2, e2, _⟩ := frame_spec g hr hk
  refine ⟨f, f', hf, hf', by omega, ?_⟩
  have := sumTo_fb_strict len r.first k
  omega

/-- The first frame of a range starts at the range, the last ends at the next range, or at `total`. -/
theorem range_ends {len : Nat} {pl : PlanM} (g : Good len pl) {i : Nat} {r : PR} (hr : pl.rs[i]? = some r) :
    (∃ f, pl.frame i 0 = some f ∧ f.start = r.start) ∧
    (∃ f, pl.frame i (r.last - r.first - 1) = some f ∧
      ((∀ r', pl.rs[i + 1]? = some r' → f.fend = r'.start) ∧ (pl.rs[i + 1]? = none → f.fend = pl.total))) := by
  obtain ⟨h1, h2, _⟩ := g.range hr
  obtain ⟨f, hf, _, _, _, s1, _⟩ := frame_spec g hr (show 0 < r.last - r.first by omega)
  refine ⟨⟨f, hf, by simpa [sumTo] using s1⟩, ?_⟩
  obtain ⟨f2, hf2, _, _, _, _, e2, _⟩ := frame_spec g hr (show r.last - r.first - 1 < r.last - r.first by omega)
  refine ⟨f2, hf2, ?_, ?_⟩
  · intro r' h'
    obtain ⟨⟨a, b⟩, c⟩ := RO_next len pl.rs 0 pl.total g.ro i r hr
    rw [e2, show r.last - r.first - 1 + 1 = r.last - r.first by omega, frame_range_end g hr, a r' h']
  · intro h'
    obtain ⟨⟨a, b⟩, c⟩ := RO_next len pl.rs 0 pl.total g.ro i r hr
    rw [e2, show r.last - r.first - 1 + 1 = r.last - r.first by omega, frame_range_end g hr, b h']

/-- The first range starts at 0. -/
theorem first_range {len : Nat} {pl : PlanM} (g : Good len pl) {r : PR} (hr : pl.rs[0]? = some r) : r.start = 0 := by
  cases hs : pl.rs with
  | nil => rw [hs] at hr; simp at hr
  | cons x rest =>
    have ro := g.ro
    rw [hs] at hr ro
    obtain ⟨_, _, h3, _⟩ := ro
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
    subst hr; exact h3

/-- No frame passes the response. -/
theorem frame_end_le_total {len : Nat} {pl : PlanM} (g : Good len pl) {i k : Nat} {r : PR} (hr : pl.rs[i]? = some r)
    (hk : k < r.last - r.first) (f : FrameM) (hf : pl.frame i k = some f) : f.fend ≤ pl.total ∧ pl.total ≤ MAXS := by
  obtain ⟨f', hf', _, _, _, _, e, _⟩ := frame_spec g hr hk
  rw [hf] at hf'; cases hf'
  refine ⟨?_, g.maxs⟩
  obtain ⟨⟨a, b⟩, c⟩ := RO_next len pl.rs 0 pl.total g.ro i r hr
  have : sumTo (fb len r.first) (k + 1) ≤ sumTo (fb len r.first) (r.last - r.first) := sumTo_mono _ _ _ (by omega)
  rw [e]
  have := frame_range_end g hr
  omega

/-- Frames of different positions never overlap: the order of positions is the order of starts. -/
theorem start_strict {len : Nat} {pl : PlanM} (g : Good len pl) {i k i' k' : Nat} {r r' : PR}
    (hr : pl.rs[i]? = some r) (hr' : pl.rs[i']? = some r') (hk : k < r.last - r.first) (hk' : k' < r'.last - r'.first)
    (hlt : i < i' ∨ (i = i' ∧ k < k')) :
    ∃ f f', pl.frame i k = some f ∧ pl.frame i' k' = some f' ∧ f.fend ≤ f'.start := by
  obtain ⟨f, hf, _, _, _, s1, e1, _⟩ := frame_spec g hr hk
  obtain ⟨f', hf', _, _, _, s2, e2, _⟩ := frame_spec g hr' hk'
  refine ⟨f, f', hf, hf', ?_⟩
  rcases hlt with h | ⟨rfl, h⟩
  · have := RO_lt len pl.rs 0 pl.total g.ro i i' r r' h hr hr'
    have h3 : sumTo (fb len r.first) (k + 1) ≤ sumTo (fb len r.first) (r.last - r.first) := sumTo_mono _ _ _ (by omega)
    have := frame_range_end g hr
    omega
  · have : r = r' := by rw [hr] at hr'; exact Option.some.inj hr'
    subst this
    have := sumTo_mono (fb len r.first) (k + 1) k' (by omega)
    omega

end Vinc.ValuesPlan
