import Vinc.Axioms
import Vinc.ValuesSysSafe

/-!
# A granule is announced once

`ann_once`: in every reachable state of the system model no group has more than one `Readable` event, however the
adversary orders the frames and whichever streams carry a group. The model takes a frame in one step: a group already
in the store is `skip`ped (`Step.skip`), and a group enters the pending write (`accept`, `acceptAhead`) only while the
store does not hold it, and nothing else runs while a write is pending. A stream that was inside a group when another
stream stored it therefore ends in `skip`, which is what `Fetch` does since the correction (`recv.rs` `drain`: the
group is not written or announced a second time); the invariant below would fail if `accept` could run on a stored
group, which is the code before the correction (`ValuesSys_midold` shows it in TLC).
-/

namespace Vinc.ValuesSys
open Classical

/-- What the once-only announcement needs on top of `Inv`. -/
structure Once (s : St) : Prop where
  annLe : ∀ g, s.ann g ≤ 1
  hdFresh : ∀ g, s.hd = some g → s.ann g = 0
  pdFresh : ∀ d, s.pd = some d → s.ver d.g = false
  idle : s.run = .idle → (∀ g, s.ann g = 0) ∧ s.hd = none ∧ s.pd = none

theorem Once.init (c : Cfg) (rs : Nat) : Once (init c rs) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Vinc.ValuesSys.init]

theorem Once.finish {s : St} (h : Once s) (t : St) (f : Final) (ha : t.ann = s.ann) (hh : t.hd = s.hd) :
    Once (finish t f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g; simpa [Vinc.ValuesSys.finish, ha] using h.annLe g
  · intro g hg; simp only [Vinc.ValuesSys.finish, hh] at hg; simpa [Vinc.ValuesSys.finish, ha] using h.hdFresh g hg
  · intro d hd; simp [Vinc.ValuesSys.finish] at hd
  · intro e; simp [Vinc.ValuesSys.finish] at e

theorem Once.view {s s' : St} (h : Once s) (ha : s'.ann = s.ann) (hh : s'.hd = s.hd) (hp : s'.pd = s.pd)
    (hv : s'.ver = s.ver) (hr : s'.run ≠ .idle) : Once s' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g; simpa [ha] using h.annLe g
  · intro g hg; rw [hh] at hg; simpa [ha] using h.hdFresh g hg
  · intro d hd; rw [hp] at hd; have := h.pdFresh d hd; rwa [hv]
  · intro e; exact absurd e hr

theorem Once.step {c : Cfg} {s s' : St} (hi : Inv c s) (h : Once s) (st : Step c s s') : Once s' := by
  cases st with
  | startBadRoot h1 h2 h3 => exact h.finish _ _ rfl rfl
  | startComplete h1 h2 h3 => exact h.finish _ _ rfl rfl
  | startNoProvider h1 h2 h3 h4 => exact h.finish _ _ rfl rfl
  | begin h1 h2 h3 h4 => exact h.view rfl rfl rfl rfl (by simp)
  | plumb q a r h1 h2 po => exact h.view rfl rfl rfl rfl (by simp [h1])
  | accept p g k h1 h2 h3 h4 h5 h6 h7 =>
    refine ⟨h.annLe, h.hdFresh, ?_, ?_⟩
    · intro d hd; simp at hd; subst hd; simpa using h6
    · intro e; simp [h1] at e
  | skip p g h1 h2 h3 h4 h5 => exact h
  | acceptAhead p g k h1 h2 h3 h4 h5 h6 h7 =>
    refine ⟨h.annLe, h.hdFresh, ?_, ?_⟩
    · intro d hd; simp at hd; subst hd; simpa using h6
    · intro e; simp [h1] at e
  | evict p h1 h2 h3 h4 =>
    have e2 : (evict2 s p).ann = s.ann ∧ (evict2 s p).hd = s.hd ∧ (evict2 s p).pd = s.pd ∧ (evict2 s p).ver = s.ver ∧
        (evict2 s p).run = s.run := by
      unfold evict2; split <;> simp [evict1]
    unfold evictSt; split
    · exact h.finish _ _ e2.1 e2.2.1
    · have e3 : (evictBooks s p).ann = s.ann ∧ (evictBooks s p).hd = s.hd ∧ (evictBooks s p).pd = s.pd ∧
          (evictBooks s p).ver = s.ver ∧ (evictBooks s p).run = s.run := by
        unfold evictBooks; simp [e2.1, e2.2.1, e2.2.2.1, e2.2.2.2.1, e2.2.2.2.2]
      exact h.view e3.1 e3.2.1 e3.2.2.1 e3.2.2.2.1 (by rw [e3.2.2.2.2]; simp [h1])
  | write d h1 h2 h3 =>
    refine ⟨h.annLe, h.hdFresh, ?_, ?_⟩
    · intro d' hd'; simp at hd'; subst hd'; exact h.pdFresh d h2
    · intro e; simp [h1] at e
  | writeRefused d h1 h2 h3 h4 => exact h.finish _ _ rfl rfl
  | commit d h1 h2 h3 =>
    have hv := h.pdFresh d h2
    have ha0 : s.ann d.g = 0 := by
      rcases Nat.eq_zero_or_pos (s.ann d.g) with e | e
      · exact e
      · have := hi.ann d.g e
        rw [hv] at this
        exact absurd this (by simp)
    unfold commitSt
    split
    · refine ⟨h.annLe, ?_, ?_, ?_⟩
      · intro x hx; simp at hx; subst hx; exact ha0
      · intro d' hd'; simp at hd'
      · intro e; simp [h1] at e
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro x; by_cases e : x = d.g
        · simp [readable, e, ha0]
        · simpa [readable, e] using h.annLe x
      · intro x hx
        have hx' : s.hd = some x := by simpa [readable] using hx
        have hxv := hi.hdVer x hx'
        have hne : x ≠ d.g := by intro e; subst e; simp_all
        simpa [readable, hne] using h.hdFresh x hx'
      · intro d' hd'; simp [readable] at hd'
      · intro e; simp [readable, h1] at e
  | commitRefused d h1 h2 h3 h4 => exact h.finish _ _ rfl rfl
  | release h1 h2 h3 =>
    obtain ⟨g, hg⟩ := h3
    unfold releaseHd; rw [hg]
    have h0 := h.hdFresh g hg
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x; by_cases e : x = g
      · simp [readable, e, h0]
      · simpa [readable, e] using h.annLe x
    · intro x hx; simp [readable] at hx
    · intro d hd; have := h.pdFresh d (by simpa [readable] using hd); simpa [readable] using this
    · intro e; simp [readable, h1] at e
  | check h1 h2 h3 =>
    have hr : Once (releaseHd s) := by
      unfold releaseHd
      cases hh : s.hd with
      | none => exact h
      | some g =>
        have h0 := h.hdFresh g hh
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro x; by_cases e : x = g
          · simp [readable, e, h0]
          · simpa [readable, e] using h.annLe x
        · intro x hx; simp [readable] at hx
        · intro d hd; have := h.pdFresh d (by simpa [readable] using hd); simpa [readable] using this
        · intro e; simp [readable, h1] at e
    have e1 : (releaseHd s).ann = (releaseHd s).ann := rfl
    exact hr.finish _ _ rfl rfl
  | tick h1 h2 => exact h.view rfl rfl rfl rfl (by simp [h1])
  | deadlineFire d h1 h2 h3 h4 => exact h.finish _ _ rfl rfl
  | restart h1 h2 =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Vinc.ValuesSys.init]

theorem reach_once {c : Cfg} {rs : Nat} {s : St} (h : Reach c rs s) : Once s := by
  induction h with
  | init => exact Once.init c rs
  | step s s' hr st ih => exact ih.step (reach_inv hr) st

/-- A group has at most one `Readable` event in every execution. -/
theorem ann_once {c : Cfg} {rs : Nat} {s : St} (h : Reach c rs s) (g : Nat) : s.ann g ≤ 1 := (reach_once h).annLe g

/-- The held first granule has not been announced. -/
theorem held_not_announced {c : Cfg} {rs : Nat} {s : St} (h : Reach c rs s) (g : Nat) (hg : s.hd = some g) :
    s.ann g = 0 := (reach_once h).hdFresh g hg

end Vinc.ValuesSys

#audit_axioms Vinc.ValuesSys.ann_once
#audit_axioms Vinc.ValuesSys.held_not_announced
