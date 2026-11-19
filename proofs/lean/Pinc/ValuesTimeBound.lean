import Pinc.ValuesTimeInv

/-!
# HEAD_HOLD: the theorems of property 4

From `Inv` (`ValuesTimeInv.lean`) and the cause lemmas (`ValuesTimeHold.lean`):

* `never_announced_unstored`, `held_not_announced`, `announced_once`, `complete_announced_once`: the first granule;
* `later_granule_immediate`, `holdCheck_release`: the order of the events;
* `noLate_checkDone`, `reach_j0`: a held granule never outlives a cause that is already true between two calls;
* `hold_poll_le`, `onTimeout_clears_head`, `onTimeout_timeout_cause`: the bound by `HOLD_MAX` as `poll_timeout` and
  `on_timeout` realise it.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Pinc.ValuesTime
open Pinc.Ranges

/-! ## The first granule over a run -/

variable {s0 s : Fs}

/-- Nothing is announced before its group is verified and every byte of it is in the store. -/
theorem never_announced_unstored (h0 : Inv s0) (hr : Reach s0 s) (o l : Nat) (hm : Ev.readable o l ∈ s.log) :
    Ev.verified o l ∈ s.log ∧ ∀ x, o ≤ x → x < o + l → Covers s.store x :=
  (reach_inv h0 hr).ann o l hm

/-- A held granule is verified, stored, and not announced. -/
theorem held_not_announced (h0 : Inv s0) (hr : Reach s0 s) (h : Head) (hh : s.head = some h) :
    Ev.verified h.off h.len ∈ s.log ∧ (∀ x, h.off ≤ x → x < h.off + h.len → Covers s.store x) ∧
      s.log.count (Ev.readable h.off h.len) = 0 ∧ s.rel = false := by
  have hi := reach_inv h0 hr
  obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := hi.heads h hh
  rcases hi.dich h.off h.len v4 v5 v1 with ⟨_, hc, _⟩ | ⟨hn, _⟩
  · exact ⟨v1, v7, hc, v3⟩
  · rw [hh] at hn; exact absurd hn (by simp)

/-- The first granule is announced at most once, and exactly once once it is not held. -/
theorem announced_once (h0 : Inv s0) (hr : Reach s0 s) (o l : Nat) (h1 : o ≤ s.o0) (h2 : s.o0 < o + l)
    (hv : Ev.verified o l ∈ s.log) :
    (s.log.count (Ev.readable o l) = 0 ∧ ∃ t, s.head = some ⟨o, l, t⟩) ∨
      (s.log.count (Ev.readable o l) = 1 ∧ s.head = none ∧ s.rel = true) := by
  rcases (reach_inv h0 hr).dich o l h1 h2 hv with ⟨hh, hc, _⟩ | ⟨hn, hr', hc⟩
  · exact Or.inl ⟨hc, hh⟩
  · exact Or.inr ⟨hc, hn, hr'⟩

/-- A completed fetch announced its first granule exactly once. -/
theorem complete_announced_once (h0 : Inv s0) (hr : Reach s0 s) (hc : Ev.complete ∈ s.log) (o l : Nat)
    (h1 : o ≤ s.o0) (h2 : s.o0 < o + l) (hv : Ev.verified o l ∈ s.log) :
    s.log.count (Ev.readable o l) = 1 := by
  have hi := reach_inv h0 hr
  have hn := hi.comp hc
  rcases hi.dich o l h1 h2 hv with ⟨⟨t, ht⟩, _⟩ | ⟨_, _, hc1⟩
  · rw [hn] at ht; exact absurd ht (by simp)
  · exact hc1

/-! ## Events and causes in order -/

/-- The log only grows. -/
def Ext (s s' : Fs) : Prop := ∃ ex, s'.log = s.log ++ ex

theorem Ext.refl (s : Fs) : Ext s s := ⟨[], by simp⟩
theorem Ext.trans {a b c : Fs} (h1 : Ext a b) (h2 : Ext b c) : Ext a c := by
  obtain ⟨x, hx⟩ := h1; obtain ⟨y, hy⟩ := h2; exact ⟨x ++ y, by simp [hy, hx]⟩
theorem Ext.mem {a b : Fs} (h : Ext a b) {e : Ev} (he : e ∈ a.log) : e ∈ b.log := by
  obtain ⟨x, hx⟩ := h; rw [hx]; exact List.mem_append_left _ he

theorem ext_emit (s : Fs) (es : List Ev) : Ext s (Fs.emit s es) := ⟨es, rfl⟩
theorem ext_hold (s : Fs) (now : Nat) (f : Option Cause) : Ext s (holdCheck s now f) := by
  cases hh : s.head with
  | none => simpa [holdCheck, hh] using Ext.refl s
  | some h =>
    cases hw : holdWhy s h now f with
    | none => simpa [holdCheck, hh, hw] using Ext.refl s
    | some c => simp only [holdCheck, hh, hw]; exact ⟨_, rfl⟩
theorem ext_checkDone (s : Fs) (now : Nat) : Ext s (checkDone s now) := by
  rw [checkDone_eq]
  split
  · exact (ext_hold s now none).trans ((ext_hold _ now _).trans ⟨[.complete], rfl⟩)
  · exact ext_hold s now none
theorem ext_fail (s : Fs) (r : Fail) : Ext s (failWith s r) := ⟨[.failed r], rfl⟩

/-- A later granule (not the one that contains `o0`) is announced right after its verification record. -/
theorem later_granule_immediate (s : Fs) (now off len : Nat) (h : ¬(off ≤ s.o0 ∧ s.o0 < off + len)) :
    ∃ ex, (groupVerified s now off len).log = s.log ++ [Ev.verified off len, Ev.readable off len] ++ ex := by
  rw [groupVerified_eq]
  have hc : ¬((!s.rel && decide (off ≤ s.o0) && decide (s.o0 < off + len)) = true) := by
    intro hh; simp at hh; exact h ⟨hh.1.2, hh.2⟩
  rw [if_neg hc]
  have hE : Ext (Fs.emit (Fs.emit s [Ev.verified off len]) [Ev.readable off len])
      (if s.head.isSome then
        holdCheck { Fs.emit (Fs.emit s [Ev.verified off len]) [Ev.readable off len] with nv := s.nv + 1 } now none
      else Fs.emit (Fs.emit s [Ev.verified off len]) [Ev.readable off len]) := by
    split
    · exact ext_hold _ _ _
    · exact Ext.refl _
  obtain ⟨x, hx⟩ := hE
  obtain ⟨y, hy⟩ := ext_checkDone (if s.head.isSome then
        holdCheck { Fs.emit (Fs.emit s [Ev.verified off len]) [Ev.readable off len] with nv := s.nv + 1 } now none
      else Fs.emit (Fs.emit s [Ev.verified off len]) [Ev.readable off len]) now
  exact ⟨x ++ y, by rw [hy, hx]; simp⟩


/-! ## No late release -/

/-- A held granule has no cause that is already true at `now`. -/
def NoLate (s : Fs) (now : Nat) : Prop :=
  ∀ h, s.head = some h → bufOf s.store (h.off + h.len) < HOLD_B ∧
    h.off + h.len + bufOf s.store (h.off + h.len) < s.wend ∧ s.nv < HOLD_NV ∧ now < sadd h.t0 HOLD_MAX

/-- The same without the clock: what holds between calls whatever time they run at. -/
def J0 (s : Fs) : Prop :=
  ∀ h, s.head = some h → bufOf s.store (h.off + h.len) < HOLD_B ∧
    h.off + h.len + bufOf s.store (h.off + h.len) < s.wend ∧ s.nv < HOLD_NV

theorem NoLate.j0 {s : Fs} {now : Nat} (h : NoLate s now) : J0 s :=
  fun hd hh => let ⟨a, b, c, _⟩ := h hd hh; ⟨a, b, c⟩

theorem noLate_hold (s : Fs) (now : Nat) : NoLate (holdCheck s now none) now := by
  intro h hh
  cases hs : s.head with
  | none => simp [holdCheck, hs] at hh
  | some h' =>
    cases hw : holdWhy s h' now none with
    | some c => simp [holdCheck, hs, hw] at hh
    | none =>
      have hres : holdCheck s now none = s := by simp [holdCheck, hs, hw]
      rw [hres] at hh ⊢
      rw [hs] at hh
      have := Option.some.inj hh
      subst this
      rw [holdWhy_none_eq] at hw
      split at hw
      · simp at hw
      · split at hw
        · simp at hw
        · split at hw
          · simp at hw
          · split at hw
            · simp at hw
            · refine ⟨by omega, by omega, by omega, by omega⟩

theorem noLate_checkDone (s : Fs) (now : Nat) : NoLate (checkDone s now) now := by
  rw [checkDone_eq]
  split
  · intro h hh
    have := holdCheck_force_head (holdCheck s now none) now .done
    simp at hh
    rw [this] at hh
    exact absurd hh (by simp)
  · exact noLate_hold s now

/-- The fields HEAD_HOLD reads are the same. -/
def Core (s s' : Fs) : Prop :=
  s'.store = s.store ∧ s'.head = s.head ∧ s'.rel = s.rel ∧ s'.nv = s.nv ∧ s'.o0 = s.o0 ∧ s'.want = s.want

theorem Core.refl (s : Fs) : Core s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem Core.trans {a b c : Fs} (h1 : Core a b) (h2 : Core b c) : Core a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1; obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6⟩

theorem J0.core {s s' : Fs} (hj : J0 s) (hc : Core s s') : J0 s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  intro h hh
  rw [h2] at hh
  have := hj h hh
  simp only [Fs.wend, h1, h4, h5, h6]
  exact this

theorem core_byteLive (s : Fs) (now : Nat) : Core s (byteLive s now) := by
  unfold byteLive; split <;> (try split) <;> exact Core.refl _
theorem core_arrival (s : Fs) (now : Nat) : Core s (arrival s now) := by
  unfold arrival; split <;> exact Core.refl _
theorem core_fail (s : Fs) (r : Fail) : Core s (failWith s r) := Core.refl _
theorem core_stall (s : Fs) (now : Nat) (ss : List Sess) : Core s (stallStep s now ss) := by
  unfold stallStep; split <;> (try split) <;> (try split) <;> first | exact Core.refl _ | (exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
theorem core_lateStall (s : Fs) (now : Nat) (ss : List Sess) : Core s (lateStall s now ss) := by
  unfold lateStall; split
  · exact Core.refl _
  · exact core_stall s now ss
theorem core_steal (s : Fs) (now : Nat) (late rearm : Bool) : Core s (stealBlock s now late rearm) := by
  unfold stealBlock; split <;> exact Core.refl _
theorem core_retry (s : Fs) (now : Nat) (rt' : Option Nat) : Core s (retryBlock s now rt') := by
  unfold retryBlock; split <;> (try split) <;> exact Core.refl _

theorem j0_checkDone (s : Fs) (now : Nat) : J0 (checkDone s now) := (noLate_checkDone s now).j0

theorem j0_verifyStep (s : Fs) (now off len : Nat) : J0 (verifyStep s now off len) := by
  unfold verifyStep
  split
  · exact j0_checkDone _ _
  · exact j0_checkDone _ _

theorem j0_headBlock {s : Fs} (hj : J0 s) (now : Nat) : J0 (headBlock s now) := by
  unfold headBlock; split
  · exact j0_checkDone _ _
  · exact hj

theorem j0_onTimeout {s : Fs} (hj : J0 s) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat) :
    J0 (onTimeout s now ss rearm rt') := by
  by_cases hrun : s.running = true
  · have h1 := j0_headBlock (hj.core (core_lateStall s now ss)) now
    by_cases hr : (headBlock (lateStall s now ss) now).running = true
    · by_cases hl : s.late now = true
      · simp only [onTimeout, hrun, hr, hl, ite_true]
        exact (h1.core (core_steal _ _ _ _)).core (core_fail _ _)
      · simp only [onTimeout, hrun, hr, hl, ite_true, ite_false]
        exact (h1.core (core_steal _ _ _ _)).core (core_retry _ _ _)
    · simp only [onTimeout, hrun, hr, ite_true, ite_false]
      exact h1
  · simp only [onTimeout, hrun, ite_false]
    exact hj

theorem j0_step {s : Fs} (hj : J0 s) (i : Inp) : J0 (step s i) := by
  unfold step
  split
  · cases i with
    | bytes now => exact hj.core (core_byteLive s now)
    | frame now b g =>
      simp only []
      have h1 : J0 (arrival (if b = true then byteLive s now else s) now) := by
        apply J0.core (s := if b = true then byteLive s now else s) _ (core_arrival _ _)
        split
        · exact hj.core (core_byteLive s now)
        · exact hj
      cases g with
      | none => exact h1
      | some p => exact j0_verifyStep _ _ _ _
    | frameStoreFail now b =>
      simp only []
      have h1 : J0 (arrival (if b = true then byteLive s now else s) now) := by
        apply J0.core (s := if b = true then byteLive s now else s) _ (core_arrival _ _)
        split
        · exact hj.core (core_byteLive s now)
        · exact hj
      exact h1.core (core_fail _ _)
    | ahead now o l => exact j0_verifyStep _ _ _ _
    | aheadStoreFail now => exact hj.core (core_fail _ _)
    | evict now b =>
      simp only []
      have h1 : J0 (if b = true then byteLive s now else s) := by
        split
        · exact hj.core (core_byteLive s now)
        · exact hj
      by_cases ht : (if b = true then byteLive s now else s).trusted ≤ 1
      · rw [if_pos ht]
        exact (h1.core ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩).core (core_fail _ _)
      · rw [if_neg ht]
        exact h1.core ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | streamEnd now => exact j0_checkDone _ _
    | arm tw rt treq => exact hj.core ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | timeout now ss rearm rt' => exact j0_onTimeout hj now ss rearm rt'
  · exact hj

/-- Between any two calls, a held granule has fewer than `HOLD_B` bytes behind it, the wanted range does not end in
the buffer and fewer than `HOLD_NV` later granules verified: the release is never late. -/
theorem reach_j0 {s0 s : Fs} (h0 : J0 s0) (hr : Reach s0 s) : J0 s := by
  induction hr with
  | init => exact h0
  | step i _ _ ih => exact j0_step ih i


/-! ## The bound -/

/-- While a granule is held, `poll_timeout` offers a time at or before `t0 + HOLD_MAX`. -/
theorem hold_poll_le (s : Fs) (h : Head) (hr : s.running = true) (hh : s.head = some h) :
    ∃ p, pollTimeout s = some p ∧ p ≤ sadd h.t0 HOLD_MAX := by
  unfold pollTimeout
  rw [if_pos hr]
  have hmem : sadd h.t0 HOLD_MAX ∈ pollList s := by simp [pollList, hh]
  cases hm : (pollList s).min? with
  | none => simp [List.min?_eq_none_iff] at hm; rw [hm] at hmem; simp at hmem
  | some p => exact ⟨p, rfl, (List.min?_eq_some_iff.1 hm).2 _ hmem⟩

/-- A hold check of a granule whose time is up releases it. -/
theorem holdCheck_timeout_head (s : Fs) (h : Head) (now : Nat) (hh : s.head = some h) (ht : sadd h.t0 HOLD_MAX ≤ now) :
    (holdCheck s now none).head = none := by
  have := (holdWhy_isSome_iff s h now).2 (Or.inr (Or.inr (Or.inr ht)))
  cases hw : holdWhy s h now none with
  | none => simp [hw] at this
  | some c => simp [holdCheck, hh, hw]

theorem checkDone_head_none (s : Fs) (now : Nat) (hn : s.head = none) : (checkDone s now).head = none := by
  rw [checkDone_eq]
  split
  · simpa using holdCheck_force_head (holdCheck s now none) now .done
  · simp [holdCheck, hn]

theorem ext_steal (s : Fs) (now : Nat) (late rearm : Bool) : Ext s (stealBlock s now late rearm) := by
  unfold stealBlock; split
  · exact ⟨[], by simp⟩
  · exact Ext.refl _
theorem ext_retry (s : Fs) (now : Nat) (rt' : Option Nat) : Ext s (retryBlock s now rt') := by
  unfold retryBlock; split
  · split
    · exact ⟨[], by simp⟩
    · exact Ext.refl _
  · exact Ext.refl _

/-- An `on_timeout` at or after `t0 + HOLD_MAX` leaves no held granule. The stall block runs first but never
touches it, so the hold is bounded by `HOLD_MAX` however stalled the fetch is. -/
theorem onTimeout_clears_head (s : Fs) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat) (h : Head)
    (hr : s.running = true) (hh : s.head = some h) (ht : sadd h.t0 HOLD_MAX ≤ now) :
    (onTimeout s now ss rearm rt').head = none := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := core_lateStall s now ss
  have hs' : (lateStall s now ss).head = some h := by rw [c2, hh]
  have hb : (headBlock (lateStall s now ss) now).head = none := by
    unfold headBlock
    rw [if_pos (by simp [hs'])]
    exact checkDone_head_none _ _ (holdCheck_timeout_head _ h now hs' ht)
  by_cases hrun : (headBlock (lateStall s now ss) now).running = true
  · by_cases hl : s.late now = true
    · simp only [onTimeout, hr, hrun, hl, ite_true]
      have := core_steal (headBlock (lateStall s now ss) now) now true rearm
      simp [failWith, this.2.1, hb]
    · simp only [onTimeout, hr, hrun, hl, ite_true, ite_false]
      have := core_retry (stealBlock (headBlock (lateStall s now ss) now) now false rearm) now rt'
      have h2 := core_steal (headBlock (lateStall s now ss) now) now false rearm
      show (retryBlock (stealBlock (headBlock (lateStall s now ss) now) now false rearm) now rt').head = none
      rw [this.2.1, h2.2.1, hb]
  · simp only [onTimeout, hr, hrun, ite_true, ite_false]
    exact hb

/-- The cause of that release is `Timeout`, in any state where no earlier cause holds (`reach_j0`): the
`Released` record and the announcement of the granule are in the log. -/
theorem onTimeout_timeout_cause (s : Fs) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat) (h : Head)
    (hj : J0 s) (hr : s.running = true) (hh : s.head = some h) (ht : sadd h.t0 HOLD_MAX ≤ now) :
    Ev.released h.off .timeout ∈ (onTimeout s now ss rearm rt').log ∧
      Ev.readable h.off h.len ∈ (onTimeout s now ss rearm rt').log := by
  have hc := core_lateStall s now ss
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hc
  have hs' : (lateStall s now ss).head = some h := by rw [c2, hh]
  have hj' := hj.core ⟨c1, c2, c3, c4, c5, c6⟩ h hs'
  have hw : holdWhy (lateStall s now ss) h now none = some .timeout :=
    (holdWhy_timeout _ h now).2 ⟨hj'.1, hj'.2.1, hj'.2.2, ht⟩
  have hhc := holdCheck_release (lateStall s now ss) now none h .timeout hs' hw
  have hmem : Ev.released h.off .timeout ∈ (holdCheck (lateStall s now ss) now none).log ∧
      Ev.readable h.off h.len ∈ (holdCheck (lateStall s now ss) now none).log := by
    rw [hhc]; simp
  have hb : Ext (holdCheck (lateStall s now ss) now none) (headBlock (lateStall s now ss) now) := by
    unfold headBlock
    rw [if_pos (by simp [hs'])]
    exact ext_checkDone _ _
  have hE : Ext (headBlock (lateStall s now ss) now) (onTimeout s now ss rearm rt') := by
    by_cases hrun : (headBlock (lateStall s now ss) now).running = true
    · by_cases hl : s.late now = true
      · simp only [onTimeout, hr, hrun, hl, ite_true]
        exact (ext_steal _ _ _ _).trans (ext_fail _ _)
      · simp only [onTimeout, hr, hrun, hl, ite_true, ite_false]
        exact (ext_steal _ _ _ _).trans (ext_retry _ _ _)
    · simp only [onTimeout, hr, hrun, ite_true, ite_false]
      exact Ext.refl _
  exact ⟨(hb.trans hE).mem hmem.1, (hb.trans hE).mem hmem.2⟩

end Pinc.ValuesTime
