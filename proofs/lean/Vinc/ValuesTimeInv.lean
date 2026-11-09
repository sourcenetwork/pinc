import Vinc.ValuesTimeHold

/-!
# HEAD_HOLD invariants over every run

`Inv` holds of every state reachable from a well-formed start by valid inputs (`reach_inv`), and says, for the
first granule (the one that contains `o0`, the first request offset):

* an announcement (`readable`) is preceded by the verification of that group and the group is in the store
  (`ann`): nothing is announced before it is verified and stored;
* a held granule is verified, stored, announced by nobody yet, and `released` is false (`heads`);
* `dich`: a verified group that contains `o0` is either the held granule (never announced) or was announced exactly
  once and nothing is held;
* `comp`: a completed fetch holds no granule; `term`: a fetch with a terminal event is not running.

`J0` (`reach_j0`): at every point between calls a held granule has fewer than `HOLD_B` bytes behind it, the wanted
range does not end in the buffer and fewer than `HOLD_NV` later granules verified.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Vinc.ValuesTime
open Vinc.Ranges

/-- The invariant of a run. -/
structure Inv (s : Fs) : Prop where
  sound : Sound s.store
  ann : ∀ o l, Ev.readable o l ∈ s.log →
    Ev.verified o l ∈ s.log ∧ ∀ x, o ≤ x → x < o + l → Covers s.store x
  heads : ∀ h, s.head = some h → Ev.verified h.off h.len ∈ s.log ∧ Ev.held h.off ∈ s.log ∧ s.rel = false ∧
    h.off ≤ s.o0 ∧ s.o0 < h.off + h.len ∧ 0 < h.len ∧ ∀ x, h.off ≤ x → x < h.off + h.len → Covers s.store x
  seen : (s.head ≠ none ∨ s.rel = true) → ∃ o l, o ≤ s.o0 ∧ s.o0 < o + l ∧ Ev.verified o l ∈ s.log
  dich : ∀ o l, o ≤ s.o0 → s.o0 < o + l → Ev.verified o l ∈ s.log →
    ((∃ t, s.head = some ⟨o, l, t⟩) ∧ s.log.count (Ev.readable o l) = 0 ∧ s.rel = false) ∨
    (s.head = none ∧ s.rel = true ∧ s.log.count (Ev.readable o l) = 1)
  comp : Ev.complete ∈ s.log → s.head = none
  term : (Ev.complete ∈ s.log ∨ ∃ r, Ev.failed r ∈ s.log) → s.running = false

/-- No held granule: whatever else, an empty log is an invariant state. -/
theorem inv_init (o0 : Nat) (want store : List Interval) (hs : Sound store) (dl : Option Nat) (st : Bool) (n : Nat) :
    Inv (Fs.init o0 want store dl st n) := by
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Fs.init]

/-- A change of fields the invariant does not read. -/
theorem Inv.view {s s' : Fs} (hi : Inv s) (hst : s'.store = s.store) (hh : s'.head = s.head) (hr : s'.rel = s.rel)
    (ho : s'.o0 = s.o0) (hl : s'.log = s.log) (hrun : s'.running = s.running) : Inv s' := by
  obtain ⟨a, b, c, d, e, f, g⟩ := hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hst, hh, hr, ho, hl, hrun] <;> assumption

/-- Committing a range keeps the invariant: every covered byte stays covered. -/
theorem inv_commit {s : Fs} (hi : Inv s) (r : Interval) : Inv { s with store := insertVec s.store r } := by
  obtain ⟨a, b, c, d, e, f, g⟩ := hi
  have hcov : ∀ x, Covers s.store x → Covers (insertVec s.store r) x :=
    fun x hx => (insertVec_covers s.store a r x).2 (Or.inl hx)
  refine ⟨insertVec_sound _ a _, ?_, ?_, d, e, f, g⟩
  · intro o l hm
    obtain ⟨h1, h2⟩ := b o l hm
    exact ⟨h1, fun x hx1 hx2 => hcov x (h2 x hx1 hx2)⟩
  · intro h hh
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := c h hh
    exact ⟨h1, h2, h3, h4, h5, h6, fun x hx1 hx2 => hcov x (h7 x hx1 hx2)⟩

/-- A failure record keeps the invariant. -/
theorem inv_fail {s : Fs} (hi : Inv s) (r : Fail) : Inv (failWith s r) := by
  obtain ⟨a, b, c, d, e, f, g⟩ := hi
  refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o l hm
    simp [failWith] at hm ⊢
    exact b o l hm
  · intro h hh
    simpa [failWith] using c h hh
  · simpa [failWith] using d
  · intro o l h1 h2 h3
    simp [failWith] at h3 ⊢
    exact e o l h1 h2 h3
  · intro hc
    simp [failWith] at hc ⊢
    exact f hc
  · intro _
    simp [failWith]

/-- A redial record keeps the invariant. -/
theorem inv_redial {s : Fs} (hi : Inv s) (now : Nat) : Inv (redial s now) := by
  have hl : (redial s now).log = s.log ++ [Ev.redial s.sw (min (smul s.sw 2) STALL_CAP)] := rfl
  obtain ⟨a, b, c, d, e, f, g⟩ := hi
  have hmem : ∀ e', (∀ w n, e' ≠ Ev.redial w n) → (e' ∈ (redial s now).log ↔ e' ∈ s.log) := by
    intro e' hne
    rw [hl]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h (hne _ _)
    · exact Or.inl
  have hcnt : (redial s now).log.count (Ev.readable 0 0) = s.log.count (Ev.readable 0 0) := by
    rw [hl]; simp
  refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o l hm
    have hm' := (hmem _ (by intro w n; simp)).1 hm
    obtain ⟨h1, h2⟩ := b o l hm'
    exact ⟨(hmem _ (by intro w n; simp)).2 h1, h2⟩
  · intro h hh
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := c h hh
    exact ⟨(hmem _ (by intro w n; simp)).2 h1, (hmem _ (by intro w n; simp)).2 h2, h3, h4, h5, h6, h7⟩
  · intro hn
    obtain ⟨o, l, h1, h2, h3⟩ := d hn
    exact ⟨o, l, h1, h2, (hmem _ (by intro w n; simp)).2 h3⟩
  · intro o l h1 h2 h3
    have h3' := (hmem _ (by intro w n; simp)).1 h3
    have hc : (redial s now).log.count (Ev.readable o l) = s.log.count (Ev.readable o l) := by
      rw [hl]; simp
    rw [hc]
    exact e o l h1 h2 h3'
  · intro hc
    exact f ((hmem _ (by intro w n; simp)).1 hc)
  · intro hc
    apply g
    rcases hc with hc | ⟨r, hr⟩
    · exact Or.inl ((hmem _ (by intro w n; simp)).1 hc)
    · exact Or.inr ⟨r, (hmem _ (by intro w n; simp)).1 hr⟩

/-- A hold check keeps the invariant, for any forced cause. -/
theorem inv_hold {s : Fs} (hi : Inv s) (now : Nat) (force : Option Cause) : Inv (holdCheck s now force) := by
  cases hh : s.head with
  | none => simpa [holdCheck, hh] using hi
  | some h =>
    cases hw : holdWhy s h now force with
    | none => simpa [holdCheck, hh, hw] using hi
    | some c =>
      obtain ⟨a, b, cc, d, e, f, g⟩ := hi
      obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := cc h hh
      have hrel : holdCheck s now force =
          Fs.emit { s with head := none, rel := true } [.released h.off c, .readable h.off h.len] := by
        simp [holdCheck, hh, hw]
      rw [hrel]
      refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro o l hm
        simp at hm ⊢
        rcases hm with hm | ⟨rfl, rfl⟩
        · obtain ⟨h1, h2⟩ := b o l hm
          exact ⟨h1, h2⟩
        · exact ⟨v1, v7⟩
      · simp
      · intro _
        exact ⟨h.off, h.len, v4, v5, by simp [v1]⟩
      · intro o l h1 h2 h3
        simp at h3 ⊢
        rcases e o l h1 h2 h3 with ⟨⟨t, ht⟩, hc0, hr0⟩ | ⟨hn, _⟩
        · rw [hh] at ht
          have := Option.some.inj ht
          obtain ⟨off, len, t0⟩ := h
          simp at this
          obtain ⟨rfl, rfl, rfl⟩ := this
          simp [List.count_append, hc0]
        · rw [hh] at hn; exact absurd hn (by simp)
      · intro _; rfl
      · intro hc
        simp at hc ⊢
        exact g (by simpa using hc)

/-- A forced release always empties the hold. -/
theorem holdCheck_force_head (s : Fs) (now : Nat) (c : Cause) : (holdCheck s now (some c)).head = none := by
  cases hh : s.head with
  | none => simp [holdCheck, hh]
  | some h => simp [holdCheck, hh, holdWhy]

/-- Completion with no held granule keeps the invariant. -/
theorem inv_complete {s : Fs} (hi : Inv s) (hn : s.head = none) :
    Inv (Fs.emit { s with running := false } [.complete]) := by
  obtain ⟨a, b, c, d, e, f, g⟩ := hi
  refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o l hm
    simp at hm ⊢
    exact b o l hm
  · intro h hh
    simp [hn] at hh
  · intro hc
    simp [hn] at hc ⊢
    obtain ⟨o, l, h1, h2, h3⟩ := d (Or.inr hc)
    exact ⟨o, h1, l, h2, h3⟩
  · intro o l h1 h2 h3
    simp [hn] at h3 ⊢
    rcases e o l h1 h2 h3 with ⟨⟨t, ht⟩, _⟩ | ⟨_, hr, hc⟩
    · simp [hn] at ht
    · exact ⟨hr, hc⟩
  · intro _; simpa using hn
  · intro _; rfl

/-- The `is_some` guards of the code are redundant: a hold check of no granule does nothing. -/
theorem hold_guard (s : Fs) (now : Nat) (f : Option Cause) :
    (if s.head.isSome then holdCheck s now f else s) = holdCheck s now f := by
  cases hh : s.head <;> simp [holdCheck, hh]

theorem checkDone_eq (s : Fs) (now : Nat) :
    checkDone s now =
      if (holdCheck s now none).wantedDone then
        Fs.emit { holdCheck (holdCheck s now none) now (some .done) with running := false } [.complete]
      else holdCheck s now none := by
  unfold checkDone
  simp only [hold_guard]

/-- The completion check keeps the invariant. -/
theorem inv_checkDone {s : Fs} (hi : Inv s) (now : Nat) : Inv (checkDone s now) := by
  rw [checkDone_eq]
  have h1 := inv_hold hi now none
  split
  · exact inv_complete (inv_hold h1 now _) (holdCheck_force_head _ _ _)
  · exact h1

/-- No group verified so far contains `o0` once a new group does (the groups are disjoint). -/
theorem GroupOk.no_old {s : Fs} {off len : Nat} (hg : GroupOk s off len) (h1 : off ≤ s.o0) (h2 : s.o0 < off + len)
    {o l : Nat} (hm : Ev.verified o l ∈ s.log) (h3 : o ≤ s.o0) (h4 : s.o0 < o + l) : False := by
  have := hg.2 o l hm
  omega

theorem groupVerified_eq (s : Fs) (now off len : Nat) :
    groupVerified s now off len = checkDone
      (if (!s.rel && decide (off ≤ s.o0) && decide (s.o0 < off + len)) = true then
        Fs.emit { Fs.emit s [Ev.verified off len] with
          head := some ⟨off, len, match s.head with | some h => h.t0 | none => now⟩, nv := 0 } [Ev.held off]
      else
        if s.head.isSome then
          holdCheck { Fs.emit (Fs.emit s [Ev.verified off len]) [Ev.readable off len] with nv := s.nv + 1 } now none
        else Fs.emit (Fs.emit s [Ev.verified off len]) [Ev.readable off len]) now := rfl

/-- A verified group keeps the invariant: the first granule is captured, a later one is announced at once. -/
theorem inv_group {s : Fs} (hi : Inv s) (now off len : Nat) (hg : GroupOk s off len)
    (hcov : ∀ x, off ≤ x → x < off + len → Covers s.store x) (hnc : Ev.complete ∉ s.log) :
    Inv (groupVerified s now off len) := by
  rw [groupVerified_eq]
  apply inv_checkDone
  obtain ⟨a, b, c, d, e, f, g⟩ := hi
  have hlen := hg.1
  have hfresh : Ev.readable off len ∉ s.log := fun hm => by
    have := (b off len hm).1
    have := hg.2 off len this
    omega
  by_cases hc : (!s.rel && decide (off ≤ s.o0) && decide (s.o0 < off + len)) = true
  · rw [if_pos hc]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨⟨hr, h1⟩, h2⟩ := hc
    refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro o l hm
      simp at hm
      obtain ⟨h1', h2'⟩ := b o l hm
      exact ⟨by simp [h1'], h2'⟩
    · intro h hh
      simp at hh
      subst hh
      exact ⟨by simp, by simp, hr, h1, h2, hlen, hcov⟩
    · intro _
      exact ⟨off, len, h1, h2, by simp⟩
    · intro o l h3 h4 h5
      simp at h5
      rcases h5 with h5 | ⟨rfl, rfl⟩
      · exact (hg.no_old h1 h2 h5 h3 h4).elim
      · left
        refine ⟨⟨_, rfl⟩, ?_, hr⟩
        simp [List.count_eq_zero, hfresh]
    · intro hcm; simp at hcm; exact absurd hcm hnc
    · intro hx
      apply g
      simp at hx
      rcases hx with hx | ⟨r, hr'⟩
      · exact absurd hx hnc
      · exact Or.inr ⟨r, hr'⟩
  · have hno : ¬(off ≤ s.o0 ∧ s.o0 < off + len) := by
      intro ⟨h1, h2⟩
      apply hc
      cases hrl : s.rel
      · simp [h1, h2]
      · obtain ⟨o, l, h3, h4, h5⟩ := d (Or.inr hrl)
        exact (hg.no_old h1 h2 h5 h3 h4).elim
    rw [if_neg hc]
    have hI : Inv (Fs.emit (Fs.emit s [.verified off len]) [.readable off len]) := by
      refine ⟨a, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro o l hm
        simp at hm ⊢
        rcases hm with hm | ⟨rfl, rfl⟩
        · obtain ⟨h1', h2'⟩ := b o l hm
          exact ⟨Or.inl h1', h2'⟩
        · exact ⟨Or.inr ⟨rfl, rfl⟩, hcov⟩
      · intro h hh
        simp at hh ⊢
        obtain ⟨h1', h2', h3', h4', h5', h6', h7'⟩ := c h hh
        exact ⟨Or.inl h1', h2', h3', h4', h5', h6', h7'⟩
      · intro hx
        simp at hx ⊢
        obtain ⟨o, l, h1', h2', h3'⟩ := d hx
        exact ⟨o, h1', l, h2', Or.inl h3'⟩
      · intro o l h3 h4 h5
        simp at h5
        have h5' : Ev.verified o l ∈ s.log := by
          rcases h5 with h5 | ⟨rfl, rfl⟩
          · exact h5
          · exact absurd ⟨h3, h4⟩ hno
        have hne : Ev.readable off len ≠ Ev.readable o l := by
          intro heq; simp at heq; obtain ⟨rfl, rfl⟩ := heq; exact hno ⟨h3, h4⟩
        have hcnt : (Fs.emit (Fs.emit s [.verified off len]) [.readable off len]).log.count (Ev.readable o l)
            = s.log.count (Ev.readable o l) := by
          simp [List.count_append, List.count_cons, hne]
        simp only [emit_head, emit_rel, hcnt]
        exact e o l h3 h4 h5'
      · intro hx; simp at hx; exact absurd hx hnc
      · intro hx
        apply g
        simp at hx
        rcases hx with hx | ⟨r, hr'⟩
        · exact absurd hx hnc
        · exact Or.inr ⟨r, hr'⟩
    split
    · exact inv_hold (hI.view (s' := { Fs.emit (Fs.emit s [Ev.verified off len]) [Ev.readable off len] with
        nv := s.nv + 1 }) rfl rfl rfl rfl rfl rfl) now none
    · exact hI

/-- Commit and announce keep the invariant (the group is disjoint from the verified ones). -/
theorem inv_verify {s : Fs} (hi : Inv s) (now off len : Nat) (hg : GroupOk s off len) (hnc : Ev.complete ∉ s.log) :
    Inv (verifyStep s now off len) := by
  unfold verifyStep
  have hc := inv_commit hi (off, off + len)
  apply inv_group hc now off len hg
  · intro x h1 h2
    exact (insertVec_covers s.store hi.sound _ x).2 (Or.inr ⟨h1, h2⟩)
  · exact hnc

/-- Bytes arriving or a frame completing keep the invariant (only the stall fields change). -/
theorem inv_byteLive {s : Fs} (hi : Inv s) (now : Nat) : Inv (byteLive s now) := by
  unfold byteLive; split
  · exact hi.view rfl rfl rfl rfl rfl rfl
  · split
    · exact hi.view rfl rfl rfl rfl rfl rfl
    · exact hi.view rfl rfl rfl rfl rfl rfl

theorem inv_arrival {s : Fs} (hi : Inv s) (now : Nat) : Inv (arrival s now) := by
  unfold arrival; split
  · exact hi.view rfl rfl rfl rfl rfl rfl
  · exact hi.view rfl rfl rfl rfl rfl rfl

theorem inv_stall {s : Fs} (hi : Inv s) (now : Nat) (ss : List Sess) : Inv (stallStep s now ss) := by
  unfold stallStep; split
  · split
    · exact hi.view rfl rfl rfl rfl rfl rfl
    · split
      · exact hi.view rfl rfl rfl rfl rfl rfl
      · exact inv_redial hi now
  · exact hi

theorem inv_headBlock {s : Fs} (hi : Inv s) (now : Nat) : Inv (headBlock s now) := by
  unfold headBlock; split
  · exact inv_checkDone (inv_hold hi now none) now
  · exact hi

theorem inv_lateStall {s : Fs} (hi : Inv s) (now : Nat) (ss : List Sess) : Inv (lateStall s now ss) := by
  unfold lateStall; split
  · exact hi
  · exact inv_stall hi now ss

theorem inv_steal {s : Fs} (hi : Inv s) (now : Nat) (late rearm : Bool) : Inv (stealBlock s now late rearm) := by
  unfold stealBlock; split
  · exact hi.view rfl rfl rfl rfl rfl rfl
  · exact hi

theorem inv_retry {s : Fs} (hi : Inv s) (now : Nat) (rt' : Option Nat) : Inv (retryBlock s now rt') := by
  unfold retryBlock
  split
  · split
    · exact hi.view rfl rfl rfl rfl rfl rfl
    · exact hi
  · exact hi

theorem inv_onTimeout {s : Fs} (hi : Inv s) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat) :
    Inv (onTimeout s now ss rearm rt') := by
  by_cases hrun : s.running = true
  · have h1 := inv_headBlock (inv_lateStall hi now ss) now
    by_cases hr : (headBlock (lateStall s now ss) now).running = true
    · by_cases hl : s.late now = true
      · simp only [onTimeout, hrun, hr, hl, ite_true]
        exact inv_fail (inv_steal h1 _ _ _) _
      · simp only [onTimeout, hrun, hr, hl, ite_true, ite_false]
        exact inv_retry (inv_steal h1 _ _ _) _ _
    · simp only [onTimeout, hrun, hr, ite_true, ite_false]
      exact h1
  · simp only [onTimeout, hrun, ite_false]
    exact hi

theorem byteLive_log (s : Fs) (now : Nat) : (byteLive s now).log = s.log := by
  unfold byteLive; split <;> (try split) <;> rfl

theorem arrival_log (s : Fs) (now : Nat) : (arrival s now).log = s.log := by
  unfold arrival; split <;> rfl

theorem GroupOk.of_log {s s' : Fs} (h : s'.log = s.log) {o l : Nat} (hg : GroupOk s o l) : GroupOk s' o l := by
  unfold GroupOk at *; rw [h]; exact hg

/-- Every input keeps the invariant. -/
theorem inv_step {s : Fs} (hi : Inv s) (i : Inp) (hv : Valid s i) : Inv (step s i) := by
  unfold step
  split
  · rename_i hrun
    have hnc : Ev.complete ∉ s.log := fun hm => by
      have := hi.term (Or.inl hm); simp_all
    cases i with
    | bytes now => exact inv_byteLive hi now
    | frame now b g =>
      simp only []
      have h1 : Inv (arrival (if b then byteLive s now else s) now) := by
        apply inv_arrival
        split
        · exact inv_byteLive hi now
        · exact hi
      cases g with
      | none => exact h1
      | some p =>
        obtain ⟨o, l⟩ := p
        simp only [Valid] at hv
        have hl : (arrival (if b = true then byteLive s now else s) now).log = s.log := by
          rw [arrival_log]; split
          · exact byteLive_log _ _
          · rfl
        exact inv_verify h1 now o l (hv.of_log hl) (by rw [hl]; exact hnc)
    | frameStoreFail now b =>
      simp only []
      exact inv_fail (inv_arrival (by split; exact inv_byteLive hi now; exact hi) now) _
    | ahead now o l => exact inv_verify hi now o l hv hnc
    | aheadStoreFail now => exact inv_fail hi _
    | evict now b =>
      simp only []
      have h1 : Inv (if b = true then byteLive s now else s) := by
        split
        · exact inv_byteLive hi now
        · exact hi
      by_cases ht : (if b = true then byteLive s now else s).trusted ≤ 1
      · rw [if_pos ht]
        exact inv_fail (h1.view (s' := { (if b = true then byteLive s now else s) with trusted := 0 })
          rfl rfl rfl rfl rfl rfl) _
      · rw [if_neg ht]
        exact h1.view rfl rfl rfl rfl rfl rfl
    | streamEnd now => exact inv_checkDone hi now
    | arm tw rt treq => exact hi.view rfl rfl rfl rfl rfl rfl
    | timeout now ss rearm rt' => exact inv_onTimeout hi now ss rearm rt'
  · exact hi

/-- The invariant holds in every reachable state. -/
theorem reach_inv {s0 s : Fs} (h0 : Inv s0) (hr : Reach s0 s) : Inv s := by
  induction hr with
  | init => exact h0
  | step i _ hv ih => exact inv_step ih i hv

end Vinc.ValuesTime
