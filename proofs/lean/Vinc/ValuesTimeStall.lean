import Vinc.ValuesTimeBound

/-!
# STALL_REDIAL (property 8)

The wait `sw` before a fresh dial, and what moves it, from `Vinc/ValuesTime.lean`:

* `arrival_*` (ARK_PACE), `byteLive_*` (BYTE_LIVE), `stallRtt_le` (STALL_RTT), `stallLive_*` (STALL_LIVE), `redial_*`
  (the doubling): each cap is respected.
* `stallStep_cases`, `redial_iff`, `redial_only_after_silence`: exactly which events trigger a redial.
* `sw_decrease`: the wait is not monotone, and `sw_decrease_cases` says exactly where it falls: ARK_PACE when the wait
  stood above 40 s, and the redial when it stood above 16 s. Nothing else lowers it.
* `sw_ge`, `sw_le`: over every run the wait is at least 4 s and at most 60 s, or at most `LIVE_CAP` plus the largest
  STALL_LIVE extension when that rule is taken.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Vinc.ValuesTime
open Vinc.Ranges

/-! ## The sequence of waits -/

/-- The wait after a redial. -/
def nextSw (sw : Nat) : Nat := min (smul sw 2) STALL_CAP

theorem nextSw_sequence : nextSw STALL_WAIT = 8 * NS ∧ nextSw (8 * NS) = 16 * NS ∧ nextSw (16 * NS) = 16 * NS := by
  unfold nextSw smul STALL_WAIT STALL_CAP NS U64Max
  decide

theorem nextSw_le (sw : Nat) : nextSw sw ≤ STALL_CAP := by unfold nextSw; ucs; omega

/-- The redial doubles the wait up to the cap, and never lowers a wait that is at most the cap. -/
theorem nextSw_ge_of_le (sw : Nat) (h : sw ≤ STALL_CAP) : sw ≤ nextSw sw := by
  unfold nextSw smul; ucs; omega

/-- It lowers a wait above the cap to the cap. -/
theorem nextSw_lt_iff (sw : Nat) : nextSw sw < sw ↔ STALL_CAP < sw := by
  unfold nextSw smul; ucs; omega

/-! ## ARK_PACE, BYTE_LIVE -/

theorem arrival_lastp (s : Fs) (now : Nat) : (arrival s now).lastp = now := by
  unfold arrival; split <;> rfl

theorem arrival_lastb (s : Fs) (now : Nat) : (arrival s now).lastb = s.lastb := by
  unfold arrival; split <;> rfl

/-- ARK_PACE never takes the wait past 40 s unless it already was. -/
theorem arrival_le (s : Fs) (now : Nat) : (arrival s now).sw ≤ max s.sw ARK_PACE_CAP := by
  unfold arrival; split <;> simp <;> omega

/-- ARK_PACE changes the wait only to `min 40 s (3 * gap)` and only when `3 * gap` exceeds it. -/
theorem arrival_sw_cases (s : Fs) (now : Nat) :
    ((arrival s now).sw = s.sw) ∨
      (s.lastp ≠ 0 ∧ s.sw < smul (now - s.lastp) 3 ∧ (arrival s now).sw = min ARK_PACE_CAP (smul (now - s.lastp) 3)) := by
  unfold arrival; split
  · exact Or.inr ⟨by omega, by omega, rfl⟩
  · exact Or.inl rfl

/-- The wait falls under ARK_PACE exactly when it stood above 40 s, the pace is slower than it, and a frame
had arrived before. -/
theorem arrival_lt_iff (s : Fs) (now : Nat) :
    (arrival s now).sw < s.sw ↔ s.lastp ≠ 0 ∧ ARK_PACE_CAP < s.sw ∧ s.sw < smul (now - s.lastp) 3 := by
  unfold arrival; split <;> simp <;> omega

theorem byteLive_lastb (s : Fs) (now : Nat) : (byteLive s now).lastb = now := by
  unfold byteLive; split <;> (try split) <;> rfl

theorem byteLive_lastp (s : Fs) (now : Nat) : (byteLive s now).lastp = s.lastp := by
  unfold byteLive; split <;> (try split) <;> rfl

/-- BYTE_LIVE only raises the wait, and not past 60 s unless it already was. -/
theorem byteLive_ge (s : Fs) (now : Nat) : s.sw ≤ (byteLive s now).sw := by
  unfold byteLive; split <;> (try split) <;> simp <;> omega

theorem byteLive_le (s : Fs) (now : Nat) : (byteLive s now).sw ≤ max s.sw BYTE_GAP_CAP := by
  unfold byteLive; split <;> (try split) <;> simp <;> omega

/-! ## STALL_RTT, STALL_LIVE -/

theorem stallRtt_le (ss : List Sess) : stallRtt ss ≤ STALL_RTT_CAP := by unfold stallRtt; simp only []; omega

theorem liveStep_some (now lastp d : Nat) (p : Sess) (v : Nat) (h : liveStep now lastp (some d) p = some v) :
    d ≤ v ∧ STALL_WAIT ≤ v ∧ v ≤ max d U64Max ∧ now - lastp ≤ LIVE_CAP ∧
      p.conn = true ∧ ∃ i, p.info = some i ∧ i.pto = false ∧ SLOW_RTT ≤ rttOf i := by
  unfold liveStep at h
  cases hi : (if p.conn = true then p.info else none) with
  | none => simp [hi] at h
  | some i =>
    simp only [hi] at h
    split at h
    · simp at h
    · rename_i hc
      have hconn : p.conn = true := by
        by_cases hc2 : p.conn = true
        · exact hc2
        · simp [hc2] at hi
      have hinfo : p.info = some i := by simpa [hconn] using hi
      simp only [not_or, Nat.not_lt] at hc
      have hv := Option.some.inj h
      obtain ⟨hc1, hc2, hc3, hc4⟩ := hc
      refine ⟨by omega, by omega, ?_, by omega, hconn, i, hinfo, by simpa using hc2, by omega⟩
      simp only [smul] at hv ⊢
      ucs
      omega

theorem foldl_none (now lastp : Nat) (l : List Sess) : l.foldl (liveStep now lastp) none = none := by
  induction l with
  | nil => rfl
  | cons p t ih => simpa [List.foldl, liveStep] using ih

/-- The fold of `stall_live`: it aborts, or every session passed. -/
theorem stallLive_fold (now lastp : Nat) (l : List Sess) (d : Nat) :
    l.foldl (liveStep now lastp) (some d) = none ∨
      ∃ v, l.foldl (liveStep now lastp) (some d) = some v ∧ d ≤ v ∧ v ≤ max d U64Max ∧ (l = [] → v = d) ∧
        (l ≠ [] → STALL_WAIT ≤ v ∧ now - lastp ≤ LIVE_CAP) ∧
        ∀ p ∈ l, p.conn = true ∧ ∃ i, p.info = some i ∧ i.pto = false ∧ SLOW_RTT ≤ rttOf i := by
  induction l generalizing d with
  | nil => exact Or.inr ⟨d, rfl, Nat.le_refl _, Nat.le_max_left _ _, fun _ => rfl, by simp, by simp⟩
  | cons p t ih =>
    cases hs : liveStep now lastp (some d) p with
    | none => left; simp [List.foldl, hs, foldl_none]
    | some v1 =>
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := liveStep_some now lastp d p v1 hs
      rcases ih v1 with h | ⟨v, hv, b1, b2, b3, b4, b5⟩
      · left; simpa [List.foldl, hs] using h
      · right
        refine ⟨v, by simpa [List.foldl, hs] using hv, by omega, by omega, by simp, fun _ => ⟨by omega, a4⟩, ?_⟩
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact ⟨a5, a6⟩
        · exact b5 q hq

/-- STALL_LIVE is 0 or at least the first wait, and at most `u64::MAX`. -/
theorem stallLive_zero_or_ge (now lastp : Nat) (ss : List Sess) :
    stallLive now lastp ss = 0 ∨ STALL_WAIT ≤ stallLive now lastp ss := by
  unfold stallLive
  rcases stallLive_fold now lastp ss 0 with h | ⟨v, hv, _, _, h0, h1, _⟩
  · simp [h]
  · rw [hv]
    by_cases hl : ss = []
    · left; simp [h0 hl]
    · right; simpa using (h1 hl).1

theorem stallLive_le (now lastp : Nat) (ss : List Sess) : stallLive now lastp ss ≤ U64Max := by
  unfold stallLive
  rcases stallLive_fold now lastp ss 0 with h | ⟨v, hv, _, b3, _⟩
  · simp [h]
  · rw [hv]; simp; omega

/-- STALL_LIVE is nonzero only for a fetch with assigned sessions, all connected, slow (250 ms or more), without a
probe timeout, and with a verified frame less than `LIVE_CAP` ago. -/
theorem stallLive_ne_zero (now lastp : Nat) (ss : List Sess) (h : stallLive now lastp ss ≠ 0) :
    ss ≠ [] ∧ now - lastp ≤ LIVE_CAP ∧ STALL_WAIT ≤ stallLive now lastp ss ∧
      ∀ p ∈ ss, p.conn = true ∧ ∃ i, p.info = some i ∧ i.pto = false ∧ SLOW_RTT ≤ rttOf i := by
  unfold stallLive at *
  rcases stallLive_fold now lastp ss 0 with h' | ⟨v, hv, _, _, h0, h1, h2⟩
  · simp [h'] at h
  · rw [hv] at h ⊢
    simp at h ⊢
    have hl : ss ≠ [] := by
      intro e; exact h (h0 e)
    exact ⟨hl, by have := (h1 hl).2; omega, (h1 hl).1, h2⟩


/-! ## The stall block of `on_timeout` -/

/-- The stall wait is spent: a frame arrived once, and no frame and no byte for `sw` (saturating). -/
def Due (s : Fs) (now : Nat) : Prop := s.lastp ≠ 0 ∧ sadd (stallBase s) s.sw ≤ now

/-- STALL_RTT applies: its wait is longer than the current one and still in the future. -/
def RttWait (s : Fs) (now : Nat) (ss : List Sess) : Prop :=
  s.sw < stallRtt ss ∧ now < sadd (lastProg s) (stallRtt ss)

theorem stallStep_idle (s : Fs) (now : Nat) (ss : List Sess) (h : ¬ Due s now) : stallStep s now ss = s := by
  unfold stallStep Due at *
  rw [if_neg h]

theorem stallStep_rtt (s : Fs) (now : Nat) (ss : List Sess) (hd : Due s now) (hr : RttWait s now ss) :
    stallStep s now ss = { s with sw := stallRtt ss } := by
  unfold stallStep Due RttWait at *
  rw [if_pos hd, if_pos hr]

theorem stallStep_live (s : Fs) (now : Nat) (ss : List Sess) (hd : Due s now) (hr : ¬ RttWait s now ss)
    (hl : stallLive now (lastProg s) ss ≠ 0) :
    stallStep s now ss = { s with sw := sadd (now - lastProg s) (stallLive now (lastProg s) ss) } := by
  unfold stallStep Due RttWait at *
  rw [if_pos hd, if_neg hr, if_pos hl]

theorem stallStep_redial (s : Fs) (now : Nat) (ss : List Sess) (hd : Due s now) (hr : ¬ RttWait s now ss)
    (hl : stallLive now (lastProg s) ss = 0) : stallStep s now ss = redial s now := by
  unfold stallStep Due RttWait at *
  rw [if_pos hd, if_neg hr, if_neg (by simpa using hl)]

/-- A redial happens exactly when the wait is spent, STALL_RTT has no longer wait in the future and STALL_LIVE finds
no slow-but-receiving session. -/
theorem redial_iff (s : Fs) (now : Nat) (ss : List Sess) :
    (stallStep s now ss).log ≠ s.log ↔ (Due s now ∧ ¬ RttWait s now ss ∧ stallLive now (lastProg s) ss = 0) := by
  by_cases hd : Due s now
  · by_cases hr : RttWait s now ss
    · rw [stallStep_rtt s now ss hd hr]; simp [hd, hr]
    · by_cases hl : stallLive now (lastProg s) ss = 0
      · rw [stallStep_redial s now ss hd hr hl]; simp [redial, hd, hr, hl]
      · rw [stallStep_live s now ss hd hr hl]; simp [hd, hr, hl]
  · rw [stallStep_idle s now ss hd]; simp [hd]

/-- A redial needs `sw` of silence: the clock has reached the later of the last frame and the last byte plus the
wait, and, if that sum does not overflow, `sw` nanoseconds really passed since both. -/
theorem redial_only_after_silence (s : Fs) (now : Nat) (ss : List Sess) (h : (stallStep s now ss).log ≠ s.log) :
    s.lastp ≠ 0 ∧ sadd (stallBase s) s.sw ≤ now ∧
      (stallBase s + s.sw ≤ U64Max → s.sw ≤ now - lastProg s ∧ s.sw ≤ now - s.lastb) := by
  obtain ⟨hd, _, _⟩ := (redial_iff s now ss).1 h
  refine ⟨hd.1, hd.2, fun hov => ?_⟩
  have := hd.2
  have e1 : lastProg s ≤ stallBase s := by simp only [lastProg, stallBase]; omega
  have e2 : s.lastb ≤ stallBase s := by simp only [stallBase]; omega
  simp only [sadd] at this
  omega

/-- The wait after each branch. -/
theorem stallStep_sw_rtt (s : Fs) (now : Nat) (ss : List Sess) (hd : Due s now) (hr : RttWait s now ss) :
    (stallStep s now ss).sw = stallRtt ss ∧ s.sw < stallRtt ss ∧ stallRtt ss ≤ STALL_RTT_CAP := by
  rw [stallStep_rtt s now ss hd hr]
  exact ⟨rfl, hr.1, stallRtt_le ss⟩

theorem stallStep_sw_live (s : Fs) (now : Nat) (ss : List Sess) (hd : Due s now) (hr : ¬ RttWait s now ss)
    (hl : stallLive now (lastProg s) ss ≠ 0) :
    (stallStep s now ss).sw ≤ LIVE_CAP + stallLive now (lastProg s) ss ∧
      (stallBase s + s.sw ≤ U64Max → s.sw ≤ (stallStep s now ss).sw) := by
  rw [stallStep_live s now ss hd hr hl]
  obtain ⟨_, hlive, hge, _⟩ := stallLive_ne_zero now (lastProg s) ss hl
  have h2 := hd.2
  have e1 : lastProg s ≤ stallBase s := by simp only [lastProg, stallBase]; omega
  simp only [sadd] at h2 ⊢
  constructor
  · omega
  · intro hov; ucs; omega

theorem stallStep_sw_redial (s : Fs) (now : Nat) (ss : List Sess) (hd : Due s now) (hr : ¬ RttWait s now ss)
    (hl : stallLive now (lastProg s) ss = 0) : (stallStep s now ss).sw = nextSw s.sw := by
  rw [stallStep_redial s now ss hd hr hl]; rfl


/-! ## What moves the wait -/

theorem sw_hold (s : Fs) (now : Nat) (f : Option Cause) : (holdCheck s now f).sw = s.sw := by
  unfold holdCheck; split <;> (try split) <;> simp

theorem sw_checkDone (s : Fs) (now : Nat) : (checkDone s now).sw = s.sw := by
  rw [checkDone_eq]; split <;> simp [sw_hold]

theorem sw_group (s : Fs) (now off len : Nat) : (groupVerified s now off len).sw = s.sw := by
  rw [groupVerified_eq, sw_checkDone]
  split
  · simp
  · split <;> simp [sw_hold]

theorem sw_verifyStep (s : Fs) (now off len : Nat) : (verifyStep s now off len).sw = s.sw := by
  unfold verifyStep
  split
  · unfold dupStep; rw [sw_checkDone]; rfl
  · rw [sw_group]

theorem sw_headBlock (s : Fs) (now : Nat) : (headBlock s now).sw = s.sw := by
  unfold headBlock; split <;> simp [sw_checkDone, sw_hold]

theorem sw_onTimeout (s : Fs) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat) :
    (onTimeout s now ss rearm rt').sw = if s.running then (lateStall s now ss).sw else s.sw := by
  by_cases hrun : s.running = true
  · by_cases hr : (headBlock (lateStall s now ss) now).running = true
    · by_cases hl : s.late now = true
      · simp only [onTimeout, hrun, hr, hl, ite_true]
        simp [failWith, stealBlock, sw_headBlock]
      · simp only [onTimeout, hrun, hr, hl, ite_true, ite_false]
        show (retryBlock (stealBlock (headBlock (lateStall s now ss) now) now false rearm) now rt').sw = _
        unfold retryBlock stealBlock; split <;> (try split) <;> (try split) <;> simp [sw_headBlock]
    · simp only [onTimeout, hrun, hr, ite_true, ite_false]; simp [sw_headBlock]
  · simp [onTimeout, hrun]

/-- Every input leaves the wait unchanged, or moves it by exactly one of the four rules. -/
theorem step_sw_eq (s : Fs) (i : Inp) :
    (step s i).sw = s.sw ∨
    (∃ now b, (step s i).sw = (if b = true then byteLive s now else s).sw) ∨
    (∃ now b, ((∃ g, i = .frame now b g) ∨ i = .frameStoreFail now b) ∧
      (step s i).sw = (arrival (if b = true then byteLive s now else s) now).sw) ∨
    (∃ now ss re rt, i = .timeout now ss re rt ∧ s.running = true ∧ (step s i).sw = (lateStall s now ss).sw) := by
  by_cases hrun : s.running = true
  · cases i with
    | bytes now =>
      right; left; exact ⟨now, true, by simp [step, hrun]⟩
    | frame now b g =>
      right; right; left
      refine ⟨now, b, Or.inl ⟨g, rfl⟩, ?_⟩
      simp only [step, hrun, ite_true]
      cases g with
      | none => rfl
      | some p => obtain ⟨o, l⟩ := p; simp [sw_verifyStep]
    | frameStoreFail now b =>
      right; right; left
      exact ⟨now, b, Or.inr rfl, by simp [step, hrun, failWith]⟩
    | ahead now o l => left; simp [step, hrun, sw_verifyStep]
    | aheadStoreFail now => left; simp [step, hrun, failWith]
    | evict now b =>
      right; left
      refine ⟨now, b, ?_⟩
      simp only [step, hrun, ite_true]
      by_cases ht : (if b = true then byteLive s now else s).trusted ≤ 1
      · rw [if_pos ht]; simp [failWith]
      · rw [if_neg ht]
    | streamEnd now => left; simp [step, hrun, sw_checkDone]
    | arm tw rt treq => left; simp [step, hrun]
    | timeout now ss re rt =>
      right; right; right
      exact ⟨now, ss, re, rt, rfl, hrun, by simp [step, hrun, sw_onTimeout]⟩
  · left; simp [step, hrun]

/-- The wait is at least the first wait, forever. -/
theorem step_sw_ge (s : Fs) (i : Inp) (h : STALL_WAIT ≤ s.sw) : STALL_WAIT ≤ (step s i).sw := by
  rcases step_sw_eq s i with h1 | ⟨now, b, h2⟩ | ⟨now, b, _, h3⟩ | ⟨now, ss, re, rt, _, _, h4⟩
  · rw [h1]; exact h
  · rw [h2]; split
    · have := byteLive_ge s now; omega
    · exact h
  · rw [h3]
    have hx : STALL_WAIT ≤ (if b = true then byteLive s now else s).sw := by
      split
      · have := byteLive_ge s now; omega
      · exact h
    generalize (if b = true then byteLive s now else s) = X at hx
    rcases arrival_sw_cases X now with e | ⟨_, e1, e2⟩
    · rw [e]; exact hx
    · rw [e2]; simp only [smul] at e1 ⊢; ucs; omega
  · rw [h4]
    unfold lateStall; split
    · exact h
    · by_cases hd : Due s now
      · by_cases hr : RttWait s now ss
        · rw [stallStep_rtt s now ss hd hr]; exact Nat.le_of_lt (Nat.lt_of_le_of_lt h hr.1)
        · by_cases hl : stallLive now (lastProg s) ss = 0
          · rw [stallStep_redial s now ss hd hr hl]
            simp only [redial, emit_sw, smul]; ucs; omega
          · rw [stallStep_live s now ss hd hr hl]
            have := (stallLive_zero_or_ge now (lastProg s) ss).resolve_left hl
            have := stallLive_le now (lastProg s) ss
            simp only [sadd]; ucs; omega
      · rw [stallStep_idle s now ss hd]; exact h


/-- The wait is not monotone: it falls only under ARK_PACE from above 40 s and at a redial from above 16 s (and, at
the clock's own saturation, under STALL_LIVE: the timer sum overflows `u64`). -/
theorem sw_decrease_cases (s : Fs) (i : Inp) (h : (step s i).sw < s.sw) :
    (ARK_PACE_CAP < s.sw ∧ ∃ now b, (∃ g, i = .frame now b g) ∨ i = .frameStoreFail now b) ∨
    (∃ now ss re rt, i = .timeout now ss re rt ∧ s.running = true ∧ s.late now = false ∧ Due s now ∧
      ¬ RttWait s now ss ∧ ((stallLive now (lastProg s) ss = 0 ∧ STALL_CAP < s.sw) ∨
        (stallLive now (lastProg s) ss ≠ 0 ∧ U64Max < stallBase s + s.sw))) := by
  rcases step_sw_eq s i with h1 | ⟨now, b, h2⟩ | ⟨now, b, hi, h3⟩ | ⟨now, ss, re, rt, hi, hrun, h4⟩
  · omega
  · exfalso; rw [h2] at h; split at h
    · have := byteLive_ge s now; omega
    · omega
  · left
    refine ⟨?_, now, b, hi⟩
    rw [h3] at h
    have hx : s.sw ≤ (if b = true then byteLive s now else s).sw := by
      split
      · exact byteLive_ge s now
      · exact Nat.le_refl _
    generalize (if b = true then byteLive s now else s) = X at hx h
    rcases arrival_sw_cases X now with e | ⟨_, e1, e2⟩
    · rw [e] at h; omega
    · rw [e2] at h; ucs; simp only [smul] at e1 h; omega
  · right
    refine ⟨now, ss, re, rt, hi, hrun, ?_⟩
    rw [h4] at h
    unfold lateStall at h
    by_cases hl : s.late now = true
    · simp [hl] at h
    · have hl' : s.late now = false := by simpa using hl
      refine ⟨hl', ?_⟩
      rw [if_neg hl] at h
      by_cases hd : Due s now
      · by_cases hr : RttWait s now ss
        · rw [stallStep_rtt s now ss hd hr] at h; simp at h; have := hr.1; omega
        · refine ⟨hd, hr, ?_⟩
          by_cases hz : stallLive now (lastProg s) ss = 0
          · left
            refine ⟨hz, ?_⟩
            rw [stallStep_redial s now ss hd hr hz] at h
            exact (nextSw_lt_iff s.sw).1 h
          · right
            refine ⟨hz, ?_⟩
            have := (stallStep_sw_live s now ss hd hr hz).2
            by_cases hov : stallBase s + s.sw ≤ U64Max
            · have := this hov; omega
            · omega
      · rw [stallStep_idle s now ss hd] at h; omega

/-- The wait is at least 4 s over every run. -/
theorem sw_ge {s0 s : Fs} (h0 : STALL_WAIT ≤ s0.sw) (hr : Reach s0 s) : STALL_WAIT ≤ s.sw := by
  induction hr with
  | init => exact h0
  | step i _ _ ih => exact step_sw_ge _ i ih

/-- The largest wait: 60 s, or, when the STALL_LIVE rule is taken, `LIVE_CAP` plus its largest extension `L`. -/
def Bd (L : Nat) : Nat := if L = 0 then STALL_RTT_CAP else LIVE_CAP + L

theorem bd_ge (L : Nat) : STALL_RTT_CAP ≤ Bd L := by unfold Bd; split <;> ucs <;> omega

/-- A timeout call whose STALL_LIVE extension is at most `L`. -/
def LiveOk (L : Nat) (s : Fs) : Inp → Prop
  | .timeout now ss _ _ => stallLive now (lastProg s) ss ≤ L
  | _ => True

theorem step_sw_le (L : Nat) (s : Fs) (i : Inp) (hs : s.sw ≤ Bd L) (hv : LiveOk L s i) :
    (step s i).sw ≤ Bd L := by
  have hb := bd_ge L
  rcases step_sw_eq s i with h1 | ⟨now, b, h2⟩ | ⟨now, b, _, h3⟩ | ⟨now, ss, re, rt, hi, _, h4⟩
  · rw [h1]; exact hs
  · rw [h2]
    have := byteLive_le s now
    split <;> ucs <;> omega
  · rw [h3]
    have hx : (if b = true then byteLive s now else s).sw ≤ Bd L := by
      have := byteLive_le s now
      split <;> ucs <;> omega
    have := arrival_le (if b = true then byteLive s now else s) now
    ucs; omega
  · rw [h4]
    subst hi
    unfold lateStall; split
    · exact hs
    · by_cases hd : Due s now
      · by_cases hr : RttWait s now ss
        · rw [stallStep_rtt s now ss hd hr]; dsimp only; have := stallRtt_le ss; omega
        · by_cases hl : stallLive now (lastProg s) ss = 0
          · rw [stallStep_redial s now ss hd hr hl]
            have h16 : (redial s now).sw = nextSw s.sw := by simp [redial, nextSw]
            rw [h16]
            have := nextSw_le s.sw
            ucs; omega
          · rw [stallStep_live s now ss hd hr hl]
            have hlv : stallLive now (lastProg s) ss ≤ L := hv
            obtain ⟨_, hlive, _, _⟩ := stallLive_ne_zero now (lastProg s) ss hl
            have hL : L ≠ 0 := by omega
            unfold Bd; rw [if_neg hL]
            simp only [sadd]; ucs; omega
      · rw [stallStep_idle s now ss hd]; exact hs

/-- A run whose STALL_LIVE extension is at most `L` on every timeout call. -/
inductive ReachL (L : Nat) (s0 : Fs) : Fs → Prop where
  | init : ReachL L s0 s0
  | step {s : Fs} (i : Inp) : ReachL L s0 s → Valid s i → LiveOk L s i → ReachL L s0 (step s i)

/-- Over every run the wait stays within `Bd L`: 60 s without STALL_LIVE (`L = 0`), else `LIVE_CAP + L`. -/
theorem sw_le {L : Nat} {s0 s : Fs} (h0 : s0.sw ≤ Bd L) (hr : ReachL L s0 s) : s.sw ≤ Bd L := by
  induction hr with
  | init => exact h0
  | step i _ _ hv ih => exact step_sw_le L _ i ih hv

theorem init_sw (o0 : Nat) (want store : List Interval) (dl : Option Nat) (st : Bool) (n : Nat) :
    (Fs.init o0 want store dl st n).sw = STALL_WAIT := rfl

/-- From the start the wait is between 4 s and 60 s when STALL_LIVE is never taken. -/
theorem sw_range_without_live (o0 : Nat) (want store : List Interval) (dl : Option Nat) (st : Bool) (n : Nat) {s : Fs}
    (hr : ReachL 0 (Fs.init o0 want store dl st n) s) : STALL_WAIT ≤ s.sw ∧ s.sw ≤ STALL_RTT_CAP := by
  have h0 : (Fs.init o0 want store dl st n).sw ≤ Bd 0 := by
    simp [Fs.init, Bd]; ucs; omega
  have hge : Reach (Fs.init o0 want store dl st n) s := by
    clear h0
    induction hr with
    | init => exact Reach.init
    | step i _ hv _ ih => exact Reach.step i ih hv
  exact ⟨sw_ge (by simp [Fs.init]) hge, by have := sw_le h0 hr; simpa [Bd] using this⟩


/-! ## The wait is not monotone: concrete cases -/

/-- A state with wait `w` and a frame at time 1. -/
def withSw (w : Nat) : Fs := { Fs.init 0 [] [] none false 1 with sw := w, lastp := 1 }

/-- ARK_PACE lowers a wait above 40 s: wait 50 s, a frame 20 s after the last one (3 x gap = 60 s), new wait 40 s. -/
theorem ark_lowers_example : (arrival (withSw (50 * NS)) (1 + 20 * NS)).sw = 40 * NS := by
  decide

/-- A redial lowers a wait above 16 s: from 60 s to 16 s. -/
theorem redial_lowers_example : (redial (withSw (60 * NS)) (200 * NS)).sw = 16 * NS := by
  decide

/-- BYTE_LIVE lifts the wait to three burst gaps, up to 60 s: wait 4 s, bursts 10 s apart give 30 s. -/
theorem byte_live_lifts_example :
    (byteLive { withSw STALL_WAIT with lastb := 5 } (5 + 10 * NS)).sw = 30 * NS := by
  decide


/-! ## A run of byte arrivals -/

/-- The largest gap between consecutive times of a run that starts after `prev`. -/
def maxGap : Nat → List Nat → Nat
  | _, [] => 0
  | prev, t :: ts => max (t - prev) (maxGap t ts)

/-- The last time of the run. -/
def lastTime : Nat → List Nat → Nat
  | prev, [] => prev
  | _, t :: ts => lastTime t ts

/-- The state after a run of byte arrivals whose last time is `tn` and largest gap `mg`. -/
def byteRun (s : Fs) (tn mg : Nat) : Fs := { s with sw := max s.sw (min BYTE_GAP_CAP (smul mg 3)), lastb := tn }

/-- BYTE_LIVE keeps the largest gap of a run: folding it over the times of the bytes (all later than the first byte
of the fetch, which has set the last byte time) is one step with the largest gap. The trace check writes a run of
byte-only steps as its first time and this summary. -/
theorem byteLive_run (s : Fs) (hb : s.lastb ≠ 0) (ts : List Nat) (hpos : ∀ t ∈ ts, t ≠ 0) :
    ts.foldl byteLive s = byteRun s (lastTime s.lastb ts) (maxGap s.lastb ts) := by
  induction ts generalizing s with
  | nil => cases s; simp [lastTime, maxGap, byteRun, smul]
  | cons t rest ih =>
    have ht : t ≠ 0 := hpos t (by simp)
    have h1 : byteLive s t = { s with sw := max s.sw (min BYTE_GAP_CAP (smul (t - s.lastb) 3)), lastb := t } := by
      simp [byteLive, hb]
    rw [List.foldl_cons, h1, ih _ (by simpa using ht) (fun x hx => hpos x (List.mem_cons_of_mem _ hx))]
    cases s
    simp only [byteRun, lastTime, maxGap, smul]
    congr 1
    ucs
    omega

end Vinc.ValuesTime
