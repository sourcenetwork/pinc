import Vinc.ValuesTimeStall

/-!
# The deadline and the failure reasons (property 8, property 2's failure side)

* `onTimeout_late_stops`, `onTimeout_late_no_work`, `onTimeout_late_outcome`: an `on_timeout` past the deadline never
  leaves the fetch running, does no stall, steal or retry work, and ends it with `Complete` (the hold and completion
  check run first, as in the code) or `Failed(Deadline)`.
* `poll_deadline`, `late_of_poll`, `deadline_max_never`: `poll_timeout` offers the deadline plus one, and that time is
  past the deadline unless the deadline is `u64::MAX`.
* `redial_only_timeout`: a redial record comes only from a timeout call with the stall rule due.
* `fail_reason`: which input reports which reason; `startFetch_*`: the reasons at the start; `terminal_once`: one
  terminal event per fetch.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Vinc.ValuesTime
open Vinc.Ranges

/-! ## Which events a transition appends -/

/-- The records of a hold check. -/
def Ph (e : Ev) : Prop := (∃ o c, e = .released o c) ∨ (∃ o l, e = .readable o l)
/-- The records of a completion check. -/
def Pd (e : Ev) : Prop := Ph e ∨ e = .complete
/-- The records of a verified group (with its completion check). -/
def Pg (e : Ev) : Prop := Pd e ∨ (∃ o l, e = .verified o l) ∨ (∃ o, e = .held o)

/-- `s'` is `s` with events of class `P` appended to the log. -/
def Gr (P : Ev → Prop) (s s' : Fs) : Prop := ∃ ex, s'.log = s.log ++ ex ∧ ∀ e ∈ ex, P e

theorem Gr.refl (P : Ev → Prop) (s : Fs) : Gr P s s := ⟨[], by simp, by simp⟩
theorem Gr.trans {P : Ev → Prop} {a b c : Fs} (h1 : Gr P a b) (h2 : Gr P b c) : Gr P a c := by
  obtain ⟨x, hx, px⟩ := h1; obtain ⟨y, hy, py⟩ := h2
  refine ⟨x ++ y, by simp [hy, hx], ?_⟩
  intro e he
  rcases List.mem_append.1 he with h | h
  · exact px e h
  · exact py e h
theorem Gr.mono {P Q : Ev → Prop} {a b : Fs} (hpq : ∀ e, P e → Q e) (h : Gr P a b) : Gr Q a b := by
  obtain ⟨x, hx, px⟩ := h; exact ⟨x, hx, fun e he => hpq e (px e he)⟩
theorem Gr.same {P : Ev → Prop} {a b : Fs} (h : b.log = a.log) : Gr P a b := ⟨[], by simp [h], by simp⟩

theorem gr_hold (s : Fs) (now : Nat) (f : Option Cause) : Gr Ph s (holdCheck s now f) := by
  cases hh : s.head with
  | none => simpa [holdCheck, hh] using Gr.refl Ph s
  | some h =>
    cases hw : holdWhy s h now f with
    | none => simpa [holdCheck, hh, hw] using Gr.refl Ph s
    | some c =>
      refine ⟨[.released h.off c, .readable h.off h.len], by simp [holdCheck, hh, hw], ?_⟩
      intro e he; simp at he
      rcases he with rfl | rfl
      · exact Or.inl ⟨_, _, rfl⟩
      · exact Or.inr ⟨_, _, rfl⟩

theorem gr_checkDone (s : Fs) (now : Nat) : Gr Pd s (checkDone s now) := by
  rw [checkDone_eq]
  split
  · refine (((gr_hold s now none).mono fun e h => Or.inl h).trans
      (((gr_hold _ now _).mono fun e h => Or.inl h).trans ⟨[.complete], rfl, ?_⟩))
    intro e he; simp at he; exact Or.inr he
  · exact (gr_hold s now none).mono fun e h => Or.inl h

theorem gr_group (s : Fs) (now off len : Nat) : Gr Pg s (groupVerified s now off len) := by
  rw [groupVerified_eq]
  refine Gr.trans (b := (if (!s.rel && decide (off ≤ s.o0) && decide (s.o0 < off + len)) = true then
        Fs.emit { Fs.emit s [Ev.verified off len] with
          head := some ⟨off, len, match s.head with | some h => h.t0 | none => now⟩, nv := 0 } [Ev.held off]
      else
        if s.head.isSome then
          holdCheck { Fs.emit (Fs.emit s [Ev.verified off len]) [Ev.readable off len] with nv := s.nv + 1 } now none
        else Fs.emit (Fs.emit s [Ev.verified off len]) [Ev.readable off len])) ?_
    ((gr_checkDone _ now).mono fun e h => Or.inl h)
  split
  · exact ⟨[.verified off len, .held off], by simp, by intro e he; simp at he; rcases he with rfl | rfl <;> simp [Pg]⟩
  · split
    · have h1 : Gr Pg s (Fs.emit (Fs.emit s [Ev.verified off len]) [Ev.readable off len]) :=
        ⟨[.verified off len, .readable off len], by simp, by intro e he; simp at he; rcases he with rfl | rfl <;> simp [Pg, Pd, Ph]⟩
      exact h1.trans ((Gr.same (by rfl)).trans ((gr_hold _ now none).mono fun e h => Or.inl (Or.inl h)))
    · exact ⟨[.verified off len, .readable off len], by simp, by intro e he; simp at he; rcases he with rfl | rfl <;> simp [Pg, Pd, Ph]⟩


theorem gr_fail (s : Fs) (r : Fail) : Gr (fun e => e = .failed r) s (failWith s r) :=
  ⟨[.failed r], rfl, by simp⟩

theorem gr_headBlock (s : Fs) (now : Nat) : Gr Pd s (headBlock s now) := by
  unfold headBlock; split
  · exact ((gr_hold s now none).mono fun e h => Or.inl h).trans (gr_checkDone _ now)
  · exact Gr.refl _ _

theorem gr_byteLive (s : Fs) (now : Nat) (P : Ev → Prop) : Gr P s (byteLive s now) :=
  Gr.same (byteLive_log s now)
theorem gr_arrival (s : Fs) (now : Nat) (P : Ev → Prop) : Gr P s (arrival s now) :=
  Gr.same (arrival_log s now)

/-! ## The deadline -/

theorem late_iff (s : Fs) (now : Nat) : s.late now = true ↔ ∃ d, s.deadline = some d ∧ d < now := by
  unfold Fs.late; cases s.deadline <;> simp

theorem running_hold (s : Fs) (now : Nat) (f : Option Cause) : (holdCheck s now f).running = s.running := by
  unfold holdCheck; split <;> (try split) <;> simp

/-- The completion check stops the fetch only by appending `Complete`. -/
theorem checkDone_stop (s : Fs) (now : Nat) (hrun : s.running = true) (hstop : (checkDone s now).running = false) :
    ∃ ex, (checkDone s now).log = s.log ++ ex ∧ Ev.complete ∈ ex := by
  by_cases hw : (holdCheck s now none).wantedDone = true
  · obtain ⟨ex1, h1⟩ := ext_hold s now none
    obtain ⟨ex2, h2⟩ := ext_hold (holdCheck s now none) now (some .done)
    refine ⟨ex1 ++ ex2 ++ [Ev.complete], ?_, by simp⟩
    rw [checkDone_eq, if_pos hw]
    simp [h2, h1]
  · rw [checkDone_eq, if_neg hw, running_hold] at hstop
    simp [hrun] at hstop

/-- The head block ends the fetch only by completing it. -/
theorem headBlock_stops (s : Fs) (now : Nat) (hrun : s.running = true) (hstop : (headBlock s now).running = false) :
    ∃ ex, (headBlock s now).log = s.log ++ ex ∧ Ev.complete ∈ ex := by
  unfold headBlock at *
  split at hstop
  · obtain ⟨ex1, h1⟩ := ext_hold s now none
    obtain ⟨ex2, h2, h3⟩ := checkDone_stop (holdCheck s now none) now (by rw [running_hold]; exact hrun) hstop
    refine ⟨ex1 ++ ex2, ?_, by simp [h3]⟩
    rename_i hh
    rw [if_pos hh, h2, h1]; simp
  · simp_all

theorem running_headBlock (s : Fs) (now : Nat) (h : s.running = false) : (headBlock s now).running = false := by
  unfold headBlock; split
  · rw [checkDone_eq]; split <;> simp [running_hold, h]
  · exact h

theorem running_stall (s : Fs) (now : Nat) (ss : List Sess) : (stallStep s now ss).running = s.running := by
  unfold stallStep; split <;> (try split) <;> (try split) <;> simp [redial]

theorem running_lateStall (s : Fs) (now : Nat) (ss : List Sess) : (lateStall s now ss).running = s.running := by
  unfold lateStall; split
  · rfl
  · exact running_stall s now ss

/-- The timers the stall, steal and retry rules own are not touched by a hold or completion check. -/
theorem timers_hold (s : Fs) (now : Nat) (f : Option Cause) :
    (holdCheck s now f).sw = s.sw ∧ (holdCheck s now f).lastp = s.lastp ∧ (holdCheck s now f).lastb = s.lastb ∧
      (holdCheck s now f).tw = s.tw ∧ (holdCheck s now f).rt = s.rt := by
  unfold holdCheck; split <;> (try split) <;> simp

theorem timers_headBlock (s : Fs) (now : Nat) :
    (headBlock s now).sw = s.sw ∧ (headBlock s now).lastp = s.lastp ∧ (headBlock s now).lastb = s.lastb ∧
      (headBlock s now).tw = s.tw ∧ (headBlock s now).rt = s.rt := by
  unfold headBlock; split
  · rw [checkDone_eq]
    split
    · simp [timers_hold]
    · simp [timers_hold]
  · simp [timers_hold]

/-- Past the deadline the whole of `on_timeout` is the head block and the failure. -/
theorem onTimeout_late_eq (s : Fs) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat)
    (hrun : s.running = true) (hl : s.late now = true) :
    onTimeout s now ss rearm rt' =
      if (headBlock s now).running = true then failWith (headBlock s now) .deadline else headBlock s now := by
  have hs : lateStall s now ss = s := by simp [lateStall, hl]
  have hst : ∀ x : Fs, stealBlock x now true rearm = x := by intro x; simp [stealBlock]
  simp only [onTimeout, hrun, hl, hs, hst, ite_true]

/-- An `on_timeout` past the deadline never leaves the fetch running. -/
theorem onTimeout_late_stops (s : Fs) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat)
    (hrun : s.running = true) (hl : s.late now = true) : (onTimeout s now ss rearm rt').running = false := by
  rw [onTimeout_late_eq s now ss rearm rt' hrun hl]
  split
  · simp [failWith]
  · rename_i h; simpa using h

/-- Past the deadline the call does no stall, steal or retry work: the timers and the wait are as they were. -/
theorem onTimeout_late_no_work (s : Fs) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat)
    (hrun : s.running = true) (hl : s.late now = true) :
    (onTimeout s now ss rearm rt').sw = s.sw ∧ (onTimeout s now ss rearm rt').lastp = s.lastp ∧
      (onTimeout s now ss rearm rt').lastb = s.lastb ∧ (onTimeout s now ss rearm rt').tw = s.tw ∧
      (onTimeout s now ss rearm rt').rt = s.rt := by
  rw [onTimeout_late_eq s now ss rearm rt' hrun hl]
  have := timers_headBlock s now
  split <;> simp [failWith, this]

/-- Past the deadline the call appends only the head block's records and ends the fetch: with `Complete` when the
completion check found nothing missing (it runs first, as in the code), else with `Failed(Deadline)`. Never any
other reason, never a redial. -/
theorem onTimeout_late_outcome (s : Fs) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat)
    (hrun : s.running = true) (hl : s.late now = true) :
    ∃ ex, (onTimeout s now ss rearm rt').log = s.log ++ ex ∧ (∀ e ∈ ex, Pd e ∨ e = .failed .deadline) ∧
      (Ev.complete ∈ ex ∨ Ev.failed .deadline ∈ ex) := by
  rw [onTimeout_late_eq s now ss rearm rt' hrun hl]
  obtain ⟨ex, hx, hp⟩ := gr_headBlock s now
  by_cases hr : (headBlock s now).running = true
  · rw [if_pos hr]
    refine ⟨ex ++ [.failed .deadline], by simp [failWith, hx], ?_, by simp⟩
    intro e he
    rcases List.mem_append.1 he with h | h
    · exact Or.inl (hp e h)
    · simp at h; exact Or.inr h
  · rw [if_neg hr]
    have hstop : (headBlock s now).running = false := by simpa using hr
    obtain ⟨ex2, h2, h3⟩ := headBlock_stops s now hrun hstop
    have hex : ex = ex2 := by
      have : s.log ++ ex = s.log ++ ex2 := by rw [← hx, ← h2]
      exact List.append_cancel_left this
    refine ⟨ex, hx, fun e he => Or.inl (hp e he), Or.inl (hex ▸ h3)⟩

/-! ## The timer and the deadline -/

/-- While running with a deadline, `poll_timeout` offers the deadline plus one at the latest. -/
theorem poll_deadline (s : Fs) (d : Nat) (hr : s.running = true) (hd : s.deadline = some d) :
    ∃ p, pollTimeout s = some p ∧ p ≤ sadd d 1 := by
  unfold pollTimeout
  rw [if_pos hr]
  have hmem : sadd d 1 ∈ pollList s := by simp [pollList, hd]
  cases hm : (pollList s).min? with
  | none => simp [List.min?_eq_none_iff] at hm; rw [hm] at hmem; simp at hmem
  | some p => exact ⟨p, rfl, (List.min?_eq_some_iff.1 hm).2 _ hmem⟩

/-- A call at or after the deadline plus one is past the deadline, unless the deadline is `u64::MAX`. -/
theorem late_of_poll (s : Fs) (d now : Nat) (hd : s.deadline = some d) (hlt : d < U64Max) (hn : sadd d 1 ≤ now) :
    s.late now = true := by
  unfold Fs.late; rw [hd]; simp only [sadd] at hn; ucs; simp; omega

/-- A deadline of `u64::MAX` never expires. -/
theorem deadline_max_never (s : Fs) (now : Nat) (hd : s.deadline = some U64Max) (hn : now ≤ U64Max) :
    s.late now = false := by
  unfold Fs.late; rw [hd]; simp; omega

/-- The fetch is done at the first timer call after the deadline, whatever the stall state. -/
theorem done_after_deadline (s : Fs) (d now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat)
    (hrun : s.running = true) (hd : s.deadline = some d) (hlt : d < U64Max) (hn : sadd d 1 ≤ now) :
    (∃ p, pollTimeout s = some p ∧ p ≤ sadd d 1) ∧ (onTimeout s now ss rearm rt').running = false :=
  ⟨poll_deadline s d hrun hd, onTimeout_late_stops s now ss rearm rt' hrun (late_of_poll s d now hd hlt hn)⟩


/-! ## Which input reports which reason -/

theorem Gr.cls {P : Ev → Prop} {a b : Fs} {ex : List Ev} (h : Gr P a b) (hx : b.log = a.log ++ ex) :
    ∀ e ∈ ex, P e := by
  obtain ⟨ex', hx', hp⟩ := h
  have : ex = ex' := List.append_cancel_left (hx.symm.trans hx')
  subst this; exact hp

/-- The class of the records a transition appends, by input. -/
def Pany (e : Ev) : Prop := Pg e ∨ (∃ r, e = .failed r) ∨ (∃ w n, e = .redial w n)

theorem gr_onTimeout_late (s : Fs) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat)
    (hrun : s.running = true) (hl : s.late now = true) :
    Gr (fun e => Pd e ∨ e = .failed .deadline) s (onTimeout s now ss rearm rt') := by
  obtain ⟨ex, hx, hp, _⟩ := onTimeout_late_outcome s now ss rearm rt' hrun hl
  exact ⟨ex, hx, hp⟩

theorem gr_onTimeout_early (s : Fs) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat)
    (hl : s.late now = false) :
    Gr (fun e => Pd e ∨ ∃ w n, e = .redial w n) s (onTimeout s now ss rearm rt') := by
  by_cases hrun : s.running = true
  · have hl' : ¬ s.late now = true := by simp [hl]
    have h1 : Gr (fun e => Pd e ∨ ∃ w n, e = .redial w n) s (lateStall s now ss) := by
      unfold lateStall; rw [if_neg hl']
      by_cases hd : Due s now ∧ ¬ RttWait s now ss ∧ stallLive now s.lastp ss = 0
      · rw [stallStep_redial s now ss hd.1 hd.2.1 hd.2.2]
        exact ⟨[.redial s.sw (min (smul s.sw 2) STALL_CAP)], rfl, by simp⟩
      · by_cases hh : (stallStep s now ss).log = s.log
        · exact Gr.same hh
        · exact absurd ((redial_iff s now ss).1 hh) hd
    have h2 := (gr_headBlock (lateStall s now ss) now).mono (P := Pd) (Q := fun e => Pd e ∨ ∃ w n, e = .redial w n)
      fun e h => Or.inl h
    have h3 := h1.trans h2
    by_cases hr : (headBlock (lateStall s now ss) now).running = true
    · simp only [onTimeout, hrun, hr, hl, ite_true, Bool.false_eq_true, ite_false]
      refine h3.trans (Gr.trans (b := stealBlock (headBlock (lateStall s now ss) now) now false rearm) ?_ ?_)
      · exact Gr.same (by unfold stealBlock; split <;> rfl)
      · exact Gr.same (by unfold retryBlock; split <;> (try split) <;> rfl)
    · simp only [onTimeout, hrun, hr, ite_true, ite_false]
      exact h3
  · simp only [onTimeout, hrun]; exact Gr.refl _ _


theorem Pg_not_failed {e : Ev} (h : Pg e) (r : Fail) : e ≠ .failed r := by
  rcases h with (((⟨o, c, rfl⟩ | ⟨o, l, rfl⟩) | rfl) | ⟨o, l, rfl⟩ | ⟨o, rfl⟩) <;> simp

theorem Pd_not_failed {e : Ev} (h : Pd e) (r : Fail) : e ≠ .failed r := Pg_not_failed (Or.inl h) r
theorem Pd_not_redial {e : Ev} (h : Pd e) (w n : Nat) : e ≠ .redial w n := by
  rcases h with (⟨o, c, rfl⟩ | ⟨o, l, rfl⟩) | rfl <;> simp
theorem Pg_not_redial {e : Ev} (h : Pg e) (w n : Nat) : e ≠ .redial w n := by
  rcases h with h | ⟨o, l, rfl⟩ | ⟨o, rfl⟩
  · exact Pd_not_redial h w n
  · simp
  · simp

theorem ex_nil {a b : Fs} {ex : List Ev} (h : b.log = a.log) (hx : b.log = a.log ++ ex) : ex = [] := by
  have : a.log ++ ex = a.log ++ [] := by rw [← hx, h]; simp
  exact List.append_cancel_left this

theorem gr_frame (s : Fs) (now : Nat) (b : Bool) (g : Option (Nat × Nat)) :
    Gr Pg s (step s (.frame now b g)) ∨ s.running = false := by
  by_cases hrun : s.running = true
  · left
    have hl : (arrival (if b = true then byteLive s now else s) now).log = s.log := by
      rw [arrival_log]; split
      · exact byteLive_log _ _
      · rfl
    simp only [step, hrun, ite_true]
    cases g with
    | none => exact Gr.same hl
    | some p =>
      obtain ⟨o, l⟩ := p
      simp only [verifyStep]
      exact Gr.trans (Gr.same (b := { arrival (if b = true then byteLive s now else s) now with
        store := insertVec (arrival (if b = true then byteLive s now else s) now).store (o, o + l) }) hl) (gr_group _ now o l)
  · right; simpa using hrun

/-- Which input reports which reason: a store refusal only a frame or an out-of-order group whose write failed, the
last provider's eviction only an eviction, the deadline only a timer call past the deadline. -/
theorem fail_reason (s : Fs) (i : Inp) (ex : List Ev) (r : Fail) (h : (step s i).log = s.log ++ ex)
    (hf : Ev.failed r ∈ ex) :
    (r = .store ∧ ((∃ now b, i = .frameStoreFail now b) ∨ ∃ now, i = .aheadStoreFail now) ∧ s.running = true) ∨
    (r = .lied ∧ (∃ now b, i = .evict now b) ∧ s.running = true ∧ s.trusted ≤ 1) ∨
    (r = .deadline ∧ (∃ now ss re rt, i = .timeout now ss re rt ∧ s.running = true ∧ s.late now = true)) := by
  by_cases hrun : s.running = true
  · cases i with
    | bytes now =>
      have := ex_nil (by simp [step, hrun, byteLive_log]) h
      simp [this] at hf
    | frame now b g =>
      rcases gr_frame s now b g with hg | hg
      · exact absurd rfl (Pg_not_failed (hg.cls h _ hf) r)
      · simp [hrun] at hg
    | frameStoreFail now b =>
      have hl : (arrival (if b = true then byteLive s now else s) now).log = s.log := by
        rw [arrival_log]; split
        · exact byteLive_log _ _
        · rfl
      have h' : (step s (.frameStoreFail now b)).log = s.log ++ [Ev.failed .store] := by
        simp only [step, hrun, ite_true, failWith, emit_log, hl]
      have : ex = [Ev.failed .store] := List.append_cancel_left (h.symm.trans h')
      subst this
      left; simp at hf; exact ⟨hf, Or.inl ⟨now, b, rfl⟩, hrun⟩
    | ahead now o l =>
      have hg : Gr Pg s (step s (.ahead now o l)) := by
        simp only [step, hrun, ite_true, verifyStep]
        exact gr_group _ now o l |> fun g => Gr.trans (Gr.same (b := { s with store := insertVec s.store (o, o + l) }) rfl) g
      exact absurd rfl (Pg_not_failed (hg.cls h _ hf) r)
    | aheadStoreFail now =>
      have h' : (step s (.aheadStoreFail now)).log = s.log ++ [Ev.failed .store] := by
        simp only [step, hrun, ite_true, failWith, emit_log]
      have : ex = [Ev.failed .store] := List.append_cancel_left (h.symm.trans h')
      subst this
      left; simp at hf; exact ⟨hf, Or.inr ⟨now, rfl⟩, hrun⟩
    | evict now b =>
      have hl : (if b = true then byteLive s now else s).log = s.log := by
        split
        · exact byteLive_log _ _
        · rfl
      have htr : (if b = true then byteLive s now else s).trusted = s.trusted := by
        split
        · unfold byteLive; split <;> (try split) <;> rfl
        · rfl
      by_cases ht : s.trusted ≤ 1
      · have h' : (step s (.evict now b)).log = s.log ++ [Ev.failed .lied] := by
          simp only [step, hrun, ite_true, htr, ht, failWith, emit_log, hl]
        have : ex = [Ev.failed .lied] := List.append_cancel_left (h.symm.trans h')
        subst this
        right; left; simp at hf; exact ⟨hf, ⟨now, b, rfl⟩, hrun, ht⟩
      · have h' : (step s (.evict now b)).log = s.log := by
          have hnot : ¬ (if b = true then byteLive s now else s).trusted ≤ 1 := by rw [htr]; exact ht
          simp only [step, hrun, ite_true]
          rw [if_neg hnot]
          exact hl
        have := ex_nil h' h
        simp [this] at hf
    | streamEnd now =>
      have hg : Gr Pd s (step s (.streamEnd now)) := by simp only [step, hrun, ite_true]; exact gr_checkDone s now
      exact absurd rfl (Pd_not_failed (hg.cls h _ hf) r)
    | arm tw rt treq =>
      have := ex_nil (by simp [step, hrun]) h
      simp [this] at hf
    | timeout now ss re rt =>
      by_cases hl : s.late now = true
      · have hg := gr_onTimeout_late s now ss re rt hrun hl
        have hg' : Gr (fun e => Pd e ∨ e = .failed .deadline) s (step s (.timeout now ss re rt)) := by
          simpa [step, hrun] using hg
        rcases hg'.cls h _ hf with hp | hp
        · exact absurd rfl (Pd_not_failed hp r)
        · right; right; simp at hp; exact ⟨hp, now, ss, re, rt, rfl, hrun, hl⟩
      · have hl' : s.late now = false := by simpa using hl
        have hg := gr_onTimeout_early s now ss re rt hl'
        have hg' : Gr (fun e => Pd e ∨ ∃ w n, e = .redial w n) s (step s (.timeout now ss re rt)) := by
          simpa [step, hrun] using hg
        rcases hg'.cls h _ hf with hp | ⟨w, n, hp⟩
        · exact absurd rfl (Pd_not_failed hp r)
        · simp at hp
  · have := ex_nil (by simp [step, hrun]) h
    simp [this] at hf


/-- Not past the deadline: the stall block's records, then the head block's; steal and retry append nothing. -/
theorem gr_onTimeout_gen (P : Ev → Prop) (hP : ∀ e, Pd e → P e) (s : Fs) (now : Nat) (ss : List Sess) (rearm : Bool)
    (rt' : Option Nat) (hl : s.late now = false) (h1 : Gr P s (lateStall s now ss)) :
    Gr P s (onTimeout s now ss rearm rt') := by
  by_cases hrun : s.running = true
  · have h2 := (gr_headBlock (lateStall s now ss) now).mono hP
    have h3 := h1.trans h2
    by_cases hr : (headBlock (lateStall s now ss) now).running = true
    · simp only [onTimeout, hrun, hr, hl, ite_true, Bool.false_eq_true, ite_false]
      refine h3.trans (Gr.trans (b := stealBlock (headBlock (lateStall s now ss) now) now false rearm) ?_ ?_)
      · exact Gr.same (by unfold stealBlock; split <;> rfl)
      · exact Gr.same (by unfold retryBlock; split <;> (try split) <;> rfl)
    · simp only [onTimeout, hrun, hr, ite_true, ite_false]
      exact h3
  · simp only [onTimeout, hrun]; exact Gr.refl _ _

theorem gr_onTimeout_calm (s : Fs) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat)
    (hl : s.late now = false) (hc : ¬ (Due s now ∧ ¬ RttWait s now ss ∧ stallLive now s.lastp ss = 0)) :
    Gr Pd s (onTimeout s now ss rearm rt') := by
  refine gr_onTimeout_gen Pd (fun _ h => h) s now ss rearm rt' hl ?_
  unfold lateStall
  have hl' : ¬ s.late now = true := by simp [hl]
  rw [if_neg hl']
  by_cases hh : (stallStep s now ss).log = s.log
  · exact Gr.same hh
  · exact absurd ((redial_iff s now ss).1 hh) hc

/-- A redial record comes only from a timeout call, not past the deadline, with the wait spent, STALL_RTT having no
longer wait to offer and STALL_LIVE finding no slow-but-receiving session. -/
theorem redial_only_timeout (s : Fs) (i : Inp) (ex : List Ev) (w n : Nat) (h : (step s i).log = s.log ++ ex)
    (hr : Ev.redial w n ∈ ex) :
    ∃ now ss re rt, i = .timeout now ss re rt ∧ s.running = true ∧ s.late now = false ∧ Due s now ∧
      ¬ RttWait s now ss ∧ stallLive now s.lastp ss = 0 := by
  have hnr : ∀ {Q : Ev → Prop}, (∀ e, Q e → e ≠ .redial w n) → Gr Q s (step s i) → False := by
    intro Q hQ hg
    exact hQ _ (hg.cls h _ hr) rfl
  by_cases hrun : s.running = true
  · cases i with
    | bytes now => exact absurd (ex_nil (by simp [step, hrun, byteLive_log]) h ▸ hr) (by simp)
    | frame now b g =>
      rcases gr_frame s now b g with hg | hg
      · exact (hnr (Q := Pg) (fun e he => Pg_not_redial he w n) hg).elim
      · simp [hrun] at hg
    | frameStoreFail now b =>
      have hl : (arrival (if b = true then byteLive s now else s) now).log = s.log := by
        rw [arrival_log]; split
        · exact byteLive_log _ _
        · rfl
      have h' : (step s (.frameStoreFail now b)).log = s.log ++ [Ev.failed .store] := by
        simp only [step, hrun, ite_true, failWith, emit_log, hl]
      have : ex = [Ev.failed .store] := List.append_cancel_left (h.symm.trans h')
      subst this; simp at hr
    | ahead now o l =>
      have hg : Gr Pg s (step s (.ahead now o l)) := by
        simp only [step, hrun, ite_true, verifyStep]
        exact gr_group _ now o l |> fun g => Gr.trans (Gr.same (b := { s with store := insertVec s.store (o, o + l) }) rfl) g
      exact (hnr (Q := Pg) (fun e he => Pg_not_redial he w n) hg).elim
    | aheadStoreFail now =>
      have h' : (step s (.aheadStoreFail now)).log = s.log ++ [Ev.failed .store] := by
        simp only [step, hrun, ite_true, failWith, emit_log]
      have : ex = [Ev.failed .store] := List.append_cancel_left (h.symm.trans h')
      subst this; simp at hr
    | evict now b =>
      have hl : (if b = true then byteLive s now else s).log = s.log := by
        split
        · exact byteLive_log _ _
        · rfl
      have htr : (if b = true then byteLive s now else s).trusted = s.trusted := by
        split
        · unfold byteLive; split <;> (try split) <;> rfl
        · rfl
      by_cases ht : s.trusted ≤ 1
      · have h' : (step s (.evict now b)).log = s.log ++ [Ev.failed .lied] := by
          simp only [step, hrun, ite_true, htr, ht, failWith, emit_log, hl]
        have : ex = [Ev.failed .lied] := List.append_cancel_left (h.symm.trans h')
        subst this; simp at hr
      · have h' : (step s (.evict now b)).log = s.log := by
          have hnot : ¬ (if b = true then byteLive s now else s).trusted ≤ 1 := by rw [htr]; exact ht
          simp only [step, hrun, ite_true]
          rw [if_neg hnot]
          exact hl
        have := ex_nil h' h
        simp [this] at hr
    | streamEnd now =>
      have hg : Gr Pd s (step s (.streamEnd now)) := by simp only [step, hrun, ite_true]; exact gr_checkDone s now
      exact (hnr (Q := Pd) (fun e he => Pd_not_redial he w n) hg).elim
    | arm tw rt treq =>
      have := ex_nil (by simp [step, hrun]) h
      simp [this] at hr
    | timeout now ss re rt =>
      refine ⟨now, ss, re, rt, rfl, hrun, ?_⟩
      by_cases hl : s.late now = true
      · have hg := gr_onTimeout_late s now ss re rt hrun hl
        have hg' : Gr (fun e => Pd e ∨ e = .failed .deadline) s (step s (.timeout now ss re rt)) := by
          simpa [step, hrun] using hg
        exact (hnr (Q := fun e => Pd e ∨ e = .failed .deadline)
          (by intro e he; rcases he with he | rfl; exact Pd_not_redial he w n; simp) hg').elim
      · have hl' : s.late now = false := by simpa using hl
        refine ⟨hl', ?_⟩
        by_cases hc : Due s now ∧ ¬ RttWait s now ss ∧ stallLive now s.lastp ss = 0
        · exact hc
        · have hg := gr_onTimeout_calm s now ss re rt hl' hc
          have hg' : Gr Pd s (step s (.timeout now ss re rt)) := by simpa [step, hrun] using hg
          exact (hnr (Q := Pd) (fun e he => Pd_not_redial he w n) hg').elim
  · have := ex_nil (by simp [step, hrun]) h
    simp [this] at hr


/-! ## The start of a fetch, and one terminal event -/

/-- A zero-length value under a root that is not the empty value's: `BadRoot`, before anything else. -/
theorem startFetch_badRoot (n : Nat) (want store : List Interval) :
    startFetch 0 false n want store = some (.failed .badRoot) := by simp [startFetch]

/-- Nothing missing completes the fetch, even with no provider named. -/
theorem startFetch_complete (length : Nat) (er : Bool) (want store : List Interval)
    (h1 : ¬ (length = 0 ∧ er = false)) (h2 : want.all (containsRange store) = true) :
    startFetch length er 0 want store = some .complete := by
  simp only [startFetch]
  rw [if_neg (by simpa using h1), if_pos h2]

/-- With bytes missing and no provider: `NoProvider`. -/
theorem startFetch_noProvider (length : Nat) (er : Bool) (want store : List Interval)
    (h1 : ¬ (length = 0 ∧ er = false)) (h2 : want.all (containsRange store) = false) :
    startFetch length er 0 want store = some (.failed .noProvider) := by
  simp only [startFetch]
  rw [if_neg (by simpa using h1), if_neg (by simp [h2])]
  simp

/-- Otherwise the fetch runs, and its only reasons to fail are those of `fail_reason`. -/
theorem startFetch_runs (length : Nat) (er : Bool) (n : Nat) (want store : List Interval)
    (h1 : ¬ (length = 0 ∧ er = false)) (h2 : want.all (containsRange store) = false) (h3 : n ≠ 0) :
    startFetch length er n want store = none := by
  simp only [startFetch]
  rw [if_neg (by simpa using h1), if_neg (by simp [h2]), if_neg h3]

/-- A stopped fetch ignores every input: no second terminal event. -/
theorem step_stopped (s : Fs) (i : Inp) (h : s.running = false) : step s i = s := by
  simp [step, h]

/-- A head block that appended `Complete` stopped the fetch. -/
theorem headBlock_complete_stops (s : Fs) (now : Nat) (ex : List Ev) (hx : (headBlock s now).log = s.log ++ ex)
    (hc : Ev.complete ∈ ex) : (headBlock s now).running = false := by
  by_cases hh : s.head.isSome = true
  · unfold headBlock at hx ⊢
    rw [if_pos hh] at hx ⊢
    by_cases hq : (holdCheck (holdCheck s now none) now none).wantedDone = true
    · rw [checkDone_eq, if_pos hq]; simp
    · rw [checkDone_eq, if_neg hq] at hx
      have hg := ((gr_hold s now none).trans (gr_hold (holdCheck s now none) now none)).cls hx _ hc
      rcases hg with ⟨o, c, h⟩ | ⟨o, l, h⟩ <;> simp at h
  · have : headBlock s now = s := by simp [headBlock, hh]
    rw [this] at hx
    have := ex_nil rfl hx
    simp [this] at hc

/-- The call past the deadline ends the fetch with exactly one terminal record. -/
theorem onTimeout_late_one_terminal (s : Fs) (now : Nat) (ss : List Sess) (rearm : Bool) (rt' : Option Nat)
    (hrun : s.running = true) (hl : s.late now = true) :
    ∃ ex, (onTimeout s now ss rearm rt').log = s.log ++ ex ∧
      ((Ev.complete ∈ ex ∧ Ev.failed .deadline ∉ ex) ∨ (Ev.failed .deadline ∈ ex ∧ Ev.complete ∉ ex)) := by
  rw [onTimeout_late_eq s now ss rearm rt' hrun hl]
  obtain ⟨ex, hx, hp⟩ := gr_headBlock s now
  by_cases hr : (headBlock s now).running = true
  · rw [if_pos hr]
    refine ⟨ex ++ [.failed .deadline], by simp [failWith, hx], Or.inr ⟨by simp, ?_⟩⟩
    intro hc
    rcases List.mem_append.1 hc with h | h
    · have hstop := headBlock_complete_stops s now ex hx h
      simp [hstop] at hr
    · simp at h
  · rw [if_neg hr]
    have hstop : (headBlock s now).running = false := by simpa using hr
    obtain ⟨ex2, h2, h3⟩ := headBlock_stops s now hrun hstop
    have hex : ex = ex2 := List.append_cancel_left ((hx.symm.trans h2))
    subst hex
    refine ⟨ex, hx, Or.inl ⟨h3, ?_⟩⟩
    intro hf
    exact Pd_not_failed (hp _ hf) .deadline rfl

end Vinc.ValuesTime
