import Pinc.ValuesTimeDeadline

/-!
# Three corrections of the time rules

* The HEAD_HOLD tail threshold is the end of the wanted ranges in delivery order (`Fs.wend`), not the first request
  offset plus the wanted bytes: `tail_waits_for_wanted_end`, `tail_means_wanted_end`.
* A group another stream already stored (the race of two streams on one group) is announced once: `dupStep` writes
  and announces nothing of its own, `dupStep_announces_only_the_held`; with `announced_once` (which now ranges over
  inputs that repeat a group) the first granule is announced exactly once however the streams race.
* The stall timer runs from the first verified granule, not before: `no_granule_not_stalled`,
  `silent_after_granule_redialled`, `poll_offers_stall_from_first_granule`, `no_granule_no_timer`.
-/

set_option linter.unusedVariables false

namespace Pinc.ValuesTime
open Pinc.Ranges

/-- While the buffer behind the held granule stops short of the end of the wanted ranges, the cause is not the tail. -/
theorem tail_waits_for_wanted_end (s : Fs) (h : Head) (now : Nat)
    (hlt : h.off + h.len + bufOf s.store (h.off + h.len) < s.wend) : holdWhy s h now none ≠ some .tail := by
  intro e
  have := (holdWhy_tail s h now).1 e
  omega

/-- The tail cause means the verified run behind the held granule reaches the end of the wanted ranges. -/
theorem tail_means_wanted_end (s : Fs) (h : Head) (now : Nat) (e : holdWhy s h now none = some .tail) :
    s.wend ≤ h.off + h.len + bufOf s.store (h.off + h.len) := ((holdWhy_tail s h now).1 e).2

theorem holdCheck_head_cases (s : Fs) (now : Nat) (f : Option Cause) :
    (holdCheck s now f).head = none ∨ (holdCheck s now f).head = s.head := by
  unfold holdCheck
  split
  · right; rfl
  · split
    · right; rfl
    · left; simp [Fs.emit]

/-- A hold check announces nothing but the held granule. -/
theorem holdCheck_readable (s : Fs) (now : Nat) (f : Option Cause) (o l : Nat)
    (hm : Ev.readable o l ∈ (holdCheck s now f).log) :
    Ev.readable o l ∈ s.log ∨ ∃ h, s.head = some h ∧ o = h.off ∧ l = h.len := by
  unfold holdCheck at hm
  cases hh : s.head with
  | none => simp [hh] at hm; exact Or.inl hm
  | some h =>
    cases hw : holdWhy s h now f with
    | none => simp [hh, hw] at hm; exact Or.inl hm
    | some c =>
      simp [hh, hw, Fs.emit] at hm
      rcases hm with hm | ⟨h1, h2⟩
      · exact Or.inl hm
      · exact Or.inr ⟨h, rfl, h1, h2⟩

theorem checkDone_readable (s : Fs) (now : Nat) (o l : Nat) (hm : Ev.readable o l ∈ (checkDone s now).log) :
    Ev.readable o l ∈ s.log ∨ ∃ h, s.head = some h ∧ o = h.off ∧ l = h.len := by
  rw [checkDone_eq] at hm
  have first := fun hm' => holdCheck_readable s now none o l hm'
  have second : Ev.readable o l ∈ (holdCheck (holdCheck s now none) now (some .done)).log →
      Ev.readable o l ∈ s.log ∨ ∃ h, s.head = some h ∧ o = h.off ∧ l = h.len := by
    intro hm2
    rcases holdCheck_readable _ now _ o l hm2 with h1 | ⟨h, hh, h3, h4⟩
    · exact first h1
    · rcases holdCheck_head_cases s now none with e | e
      · rw [e] at hh; simp at hh
      · exact Or.inr ⟨h, by rw [← e]; exact hh, h3, h4⟩
  split at hm
  · simp [Fs.emit] at hm
    exact second hm
  · exact first hm

/-- A group the store already holds announces nothing of its own: any announcement is of the held granule. -/
theorem dupStep_announces_only_the_held (s : Fs) (now off len o l : Nat)
    (hm : Ev.readable o l ∈ (dupStep s now off len).log) :
    Ev.readable o l ∈ s.log ∨ ∃ h, s.head = some h ∧ o = h.off ∧ l = h.len := by
  unfold dupStep at hm
  rcases checkDone_readable _ now o l hm with h1 | h1
  · simp [Fs.emit] at h1; exact Or.inl h1
  · exact Or.inr h1

/-- A group already in the store, however it got there, adds only its `Verified` record to the log (apart from the
release of a held granule). -/
theorem verifyStep_dup_log (s : Fs) (now off len : Nat) (h : containsRange s.store (off, off + len) = true) :
    verifyStep s now off len = dupStep s now off len := by
  unfold verifyStep; rw [if_pos h]

/-- A fetch that has verified no granule is never stalled: the stall block of `on_timeout` changes nothing, whatever
was requested, whatever bytes arrived and however late the call is. -/
theorem no_granule_not_stalled (s : Fs) (now : Nat) (ss : List Sess) (h0 : s.lastp = 0) : stallStep s now ss = s := by
  simp [stallStep, h0]

/-- A fetch that verified a granule and heard nothing since is redialled when the wait is spent. -/
theorem silent_after_granule_redialled (s : Fs) (now : Nat) (ss : List Sess) (h0 : s.lastp ≠ 0) (hb : s.lastb ≤ s.lastp)
    (hdue : sadd s.lastp s.sw ≤ now) (hr : ¬ RttWait s now ss)
    (hl : stallLive now (lastProg s) ss = 0) : (stallStep s now ss).log ≠ s.log := by
  refine (redial_iff s now ss).2 ⟨⟨h0, ?_⟩, hr, hl⟩
  simpa [stallBase, Nat.max_eq_left hb] using hdue

/-- `poll_timeout` offers the stall time from the first verified granule on. -/
theorem poll_offers_stall_from_first_granule (s : Fs) (h : s.lastp ≠ 0) : sadd (stallBase s) s.sw ∈ pollList s := by
  simp [pollList, h]

/-- Before the first verified granule the stall rule arms nothing: a running fetch with no held granule, no steal
timer, no deadline and no retry has no timer at all, whatever was requested. -/
theorem no_granule_no_timer (s : Fs) (h0 : s.lastp = 0) (hh : s.head = none) (ht : s.tw = 0) (hd : s.deadline = none)
    (hr : s.rt = none) : pollTimeout s = none := by
  simp [pollTimeout, pollList, h0, hh, ht, hd, hr]

end Pinc.ValuesTime
