import Pinc.ConnectLink

/-!
# The client carrier state machine: the theorems

Every call of `ConnectLink.lean` is a `Call`; `Call.apply` runs it. The theorems hold for every link, every shared
state, every clock reading and every context, hence for every sequence of calls.

* `retry_ok`: the wait before a dial is retried is 1 s or 2 s, whatever the calls.
* `open_by_opened`: a call other than `opened` never makes a link `Open`.
* `lease_mono`: `lease_hi` never rises once it is set.
* `kiv_learn`: the learned keepalive interval is at least 15 s and at most half of an earlier one (or 15 s).
* `watchdog`: a dial past the watchdog is closed by the next tick.
* `tick_before_deadline`: a tick before the reported deadline does nothing.
* `tick_none_future`: when a tick does nothing, the next deadline is in the future (no busy loop).
* `tick_at_deadline_acts`: the tick at the reported deadline acts (no wake-up for nothing).
* `check_future`: a check started now is due in the future.
* `check_fail_lease`: an unanswered, unridden check at an idle gap of 15 s or more teaches the lease.
* `stale_send_iff`: a send resets the carrier exactly when it was idle both ways for the lease.
* `defer_waits`, `defer_cancelled`: the restart defer.
-/

namespace Pinc.ConnectLink

/-- The calls of the module. -/
inductive Call where
  | wd (now : Nat) (c : Ctx)
  | op (now : Nat)
  | cl (now : Nat)
  | hr (now : Nat)
  | wr (now : Nat)
  | pu (now : Nat) (c : Ctx)
  | rs (now : Nat)
  | bs (now : Nat) (c : Ctx)
  | ck (now : Nat) (c : Ctx) (ridden : Bool)
  | tk (now : Nat) (c : Ctx)

/-- Run a call. -/
def Call.apply : Call → Link → Shared → Link × Shared
  | .wd now c, l, s => let r := wantDial l s now c; (r.2.1, r.2.2)
  | .op now, l, s => ((opened l now).2, s)
  | .cl now, l, s => (closed l now, s)
  | .hr now, l, s => (heard l now, s)
  | .wr now, l, s => (wrote l now, s)
  | .pu now c, l, s => ((pulse l now c).2, s)
  | .rs now, l, s => ((reset l now).2, s)
  | .bs now c, l, s => ((beforeSend l s now c).2, s)
  | .ck now c r, l, s => ((startCheck l now c r).2, s)
  | .tk now c, l, s => let r := tick l s now c; (r.2.1, r.2.2)

/-! ## The pieces -/

theorem cancelDefer_retry (l : Link) (s : Shared) (now : Nat) (c : Ctx) : (cancelDefer l s now c).retry = l.retry := by
  unfold cancelDefer; split <;> rfl

theorem cancelDefer_st (l : Link) (s : Shared) (now : Nat) (c : Ctx) : (cancelDefer l s now c).st = l.st := by
  unfold cancelDefer; split <;> rfl

theorem dialOrWait_retry (l : Link) (s : Shared) (now : Nat) (c : Ctx) : (dialOrWait l s now c).2.1.retry = l.retry := by
  unfold dialOrWait; split <;> rfl

theorem dialOrWait_st (l : Link) (s : Shared) (now : Nat) (c : Ctx) :
    (dialOrWait l s now c).2.1.st = .open_ → l.st = .open_ := by
  unfold dialOrWait; split <;> simp

theorem wantDial_retry (l : Link) (s : Shared) (now : Nat) (c : Ctx) : (wantDial l s now c).2.1.retry = l.retry := by
  unfold wantDial
  split
  · rfl
  · split
    · rfl
    · rw [dialOrWait_retry, cancelDefer_retry]

theorem wantDial_st (l : Link) (s : Shared) (now : Nat) (c : Ctx) :
    (wantDial l s now c).2.1.st = .open_ → l.st = .open_ := by
  unfold wantDial
  split
  · exact id
  · split
    · intro h; simpa using h
    · intro h
      have := dialOrWait_st _ _ _ _ h
      rwa [cancelDefer_st] at this

theorem startCheck_retry (l : Link) (now : Nat) (c : Ctx) (r : Bool) : (startCheck l now c r).2.retry = l.retry := by
  unfold startCheck; split
  · rfl
  · split <;> rfl

theorem startCheck_st (l : Link) (now : Nat) (c : Ctx) (r : Bool) : (startCheck l now c r).2.st = l.st := by
  unfold startCheck; split
  · rfl
  · split <;> rfl

theorem startCheck_chk (l : Link) (now : Nat) (c : Ctx) (r : Bool) :
    (startCheck l now c r).2.chk = l.chk ∨ (startCheck l now c r).2.chk = now + checkWait c.rtt := by
  unfold startCheck; split
  · exact Or.inl rfl
  · split <;> exact Or.inr rfl

theorem startCheck_future (l : Link) (now : Nat) (c : Ctx) (r : Bool) (h : l.isOpen ∧ l.chk = 0) :
    (startCheck l now c r).2.chk = now + checkWait c.rtt := by
  unfold startCheck
  have : ¬ (¬ l.isOpen ∨ l.chk ≠ 0) := by simp [h.1, h.2]
  rw [if_neg this]
  split <;> rfl

theorem checkWait_pos (rtt : Nat) : 0 < checkWait rtt := by
  have hm : 0 < checkMin := by simp [checkMin, sec]
  unfold checkWait
  by_cases h : rtt * checkRtts > checkMin
  · rw [if_pos h]; omega
  · rw [if_neg h]; exact hm

/-! ## Retry, opening, lease and keepalive learning -/

theorem tickOpen_retry (l : Link) (s : Shared) (now : Nat) (c : Ctx) : (tickOpen l s now c).2.1.retry = l.retry := by
  unfold tickOpen
  dsimp only
  split
  · split
    · exact startCheck_retry _ _ _ _
    · simp [reset]
  · split
    · rfl
    · split
      · exact startCheck_retry _ _ _ _
      · split <;> rfl

theorem tickOpen_st (l : Link) (s : Shared) (now : Nat) (c : Ctx) :
    (tickOpen l s now c).2.1.st = .open_ → l.st = .open_ := by
  unfold tickOpen
  dsimp only
  split
  · split
    · intro h; rw [startCheck_st] at h; exact h
    · intro h; simp [reset] at h
  · split
    · exact id
    · split
      · intro h; rw [startCheck_st] at h; exact h
      · split <;> exact id

theorem tick_retry (l : Link) (s : Shared) (now : Nat) (c : Ctx) : (tick l s now c).2.1.retry = l.retry := by
  unfold tick
  split
  · split <;> rfl
  · exact wantDial_retry l s now c
  · exact tickOpen_retry l s now c

theorem tick_st (l : Link) (s : Shared) (now : Nat) (c : Ctx) :
    (tick l s now c).2.1.st = .open_ → l.st = .open_ := by
  unfold tick
  split
  · split <;> simp
  · exact wantDial_st l s now c
  · exact tickOpen_st l s now c

/-- The wait before a dial is retried is 1 s or 2 s, whatever the calls. -/
theorem retry_ok (cl : Call) (l : Link) (s : Shared) (h : l.retry = retryMin ∨ l.retry = retryMax) :
    (cl.apply l s).1.retry = retryMin ∨ (cl.apply l s).1.retry = retryMax := by
  cases cl with
  | wd now c => simpa [Call.apply, wantDial_retry] using h
  | op now => simp [Call.apply, opened]
  | cl now =>
    simp only [Call.apply, closed]
    rcases h with h | h <;> simp [h, retryMin, retryMax, sec]
  | hr now => simpa [Call.apply, heard] using h
  | wr now => simpa [Call.apply, wrote] using h
  | pu now c =>
    simp only [Call.apply, pulse]
    split
    · exact h
    · simpa [startCheck_retry] using h
  | rs now => simpa [Call.apply, reset] using h
  | bs now c =>
    simp only [Call.apply, beforeSend, reset]
    split <;> simpa using h
  | ck now c r => simpa [Call.apply, startCheck_retry] using h
  | tk now c => simpa [Call.apply, tick_retry] using h

/-- `Open` is reached only through `opened`. -/
theorem open_by_opened (cl : Call) (l : Link) (s : Shared) (hn : ∀ now, cl ≠ Call.op now)
    (h : (cl.apply l s).1.st = .open_) : l.st = .open_ := by
  cases cl with
  | wd now c => exact wantDial_st l s now c (by simpa [Call.apply] using h)
  | op now => exact absurd rfl (hn now)
  | cl now => simp [Call.apply, closed] at h
  | hr now => simpa [Call.apply, heard] using h
  | wr now => simpa [Call.apply, wrote] using h
  | pu now c =>
    simp only [Call.apply, pulse] at h
    split at h
    · exact h
    · simpa [startCheck_st] using h
  | rs now => simp [Call.apply, reset] at h
  | bs now c =>
    simp only [Call.apply, beforeSend, reset] at h
    split at h <;> simp_all
  | ck now c r => simpa [Call.apply, startCheck_st] using h
  | tk now c => exact tick_st l s now c (by simpa [Call.apply] using h)

/-! ## The lease and the learned keepalive -/

theorem wantDial_shared (l : Link) (s : Shared) (now : Nat) (c : Ctx) :
    (wantDial l s now c).2.2.lhi = s.lhi ∧ (wantDial l s now c).2.2.kiv = s.kiv := by
  unfold wantDial
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · unfold dialOrWait
      split <;> exact ⟨rfl, rfl⟩

/-- The lease handed out by an unanswered check. -/
theorem tickOpen_lhi (l : Link) (s : Shared) (now : Nat) (c : Ctx) (h : s.lhi ≠ 0) :
    (tickOpen l s now c).2.2.lhi ≠ 0 ∧ (tickOpen l s now c).2.2.lhi ≤ s.lhi := by
  unfold tickOpen
  dsimp only
  split
  · split
    · simp [h]
    · have hf : 0 < leaseFloor := by simp [leaseFloor, sec]
      by_cases hc : c.udp = false ∧ leaseFloor ≤ l.gap
      · by_cases hk : s.klearn = true <;> simp [hc, hk, h] <;> omega
      · by_cases hk : s.klearn = true <;> simp [hc, hk, h]
  · split <;> (try split) <;> (try split) <;> simp [h]

theorem tick_lhi (l : Link) (s : Shared) (now : Nat) (c : Ctx) (h : s.lhi ≠ 0) :
    (tick l s now c).2.2.lhi ≠ 0 ∧ (tick l s now c).2.2.lhi ≤ s.lhi := by
  unfold tick
  split
  · split <;> simp [h]
  · exact ⟨by rw [(wantDial_shared l s now c).1]; exact h, by rw [(wantDial_shared l s now c).1]; exact Nat.le_refl _⟩
  · exact tickOpen_lhi l s now c h

/-- `lease_hi` never rises once it is set. -/
theorem lease_mono (cl : Call) (l : Link) (s : Shared) (h : s.lhi ≠ 0) :
    (cl.apply l s).2.lhi ≠ 0 ∧ (cl.apply l s).2.lhi ≤ s.lhi := by
  cases cl with
  | wd now c =>
    simp only [Call.apply]
    rw [(wantDial_shared l s now c).1]; exact ⟨h, Nat.le_refl _⟩
  | tk now c => simpa [Call.apply] using tick_lhi l s now c h
  | _ => exact ⟨h, Nat.le_refl _⟩

/-- A learned keepalive interval is at least 15 s and at most half of the one it replaces (or 15 s). -/
theorem kiv_learn (l : Link) (s : Shared) (now : Nat) (c : Ctx) (h : (tickOpen l s now c).2.2.kiv ≠ s.kiv) :
    keepFloor ≤ (tickOpen l s now c).2.2.kiv ∧
      (s.kiv ≠ 0 → (tickOpen l s now c).2.2.kiv ≤ max keepFloor (s.kiv / 2)) := by
  revert h
  unfold tickOpen
  dsimp only
  split
  · split
    · intro h; simp at h
    · simp only []
      by_cases hk : s.klearn = true
      · by_cases hc : c.udp = false ∧ leaseFloor ≤ l.gap
        · intro h
          simp [hc, hk]
          refine ⟨by omega, ?_⟩
          intro hs
          by_cases hz : s.kiv = 0
          · exact absurd hz hs
          · simp only [hz, if_false]
            have : min s.kiv (satSub now l.lrx) ≤ s.kiv := Nat.min_le_left _ _
            omega
        · intro h
          simp [hc, hk]
          refine ⟨by omega, ?_⟩
          intro hs
          by_cases hz : s.kiv = 0
          · exact absurd hz hs
          · simp only [hz, if_false]
            have : min s.kiv (satSub now l.lrx) ≤ s.kiv := Nat.min_le_left _ _
            omega
      · intro h
        have : ((if c.udp = false ∧ leaseFloor ≤ l.gap then
            ({ phone := s.phone, kfail := some now, lhi := if s.lhi = 0 then l.gap else min s.lhi l.gap, klearn := s.klearn,
               kiv := s.kiv, restarted := s.restarted, du := s.du } : Shared) else
            { phone := s.phone, kfail := some now, lhi := s.lhi, klearn := s.klearn, kiv := s.kiv,
              restarted := s.restarted, du := s.du })).kiv = s.kiv := by split <;> rfl
        simp [hk] at h
        split at h <;> simp_all
  · intro h
    split at h <;> (try split at h) <;> (try split at h) <;> simp_all

/-- A dial past the watchdog is closed at once. -/
theorem watchdog (l : Link) (s : Shared) (now : Nat) (c : Ctx) (hd : l.st = .dialing)
    (h : satSub now l.ds > dialWait c.rtt) :
    tick l s now c = (some .close, { l with st := .down, at_ := now }, s) := by
  simp [tick, hd, h]

/-- A check started now is due in the future. -/
theorem check_future (l : Link) (now : Nat) (c : Ctx) (r : Bool) (h : l.isOpen ∧ l.chk = 0) :
    now < (startCheck l now c r).2.chk := by
  rw [startCheck_future l now c r h]
  have := checkWait_pos c.rtt
  omega

/-- An unanswered, unridden check taken at an idle gap of 15 s or more teaches the lease. -/
theorem check_fail_lease (l : Link) (s : Shared) (now : Nat) (c : Ctx) (hc : l.chk ≠ 0 ∧ l.chk ≤ now)
    (hr : l.ride = false) (hu : c.udp = false) (hg : leaseFloor ≤ l.gap) :
    (tickOpen l s now c).1 = some .close ∧
      (tickOpen l s now c).2.2.lhi = (if s.lhi = 0 then l.gap else min s.lhi l.gap) := by
  unfold tickOpen
  dsimp only
  have h1 : l.chk ≠ 0 ∧ now ≥ l.chk := hc
  rw [if_pos h1]
  simp only [hr, Bool.false_eq_true, if_false]
  by_cases hk : s.klearn = true <;> simp [hk, hu, hg, reset]

/-- A send resets the carrier exactly when it was idle both ways for the lease. -/
theorem stale_send_iff (l : Link) (s : Shared) (now : Nat) (c : Ctx) :
    (beforeSend l s now c).1 = some .close ↔
      (l.isOpen = true ∧ s.lhi ≠ 0 ∧ c.udp = false ∧ satSub now l.hlt ≥ s.lhi ∧ satSub now l.lrx ≥ s.lhi) := by
  unfold beforeSend
  by_cases h : l.isOpen = true ∧ s.lhi ≠ 0 ∧ ¬ c.udp = true ∧ satSub now l.hlt ≥ s.lhi ∧ satSub now l.lrx ≥ s.lhi
  · rw [if_pos h]
    simp [reset]
    simpa using h
  · rw [if_neg h]
    simp
    intro h1 h2 h3 h4
    by_cases h5 : s.lhi ≤ satSub now l.lrx
    · exact absurd ⟨h1, h2, by simpa using h3, h4, h5⟩ h
    · omega

/-- During the restart defer, whose end is fixed when the shared state is built, the home carrier's own dial waits. -/
theorem defer_waits (l : Link) (s : Shared) (now : Nat) (c : Ctx) (hd : l.st = .down) (hr : s.restarted = true)
    (hq : c.queued = false) (hh : c.home = true) (hn : now < s.du.getD 0) :
    (wantDial l s now c).1 = none := by
  unfold wantDial
  rw [if_neg (by simp [hd]), if_pos (by exact ⟨hr, hq, hh, hn⟩)]

/-- A frame to send cancels it. -/
theorem defer_cancelled (l : Link) (s : Shared) (now : Nat) (c : Ctx) (hd : l.st = .down) (hr : s.restarted = true)
    (hq : c.queued = true) (hdf : l.defer = true) : (wantDial l s now c).1 = some .dial := by
  have hnd : ¬ deferring s now c := fun h => absurd (h.2.1.symm.trans hq) (by decide)
  unfold wantDial
  rw [if_neg (by simp [hd]), if_neg hnd]
  simp [dialOrWait, cancelDefer, hr, hq, hdf, Nat.min_le_right]

/-! ## The deadline -/

theorem keepAfter_pos (s : Shared) (now : Nat) (c : Ctx) : 0 < keepAfter s now c := by
  have h1 : 0 < homeKeep := by simp [homeKeep, sec]
  have h2 : 0 < relayKeep := by simp [relayKeep, sec]
  have hbase : ∀ b : Bool, 0 < (if b = true then homeKeep else relayKeep) := by
    intro b; split <;> assumption
  unfold keepAfter keepOf
  dsimp only
  by_cases hz : s.kiv = 0
  · rw [if_pos hz]; exact hbase _
  · rw [if_neg hz]
    apply Nat.lt_min.2
    exact ⟨hbase _, by omega⟩

theorem leaseKeep_pos (hi : Nat) : 0 < leaseKeep hi := by
  have hf : 0 < leaseFloor := by simp [leaseFloor, sec]
  unfold leaseKeep
  dsimp only
  split <;> split <;> omega

theorem tbd_dialing (l : Link) (s : Shared) (now : Nat) (c : Ctx) (hst : l.st = .dialing)
    (hn : now < l.ds + dialWait c.rtt + 1) : (tick l s now c).1 = none := by
  by_cases hw : satSub now l.ds > dialWait c.rtt
  · simp only [satSub] at hw; omega
  · simp [tick, hst, hw]

theorem tbd_down (l : Link) (s : Shared) (now : Nat) (c : Ctx) (hst : l.st = .down) (hqh : c.queued = true ∨ c.home = true)
    (hrq : ¬(s.restarted = true ∧ c.queued = true ∧ l.defer = true)) (hn : now < l.at_) : (tick l s now c).1 = none := by
  have hcd : cancelDefer l s now c = l := by unfold cancelDefer; rw [if_neg hrq]
  have hdw : (dialOrWait l s now c).1 = none := by
    unfold dialOrWait; rw [if_neg (by omega)]
  have hdw' : ∀ s1, (dialOrWait l s1 now c).1 = none := by
    intro s1; unfold dialOrWait; rw [if_neg (by omega)]
  simp only [tick, hst]
  unfold wantDial
  rw [if_neg (by simp [hst])]
  split
  · rfl
  · rw [hcd]; exact hdw' _

theorem tbd_open_chk (l : Link) (s : Shared) (now : Nat) (c : Ctx) (hst : l.st = .open_) (hc : l.chk ≠ 0)
    (hn : now < l.chk) : (tick l s now c).1 = none := by
  simp only [tick, hst]
  unfold tickOpen
  dsimp only
  rw [if_neg (by omega), if_pos hc]

theorem tbd_open (l : Link) (s : Shared) (now : Nat) (c : Ctx) (hst : l.st = .open_) (hc : l.chk = 0)
    (hlk : (s.lhi ≠ 0 ∧ c.udp = false) → now < l.hlt + leaseKeep s.lhi)
    (hsil : now < keepDue l s now c) : (tick l s now c).1 = none := by
  simp only [tick, hst]
  unfold tickOpen
  dsimp only
  rw [if_neg (by omega), if_neg (by omega)]
  have h1 : ¬ ((s.lhi ≠ 0 ∧ ¬ c.udp = true) ∧ (c.home = true ∨ c.rides = true) ∧ satSub now l.hlt ≥ leaseKeep s.lhi) := by
    intro ⟨⟨a, b⟩, _, d⟩
    have := hlk ⟨a, by simpa using b⟩
    have := leaseKeep_pos s.lhi
    simp only [satSub] at d
    omega
  rw [if_neg h1]
  have h2 : ¬ ((c.home = true ∨ c.rides = true) ∧ now ≥ keepDue l s now c) := by
    intro ⟨_, d⟩
    omega
  rw [if_neg h2]

/-- A tick before the reported deadline does nothing. -/
theorem tick_before_deadline (l : Link) (s : Shared) (now : Nat) (c : Ctx) (d : Nat)
    (h : nextDeadline l s now c = some d) (hn : now < d) : (tick l s now c).1 = none := by
  unfold nextDeadline at h
  cases hst : l.st with
  | dialing =>
    rw [hst] at h
    simp only [Option.some.injEq] at h
    subst h
    exact tbd_dialing l s now c hst hn
  | down =>
    rw [hst] at h
    dsimp only at h
    split at h
    · rename_i hqh
      simp only [Option.some.injEq] at h
      subst h
      by_cases hdf : deferring s now c
      · simp only [tick, hst]
        unfold wantDial
        rw [if_neg (by simp [hst]), if_pos hdf]
      · unfold dialAt at hn
        rw [if_neg hdf] at hn
        by_cases hrq : s.restarted = true ∧ c.queued = true ∧ l.defer = true
        · rw [if_pos (by simpa using hrq)] at hn
          have := Nat.min_le_right l.at_ now
          omega
        · rw [if_neg (by simpa using hrq)] at hn
          exact tbd_down l s now c hst (by simpa using hqh) hrq hn
    · simp at h
  | open_ =>
    rw [hst] at h
    dsimp only at h
    by_cases hc : l.chk ≠ 0
    · rw [if_pos hc] at h
      simp only [Option.some.injEq] at h
      subst h
      exact tbd_open_chk l s now c hst hc hn
    · rw [if_neg hc] at h
      have hc0 : l.chk = 0 := by omega
      split at h
      · simp at h
      · rename_i hhr
        by_cases hlease : s.lhi ≠ 0 ∧ ¬ c.udp = true
        · rw [if_pos hlease] at h
          simp only [Option.some.injEq] at h
          subst h
          exact tbd_open l s now c hst hc0 (fun _ => Nat.lt_of_lt_of_le hn (Nat.min_le_left _ _))
            (Nat.lt_of_lt_of_le hn (Nat.min_le_right _ _))
        · rw [if_neg hlease] at h
          simp only [Option.some.injEq] at h
          subst h
          exact tbd_open l s now c hst hc0 (fun hh => absurd ⟨hh.1, by simpa using hh.2⟩ hlease) hn

theorem dialOrWait_none {l1 : Link} {s1 s' : Shared} {now : Nat} {c : Ctx} {l' : Link}
    (h : dialOrWait l1 s1 now c = (none, l', s')) : l' = l1 ∧ s' = s1 ∧ ¬ (l1.at_ ≤ now ∧ (c.queued = true ∨ c.home = true)) := by
  unfold dialOrWait at h
  by_cases hc : l1.at_ ≤ now ∧ (c.queued = true ∨ c.home = true)
  · rw [if_pos hc] at h; simp at h
  · rw [if_neg hc] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨_, h2, h3⟩ := h
    exact ⟨h2.symm, h3.symm, hc⟩

theorem tnf_down (l : Link) (s : Shared) (now : Nat) (c : Ctx) (l' : Link) (s' : Shared) (hst : l.st = .down)
    (h : wantDial l s now c = (none, l', s')) :
    nextDeadline l' s' now c = none ∨ ∃ d, nextDeadline l' s' now c = some d ∧ now < d := by
  unfold wantDial at h
  rw [if_neg (by simp [hst])] at h
  by_cases hd : deferring s now c
  · rw [if_pos hd] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨_, hl, hs⟩ := h
    subst hl hs
    right
    have hh : c.home = true := hd.2.2.1
    have hn := hd.2.2.2
    refine ⟨dialAt { l with at_ := dialAt l s now c, defer := true } s now c, ?_, ?_⟩
    · simp [nextDeadline, hst, hh]
    · have : s.du.getD 0 ≤ dialAt { l with at_ := dialAt l s now c, defer := true } s now c := by
        unfold dialAt; rw [if_pos hd]; exact Nat.le_max_right _ _
      omega
  · rw [if_neg hd] at h
    obtain ⟨hl, hs, hn⟩ := dialOrWait_none h
    subst hl
    subst s'
    simp only [nextDeadline]
    have hst1 : (cancelDefer l s now c).st = .down := by rw [cancelDefer_st]; exact hst
    by_cases hqh : c.queued = true ∨ c.home = true
    · right
      have hat : now < (cancelDefer l s now c).at_ := Classical.byContradiction fun hx => hn ⟨by omega, hqh⟩
      have hrq : ¬ (s.restarted = true ∧ c.queued = true ∧ (cancelDefer l s now c).defer = true) := by
        intro hrq
        unfold cancelDefer at hrq
        by_cases hc : s.restarted = true ∧ c.queued = true ∧ l.defer = true
        · rw [if_pos hc] at hrq; simp at hrq
        · rw [if_neg hc] at hrq
          exact hc hrq
      refine ⟨(cancelDefer l s now c).at_, ?_, hat⟩
      simp only [hst1, hqh, or_self, if_true]
      unfold dialAt
      rw [if_neg hd, if_neg hrq]
    · left
      simp [hst1, hqh]

theorem startCheck_ping (l : Link) (now : Nat) (c : Ctx) (hst : l.st = .open_) (hc : l.chk = 0) :
    (startCheck l now c false).1 = some .ping := by
  unfold startCheck
  rw [if_neg (by simp [Link.isOpen, hst, hc])]
  simp

theorem tnf_open (l : Link) (s : Shared) (now : Nat) (c : Ctx) (l' : Link) (s' : Shared) (hst : l.st = .open_)
    (h : tickOpen l s now c = (none, l', s')) :
    nextDeadline l' s' now c = none ∨ ∃ d, nextDeadline l' s' now c = some d ∧ now < d := by
  unfold tickOpen at h
  dsimp only at h
  by_cases hA : l.chk ≠ 0 ∧ now ≥ l.chk
  · rw [if_pos hA] at h
    by_cases hr : l.ride = true
    · rw [if_pos hr] at h
      have := startCheck_ping { l with chk := 0 } now c hst rfl
      simp only [Prod.mk.injEq] at h
      rw [h.1] at this
      simp at this
    · rw [if_neg hr] at h
      simp only [reset] at h
      split at h <;> simp at h
  · rw [if_neg hA] at h
    by_cases hB : l.chk ≠ 0
    · rw [if_pos hB] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨_, hl, hs⟩ := h
      subst hl hs
      right
      refine ⟨l.chk, ?_, by omega⟩
      simp [nextDeadline, hst, hB]
    · rw [if_neg hB] at h
      have hc0 : l.chk = 0 := by omega
      by_cases hC : (s.lhi ≠ 0 ∧ ¬ c.udp = true) ∧ (c.home = true ∨ c.rides = true) ∧ satSub now l.hlt ≥ leaseKeep s.lhi
      · rw [if_pos hC] at h
        have := startCheck_ping l now c hst hc0
        simp only [Prod.mk.injEq] at h
        rw [h.1] at this
        simp at this
      · rw [if_neg hC] at h
        by_cases hD : (c.home = true ∨ c.rides = true) ∧ now ≥ keepDue l s now c
        · rw [if_pos hD] at h; simp at h
        · rw [if_neg hD] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨_, hl, hs⟩ := h
          subst hl hs
          by_cases hhr : c.home = true ∨ c.rides = true
          · right
            have hl := leaseKeep_pos s.lhi
            have hD' : now < keepDue l s now c := by
              by_cases hh : now ≥ keepDue l s now c
              · exact absurd ⟨hhr, hh⟩ hD
              · omega
            by_cases hlease : s.lhi ≠ 0 ∧ ¬ c.udp = true
            · have hC' : now < l.hlt + leaseKeep s.lhi := by
                by_cases hh : satSub now l.hlt ≥ leaseKeep s.lhi
                · exact absurd ⟨hlease, hhr, hh⟩ hC
                · simp only [satSub] at hh; omega
              refine ⟨min (l.hlt + leaseKeep s.lhi) (keepDue l s now c), ?_, by omega⟩
              simp [nextDeadline, hst, hc0, hhr, hlease.1, hlease.2]
            · refine ⟨keepDue l s now c, ?_, hD'⟩
              have : ¬ (s.lhi ≠ 0 ∧ c.udp = false) := by simpa using hlease
              simp [nextDeadline, hst, hc0, hhr, this]
          · left
            simp [nextDeadline, hst, hc0, hhr]

/-- When a tick does nothing, the next deadline is in the future: the host that sleeps until it does not spin. -/
theorem tick_none_future (l : Link) (s : Shared) (now : Nat) (c : Ctx) (l' : Link) (s' : Shared)
    (h : tick l s now c = (none, l', s')) :
    nextDeadline l' s' now c = none ∨ ∃ d, nextDeadline l' s' now c = some d ∧ now < d := by
  cases hst : l.st with
  | dialing =>
    simp only [tick, hst] at h
    by_cases hw : satSub now l.ds > dialWait c.rtt
    · rw [if_pos hw] at h; simp at h
    · rw [if_neg hw] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨_, hl, hs⟩ := h
      subst hl hs
      right
      refine ⟨l.ds + dialWait c.rtt + 1, ?_, ?_⟩
      · simp [nextDeadline, hst]
      · simp only [satSub] at hw; omega
  | down =>
    simp only [tick, hst] at h
    exact tnf_down l s now c l' s' hst h
  | open_ =>
    simp only [tick, hst] at h
    exact tnf_open l s now c l' s' hst h

/-! ## The tick at the deadline acts -/

theorem recent_anti (s : Shared) {t1 t2 : Nat} (h : t1 ≤ t2) (hr : recent s t2 = true) : recent s t1 = true := by
  unfold recent at hr ⊢
  cases hk : s.kfail with
  | none => simp [hk] at hr
  | some k =>
    simp [hk, satSub] at hr ⊢
    omega

theorem keepOf_mono (s : Shared) (c : Ctx) : keepOf s c true ≤ keepOf s c false := by
  have hb : ∀ b1 b2 : Bool, (b2 = true → b1 = true) →
      (if b1 = true then homeKeep else relayKeep) ≤ (if b2 = true then homeKeep else relayKeep) := by
    have : homeKeep ≤ relayKeep := by simp [homeKeep, relayKeep, sec]
    intro b1 b2 h
    cases b1 <;> cases b2 <;> simp at h ⊢ <;> omega
  have hb' := hb (c.home && (s.phone || true)) (c.home && (s.phone || false))
    (by cases c.home <;> cases s.phone <;> simp)
  unfold keepOf
  dsimp only
  by_cases hz : s.kiv = 0
  · rw [if_pos hz, if_pos hz]; exact hb'
  · rw [if_neg hz, if_neg hz]
    omega

/-- The keepalive interval only grows with time: the memory of a silent death ends and never comes back by itself. -/
theorem keepAfter_mono (s : Shared) (c : Ctx) {t1 t2 : Nat} (h : t1 ≤ t2) : keepAfter s t1 c ≤ keepAfter s t2 c := by
  unfold keepAfter
  cases h2 : recent s t2
  · cases h1 : recent s t1
    · exact Nat.le_refl _
    · exact keepOf_mono s c
  · simp [recent_anti s h h2]

/-- Once the interval has changed it changes no more. -/
theorem keepAfter_settles (s : Shared) (c : Ctx) {t1 t2 t3 : Nat} (h12 : t1 ≤ t2) (h23 : t2 ≤ t3)
    (hne : keepAfter s t1 c ≠ keepAfter s t2 c) : keepAfter s t2 c = keepAfter s t3 c := by
  unfold keepAfter at hne ⊢
  cases h2 : recent s t2
  · cases h3 : recent s t3
    · rfl
    · exact absurd (h2.symm.trans (recent_anti s h23 h3)) (by decide)
  · rw [h2, recent_anti s h12 h2] at hne
    exact absurd rfl hne

/-- The fixed point under `keepDue`, for any interval `A` that only grows and changes at most once. -/
theorem due_fix (A : Nat → Nat) (mono : ∀ x y, x ≤ y → A x ≤ A y)
    (settle : ∀ x y z, x ≤ y → y ≤ z → A x ≠ A y → A y = A z) (r n : Nat) :
    r + A (max (r + A (max (r + A (max (r + A n) n)) n)) (max (r + A (max (r + A n) n)) n))
      ≤ max (r + A (max (r + A n) n)) n := by
  by_cases hf : r + A n ≤ n
  · have e : max (r + A n) n = n := Nat.max_eq_right hf
    simp only [e]
    exact hf
  · have hnf : n ≤ r + A n := by omega
    have e1 : max (r + A n) n = r + A n := Nat.max_eq_left hnf
    simp only [e1]
    generalize hfv : r + A n = f at *
    have hA := mono n f hnf
    have hfB : f ≤ r + A f := by omega
    have e2 : max (r + A f) n = r + A f := Nat.max_eq_left (by omega)
    simp only [e2]
    generalize hBv : r + A f = B at *
    have hB := mono f B hfB
    have e3 : max (r + A B) B = r + A B := Nat.max_eq_left (by omega)
    simp only [e3]
    by_cases he : A n = A f
    · have h1 : A B = A f := congrArg A (by omega)
      have h2 : A (r + A B) = A B := congrArg A (by omega)
      omega
    · have hs := settle n f (r + A B) hnf (by omega) he
      omega

/-- The check reported due is due when read again at that instant (or at `now`, if that is later). -/
theorem keepDue_fix (l : Link) (s : Shared) (now : Nat) (c : Ctx) :
    keepDue l s (max (keepDue l s now c) now) c ≤ max (keepDue l s now c) now := by
  unfold keepDue
  exact due_fix (fun t => keepAfter s t c) (fun _ _ h => keepAfter_mono s c h)
    (fun _ _ _ h1 h2 h => keepAfter_settles s c h1 h2 h) l.lrx now

/-- The tick at the reported deadline (or at `now`, if the deadline is past) acts: a host that sleeps until the
deadline is never woken for nothing. -/
theorem tick_at_deadline_acts (l : Link) (s : Shared) (now : Nat) (c : Ctx) (d : Nat)
    (h : nextDeadline l s now c = some d) : (tick l s (max d now) c).1.isSome = true := by
  unfold nextDeadline at h
  cases hst : l.st with
  | dialing =>
    rw [hst] at h
    simp only [Option.some.injEq] at h
    subst h
    have hw : satSub (max (l.ds + dialWait c.rtt + 1) now) l.ds > dialWait c.rtt := by
      have := Nat.le_max_left (l.ds + dialWait c.rtt + 1) now
      simp only [satSub]; omega
    simp [tick, hst, hw]
  | down =>
    rw [hst] at h
    dsimp only at h
    split at h
    · rename_i hqh
      simp only [Option.some.injEq] at h
      subst h
      simp only [tick, hst]
      unfold wantDial
      rw [if_neg (by simp [hst])]
      by_cases hd : deferring s now c
      · have hD : dialAt l s now c = max l.at_ (s.du.getD 0) := by unfold dialAt; rw [if_pos hd]
        have h1 := Nat.le_max_left l.at_ (s.du.getD 0)
        have h2 := Nat.le_max_right l.at_ (s.du.getD 0)
        have hn := hd.2.2.2
        have ht : max (dialAt l s now c) now = dialAt l s now c := Nat.max_eq_left (by omega)
        rw [ht, hD, if_neg (by intro hx; have := hx.2.2.2; omega)]
        have hcd : cancelDefer l s (max l.at_ (s.du.getD 0)) c = l := by
          unfold cancelDefer; rw [if_neg (by simp [hd.2.1])]
        rw [hcd]
        unfold dialOrWait
        rw [if_pos (by exact ⟨h1, Or.inr hd.2.2.1⟩)]
        rfl
      · by_cases hrq : s.restarted = true ∧ c.queued = true ∧ l.defer = true
        · have hD : dialAt l s now c = min l.at_ now := by
            unfold dialAt; rw [if_neg hd, if_pos (by simpa using hrq)]
          have ht : max (dialAt l s now c) now = now := by rw [hD]; exact Nat.max_eq_right (Nat.min_le_right _ _)
          rw [ht, if_neg hd]
          unfold cancelDefer
          rw [if_pos (by simpa using hrq)]
          unfold dialOrWait
          rw [if_pos (by exact ⟨Nat.min_le_right _ _, Or.inl hrq.2.1⟩)]
          rfl
        · have hD : dialAt l s now c = l.at_ := by
            unfold dialAt; rw [if_neg hd, if_neg (by simpa using hrq)]
          rw [hD]
          have h1 := Nat.le_max_left l.at_ now
          have h2 := Nat.le_max_right l.at_ now
          rw [if_neg (by intro hx; exact hd ⟨hx.1, hx.2.1, hx.2.2.1, by have := hx.2.2.2; omega⟩)]
          have hcd : cancelDefer l s (max l.at_ now) c = l := by
            unfold cancelDefer; rw [if_neg (by simpa using hrq)]
          rw [hcd]
          unfold dialOrWait
          rw [if_pos (by exact ⟨h1, by simpa using hqh⟩)]
          rfl
    · simp at h
  | open_ =>
    rw [hst] at h
    dsimp only at h
    simp only [tick, hst]
    by_cases hc : l.chk ≠ 0
    · rw [if_pos hc] at h
      simp only [Option.some.injEq] at h
      subst h
      unfold tickOpen
      dsimp only
      rw [if_pos (by exact ⟨hc, Nat.le_max_left _ _⟩)]
      by_cases hr : l.ride = true
      · rw [if_pos hr]
        have := startCheck_ping { l with chk := 0 } (max l.chk now) c hst rfl
        simp [this]
      · rw [if_neg hr]
        simp
    · rw [if_neg hc] at h
      have hc0 : l.chk = 0 := by omega
      split at h
      · simp at h
      · rename_i hhr
        have hhr' : c.home = true ∨ c.rides = true := Classical.byContradiction fun hx => hhr hx
        -- the deadline is the check due, or the lease's when that comes first
        have hdk : d ≤ keepDue l s now c ∧ (d = keepDue l s now c ∨
            (s.lhi ≠ 0 ∧ c.udp = false ∧ d = l.hlt + leaseKeep s.lhi)) := by
          by_cases hlease : s.lhi ≠ 0 ∧ ¬ c.udp = true
          · rw [if_pos hlease] at h
            simp only [Option.some.injEq] at h
            subst h
            have hu : c.udp = false := by simpa using hlease.2
            constructor
            · exact Nat.min_le_right _ _
            · by_cases hab : l.hlt + leaseKeep s.lhi ≤ keepDue l s now c
              · exact Or.inr ⟨hlease.1, hu, Nat.min_eq_left hab⟩
              · exact Or.inl (Nat.min_eq_right (by omega))
          · rw [if_neg hlease] at h
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨Nat.le_refl _, Or.inl rfl⟩
        unfold tickOpen
        dsimp only
        rw [if_neg (by omega), if_neg (by omega)]
        by_cases hC : (s.lhi ≠ 0 ∧ ¬ c.udp = true) ∧ (c.home = true ∨ c.rides = true) ∧
            satSub (max d now) l.hlt ≥ leaseKeep s.lhi
        · rw [if_pos hC]
          have := startCheck_ping l (max d now) c hst hc0
          simp [this]
        · rw [if_neg hC]
          have hkd : d = keepDue l s now c := by
            rcases hdk.2 with e | ⟨h1, h2, e⟩
            · exact e
            · exfalso
              apply hC
              refine ⟨⟨h1, by simp [h2]⟩, hhr', ?_⟩
              have := Nat.le_max_left d now
              simp only [satSub]; omega
          have hfix := keepDue_fix l s now c
          rw [← hkd] at hfix
          rw [if_pos (by exact ⟨hhr', hfix⟩)]
          rfl

end Pinc.ConnectLink
