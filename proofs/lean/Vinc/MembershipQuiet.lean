import Vinc.MembershipViewPrimary

/-!
# Membership view: the quiet-window schedule (property 4)

After a late timer or a heal the node opens a quiet window (`begin_quiet`): a removal found inside it is deferred, the
member queued in the `recheck` set. The first block of `tick` then drives the schedule:

* `beginQuiet_window`: the window lasts `QUIET` from the call and clears the second-look flag.
* `recomputeOne_defers`: a removal found inside the window changes nothing in the view and queues the member.
* `tickRecheck_first`: the first tick at or after the end of the window, with deferred members and no second look
  yet, re-opens the window for `RECHECK_GAP` (the members stay queued, the view is untouched).
* `tickRecheck_early`: while that second window lasts, further ticks do nothing in this block.
* `tickRecheck_second`: the first tick at or after the end of the second window runs `recheck_now` on the queue.
* `removeFromView_holds`: a removal found while the source is held (no confirmed home view) queues the member, the view
  untouched.
* `recheckNow_clears`: with the window over and the source not held, the queue ends empty (nothing is deferred again).
* `recheckNow_keeps_listed`: a member in the view that some eligible hub copy still lists is in the view after
  `recheck_now` (a member that is back is never reported); `recomputeOne_removes`: one that no copy lists, with the window
  over, is removed.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.MemInc

/-- The first block of `tick`: the schedule of the deferred removals. -/
def N.tickRecheck (e : Env) (n : N) (now : Nat) : N :=
  if !n.recheck.isEmpty && n.quietUntil ≤ now then
    (if n.regrace then N.recheckNow e { n with regrace := false } now
     else { n with regrace := true, quietUntil := satAdd now RECHECK_GAP })
  else n

/-- `tick` is this block followed by the rest (renew, slow tick, hub tick): proved equal to the model by `rfl`. -/
theorem tick_eq (e : Env) (n : N) (now : Nat) :
    N.tick e n now =
      (let n := N.tickRecheck e n now
       let n := if n.sent != some (n.ver, n.th) then N.renew e n now false false else n
       let n := if n.isHub || n.nextSlow ≤ now then
           N.slowTick e (if !n.isHub then { n with nextSlow := satAdd now SLOW_TICK } else n) now
         else n
       if n.isHub then N.hubTick e n now else n) := rfl

theorem beginQuiet_window (n : N) (now cause : Nat) :
    (n.beginQuiet now cause).quietUntil = satAdd now QUIET ∧ (n.beginQuiet now cause).regrace = false := by
  unfold N.beginQuiet N.trace; split <;> (try split) <;> simp

/-- A removal found inside the quiet window is deferred. -/
theorem recomputeOne_defers (e : Env) (n : N) (now m : Nat) (hin : n.members.has m = true)
    (hc : (n.candidates now (n.source now) m).1 = none) (hold : (n.source now).hold = false)
    (hq : now < n.quietUntil) (hr : n.recheck.len < MAX_TABLE) :
    (N.recomputeOne e n now m).1.members = n.members ∧ (N.recomputeOne e n now m).1.recheck = n.recheck.ins m ∧
    (N.recomputeOne e n now m).2 = false := by
  rw [recomputeOne_none e n now m hc]
  obtain ⟨c, hcur⟩ : ∃ c, n.members.get? m = some c := by
    rw [AMap.has_iff_get] at hin
    cases h : n.members.get? m with
    | none => rw [h] at hin; simp at hin
    | some c => exact ⟨c, rfl⟩
  rw [hcur]
  exact removeFromView_defers e n now m c _ _ hold hq hr

theorem tickRecheck_first (e : Env) (n : N) (now : Nat) (hne : n.recheck.isEmpty = false) (hq : n.quietUntil ≤ now)
    (hr : n.regrace = false) :
    N.tickRecheck e n now = { n with regrace := true, quietUntil := satAdd now RECHECK_GAP } := by
  unfold N.tickRecheck; simp [hne, hq, hr]

theorem tickRecheck_early (e : Env) (n : N) (now : Nat) (hq : now < n.quietUntil) : N.tickRecheck e n now = n := by
  unfold N.tickRecheck
  have : ¬ (n.quietUntil ≤ now) := by omega
  simp [this]

theorem tickRecheck_empty (e : Env) (n : N) (now : Nat) (hne : n.recheck.isEmpty = true) : N.tickRecheck e n now = n := by
  unfold N.tickRecheck; simp [hne]

theorem tickRecheck_second (e : Env) (n : N) (now : Nat) (hne : n.recheck.isEmpty = false) (hq : n.quietUntil ≤ now)
    (hr : n.regrace = true) : N.tickRecheck e n now = N.recheckNow e { n with regrace := false } now := by
  unfold N.tickRecheck; simp [hne, hq, hr]

/-- The schedule over two ticks: the first tick after the window opens a second one of `RECHECK_GAP`; a tick inside it
does nothing; the first tick after it rechecks the queue. -/
theorem quiet_schedule (e : Env) (n : N) (t1 t2 : Nat) (hne : n.recheck.isEmpty = false) (hq : n.quietUntil ≤ t1)
    (hr : n.regrace = false) :
    (t2 < satAdd t1 RECHECK_GAP → N.tickRecheck e (N.tickRecheck e n t1) t2 = N.tickRecheck e n t1) ∧
    (satAdd t1 RECHECK_GAP ≤ t2 → N.tickRecheck e (N.tickRecheck e n t1) t2 =
      N.recheckNow e { n with regrace := false, quietUntil := satAdd t1 RECHECK_GAP } t2) := by
  rw [tickRecheck_first e n t1 hne hq hr]
  constructor
  · intro h; exact tickRecheck_early e _ t2 h
  · intro h
    exact tickRecheck_second e _ t2 hne h rfl

/-! ## `recheck_now` -/

theorem removeFromView_recheck (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (x : Bool)
    (hq : ¬ now < n.quietUntil) (hh : src.hold = false) : (N.removeFromView e n now m cur src x).1.recheck = n.recheck := by
  unfold N.removeFromView
  split
  · rfl
  · split
    · rename_i h; rw [hh] at h; cases h
    · split
      · rename_i h; simp at h; omega
      · by_cases hh : n.isHub = true <;> by_cases hg : (n.goneVer.len < MAX_TABLE ∨ n.goneVer.has m = true) <;>
          by_cases hl : n.left.has m = true <;> by_cases hx : x = true <;> simp [hh, hg, hl, hx]

/-- A removal found while the source is held (no confirmed home view) changes nothing in the view and queues the member for
a second look, as a removal inside the quiet window does (commit 6355d7d): no hub copy lists the member to bring it back. -/
theorem removeFromView_holds (e : Env) (n : N) (now m : Nat) (c : ViewEntry) (src : Source) (x : Bool)
    (hh : src.hold = true) (hr : n.recheck.len < MAX_TABLE) :
    N.removeFromView e n now m (some c) src x = ({ n with recheck := n.recheck.ins m }, false) := by
  unfold N.removeFromView
  simp [hh, hr]

theorem rcKnown_recheck (e : Env) (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : (rcKnown e n m best c).1.recheck = n.recheck := by
  unfold rcKnown
  by_cases h1 : best.inc / 65536 ≤ c.rc.inc / 65536 <;> by_cases h2 : (best.inc / 65536 == c.rc.inc / 65536 && decide (c.rc.inc ≤ best.inc)) = true <;>
    by_cases h3 : (best.ver != c.rc.ver) = true <;> by_cases h4 : (best.th != c.rc.th) = true <;>
    by_cases h5 : (match (some (c.rc.ver, c.rc.th)).orElse (fun _ => (n.emit (.joined m)).goneVer.get? m) with | some (ver, th) => ver != best.ver | none => false) = true <;>
    simp [h1, h2, h3, h4, h5] <;> split <;> simp_all

theorem rcNew_recheck (e : Env) (n : N) (m : Nat) (best : Rec) : (rcNew e n m best).1.recheck = n.recheck := by
  unfold rcNew
  split
  · rfl
  · dsimp only
    repeat' split
    all_goals simp_all

theorem rcTail_recheck (n : N) (m : Nat) (absent changed : Bool) : (rcTail n m absent changed).1.recheck = n.recheck := by
  rfl

theorem recomputeOne_recheck (e : Env) (n : N) (now m : Nat) (hq : ¬ now < n.quietUntil)
    (hh : (n.source now).hold = false) :
    (N.recomputeOne e n now m).1.recheck = n.recheck := by
  rw [recomputeOne_eq_v]
  dsimp only
  split
  · exact removeFromView_recheck e n now m _ _ _ hq hh
  · rename_i b0 a0 hb
    have hm : (if (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0))) = true then
        N.homeDelta e n m b0 .alive else n).recheck = n.recheck := by
      by_cases hc : (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0))) = true
      · rw [if_pos hc]; exact homeDelta_recheck n e m b0 .alive
      · rw [if_neg hc]
    generalize (if (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0))) = true then
        N.homeDelta e n m b0 .alive else n) = n1 at hm ⊢
    split
    · rename_i c hc
      have k1 := rcKnown_recheck e n1 m b0 c
      generalize rcKnown e n1 m b0 c = R at k1 ⊢
      obtain ⟨r1, r2, r3⟩ := R
      simp only [] at k1 ⊢
      split
      · simp [k1, hm]
      · rw [rcTail_recheck]; simp [k1, hm]
    · rename_i hc
      have k1 := rcNew_recheck e n1 m b0
      generalize rcNew e n1 m b0 = R at k1 ⊢
      obtain ⟨r1, r2, r3⟩ := R
      simp only [] at k1 ⊢
      split
      · simp [k1, hm]
      · rw [rcTail_recheck]; simp [k1, hm]

theorem bump_recheck (n : N) : n.bump.recheck = n.recheck := by unfold N.bump; simp

theorem Keeps.hubUp {n n' : N} (h : Keeps n n') (now x : Nat) : n'.hubUp now x = n.hubUp now x := by
  obtain ⟨-, -, -, hme, -, -, -, hup, hhe, -⟩ := h
  unfold N.hubUp; rw [hme, hup, hhe]

theorem Keeps.source {n n' : N} (h : Keeps n n') (now : Nat) : n'.source now = n.source now := by
  have hu := h.hubUp
  obtain ⟨hv, -, -, hme, hhub, -, -, hup, hhe, hpr, hho, -⟩ := h
  unfold N.source
  rw [hpr, hhub, hho, hv]
  simp only [hu]

/-- With the window over and a confirmed home view (the source is not held), `recheck_now` leaves the queue empty: no removal
is deferred again. (While the source is held the removal is queued again: `removeFromView_holds`.) -/
theorem recheckNow_clears (e : Env) (n : N) (now : Nat) (hq : ¬ now < n.quietUntil) (hh : (n.source now).hold = false) :
    (N.recheckNow e n now).recheck = [] := by
  unfold N.recheckNow
  dsimp only
  have key : ∀ (ks : List Nat) (a : N × Bool), a.1.recheck = [] → ¬ now < a.1.quietUntil → (a.1.source now).hold = false →
      (ks.foldl (fun (a : N × Bool) m => let (n', c) := N.recomputeOne e a.1 now m; (n', a.2 || c)) a).1.recheck = [] := by
    intro ks
    induction ks with
    | nil => intro a h _ _; exact h
    | cons k r ih =>
      intro a h1 h2 h3
      simp only [List.foldl_cons]
      apply ih
      · simp only []; rw [recomputeOne_recheck e a.1 now k h2 h3]; exact h1
      · simp only []; rw [(recomputeOne_keeps2 e a.1 now k).1.2.2.2.2.2.2.2.2.2.2.2]; exact h2
      · simp only []; rw [((recomputeOne_keeps2 e a.1 now k).1).source now]; exact h3
  have := key n.recheck.keys ({ n with recheck := [] }, false) rfl hq hh
  generalize (n.recheck.keys.foldl (fun (a : N × Bool) m => let (n', c) := N.recomputeOne e a.1 now m; (n', a.2 || c)) ({ n with recheck := [] }, false)) = F at this ⊢
  obtain ⟨f1, f2⟩ := F
  by_cases h : f2 = true <;> simp [h, bump_recheck] at this ⊢ <;> exact this

theorem Keeps.candidates {n n' : N} (h : Keeps n n') (now m : Nat) :
    n'.candidates now (n'.source now) m = n.candidates now (n.source now) m := by
  rw [h.source now]
  exact candidates_congr n n' now _ m h.1 (h.hubUp now)

/-- A member in the view that some eligible hub copy still lists is in the view after `recheck_now`: a member that is
back is never reported down. -/
theorem recheckNow_keeps_listed (e : Env) (n : N) (now m : Nat) (hin : n.members.has m = true)
    (hc : (n.candidates now (n.source now) m).1 ≠ none) : (N.recheckNow e n now).members.has m = true := by
  unfold N.recheckNow
  dsimp only
  have key : ∀ (ks : List Nat) (a : N × Bool), Keeps ({ n with recheck := [] } : N) a.1 → a.1.members.has m = true →
      (Keeps ({ n with recheck := [] } : N) (ks.foldl (fun (a : N × Bool) m => let (n', c) := N.recomputeOne e a.1 now m; (n', a.2 || c)) a).1 ∧
       (ks.foldl (fun (a : N × Bool) m => let (n', c) := N.recomputeOne e a.1 now m; (n', a.2 || c)) a).1.members.has m = true) := by
    intro ks
    induction ks with
    | nil => intro a h1 h2; exact ⟨h1, h2⟩
    | cons k r ih =>
      intro a h1 h2
      simp only [List.foldl_cons]
      apply ih
      · exact Keeps.trans h1 (recomputeOne_keeps2 e a.1 now k).1
      · simp only []
        by_cases hk : k = m
        · subst hk
          have hcand : (a.1.candidates now (a.1.source now) k).1 ≠ none := by
            rw [h1.candidates now k]; exact hc
          rcases recomputeOne_listed_stays e a.1 now k hcand with h | ⟨h, -⟩
          · exact h
          · rw [h] at h2; cases h2
        · have := (recomputeOne_keeps2 e a.1 now k).2 m (Ne.symm hk)
          rw [AMap.has_iff_get] at h2 ⊢
          rw [this]; exact h2
  obtain ⟨-, hm⟩ := key n.recheck.keys ({ n with recheck := [] }, false) (Keeps.refl _) hin
  generalize (n.recheck.keys.foldl (fun (a : N × Bool) m => let (n', c) := N.recomputeOne e a.1 now m; (n', a.2 || c)) ({ n with recheck := [] }, false)) = F at hm ⊢
  obtain ⟨f1, f2⟩ := F
  by_cases h : f2 = true <;> simp [h, bump_members] at hm ⊢ <;> exact hm

/-- With no copy listing the member, no hold on removals and the window over, the member is removed. -/
theorem recomputeOne_removes (e : Env) (n : N) (now m : Nat) (hin : n.members.has m = true)
    (hc : (n.candidates now (n.source now) m).1 = none) (hold : (n.source now).hold = false)
    (hq : ¬ now < n.quietUntil) : (N.recomputeOne e n now m).1.members.has m = false := by
  rw [recomputeOne_none e n now m hc]
  obtain ⟨c, hcur⟩ : ∃ c, n.members.get? m = some c := by
    rw [AMap.has_iff_get] at hin
    cases h : n.members.get? m with
    | none => rw [h] at hin; simp at hin
    | some c => exact ⟨c, rfl⟩
  rw [hcur]
  unfold N.removeFromView
  simp only [hold, Bool.false_eq_true, if_false]
  have : ¬ (decide (now < n.quietUntil) && decide (n.recheck.len < MAX_TABLE)) = true := by simp [hq]
  rw [if_neg this]
  by_cases hh : n.isHub = true <;> by_cases hg : (n.goneVer.len < MAX_TABLE ∨ n.goneVer.has m = true) <;>
    by_cases hl : n.left.has m = true <;> by_cases hx : (n.candidates now (n.source now) m).2 = true <;>
    simp [hh, hg, hl, hx, AMap.has_erase_self]

end Vinc.Membership
