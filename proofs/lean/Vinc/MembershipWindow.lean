import Vinc.MembershipQuiet
import Vinc.MembershipCompleteTimeout
import Vinc.MembershipInvTab
import Vinc.MembershipCompleteDelta

/-!
# Completeness, view side: a removal that a quiet window deferred is applied on its own schedule

A removal a quiet window defers waits under its own entry: the instant it is due (the end of the window then open) and
whether its extra look has begun (#284). `recheck_due` gives it the look at the first tick at or after that instant and
recomputes it at the first tick after the look, with no window open (`recheckDue_removes`): a member that no eligible
copy lists, with no hold, is out of the view, whatever window a heal has opened since. `deferred_removal` is the two
ticks together; `down_then_gone` joins them to the DOWN delta itself: after a DOWN delta from the only hub that lists the
member, the member is out of the view at once or waits under its own entry, and `down_then_gone_ticks` is out of the
view at the second tick after the window's end. `awareness_budget` adds up the times of the whole chain.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.MemInc
open Vinc.Membership.Cmp

/-- With no copy listing the member, no hold and the window over, recomputing the member leaves it out of the view
(whether or not it was in). -/
theorem recomputeOne_gone (e : Env) (n : N) (now m : Nat)
    (hc : (n.candidates now (n.source now) m).1 = none) (hold : (n.source now).hold = false)
    (hq : ¬ now < n.quietUntil) : (N.recomputeOne e n now m).1.members.has m = false := by
  cases hg : n.members.get? m with
  | some c =>
    exact recomputeOne_removes e n now m (by rw [AMap.has_iff_get, hg]; rfl) hc hold hq
  | none =>
    rw [recomputeOne_none e n now m hc, hg]
    unfold N.removeFromView
    rw [AMap.has_iff_get, hg]
    rfl

/-- The recompute loop of `recheck_due` removes a member it reaches when no eligible copy lists it, nothing holds
removals and no quiet window is open. -/
theorem recheckFold_removes (e : Env) (n : N) (now m : Nat) (ks : List Nat) (hm : m ∈ ks)
    (hc : (n.candidates now (n.source now) m).1 = none) (hold : (n.source now).hold = false)
    (hq : ¬ now < n.quietUntil) : (N.recheckFold e n now ks).1.members.has m = false := by
  unfold N.recheckFold
  have key : ∀ (ks : List Nat) (a : N × Bool), Keeps n a.1 → (m ∈ ks ∨ a.1.members.has m = false) →
      (ks.foldl (fun (a : N × Bool) m => let (n', c) := N.recomputeOne e a.1 now m; (n', a.2 || c)) a).1.members.has m = false := by
    intro ks
    induction ks with
    | nil =>
      intro a h1 h2
      rcases h2 with h | h
      · exact absurd h (List.not_mem_nil)
      · exact h
    | cons k r ih =>
      intro a h1 h2
      simp only [List.foldl_cons]
      refine ih _ (Keeps.trans h1 (recomputeOne_keeps2 e a.1 now k).1) ?_
      by_cases hk : k = m
      · subst hk
        right
        have hc' : (a.1.candidates now (a.1.source now) k).1 = none := by rw [h1.candidates now k]; exact hc
        have hh' : (a.1.source now).hold = false := by rw [h1.source now]; exact hold
        have hq' : ¬ now < a.1.quietUntil := by rw [h1.2.2.2.2.2.2.2.2.2.2.2]; exact hq
        exact recomputeOne_gone e a.1 now k hc' hh' hq'
      · rcases h2 with h | h
        · rcases List.mem_cons.mp h with h | h
          · exact absurd h.symm hk
          · exact Or.inl h
        · right
          have := (recomputeOne_keeps2 e a.1 now k).2 m (Ne.symm hk)
          rw [AMap.has_iff_get] at h ⊢
          rw [this]; exact h
  exact key ks (n, false) (Keeps.refl n) (Or.inl hm)

/-- The recompute of `recheck_due` takes the window for the loop: a member it runs that no eligible copy lists, with
no hold, is out of the view whatever window is open. -/
theorem recheckRun_removes (e : Env) (n : N) (now m : Nat) (ks : List Nat) (hm : m ∈ ks)
    (hc : (n.candidates now (n.source now) m).1 = none) (hold : (n.source now).hold = false) :
    (N.recheckRun e n now ks).members.has m = false := by
  have h0 : SrcEq n ({ n with quietUntil := 0 } : N) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have h := recheckFold_removes e ({ n with quietUntil := 0 } : N) now m ks hm (by rw [h0.candidates now m]; exact hc)
    (by rw [h0.source now]; exact hold) (Nat.not_lt_zero now)
  unfold N.recheckRun
  dsimp only
  split
  · rw [bump_members]; exact h
  · exact h

/-- **A removal whose extra look ran is applied at its own instant, whatever window is open** (#284). A member waiting
under `(d, true)` with `d ≤ now`, that no eligible copy lists, with no hold on removals, is out of the view after
`recheck_due` at `now`: nothing is asked of the quiet window, since the recompute runs with none open. -/
theorem recheckDue_removes (e : Env) (n : N) (now m d : Nat) (hw : n.recheck.get? m = some (d, true)) (hd : d ≤ now)
    (hc : (n.candidates now (n.source now) m).1 = none) (hold : (n.source now).hold = false) :
    (N.recheckDue e n now).members.has m = false := by
  have hr : recheckReady now (m, (d, true)) = true := by simp [recheckReady, hd]
  have hm : m ∈ AMap.keys (n.recheck.filter (recheckReady now)) :=
    AMap.key_mem_of_get? _ _ _ (AMap.get?_filter_of _ _ _ _ hw hr)
  have hne : (AMap.keys (n.recheck.filter (recheckReady now))).isEmpty = false := by
    cases hk : AMap.keys (n.recheck.filter (recheckReady now)) with
    | nil => rw [hk] at hm; cases hm
    | cons a l => rfl
  have hs := recheckArm_srcEq n now
  rw [recheckDue_eq, hne, if_neg Bool.false_ne_true]
  exact recheckRun_removes e ({ N.recheckArm n now with regrace := false } : N) now m _ hm (by rw [hs.candidates now m]; exact hc)
    (by rw [hs.source now]; exact hold)

/-- **A deferred removal is applied at the second tick after its own instant.** A member waiting under `(d, false)`
(its extra look not begun) gets the look at the first tick `t1 ≥ d` and is out of the view at the next tick
`t2 ≥ t1 + RECHECK_GAP`, when no eligible copy lists it then and nothing holds removals. Neither tick asks anything of
the quiet window, so a heal between the deferral and the removal changes nothing (#284); only a late timer moves the
instant (`beginQuiet_late`). -/
theorem deferred_removal (e : Env) (n : N) (t1 t2 m d : Nat) (hw : n.recheck.get? m = some (d, false)) (hd : d ≤ t1)
    (hdue : satAdd t1 RECHECK_GAP ≤ t2)
    (hc : (n.candidates t2 (n.source t2) m).1 = none) (hold : (n.source t2).hold = false) :
    (N.recheckDue e (N.recheckDue e n t1) t2).members.has m = false := by
  obtain ⟨h1, -⟩ := recheckDue_arms e n t1 m d hw hd
  have hs := recheckDue_srcEq e n t1
  exact recheckDue_removes e _ t2 m _ h1 hdue (by rw [hs.candidates t2 m]; exact hc) (by rw [hs.source t2]; exact hold)

/-- **A DOWN delta takes the member out of the view.** The hub whose copy is the only one listing the member sends
DOWN: the node applying it removes the member at once, or, when a quiet window defers the removal, the member waits
under its own entry: the one it already had, or the end of the window then open with the window's grace state. From
there `deferred_removal` and `recheckDue_removes` take it out of the view at its own instant. -/
theorem down_then_gone (e : Env) (n : N) (now H m : Nat) (rc : Rec) (c : HubCopy) (hrev : n.revoked.has m = false)
    (hs : Srt n.hv) (hH : n.hv.get? H = some c)
    (hent : ∀ x, c.entries.get? m = some x → x.rc.inc / 65536 ≤ rc.inc / 65536)
    (hothers : ∀ p ∈ n.hv, p.1 ≠ H → n.eligible now (n.source now) p.1 = true → p.2.entries.get? m = none)
    (hhold : (n.source now).hold = false) (c0 : ViewEntry) (hcur : n.members.get? m = some c0) :
    (N.applyDeltaCore e n now H m rc .down).members.get? m = none ∨
    (N.applyDeltaCore e n now H m rc .down).recheck.get? m = some ((n.recheck.get? m).getD (n.quietUntil, n.regrace)) := by
  by_cases hq : now < n.quietUntil ∧ n.recheck.len < MAX_TABLE
  · right
    obtain ⟨-, hrc⟩ := applyDeltaCore_down_defers e n now H m rc c hrev hs hH hent hothers hhold hq c0 hcur
    rw [hrc]
    exact AMap.get?_orIns_self _ _ _
  · left
    exact applyDeltaCore_down_removes e n now H m rc c hrev hs hH hent hothers hhold hq

/-- `down_then_gone` and `deferred_removal` together: a DOWN delta that a window defers, for a member not waiting
already, found while the window's extra look has not begun, takes the member out of the view at the second tick after
the window's end. -/
theorem down_then_gone_ticks (e : Env) (n : N) (now H m : Nat) (rc : Rec) (c : HubCopy) (hrev : n.revoked.has m = false)
    (hs : Srt n.hv) (hH : n.hv.get? H = some c)
    (hent : ∀ x, c.entries.get? m = some x → x.rc.inc / 65536 ≤ rc.inc / 65536)
    (hothers : ∀ p ∈ n.hv, p.1 ≠ H → n.eligible now (n.source now) p.1 = true → p.2.entries.get? m = none)
    (hhold : (n.source now).hold = false) (c0 : ViewEntry) (hcur : n.members.get? m = some c0)
    (hnew : n.recheck.get? m = none) (hr0 : n.regrace = false) (t1 t2 : Nat) (hq1 : n.quietUntil ≤ t1)
    (hdue : satAdd t1 RECHECK_GAP ≤ t2)
    (hc : ((N.applyDeltaCore e n now H m rc .down).candidates t2 ((N.applyDeltaCore e n now H m rc .down).source t2) m).1 = none)
    (hold : ((N.applyDeltaCore e n now H m rc .down).source t2).hold = false) :
    (N.applyDeltaCore e n now H m rc .down).members.get? m = none ∨
    (N.recheckDue e (N.recheckDue e (N.applyDeltaCore e n now H m rc .down) t1) t2).members.has m = false := by
  rcases down_then_gone e n now H m rc c hrev hs hH hent hothers hhold c0 hcur with h | h
  · exact Or.inl h
  · right
    rw [hnew, hr0] at h
    exact deferred_removal e _ t1 t2 m _ h hq1 hdue hc hold

/-- The time budget of the awareness bound: the hub drops the lease at its first tick after `t0 + LEASE` (within
`HUB_TICK`), the DOWN reaches the node within `D`, the removal waits for its own instant `q`, the end of the quiet
window open when the DOWN arrived, at most `QUIET` after it (`beginQuiet_window`; a window's extra look lasts
`RECHECK_GAP`, less), and the node's ticks come every `NODE_TICK`: the member is out of the view by `t0 + 145 s` when
`D` is at most 48 s. Over any run of the host's calls, `hub_lease_gone` (`MembershipTimerLease.lean`) gives `h1` and
`h1'` with `HUB_TICK + σ` for the host's slack `σ` (`σ = 0` here). No heal moves `q` (`beginQuiet_heal`,
`heal_keeps_waiting`, #284) and the removal at `t2` holds whatever window a heal opened (`recheckDue_removes`); a late
tick at the node does move it (`late_tick_reopens`, the reference model's rule), so `hq` asks that the node's host is not
later than `WAKE_GAP` at a tick between the DOWN and the removal. -/
theorem awareness_budget (t0 tau1 taud q t1 t2 D : Nat) (h1 : t0 + LEASE < tau1) (h1' : tau1 ≤ t0 + LEASE + HUB_TICK)
    (hd : taud ≤ tau1 + D) (hD : D ≤ 48 * S) (hq : q ≤ taud + QUIET) (ht1 : t1 ≤ max taud q + NODE_TICK)
    (ht2 : t2 ≤ t1 + RECHECK_GAP + NODE_TICK) : t2 ≤ t0 + 145 * S := by
  simp only [LEASE, HUB_TICK, QUIET, NODE_TICK, RECHECK_GAP, S, MS] at *
  omega

/-! ## Convergence: the view is a function of the hub copies -/

/-- **The view is the union of the fresh copies.** With no hold on removals and no quiet window, recomputing a member
lists it exactly when some eligible hub copy lists it with a live omission state (a full view table refuses a new
member and evicts nobody), and the entry it lists is the highest incarnation among the live listings
(`candidates_max`, `candidates_listed`). -/
theorem recomputeOne_union (e : Env) (n : N) (now m : Nat) (hold : (n.source now).hold = false)
    (hq : ¬ now < n.quietUntil) :
    ((∃ p ∈ n.hv, ∃ ce, Live n now (n.source now) m p ce) →
      (N.recomputeOne e n now m).1.members.has m = true ∨ (n.members.has m = false ∧ MAX_TABLE ≤ n.members.len)) ∧
    ((∀ p ∈ n.hv, ∀ ce, ¬ Live n now (n.source now) m p ce) →
      (N.recomputeOne e n now m).1.members.has m = false) := by
  constructor
  · rintro ⟨p, hp, ce, hl⟩
    refine recomputeOne_listed_stays e n now m ?_
    intro h0
    exact ((candidates_none_iff n now (n.source now) m).1 h0) p hp ce hl
  · intro h
    exact recomputeOne_gone e n now m ((candidates_none_iff n now (n.source now) m).2 h) hold hq

/-- **Two nodes with the same hub copies agree on a member.** After a heal two nodes that hold the same copies of
the fresh hubs (and consider the same hubs fresh) list a member alike: one with room in its view table lists it
exactly when the other does. -/
theorem views_merge_key (e1 e2 : Env) (n1 n2 : N) (now m : Nat) (hv : n2.hv = n1.hv)
    (hup : ∀ h, n2.hubUp now h = n1.hubUp now h) (hsrc : n2.source now = n1.source now)
    (hold : (n1.source now).hold = false) (hq1 : ¬ now < n1.quietUntil) (hq2 : ¬ now < n2.quietUntil)
    (hf1 : ¬ (n1.members.has m = false ∧ MAX_TABLE ≤ n1.members.len))
    (hf2 : ¬ (n2.members.has m = false ∧ MAX_TABLE ≤ n2.members.len)) :
    (N.recomputeOne e1 n1 now m).1.members.has m = (N.recomputeOne e2 n2 now m).1.members.has m := by
  have hc : n2.candidates now (n2.source now) m = n1.candidates now (n1.source now) m := by
    rw [hsrc]; exact candidates_congr n1 n2 now _ m hv hup
  have hold2 : (n2.source now).hold = false := by rw [hsrc]; exact hold
  cases hcand : (n1.candidates now (n1.source now) m).1 with
  | none =>
    rw [recomputeOne_gone e1 n1 now m hcand hold hq1,
      recomputeOne_gone e2 n2 now m (by rw [hc]; exact hcand) hold2 hq2]
  | some b =>
    have h1 := recomputeOne_listed_stays e1 n1 now m (by rw [hcand]; simp)
    have h2 := recomputeOne_listed_stays e2 n2 now m (by rw [hc, hcand]; simp)
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · rw [h1, h2]
      · exact absurd h2 hf2
    · exact absurd h1 hf1

end Vinc.Membership
