import Vinc.MembershipQuiet
import Vinc.MembershipCompleteTimeout
import Vinc.MembershipInvTab
import Vinc.MembershipCompleteDelta

/-!
# Completeness, view side: a removal that a quiet window deferred is applied at the second tick

`recheck_now` removes a deferred member when no eligible hub copy lists it, no hold stands and the quiet window is
over (`recheckNow_removes`). With the two-step schedule of the tick (the first tick after the window arms a grace of
`RECHECK_GAP`, the next tick after the grace runs `recheck_now`), a DOWN delta that the window deferred is applied at
the second tick (`deferred_removal`). `down_then_gone` joins this to the delta itself: after a DOWN delta from the
only hub that lists the member, the member is out of the view at once or out after those two ticks.
`awareness_budget` adds up the times of the whole chain.
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

theorem keys_mem_of_has (s : ASet) (m : Nat) (h : s.has m = true) : m ∈ s.keys := by
  rw [ASet.has, AMap.has_iff_get] at h
  cases hg : AMap.get? s m with
  | none => rw [hg] at h; simp at h
  | some u =>
    have := AMap.mem_of_get? s m u hg
    exact List.mem_map_of_mem (f := Prod.fst) this

/-- `recheck_now` removes a deferred member that no eligible copy lists, when the window is over and nothing holds
removals. -/
theorem recheckNow_removes (e : Env) (n : N) (now m : Nat) (hm : n.recheck.has m = true)
    (hc : (n.candidates now (n.source now) m).1 = none) (hold : (n.source now).hold = false)
    (hq : ¬ now < n.quietUntil) : (N.recheckNow e n now).members.has m = false := by
  have hkb : Keeps n ({ n with recheck := [] } : N) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold N.recheckNow
  dsimp only
  have key : ∀ (ks : List Nat) (a : N × Bool), Keeps ({ n with recheck := [] } : N) a.1 →
      (m ∈ ks ∨ a.1.members.has m = false) →
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
        have hk2 := Keeps.trans hkb h1
        have hc' : (a.1.candidates now (a.1.source now) k).1 = none := by rw [hk2.candidates now k]; exact hc
        have hh' : (a.1.source now).hold = false := by rw [hk2.source now]; exact hold
        have hq' : ¬ now < a.1.quietUntil := by rw [hk2.2.2.2.2.2.2.2.2.2.2.2]; exact hq
        exact recomputeOne_gone e a.1 now k hc' hh' hq'
      · rcases h2 with h | h
        · rcases List.mem_cons.mp h with h | h
          · exact absurd h.symm hk
          · exact Or.inl h
        · right
          have := (recomputeOne_keeps2 e a.1 now k).2 m (Ne.symm hk)
          rw [AMap.has_iff_get] at h ⊢
          rw [this]; exact h
  have := key n.recheck.keys ({ n with recheck := [] }, false) (Keeps.refl _) (Or.inl (keys_mem_of_has _ _ hm))
  generalize (n.recheck.keys.foldl (fun (a : N × Bool) m => let (n', c) := N.recomputeOne e a.1 now m; (n', a.2 || c)) ({ n with recheck := [] }, false)) = F at this ⊢
  obtain ⟨f1, f2⟩ := F
  by_cases h : f2 = true <;> simp [h, bump_members] at this ⊢ <;> exact this

/-- **A deferred removal is applied at the second tick.** A node with deferred removals, whose quiet window is over at
`t1` and that has not yet armed its grace, applies them at the next tick at or after `t1 + RECHECK_GAP`: a member
that no eligible copy lists then, with no hold, is out of the view. -/
theorem deferred_removal (e : Env) (n : N) (t1 t2 m : Nat) (hne : n.recheck.isEmpty = false) (hq : n.quietUntil ≤ t1)
    (hr : n.regrace = false) (hdue : satAdd t1 RECHECK_GAP ≤ t2) (hm : n.recheck.has m = true)
    (hc : (n.candidates t2 (n.source t2) m).1 = none) (hold : (n.source t2).hold = false) :
    (N.tickRecheck e (N.tickRecheck e n t1) t2).members.has m = false := by
  rw [(quiet_schedule e n t1 t2 hne hq hr).2 hdue]
  have hsrc : ({ n with regrace := false, quietUntil := satAdd t1 RECHECK_GAP } : N).source t2 = n.source t2 := by
    dsimp only [N.source, N.hubUp]
  have hcc : ({ n with regrace := false, quietUntil := satAdd t1 RECHECK_GAP } : N).candidates t2
      (({ n with regrace := false, quietUntil := satAdd t1 RECHECK_GAP } : N).source t2) m =
      n.candidates t2 (n.source t2) m := by
    rw [hsrc]; exact candidates_congr n _ t2 _ m rfl (fun h => by dsimp only [N.hubUp])
  refine recheckNow_removes e _ t2 m hm ?_ ?_ ?_
  · rw [hcc]; exact hc
  · rw [hsrc]; exact hold
  · exact Nat.not_lt.mpr hdue

theorem recheck_ne_empty (n : N) (m : Nat) (h : n.recheck.has m = true) : n.recheck.isEmpty = false := by
  cases hl : n.recheck with
  | nil => rw [ASet.has, AMap.has_iff_get, hl] at h; simp [AMap.get?] at h
  | cons x r => simp

/-- **A DOWN delta takes the member out of the view.** The hub whose copy is the only one listing the member sends
DOWN: the node applying it removes the member at once, or, when a quiet window defers the removal, the member is in the
recheck set and is out of the view at the second tick (`deferred_removal`), provided that at that tick no eligible copy
lists it and nothing holds removals. -/
theorem down_then_gone (e : Env) (n : N) (now H m : Nat) (rc : Rec) (c : HubCopy) (hrev : n.revoked.has m = false)
    (hs : Srt n.hv) (hH : n.hv.get? H = some c)
    (hent : ∀ x, c.entries.get? m = some x → x.rc.inc / 65536 ≤ rc.inc / 65536)
    (hothers : ∀ p ∈ n.hv, p.1 ≠ H → n.eligible now (n.source now) p.1 = true → p.2.entries.get? m = none)
    (hhold : (n.source now).hold = false) (c0 : ViewEntry) (hcur : n.members.get? m = some c0) (t1 t2 : Nat)
    (hq1 : (N.applyDeltaCore e n now H m rc .down).quietUntil ≤ t1)
    (hr1 : (N.applyDeltaCore e n now H m rc .down).regrace = false) (hdue : satAdd t1 RECHECK_GAP ≤ t2)
    (hc : ((N.applyDeltaCore e n now H m rc .down).candidates t2 ((N.applyDeltaCore e n now H m rc .down).source t2) m).1 = none)
    (hold : ((N.applyDeltaCore e n now H m rc .down).source t2).hold = false) :
    (N.applyDeltaCore e n now H m rc .down).members.get? m = none ∨
    (N.tickRecheck e (N.tickRecheck e (N.applyDeltaCore e n now H m rc .down) t1) t2).members.has m = false := by
  by_cases hq : now < n.quietUntil ∧ n.recheck.len < MAX_TABLE
  · right
    obtain ⟨-, hrc⟩ := applyDeltaCore_down_defers e n now H m rc c hrev hs hH hent hothers hhold hq c0 hcur
    have hm : (N.applyDeltaCore e n now H m rc .down).recheck.has m = true := by
      rw [hrc]; exact AMap.has_insert_self _ _ _
    exact deferred_removal e _ t1 t2 m (recheck_ne_empty _ m hm) hq1 hr1 hdue hm hc hold
  · left
    exact applyDeltaCore_down_removes e n now H m rc c hrev hs hH hent hothers hhold hq

/-- The time budget of the awareness bound: the hub drops the lease at its first tick after `t0 + LEASE` (within
`HUB_TICK`), the DOWN reaches the node within `D`, the quiet window lasts at most `QUIET`, and the node's ticks come
every `NODE_TICK`: the member is out of the view by `t0 + 145 s` when `D` is at most 48 s. -/
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
