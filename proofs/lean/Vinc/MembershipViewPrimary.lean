import Vinc.MembershipViewSnap

/-!
# Membership view: the primary hub with its hysteresis, and PULSE suppression (property 10)

* `reselect_switch_requires`: the primary of a member changes to a different hub only when there was none, the old one
  is not alive, or the new one beats it by `HYST_ABS` (20 ms) and a quarter: `rn + 20 ms < rc * 3 / 4` (all saturating
  as in the code). A hub is its own primary and never changes.
* `rnStep_suppress`: a periodic HELLO to a hub is skipped (and `helloSuppressed` traced) exactly when the periodic
  renewal is on, no snapshot is wanted, the hub is not the unconfirmed home, and the transport shows the session alive
  (`pto = 0` and a packet within `PULSE_FRESH`); otherwise the HELLO is sent (`rnStep_sends`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.MemInc

/-- The hub is demonstrably alive on transport evidence alone. -/
theorem pulseFresh_iff (e : Env) (now hub : Nat) :
    N.pulseFresh e now hub = true ↔ ∃ ev, e.evidence hub = some ev ∧ ev.pto = 0 ∧ now - ev.rx < PULSE_FRESH := by
  unfold N.pulseFresh
  cases h : e.evidence hub with
  | none => simp
  | some ev => simp

theorem rnStep_suppress (e : Env) (now : Nat) (fs per : Bool) (n : N) (hub : Nat)
    (hup : (hub == n.me || !n.up.has hub) = false)
    (hc : (per && !(fs || !n.hv.has hub) && (n.primary != some hub || n.homeOk == some hub) && N.pulseFresh e now hub) = true) :
    rnStep e now fs per n hub = n.trace (.helloSuppressed hub) := by
  unfold rnStep
  simp only [hup, Bool.false_eq_true, if_false, hc, if_true]

theorem rnStep_sends (e : Env) (now : Nat) (fs per : Bool) (n : N) (hub : Nat)
    (hup : (hub == n.me || !n.up.has hub) = false)
    (hc : (per && !(fs || !n.hv.has hub) && (n.primary != some hub || n.homeOk == some hub) && N.pulseFresh e now hub) = false) :
    ∃ n', rnStep e now fs per n hub = N.helloTo e n' hub (fs || !n.hv.has hub) ∧ n'.me = n.me := by
  unfold rnStep
  simp only [hup, Bool.false_eq_true, if_false, hc]
  refine ⟨_, rfl, ?_⟩
  simp [N.markHello]


/-- The primary of `reselect` in two steps: the choice and the switch. -/
def chosen (n : N) (now : Nat) : Option Nat :=
  if n.isHub then some n.me
  else
    let p := n.bestHub now
    match p, n.primary with
    | some np, some cur =>
      if np != cur && n.hubUp now cur then
        let rc := (n.hrtt.get? cur).getD RTT_UNKNOWN
        let rn := (n.hrtt.get? np).getD RTT_UNKNOWN
        if min (rc * 3) U64MAX / 4 ≤ min (rn + HYST_ABS) U64MAX then some cur else p
      else p
    | _, _ => p

/-- The switch of `reselect` to the new primary `p`. -/
def rsSwitch (e : Env) (n : N) (now p : Nat) : N :=
  let old := n.primary
  let n := ({ n with primary := some p }).trace (.primary p)
  let n := if !n.isHub then
      let n := { n with homeOk := none }
      let n := N.helloTo e n p true
      match old with
      | some o => if n.up.has o then N.helloTo e n o false else n
      | none => n
    else n
  n.bc (.primary old p)

theorem reselect_eq (e : Env) (n : N) (now : Nat) :
    N.reselect e n now =
      (match chosen n now with
       | none => n
       | some p => if n.primary == some p then n else rsSwitch e n now p) := rfl

theorem rsSwitch_primary (e : Env) (n : N) (now p : Nat) : (rsSwitch e n now p).primary = some p := by
  unfold rsSwitch
  dsimp only
  simp only [bc_primary_v, N.helloTo]
  repeat' split
  all_goals simp

/-- **The primary changes only past the hysteresis.** If a member's primary changes from `cur` to a different hub `p`,
then `cur` was not alive, or `p` is the best hub and `rn + 20 ms < rc * 3 / 4` (saturating, as in the code), where
`rc` and `rn` are the smoothed round trips (unknown ones count as 2^40). -/
theorem reselect_switch_requires (e : Env) (n : N) (now cur p : Nat) (hnh : n.isHub = false) (hc : n.primary = some cur)
    (hp : (N.reselect e n now).primary = some p) (hne : p ≠ cur) :
    n.hubUp now cur = false ∨
    (n.bestHub now = some p ∧
      min (((n.hrtt.get? p).getD RTT_UNKNOWN) + HYST_ABS) U64MAX <
        min (((n.hrtt.get? cur).getD RTT_UNKNOWN) * 3) U64MAX / 4) := by
  rw [reselect_eq] at hp
  cases hch : chosen n now with
  | none => rw [hch] at hp; simp only [] at hp; rw [hc] at hp; simp at hp; exact absurd hp.symm hne
  | some q =>
    rw [hch] at hp
    simp only [] at hp
    by_cases hq : (n.primary == some q) = true
    · simp only [hq, if_true] at hp
      rw [hc] at hp; simp at hp; exact absurd hp.symm hne
    · simp only [hq, Bool.false_eq_true, if_false] at hp
      rw [rsSwitch_primary] at hp
      have hqp : q = p := (Option.some.inj hp)
      subst hqp
      unfold chosen at hch
      simp only [hnh, Bool.false_eq_true, if_false] at hch
      rw [hc] at hch
      cases hb : n.bestHub now with
      | none => rw [hb] at hch; simp at hch
      | some np =>
        rw [hb] at hch
        simp only [] at hch
        by_cases h1 : (np != cur && n.hubUp now cur) = true
        · simp only [h1, if_true] at hch
          by_cases h2 : min (((n.hrtt.get? cur).getD RTT_UNKNOWN) * 3) U64MAX / 4 ≤ min (((n.hrtt.get? np).getD RTT_UNKNOWN) + HYST_ABS) U64MAX
          · simp only [h2, if_true] at hch; exact absurd (Option.some.inj hch).symm hne
          · simp only [h2, if_false] at hch
            right
            have : np = q := Option.some.inj hch
            subst this
            exact ⟨rfl, by omega⟩
        · simp only [h1, Bool.false_eq_true, if_false] at hch
          have : np = q := Option.some.inj hch
          subst this
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h1
          by_cases h3 : np = cur
          · exact absurd h3 hne
          · left
            cases hu : n.hubUp now cur
            · rfl
            · exact absurd ⟨h3, hu⟩ h1


/-! ## The quiet window and revocation -/

/-- A removal found inside a quiet window (after a late timer or a heal) is deferred: the view is unchanged, the member
is queued in the recheck table at the window's end with the window's grace state (a member already waiting keeps its
own entry, #284), and `Deferred` is traced; `recheckDue` recomputes it at that instant and again after `RECHECK_GAP`,
and a member that is listed again by then stays (`recomputeOne_listed_stays`). -/
theorem removeFromView_defers (e : Env) (n : N) (now m : Nat) (c : ViewEntry) (src : Source) (x : Bool)
    (hold : src.hold = false) (hq : now < n.quietUntil) (hr : n.recheck.len < MAX_TABLE) :
    (N.removeFromView e n now m (some c) src x).1.members = n.members ∧
    (N.removeFromView e n now m (some c) src x).1.recheck = n.recheck.orIns m (n.quietUntil, n.regrace) ∧
    (N.removeFromView e n now m (some c) src x).2 = false := by
  unfold N.removeFromView
  simp [hold, hq, hr]

/-- A delta about a revoked member is dropped: nothing changes. -/
theorem applyDeltaCore_revoked (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) (h : n.revoked.has m = true) :
    N.applyDeltaCore e n now hub m rc a = n := by
  rw [applyDeltaCore_eq_v]; simp [h]

end Vinc.Membership
