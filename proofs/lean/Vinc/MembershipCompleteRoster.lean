import Vinc.MembershipViewPrimary
import Vinc.MembershipHubRevoke

/-!
# Completeness and accuracy over timed hypotheses, part 1: what the timer leaves alone in the roster

The hub's lease table (`roster`) is changed in `on_timeout` only by `hub_tick` (the pulse refresh, the expiry and the
carrier watch of the first loop, the restore of the second), by `carrier_watch` from the confirmation deadline, and by
nothing else: every other part of the call (`pulse_refresh`, `refresh_local`, `renew`, `recheck_now`, `slow_tick`
with its `drop_peer`, `reselect`, `drop_stale_hubs`, `sweep_absent`, `sample_session_rtts`) leaves it as it is. This file
proves that, so that the timeline theorems can follow one lease through a whole call.

* `Held t0 m n`: the roster has no lease for `m`, or one renewed at `t0` or earlier.
* `Silent t0 e m`: the host shows no evidence of `m` after `t0` and `m`'s carrier is not open.
* `onTimeout_held`: a call of `on_timeout` keeps `Held` under `Silent`; `onTimeout_roster_other`: it never touches the
  lease of another member through a path other than that member's own rules (`Other`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership.Cmp
open Vinc.Membership
open Vinc.MemInc

/-- The roster has no lease for `m`, or one last renewed at `t0` or earlier. -/
def Held (t0 m : Nat) (n : N) : Prop :=
  n.roster.get? m = none ∨ ∃ l, n.roster.get? m = some l ∧ l.renewed ≤ t0

/-- The roster of `n'` is that of `n` at every key except `k`. -/
def Other (k : Nat) (n n' : N) : Prop := ∀ j, j ≠ k → n'.roster.get? j = n.roster.get? j

theorem Other.refl (k : Nat) (n : N) : Other k n n := fun _ _ => rfl
theorem Other.trans {k : Nat} {a b c : N} (h1 : Other k a b) (h2 : Other k b c) : Other k a c :=
  fun j hj => (h2 j hj).trans (h1 j hj)
theorem Other.of_eq {k : Nat} {n n' : N} (h : n'.roster = n.roster) : Other k n n' := fun j _ => by rw [h]

theorem Held.of_other {t0 m k : Nat} {n n' : N} (hk : m ≠ k) (ho : Other k n n') (h : Held t0 m n) : Held t0 m n' := by
  unfold Held at *; rw [ho m hk]; exact h

theorem Held.of_eq {t0 m : Nat} {n n' : N} (h : n'.roster = n.roster) (hh : Held t0 m n) : Held t0 m n' := by
  unfold Held at *; rw [h]; exact hh

theorem modify_get_self {α : Type} (m : AMap α) (k : Nat) (f : α → α) : (m.modify k f).get? k = (m.get? k).map f := by
  induction m with
  | nil => simp [AMap.modify, AMap.get?]
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    by_cases h1 : a = k
    · subst h1; simp [AMap.modify, AMap.get?, List.find?]
    · have hak : (a == k) = false := by simp; omega
      simp only [AMap.modify, AMap.get?, List.map_cons, List.find?_cons] at ih ⊢
      simp [hak, h1] at ih ⊢
      exact ih

theorem erase_of_get_none {α : Type} (m : AMap α) (k : Nat) (h : m.get? k = none) : m.erase k = m := by
  unfold AMap.erase
  apply List.filter_eq_self.mpr
  intro p hp
  unfold AMap.get? at h
  simp only [Option.map_eq_none_iff, List.find?_eq_none] at h
  have := h p hp
  simpa using this

/-! ## Generic pieces -/

@[simp] theorem close_roster (n : N) (p : Nat) (r : CloseR) : (n.close p r).roster = n.roster := rfl
@[simp] theorem beginQuiet_roster (n : N) (now c : Nat) : (n.beginQuiet now c).roster = n.roster := by
  unfold N.beginQuiet; simp
@[simp] theorem rttSample_roster (n : N) (h r : Nat) : (n.rttSample h r).roster = n.roster := by
  unfold N.rttSample; rfl
@[simp] theorem helloTo_roster (e : Env) (n : N) (p : Nat) (s : Bool) : (N.helloTo e n p s).roster = n.roster := by
  unfold N.helloTo; simp

theorem forKeys_roster (ks : List Nat) (f : Nat → N → N) (h : ∀ k n, (f k n).roster = n.roster) (n : N) :
    (forKeys ks f n).roster = n.roster := by
  unfold forKeys
  exact foldl_inv (fun x : N => x.roster = n.roster) _ _ _ (fun b a hb => by rw [h]; exact hb) rfl

theorem recomputeOne_roster (e : Env) (n : N) (now m : Nat) : (N.recomputeOne e n now m).1.roster = n.roster :=
  (recomputeOne_ht e n now m).1

@[simp] theorem pushDelta_roster (e : Env) (n : N) (now m : Nat) (rc : Rec) (a : Alive) :
    (N.pushDelta e n now m rc a).roster = n.roster := (pushDelta_ht e n now m rc a).1

theorem rsSwitch_roster (e : Env) (n : N) (now p : Nat) : (rsSwitch e n now p).roster = n.roster := by
  unfold rsSwitch
  dsimp only
  split <;> (try split) <;> (try split) <;> simp [N.helloTo]

theorem reselect_roster (e : Env) (n : N) (now : Nat) : (N.reselect e n now).roster = n.roster := by
  rw [reselect_eq]
  split
  · rfl
  · split
    · rfl
    · exact rsSwitch_roster ..

theorem dropPeer_roster (e : Env) (n : N) (now peer : Nat) : (N.dropPeer e n now peer).roster = n.roster := by
  unfold N.dropPeer
  repeat' split
  all_goals simp_all [reselect_roster]

theorem pulseRefresh_roster (e : Env) (n : N) (now : Nat) : (N.pulseRefresh e n now).roster = n.roster := by
  unfold N.pulseRefresh
  exact foldl_inv (fun x : N => x.roster = n.roster) _ _ _ (fun b a hb => by
    repeat' split
    all_goals simp_all) rfl

theorem refreshLocal_roster (e : Env) (n : N) (now : Nat) : (N.refreshLocal e n now).roster = n.roster := rfl

theorem bumpRecord_roster (n : N) : n.bumpRecord.roster = n.roster := by
  unfold N.bumpRecord; split <;> simp

theorem rnPre_roster (n : N) (p : Bool) : (rnPre n p).1.roster = n.roster := by
  unfold rnPre
  dsimp only
  simp [ite_roster, bumpRecord_roster]

theorem rnPush_roster (e : Env) (n : N) (now : Nat) : (rnPush e n now).roster = n.roster := by
  unfold rnPush
  simp [ite_roster]

theorem rnStep_roster (e : Env) (now : Nat) (fs p : Bool) (n : N) (hub : Nat) : (rnStep e now fs p n hub).roster = n.roster := by
  unfold rnStep
  split
  · rfl
  · dsimp only
    split
    · simp
    · unfold N.helloTo; split <;> simp [N.markHello]

theorem renew_roster (e : Env) (n : N) (now : Nat) (fs p : Bool) : (N.renew e n now fs p).roster = n.roster := by
  rw [renew_eq']
  have e1 := rnPre_roster n p
  have e3 : (List.foldl (rnStep e now fs (rnPre n p).2) (rnPush e (rnPre n p).1 now) (rnPush e (rnPre n p).1 now).boot).roster
      = (rnPush e (rnPre n p).1 now).roster :=
    foldl_inv (fun (x : N) => x.roster = (rnPush e (rnPre n p).1 now).roster) _ _ _ (fun b a hb => by rw [rnStep_roster]; exact hb) rfl
  exact e3.trans ((rnPush_roster e _ now).trans e1)

theorem recheckNow_roster (e : Env) (n : N) (now : Nat) : (N.recheckNow e n now).roster = n.roster := by
  unfold N.recheckNow
  dsimp only
  split
  · simp
    exact foldl_inv (fun x : N × Bool => x.1.roster = n.roster) _ _ _ (fun b a hb => by
      simp only [recomputeOne_roster]; exact hb) rfl
  · exact foldl_inv (fun x : N × Bool => x.1.roster = n.roster) _ _ _ (fun b a hb => by
      simp only [recomputeOne_roster]; exact hb) rfl

end Vinc.Membership.Cmp
