import Vinc.MembershipTickSusp

/-!
# Hub tick, part 2: the held table around a step

`RD m` says a step at key `m` changes the held table (`downed`) only at `m`. It holds for `hub_down`, `carrier_watch`,
the expiry and a step of the tick, and for a step of the second loop (`carrier_return` and the release of a held
member change the entry of that member only). With `RM` of `MembershipTick.lean` this lets the tick theorems follow one
member through the loops over all the others.
-/

set_option linter.unusedVariables false

namespace Vinc.Membership
open Vinc.MemInc

def RD (m : Nat) (n n' : N) : Prop := ∀ j, j ≠ m → n'.downed.get? j = n.downed.get? j

theorem RD.refl (m : Nat) (n : N) : RD m n n := fun _ _ => rfl
theorem RD.of_eq {m : Nat} {n n' : N} (h : n'.downed = n.downed) : RD m n n' := fun j _ => by rw [h]
theorem RD.trans {m : Nat} {a b c : N} (h1 : RD m a b) (h2 : RD m b c) : RD m a c := fun j hj => (h2 j hj).trans (h1 j hj)

theorem hubDown_rd (e : Env) (n : N) (now m : Nat) (cause : Cause) : RD m n (N.hubDown e n now m cause) := by
  cases hl : n.roster.get? m with
  | none => unfold N.hubDown; rw [hl]; exact RD.refl _ _
  | some lease =>
    have hpd := fun (b : Bc) (rc : Rec) (a : Alive) => (pushDelta_ht e ((n.hdPre m).bc b) now m rc a).2.2.1
    have hd0 : ∀ b : Bc, ((n.hdPre m).bc b).downed = n.downed := fun b => rfl
    have hhold : ∀ (x : N), x.downed = n.downed → RD m n (x.hdHold lease m now) := by
      intro x hx j hj
      unfold N.hdHold; split
      · simp only []; rw [AMap.get?_insert_ne _ _ _ _ hj, hx]
      · rw [hx]
    cases cause with
    | left =>
      rw [hubDown_left_eq e n now m lease hl]
      exact RD.of_eq ((hpd _ _ _).trans (hd0 _))
    | remote =>
      rw [hubDown_remote_eq e n now m lease hl]
      exact hhold _ ((hpd _ _ _).trans (hd0 _))
    | confirmed pf =>
      rw [hubDown_conf_eq e n now m lease pf hl]
      dsimp only
      obtain ⟨-, -, r, -⟩ := confirmDowns_ht e (((N.pushDelta e ((n.hdPre m).bc (.hold m)) now m lease.rc .down).hdHold lease m now).trace
        (.confirmed m)) m lease.rc.inc pf
      intro j hj
      rw [r]; simp only [trace_downed]
      exact hhold _ ((hpd _ _ _).trans (hd0 _)) j hj

theorem newSusp_rd (e : Env) (n : N) (now m since : Nat) (ev : Option Evid) (k : Nat) : RD k n (N.newSusp e n now m since ev) := by
  apply RD.of_eq
  unfold N.newSusp
  split
  · rfl
  · dsimp only
    repeat' split
    all_goals simp [N.scheduleConfirm, N.nsFirst, N.nsSecond]


theorem confirm_rd (e : Env) (n : N) (now m : Nat) (sp : Susp) (l : Lease) : RD m n (N.confirm e n now m sp l) := by
  unfold N.confirm; exact hubDown_rd e n now m _

theorem newSusp_rd' (e : Env) (n : N) (now m since : Nat) (ev : Option Evid) : (N.newSusp e n now m since ev).downed = n.downed := by
  unfold N.newSusp
  split
  · rfl
  · dsimp only
    repeat' split
    all_goals simp [N.scheduleConfirm, N.nsFirst, N.nsSecond]

theorem cwMain_rd (e : Env) (n : N) (now m since : Nat) (l : Lease) (ev : Option Evid) :
    RD m n (N.cwMain e n now m since l ev) := by
  unfold N.cwMain
  cases hs : n.susp.get? m with
  | none => exact RD.of_eq (newSusp_rd' ..)
  | some sp0 =>
    simp only []
    by_cases hsi : sp0.since = since
    · subst hsi
      simp only [beq_self_eq_true, if_true, rewatch_indep]
      cases hb : sp0.probeB with
      | none =>
        simp only [hb, Option.isNone_none, if_true, rewatch_indep]
        cases hr : n.independentRoute now m ev with
        | none => simp only [hr, hb, rewatch_indep]; exact RD.of_eq (rewatch_downed ..)
        | some rp =>
          obtain ⟨route, path⟩ := rp
          simp only []
          by_cases hdl : max (max (sp0.since + CONFIRM) (sp0.probeA + sp0.wait)) (now + sp0.wait) ≤ now
          · simp only [hr, hdl, ite_true, rewatch_indep]
            refine RD.trans (b := _) ?_ (confirm_rd _ _ _ _ _ _)
            exact RD.of_eq (by simp [rewatch_downed])
          · simp only [hr, hdl, ite_false, rewatch_indep]
            exact RD.of_eq (by simp [N.scheduleConfirm, rewatch_downed])
      | some tbp =>
        obtain ⟨tb, path⟩ := tbp
        simp only [hb, Option.isNone_some, Bool.false_eq_true, ite_false, rewatch_indep]
        by_cases hdl : max (max (sp0.since + CONFIRM) (sp0.probeA + sp0.wait)) (tb + sp0.wait) ≤ now
        · rw [if_pos hdl]; exact RD.trans (b := _) (RD.of_eq (rewatch_downed ..)) (confirm_rd _ _ _ _ _ _)
        · rw [if_neg hdl]; exact RD.of_eq (by simp [N.scheduleConfirm, rewatch_downed])
    · simp only [show (sp0.since == since) = false by simpa using hsi]
      exact RD.of_eq (newSusp_rd' ..)

theorem carrierWatch_rd (e : Env) (n : N) (now m : Nat) : RD m n (N.carrierWatch e n now m) := by
  cases hl : n.roster.get? m with
  | none => rw [cw_unknown e n now m hl]; exact RD.of_eq rfl
  | some l =>
    cases hcar : e.carrier m with
    | unknown => rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hcar] at h; cases h)]; exact RD.of_eq rfl
    | open_ => rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hcar] at h; cases h)]; exact RD.of_eq rfl
    | gone since sleep =>
      by_cases hx : Excused l since sleep (e.evidence m)
      · unfold N.carrierWatch
        rw [hl]; dsimp only; simp only [hcar]
        cases hev : e.evidence m with
        | none =>
          rcases hx with h | ⟨x, hx, _⟩ | ⟨s, hs, h⟩
          · simp [h]; exact RD.of_eq rfl
          · simp [hev] at hx
          · subst hs; simp [h]; exact RD.of_eq rfl
        | some x =>
          by_cases hh : since ≤ x.rx
          · simp [hh]; exact RD.of_eq rfl
          · rcases hx with h | ⟨x', hx', h'⟩ | ⟨s, hs, h⟩
            · simp [h]; split <;> exact RD.of_eq rfl
            · simp [hev] at hx'; subst hx'; exact absurd h' hh
            · subst hs; simp [h]; split <;> exact RD.of_eq rfl
      · rw [cw_eq_main e n now m since sleep l hl hcar hx]; exact cwMain_rd e n now m since l _

theorem htStep_rd (e : Env) (now m : Nat) (n : N) : RD m n (N.htStep e now m n) := by
  unfold N.htStep
  cases hl : n.roster.get? m with
  | none => exact RD.refl _ _
  | some l0 =>
    simp only []
    have hd : (N.htPulse e n now m l0).1.downed = n.downed := by
      unfold N.htPulse
      cases hev : e.evidence m with
      | none => rfl
      | some ev => simp only []; split <;> simp
    generalize hP : N.htPulse e n now m l0 = P at *
    obtain ⟨n1, l⟩ := P
    simp only [] at hd ⊢
    split
    · exact RD.of_eq ((htExpire_spec e n1 now m l).2.2.trans hd)
    · split
      · exact RD.trans (b := n1) (RD.of_eq hd) (carrierWatch_rd e n1 now m)
      · exact RD.of_eq hd

end Vinc.Membership
