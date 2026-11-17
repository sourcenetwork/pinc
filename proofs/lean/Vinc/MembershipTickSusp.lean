import Vinc.MembershipTick
import Vinc.MembershipHubRevoke

/-!
# Suspicion records: `SuspOk` through every writer of `susp` (property 3, hub side)

`SuspOk` says that a suspicion record whose second probe is recorded sent it on a path other than the session (1 direct,
2 relay through another hub). `carrierWatch_keeps_unless` (`MembershipHubWatch.lean`) assumes it. The writers of `susp`
are `N.newSusp` (the model's cut of `carrier_watch`) and `carrier_watch` (insert a record whose second probe comes from `independent_route`), and
`hub_down`, `hub_tick` (expiry), `revoke`, `carrier_watch` itself (erase). This file proves each preserves `SuspOk`:

* `newSusp_cw2`, `cwMain_cw2`, `carrierWatch_cw2`, `htStep_cw2` (each states `CW2`: `SuspOk` is kept and the broadcast
  output only grows), `hubDown_susp`, `hubTick_susp` (`MembershipTickLoop`).
* `OBg`: the broadcast-layer output of `carrier_watch`, `hub_down` and the tick only grows (used to find the `release`
  of an expired lease in the output; it is the second half of `CW2`).
-/

set_option linter.unusedVariables false

namespace Vinc.Membership
open Vinc.MemInc

/-- A step's broadcast output only grows. -/
def OBg (n n' : N) : Prop := ∃ ex, n'.outBc = n.outBc ++ ex

theorem OBg.refl (n : N) : OBg n n := ⟨[], by simp⟩
theorem OBg.trans {a b c : N} (h1 : OBg a b) (h2 : OBg b c) : OBg a c := by
  obtain ⟨x, hx⟩ := h1; obtain ⟨y, hy⟩ := h2; exact ⟨x ++ y, by rw [hy, hx, List.append_assoc]⟩
theorem OBg.of_ht {a b : N} (h : b.HT a) : OBg a b := ⟨[], by rw [h.2.2.2.2.2.2.2.2.2.2.2.1]; simp⟩

theorem SuspOk.of_eq {n n' : N} (h : n'.susp = n.susp) (hn : n.SuspOk) : n'.SuspOk := by
  unfold N.SuspOk at *; rw [h]; exact hn

theorem SuspOk.erase {n n' : N} (m : Nat) (h : n'.susp = n.susp.erase m) (hn : n.SuspOk) : n'.SuspOk := by
  unfold N.SuspOk at *
  intro k sp tb path hk hb
  rw [h] at hk
  by_cases hkm : k = m
  · subst hkm; rw [AMap.get?_erase_self] at hk; cases hk
  · rw [AMap.get?_erase_ne _ _ _ hkm] at hk; exact hn k sp tb path hk hb

theorem SuspOk.insert {n n' : N} (m : Nat) (sp : Susp) (h : n'.susp = n.susp.insert m sp)
    (hsp : ∀ tb path, sp.probeB = some (tb, path) → path = 1 ∨ path = 2) (hn : n.SuspOk) : n'.SuspOk := by
  unfold N.SuspOk at *
  intro k sp' tb path hk hb
  rw [h] at hk
  by_cases hkm : k = m
  · subst hkm; rw [AMap.get?_insert_self] at hk; injection hk with hk; subst hk; exact hsp tb path hb
  · rw [AMap.get?_insert_ne _ _ _ _ hkm] at hk; exact hn k sp' tb path hk hb

/-- The suspicion table is kept or kept good, and the broadcast-layer output only grows. -/
def CW2 (n n' : N) : Prop := (n.SuspOk → n'.SuspOk) ∧ OBg n n'

theorem CW2.refl (n : N) : CW2 n n := ⟨id, OBg.refl n⟩
theorem CW2.trans {a b c : N} (h1 : CW2 a b) (h2 : CW2 b c) : CW2 a c := ⟨fun h => h2.1 (h1.1 h), h1.2.trans h2.2⟩
theorem CW2.of_eq {a b : N} (hs : b.susp = a.susp) (hb : b.outBc = a.outBc) : CW2 a b :=
  ⟨SuspOk.of_eq hs, ⟨[], by rw [hb]; simp⟩⟩

theorem nsSecond_spec (e : Env) (n : N) (now m : Nat) (ev : Option Evid) :
    (N.nsSecond e n now m ev).1.susp = n.susp ∧ (N.nsSecond e n now m ev).1.outBc = n.outBc ∧
    ∀ tb path, (N.nsSecond e n now m ev).2 = some (tb, path) → path = 1 ∨ path = 2 := by
  unfold N.nsSecond
  cases hr : n.independentRoute e now m ev with
  | none => simp
  | some rp =>
    obtain ⟨route, path⟩ := rp
    simp only []
    refine ⟨by simp, by simp, ?_⟩
    intro tb p h
    simp at h
    obtain ⟨-, rfl⟩ := h
    exact independentRoute_path e n now m ev route path hr

theorem newSusp_cw2 (e : Env) (n : N) (now m since : Nat) (ev : Option Evid) : CW2 n (N.newSusp e n now m since ev) := by
  have h : N.newSusp e n now m since ev =
      if MAX_TABLE ≤ n.susp.len then n
      else
        let wait := max PROBE_WAIT_MIN (match ev with | some x => min (x.srtt * 3) U64MAX | none => 0)
        let n1 := N.nsFirst e n m
        let (n2, probeB) := N.nsSecond e n1 now m ev
        let sp : Susp := ⟨since, now, probeB, wait⟩
        let n3 := ({ n2 with susp := n2.susp.insert m sp }).scheduleConfirm now (now + wait)
        match probeB with
        | some (tb, _) => n3.scheduleConfirm now (max (max (since + CONFIRM) (now + wait)) (tb + wait))
        | none => n3.trace (.noIndependentPath m) := by
    unfold N.newSusp N.nsFirst N.nsSecond
    rfl
  rw [h]
  split
  · exact CW2.refl n
  · dsimp only
    obtain ⟨s1, s2, s3⟩ := nsSecond_spec e (N.nsFirst e n m) now m ev
    have f1 : (N.nsFirst e n m).susp = n.susp := by unfold N.nsFirst; simp
    have f2 : (N.nsFirst e n m).outBc = n.outBc := by unfold N.nsFirst; simp
    generalize hq : N.nsSecond e (N.nsFirst e n m) now m ev = q at s1 s2 s3
    obtain ⟨n2, pb⟩ := q
    simp only [] at s1 s2 s3 ⊢
    clear hq h
    have hok : ∀ x : N, x.susp = n2.susp.insert m ⟨since, now, pb, max PROBE_WAIT_MIN (match ev with | some x => min (x.srtt * 3) U64MAX | none => 0)⟩ →
        x.outBc = n.outBc → CW2 n x := fun x hx hb =>
      ⟨SuspOk.insert m _ (by rw [hx, s1, f1]) (fun tb path hp => s3 tb path hp), ⟨[], by rw [hb]; simp⟩⟩
    cases pb with
    | none =>
      refine hok _ ?_ ?_
      · dsimp only; rw [trace_susp]; simp [N.scheduleConfirm]
      · dsimp only; rw [trace_outBc]; simp only [N.scheduleConfirm]; exact s2.trans f2
    | some p =>
      obtain ⟨tb, pa⟩ := p
      refine hok _ ?_ ?_
      · dsimp only; simp [N.scheduleConfirm]
      · dsimp only; simp only [N.scheduleConfirm]; exact s2.trans f2


theorem hubDown_obg (e : Env) (n : N) (now m : Nat) (cause : Cause) : OBg n (N.hubDown e n now m cause) := by
  cases hl : n.roster.get? m with
  | none => unfold N.hubDown; rw [hl]; exact OBg.refl _
  | some lease =>
    cases cause with
    | left =>
      rw [hubDown_left_eq e n now m lease hl]
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, q, -⟩ := pushDelta_ht e ((n.hdPre m).bc (.release m)) now m lease.rc .left
      exact ⟨[.release m], by rw [q]; rfl⟩
    | remote =>
      rw [hubDown_remote_eq e n now m lease hl]
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, q, -⟩ := pushDelta_ht e ((n.hdPre m).bc (.hold m)) now m lease.rc .down
      obtain ⟨-, g⟩ := hdHold_ht (N.pushDelta e ((n.hdPre m).bc (.hold m)) now m lease.rc .down) lease m now
      exact ⟨[.hold m], by rw [g, q]; rfl⟩
    | confirmed pf =>
      rw [hubDown_conf_eq e n now m lease pf hl]
      dsimp only
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, r, -⟩ := confirmDowns_ht e (((N.pushDelta e ((n.hdPre m).bc (.hold m)) now m lease.rc .down).hdHold lease m now).trace
        (.confirmed m)) m lease.rc.inc pf
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, q, -⟩ := pushDelta_ht e ((n.hdPre m).bc (.hold m)) now m lease.rc .down
      obtain ⟨-, g⟩ := hdHold_ht (N.pushDelta e ((n.hdPre m).bc (.hold m)) now m lease.rc .down) lease m now
      exact ⟨[.hold m], by rw [r]; simp only [trace_outBc]; rw [g, q]; rfl⟩


/-! ## `carrier_watch` -/

theorem hubDown_susp (e : Env) (n : N) (now m : Nat) (cause : Cause) : CW2 n (N.hubDown e n now m cause) := by
  refine ⟨?_, hubDown_obg e n now m cause⟩
  intro hs
  cases hl : n.roster.get? m with
  | none => unfold N.hubDown; rw [hl]; exact hs
  | some lease =>
    cases cause with
    | left =>
      rw [hubDown_left_eq e n now m lease hl]
      obtain ⟨-, q, -⟩ := pushDelta_ht e ((n.hdPre m).bc (.release m)) now m lease.rc .left
      exact SuspOk.erase m (by rw [q]; rfl) hs
    | remote =>
      rw [hubDown_remote_eq e n now m lease hl]
      obtain ⟨-, q, -⟩ := pushDelta_ht e ((n.hdPre m).bc (.hold m)) now m lease.rc .down
      have g : ((N.pushDelta e ((n.hdPre m).bc (.hold m)) now m lease.rc .down).hdHold lease m now).susp = n.susp.erase m := by
        unfold N.hdHold; split <;> exact q.trans rfl
      exact SuspOk.erase m g hs
    | confirmed pf =>
      rw [hubDown_conf_eq e n now m lease pf hl]
      dsimp only
      obtain ⟨-, r, -⟩ := confirmDowns_ht e (((N.pushDelta e ((n.hdPre m).bc (.hold m)) now m lease.rc .down).hdHold lease m now).trace
        (.confirmed m)) m lease.rc.inc pf
      obtain ⟨-, q, -⟩ := pushDelta_ht e ((n.hdPre m).bc (.hold m)) now m lease.rc .down
      have g : ((N.pushDelta e ((n.hdPre m).bc (.hold m)) now m lease.rc .down).hdHold lease m now).susp = n.susp.erase m := by
        unfold N.hdHold; split <;> exact q.trans rfl
      exact SuspOk.erase m (by rw [r]; simp only [trace_susp]; exact g) hs

theorem rewatch_cw2 (n : N) (now : Nat) (sp : Susp) : CW2 n (N.rewatch n now sp) := by
  unfold N.rewatch
  split
  · exact CW2.of_eq (by simp [N.scheduleConfirm]) (by simp [N.scheduleConfirm])
  · exact CW2.refl _

theorem confirm_cw2 (e : Env) (n : N) (now m : Nat) (sp : Susp) (l : Lease) : CW2 n (N.confirm e n now m sp l) := by
  unfold N.confirm; exact hubDown_susp ..

theorem cwMain_cw2 (e : Env) (n : N) (now m since : Nat) (l : Lease) (ev : Option Evid) :
    CW2 n (N.cwMain e n now m since l ev) := by
  unfold N.cwMain
  cases hs : n.susp.get? m with
  | none => exact newSusp_cw2 ..
  | some sp0 =>
    simp only []
    by_cases hsi : sp0.since = since
    · subst hsi
      simp only [beq_self_eq_true, if_true, rewatch_indep]
      refine CW2.trans (rewatch_cw2 n now sp0) ?_
      have hsA : (N.rewatch n now sp0).susp.get? m = some sp0 := by rw [rewatch_susp]; exact hs
      generalize hN : N.rewatch n now sp0 = n1 at hsA ⊢
      have hind : n1.independentRoute e now m ev = n.independentRoute e now m ev := by rw [← hN]; exact rewatch_indep ..
      cases hb : sp0.probeB with
      | none =>
        simp only [hb, Option.isNone_none, if_true]
        cases hr : n.independentRoute e now m ev with
        | none => simp only [hind, hr, hb]; exact CW2.refl _
        | some rp =>
          obtain ⟨route, path⟩ := rp
          simp only []
          have key : ∀ x : N, x.susp = n1.susp.insert m { sp0 with probeB := some (now, path) } →
              x.outBc = n1.outBc → CW2 n1 x := by
            intro x hx hb'
            refine ⟨fun hok => SuspOk.insert m _ hx ?_ hok, ⟨[], by rw [hb']; simp⟩⟩
            intro tb p h; simp at h; obtain ⟨-, rfl⟩ := h; exact independentRoute_path e n now m ev route path hr
          by_cases hdl : max (max (sp0.since + CONFIRM) (sp0.probeA + sp0.wait)) (now + sp0.wait) ≤ now
          · simp only [hind, hr, hdl, ite_true, hb]
            refine CW2.trans ?_ (confirm_cw2 ..)
            exact key _ (by simp) (by simp)
          · simp only [hind, hr, hdl, ite_false, hb]
            exact key _ (by simp [N.scheduleConfirm]) (by simp [N.scheduleConfirm])
      | some tbp =>
        obtain ⟨tb, path⟩ := tbp
        simp only [hb, Option.isNone_some, Bool.false_eq_true, ite_false]
        by_cases hdl : max (max (sp0.since + CONFIRM) (sp0.probeA + sp0.wait)) (tb + sp0.wait) ≤ now
        · rw [if_pos hdl]; exact confirm_cw2 ..
        · rw [if_neg hdl]; exact CW2.of_eq (by simp [N.scheduleConfirm]) (by simp [N.scheduleConfirm])
    · simp only [show (sp0.since == since) = false by simpa using hsi]
      exact newSusp_cw2 ..

theorem carrierWatch_cw2 (e : Env) (n : N) (now m : Nat) : CW2 n (N.carrierWatch e n now m) := by
  cases hl : n.roster.get? m with
  | none => rw [cw_unknown e n now m hl]; exact ⟨SuspOk.erase m rfl, OBg.refl _⟩
  | some l =>
    cases hcar : e.carrier m with
    | unknown => rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hcar] at h; cases h)]; exact ⟨SuspOk.erase m rfl, OBg.refl _⟩
    | open_ => rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hcar] at h; cases h)]; exact ⟨SuspOk.erase m rfl, OBg.refl _⟩
    | gone since sleep =>
      by_cases hx : Excused l since sleep (e.evidence m)
      · obtain ⟨-, h2, -, h4⟩ := cw_cleared e n now m since sleep l hl hcar hx
        exact ⟨SuspOk.erase m h2, ⟨[], by rw [h4]; simp⟩⟩
      · rw [cw_eq_main e n now m since sleep l hl hcar hx]; exact cwMain_cw2 ..


/-! ## The tick -/

theorem htPulse_susp (e : Env) (n : N) (now m : Nat) (l0 : Lease) : (N.htPulse e n now m l0).1.susp = n.susp := by
  unfold N.htPulse
  cases hev : e.evidence m with
  | none => rfl
  | some ev => simp only []; split <;> simp

@[simp] theorem pushDelta_susp' (e : Env) (n : N) (now m : Nat) (rc : Rec) (a : Alive) : (N.pushDelta e n now m rc a).susp = n.susp :=
  (pushDelta_ht e n now m rc a).2.1
@[simp] theorem pushDelta_outBc' (e : Env) (n : N) (now m : Nat) (rc : Rec) (a : Alive) : (N.pushDelta e n now m rc a).outBc = n.outBc :=
  (pushDelta_ht e n now m rc a).2.2.2.2.2.2.2.2.2.2.2.1

theorem carrierReturn_cw2 (e : Env) (n : N) (now m : Nat) : CW2 n (N.carrierReturn e n now m) := by
  have key : ∀ x : N, x.susp = n.susp → (∃ ex, x.outBc = n.outBc ++ ex) → CW2 n x := fun x h1 h2 =>
    ⟨SuspOk.of_eq h1, h2⟩
  unfold N.carrierReturn
  split
  · exact key _ (by simp) ⟨[], by simp⟩
  · rename_i l t0 hd
    dsimp only
    split
    · exact key _ rfl ⟨[], by simp⟩
    · split
      · exact key _ (by simp) ⟨[.release m], by simp⟩
      · refine key _ ?_ ⟨[.restore m], ?_⟩
        · simp
        · simp

theorem htStep_cw2 (e : Env) (now m : Nat) (n : N) : CW2 n (N.htStep e now m n) := by
  unfold N.htStep
  cases hl : n.roster.get? m with
  | none => exact CW2.refl _
  | some l0 =>
    simp only []
    have hs := htPulse_susp e n now m l0
    have hb := htPulse_bc e n now m l0
    generalize hP : N.htPulse e n now m l0 = P at *
    obtain ⟨n1, l⟩ := P
    simp only [] at hs hb ⊢
    have h1 : CW2 n n1 := CW2.of_eq hs hb
    split
    · refine h1.trans ?_
      obtain ⟨-, q2, -⟩ := htExpire_spec e n1 now m l
      refine ⟨SuspOk.erase m ?_, ⟨[.release m], q2⟩⟩
      unfold N.htExpire
      obtain ⟨-, q, -⟩ := pushDelta_ht e (({ n1 with roster := n1.roster.erase m, susp := n1.susp.erase m } : N).trace (.leaseExpired m)) now m l.rc .down
      simp only [bc_susp]; rw [q]; simp
    · split
      · exact h1.trans (carrierWatch_cw2 ..)
      · exact h1

theorem htDown_cw2 (e : Env) (now m : Nat) (n : N) : CW2 n (N.htDown e now m n) := by
  unfold N.htDown
  cases hd : n.downed.get? m with
  | none => exact CW2.refl _
  | some p =>
    obtain ⟨l, t0⟩ := p
    simp only []
    split
    · exact ⟨SuspOk.of_eq (by simp), ⟨[.release m], by simp⟩⟩
    · split
      · exact carrierReturn_cw2 ..
      · exact CW2.refl _

end Vinc.Membership
