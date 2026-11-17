import Vinc.MembershipTimerLease

/-!
# Completeness over a run, part 4: the Down delta of the expired lease

`hub_hands_down`: the call of `on_timeout` in which `hub_lease_gone` (`MembershipTimerLease`) drops a crashed member's
lease is a `hub_tick` that hands `Delta(m, record, Down)` to the session of every attached hub (`hubTick_hands_down`),
unless the lease was dropped before. The frames handed to the sessions only accumulate through a call (`*_ps`), and a
step of the tick keeps the revoked set, the node itself, the hubs and every attached hub (`AK`, `*_ak`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership.Cmp
open Vinc.Membership
open Vinc.MemInc

/-! ## The Down delta of an expired lease is handed to every attached hub

`push_delta` in the expiry branch of `hub_tick` hands `Delta(m, record, Down)` to the session of every attached hub.
The frames a call hands to the sessions only accumulate (`PS`, `MembershipCompleteSent.lean`), so the frame is among
the sends of the call. -/

theorem hdHold_ps (n1 : N) (lease : Lease) (member now : Nat) : PS (n1.hdHold lease member now) n1 :=
  PS_of_sent (by unfold N.hdHold; split <;> rfl)

theorem confirmDowns_ps (e : Env) (member inc : Nat) (pf : Proof) : ∀ (L : List Nat) (n : N),
    PS (L.foldl
      (fun n hub =>
        if hub != n.me then
          let (n, ok) := N.tx e n hub .session (.down member inc pf)
          if ok then n.trace (.downSent member) else n
        else n) n) n := by
  intro L
  induction L with
  | nil => intro n; exact PS_refl n
  | cons k r ih =>
    intro n
    simp only [List.foldl_cons]
    refine PS_trans (ih _) ?_
    split
    · have h := tx_ps e n k .session (.down member inc pf)
      generalize N.tx e n k .session (.down member inc pf) = r at h ⊢
      obtain ⟨n', ok⟩ := r
      simp only [] at h ⊢
      exact ite_ps _ _ _ _ (PS_trans (PS_of_sent (trace_outSent_c _ _)) h) h
    · exact PS_refl n

theorem hubDown_ps (e : Env) (n : N) (now member : Nat) (cause : Cause) : PS (N.hubDown e n now member cause) n := by
  cases hl : n.roster.get? member with
  | none => unfold N.hubDown; rw [hl]; exact PS_refl _
  | some lease =>
    cases cause with
    | left => rw [hubDown_left_eq e n now member lease hl]; exact PS_trans (pushDelta_ps ..) (PS_of_sent rfl)
    | remote =>
      rw [hubDown_remote_eq e n now member lease hl]
      exact PS_trans (hdHold_ps ..) (PS_trans (pushDelta_ps ..) (PS_of_sent rfl))
    | confirmed pf =>
      rw [hubDown_conf_eq e n now member lease pf hl]
      refine PS_trans (confirmDowns_ps e member lease.rc.inc pf _ _) ?_
      refine PS_trans (PS_of_sent (trace_outSent_c _ _)) ?_
      refine PS_trans (hdHold_ps _ _ _ _) ?_
      refine PS_trans (pushDelta_ps _ _ _ _ _ _) ?_
      exact PS_of_sent rfl

theorem confirm_ps (e : Env) (n : N) (now m : Nat) (sp : Susp) (l : Lease) : PS (N.confirm e n now m sp l) n := by
  unfold N.confirm; exact hubDown_ps ..

theorem newSusp_eq2 (e : Env) (n : N) (now m since : Nat) (ev : Option Evid) :
    N.newSusp e n now m since ev =
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

theorem newSusp_ps (e : Env) (n : N) (now m since : Nat) (ev : Option Evid) : PS (N.newSusp e n now m since ev) n := by
  rw [newSusp_eq2]
  split
  · exact PS_refl n
  · dsimp only
    have h1 : PS (N.nsFirst e n m) n := by
      unfold N.nsFirst; exact PS_trans (PS_of_sent (trace_outSent_c _ _)) (tx_ps e n m .session .probe)
    have h2 : PS (N.nsSecond e (N.nsFirst e n m) now m ev).1 (N.nsFirst e n m) := by
      unfold N.nsSecond; split
      · dsimp only
        refine PS_trans (PS_of_sent (trace_outSent_c _ _)) ?_
        exact tx_ps _ _ _ _ _
      · exact PS_refl _
    generalize N.nsSecond e (N.nsFirst e n m) now m ev = q at h2 ⊢
    obtain ⟨n2, pb⟩ := q
    simp only [] at h2 ⊢
    cases pb with
    | none => exact PS_trans (PS_of_sent (by simp [N.scheduleConfirm])) (PS_trans h2 h1)
    | some p => obtain ⟨tb, pa⟩ := p; exact PS_trans (PS_of_sent (by simp [N.scheduleConfirm])) (PS_trans h2 h1)

theorem rewatch_ps (n : N) (now : Nat) (sp : Susp) : PS (N.rewatch n now sp) n := by
  unfold N.rewatch N.scheduleConfirm; split
  · exact PS_of_sent rfl
  · exact PS_refl n

theorem cwMain_ps (e : Env) (n : N) (now m since : Nat) (l : Lease) (ev : Option Evid) :
    PS (N.cwMain e n now m since l ev) n := by
  unfold N.cwMain
  cases hs : n.susp.get? m with
  | none => exact newSusp_ps ..
  | some sp0 =>
    simp only []
    by_cases hsi : sp0.since = since
    · subst hsi
      simp only [beq_self_eq_true, if_true, rewatch_indep]
      refine PS_trans ?_ (rewatch_ps n now sp0)
      generalize N.rewatch n now sp0 = n1
      cases hb : sp0.probeB with
      | none =>
        simp only [Option.isNone_none, if_true]
        cases hr : n.independentRoute e now m ev with
        | none => simp only [hb]; exact PS_refl _
        | some rp =>
          obtain ⟨route, path⟩ := rp
          simp only []
          have key : PS ({ (N.tx e n1 m route .probe).1.trace (.probeSent m path) with
              susp := ((N.tx e n1 m route .probe).1.trace (.probeSent m path)).susp.insert m { sp0 with probeB := some (now, path) } } : N) n1 :=
            PS_trans (PS_of_sent (trace_outSent_c _ _)) (tx_ps e n1 m route .probe)
          repeat' split
          all_goals first | exact PS_trans (confirm_ps _ _ _ _ _ _) key | (refine PS_trans ?_ key; exact PS_of_sent rfl)
      | some tbp =>
        obtain ⟨tb, path⟩ := tbp
        simp only [Option.isNone_some, Bool.false_eq_true, ite_false]
        repeat' split
        all_goals first | exact confirm_ps _ _ _ _ _ _ | exact PS_of_sent rfl
    · simp only [show (sp0.since == since) = false by simpa using hsi]
      exact newSusp_ps ..

theorem carrierWatch_ps (e : Env) (n : N) (now m : Nat) : PS (N.carrierWatch e n now m) n := by
  cases hl : n.roster.get? m with
  | none => rw [cw_unknown e n now m hl]; exact PS_of_sent rfl
  | some l =>
    cases hcar : e.carrier m with
    | unknown => rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hcar] at h; cases h)]; exact PS_of_sent rfl
    | open_ => rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hcar] at h; cases h)]; exact PS_of_sent rfl
    | gone since sleep =>
      by_cases hx : Excused l since sleep (e.evidence m)
      · exact PS_of_sent (cw_cleared e n now m since sleep l hl hcar hx).2.2.1
      · rw [cw_eq_main e n now m since sleep l hl hcar hx]; exact cwMain_ps ..

theorem carrierReturn_ps (e : Env) (n : N) (now member : Nat) : PS (N.carrierReturn e n now member) n := by
  unfold N.carrierReturn
  split
  · exact PS_of_sent (by simp)
  · dsimp only
    split
    · exact PS_of_sent rfl
    · split
      · exact PS_of_sent (by simp)
      · refine PS_trans (PS_of_sent (trace_outSent_c _ _)) ?_
        refine PS_trans (deltaTo_ps _ _ _ _ _ _) ?_
        refine PS_trans (pushDelta_ps _ _ _ _ _ _) ?_
        refine PS_trans (PS_of_sent (bc_outSent _ _)) ?_
        exact PS_of_sent (by split <;> rfl)

theorem htBody1_ps (e : Env) (now k : Nat) (n : N) : PS (N.htBody1 e now k n) n := by
  cases hl : n.roster.get? k with
  | none => rw [htBody1_none e now k n hl]; exact PS_refl n
  | some l0 =>
    rw [htBody1_some e now k n l0 hl]
    have h1 : PS (N.htRefresh e now k n l0).1 n := by
      unfold N.htRefresh; split
      · split
        · exact PS_of_sent (by simp)
        · exact PS_refl n
      · exact PS_refl n
    refine PS_trans ?_ h1
    unfold N.htAfter
    split
    · refine PS_trans (PS_of_sent (bc_outSent _ _)) ?_
      refine PS_trans (pushDelta_ps _ _ _ _ _ _) ?_
      exact PS_of_sent (by simp)
    · split
      · exact carrierWatch_ps ..
      · exact PS_refl _

theorem htBody2_ps (e : Env) (now k : Nat) (n : N) : PS (N.htBody2 e now k n) n := by
  unfold N.htBody2
  split
  · exact PS_refl n
  · split
    · exact PS_of_sent rfl
    · split
      · exact carrierReturn_ps ..
      · exact PS_refl n

/-- The facts of a hub tick's step that the hand-off reads: the revoked set, the node itself, the hubs, and an attached
hub stays attached (`carrier_watch` only drops the member it watches, which is not a hub). -/
def AK (n n' : N) : Prop := n'.revoked = n.revoked ∧ n'.me = n.me ∧ n'.boot = n.boot ∧ ∀ p, n.isBoot p = true →
  n.attached.has p = true → n'.attached.has p = true

theorem AK.refl (n : N) : AK n n := ⟨rfl, rfl, rfl, fun _ _ h => h⟩
theorem AK.trans {a b c : N} (h1 : AK a b) (h2 : AK b c) : AK a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, fun p hb ha =>
    h2.2.2.2 p (by unfold N.isBoot at hb ⊢; rw [h1.2.2.1]; exact hb) (h1.2.2.2 p hb ha)⟩
theorem AK.of_ht {a b : N} (h : b.HT a) : AK a b := by
  obtain ⟨-, -, -, h4, h5, -, -, -, h9, h10, -⟩ := h
  exact ⟨h4, h9, h10, fun p _ ha => by rw [h5]; exact ha⟩

theorem ASet.has_del_ne (s : ASet) (k p : Nat) (h : p ≠ k) (hp : s.has p = true) : (s.del k).has p = true := by
  unfold ASet.has ASet.del at *
  rw [AMap.has_iff_get, AMap.get?_erase_ne _ _ _ h, ← AMap.has_iff_get]
  exact hp

theorem hubDown_ak (e : Env) (n : N) (now member : Nat) (cause : Cause) (hb : n.isBoot member = false) :
    AK n (N.hubDown e n now member cause) := by
  cases hl : n.roster.get? member with
  | none => unfold N.hubDown; rw [hl]; exact AK.refl _
  | some lease =>
    have hpre : ∀ b, AK n ((n.hdPre member).bc b) := by
      intro b
      refine ⟨rfl, rfl, rfl, fun p hp ha => ?_⟩
      have : p ≠ member := by intro h; subst h; rw [hp] at hb; cases hb
      exact ASet.has_del_ne _ _ _ this ha
    have hhold : ∀ x : N, AK x (x.hdHold lease member now) := fun x =>
      ⟨by unfold N.hdHold; split <;> rfl, by unfold N.hdHold; split <;> rfl, by unfold N.hdHold; split <;> rfl,
        fun p _ ha => by unfold N.hdHold; split <;> exact ha⟩
    cases cause with
    | left =>
      rw [hubDown_left_eq e n now member lease hl]
      exact (hpre _).trans (AK.of_ht (pushDelta_ht e ((n.hdPre member).bc (.release member)) now member lease.rc .left))
    | remote =>
      rw [hubDown_remote_eq e n now member lease hl]
      exact ((hpre _).trans (AK.of_ht (pushDelta_ht e ((n.hdPre member).bc (.hold member)) now member lease.rc .down))).trans
        (hhold _)
    | confirmed pf =>
      rw [hubDown_conf_eq e n now member lease pf hl]
      dsimp only
      refine AK.trans ?_ (AK.of_ht (confirmDowns_ht _ _ _ _ _))
      refine AK.trans ?_ (AK.of_ht (trace_ht _ _))
      exact ((hpre _).trans (AK.of_ht (pushDelta_ht e ((n.hdPre member).bc (.hold member)) now member lease.rc .down))).trans
        (hhold _)

theorem newSusp_ak (e : Env) (n : N) (now m since : Nat) (ev : Option Evid) : AK n (N.newSusp e n now m since ev) := by
  rw [newSusp_eq2]
  split
  · exact AK.refl n
  · dsimp only
    have h1 : AK n (N.nsFirst e n m) := by
      unfold N.nsFirst; exact AK.of_ht (N.HT_trans (trace_ht _ _) (tx_ht e n m .session .probe))
    have h2 : AK (N.nsFirst e n m) (N.nsSecond e (N.nsFirst e n m) now m ev).1 := by
      unfold N.nsSecond; split
      · dsimp only; exact AK.of_ht (N.HT_trans (trace_ht _ _) (tx_ht _ _ _ _ _))
      · exact AK.refl _
    generalize N.nsSecond e (N.nsFirst e n m) now m ev = q at h2 ⊢
    obtain ⟨n2, pb⟩ := q
    simp only [] at h2 ⊢
    refine (h1.trans h2).trans ?_
    cases pb with
    | none =>
      refine AK.trans ?_ (AK.of_ht (trace_ht _ _))
      exact ⟨rfl, rfl, rfl, fun _ _ h => h⟩
    | some p => obtain ⟨tb, pa⟩ := p; exact ⟨rfl, rfl, rfl, fun _ _ h => h⟩

theorem cwMain_ak (e : Env) (n : N) (now m since : Nat) (l : Lease) (ev : Option Evid) (hb : n.isBoot m = false) :
    AK n (N.cwMain e n now m since l ev) := by
  have hsc : ∀ (x : N) t d, AK x (x.scheduleConfirm t d) := fun x t d => ⟨rfl, rfl, rfl, fun _ _ h => h⟩
  have hcf : ∀ (x : N) sp, x.isBoot m = false → AK x (N.confirm e x now m sp l) := fun x sp hx => by
    unfold N.confirm; exact hubDown_ak e x now m _ hx
  unfold N.cwMain
  cases hs : n.susp.get? m with
  | none => exact newSusp_ak ..
  | some sp0 =>
    simp only []
    by_cases hsi : sp0.since = since
    · subst hsi
      simp only [beq_self_eq_true, if_true, rewatch_indep]
      have hrw : AK n (N.rewatch n now sp0) := by
        unfold N.rewatch; split
        · exact hsc _ _ _
        · exact AK.refl _
      have hb1 : (N.rewatch n now sp0).isBoot m = false := by
        unfold N.rewatch N.scheduleConfirm N.isBoot at *; split <;> exact hb
      refine hrw.trans ?_
      generalize N.rewatch n now sp0 = n1 at hb1 ⊢
      cases hpb : sp0.probeB with
      | none =>
        simp only [Option.isNone_none, if_true]
        cases hr : n.independentRoute e now m ev with
        | none => simp only [hpb]; exact AK.refl _
        | some rp =>
          obtain ⟨route, path⟩ := rp
          simp only []
          have key : AK n1 ({ (N.tx e n1 m route .probe).1.trace (.probeSent m path) with
              susp := ((N.tx e n1 m route .probe).1.trace (.probeSent m path)).susp.insert m { sp0 with probeB := some (now, path) } } : N) :=
            AK.trans (AK.of_ht (N.HT_trans (trace_ht _ _) (tx_ht e n1 m route .probe))) ⟨rfl, rfl, rfl, fun _ _ h => h⟩
          have hb2 : ({ (N.tx e n1 m route .probe).1.trace (.probeSent m path) with
              susp := ((N.tx e n1 m route .probe).1.trace (.probeSent m path)).susp.insert m { sp0 with probeB := some (now, path) } } : N).isBoot m = false := by
            unfold N.isBoot at *; simpa using hb1
          repeat' split
          all_goals first | exact key | exact key.trans (hcf _ _ hb2) | exact key.trans (hsc _ _ _)
      | some tbp =>
        obtain ⟨tb, path⟩ := tbp
        simp only [Option.isNone_some, Bool.false_eq_true, ite_false]
        repeat' split
        all_goals first | exact AK.refl _ | exact hcf _ _ hb1 | exact hsc n1 _ _
    · simp only [show (sp0.since == since) = false by simpa using hsi]
      exact newSusp_ak ..

theorem carrierWatch_ak (e : Env) (n : N) (now m : Nat) (hb : n.isBoot m = false) : AK n (N.carrierWatch e n now m) := by
  have hsu : AK n ({ n with susp := n.susp.erase m } : N) := ⟨rfl, rfl, rfl, fun _ _ h => h⟩
  cases hl : n.roster.get? m with
  | none => rw [cw_unknown e n now m hl]; exact hsu
  | some l =>
    cases hcar : e.carrier m with
    | unknown => rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hcar] at h; cases h)]; exact hsu
    | open_ => rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hcar] at h; cases h)]; exact hsu
    | gone since sleep =>
      by_cases hx : Excused l since sleep (e.evidence m)
      · unfold N.carrierWatch
        rw [hl]
        dsimp only
        simp only [hcar]
        rcases hx with h | ⟨x, hx', h⟩ | ⟨s, hs, h⟩
        · cases hev : e.evidence m <;> simp [h, hev] <;> (repeat' split) <;> exact ⟨rfl, rfl, rfl, fun _ _ h => h⟩
        · simp [hx', h]; exact ⟨rfl, rfl, rfl, fun _ _ h => h⟩
        · subst hs
          cases hev : e.evidence m <;> simp [h, hev] <;> (repeat' split) <;> exact ⟨rfl, rfl, rfl, fun _ _ h => h⟩
      · rw [cw_eq_main e n now m since sleep l hl hcar hx]; exact cwMain_ak e n now m since l _ hb

theorem htBody1_ak (e : Env) (now k : Nat) (n : N) : AK n (N.htBody1 e now k n) := by
  cases hl : n.roster.get? k with
  | none => rw [htBody1_none e now k n hl]; exact AK.refl n
  | some l0 =>
    rw [htBody1_some e now k n l0 hl]
    have h1 : AK n (N.htRefresh e now k n l0).1 := by
      obtain ⟨a1, a2, a3, -, a5, -, -⟩ := htRefresh_fields e now k n l0
      exact ⟨a5, a3, a2, fun p _ ha => by rw [a1]; exact ha⟩
    refine h1.trans ?_
    generalize (N.htRefresh e now k n l0) = R
    obtain ⟨n1, l⟩ := R
    unfold N.htAfter
    split
    · dsimp only
      have h1 : AK n1 ({ n1 with roster := n1.roster.erase k, susp := n1.susp.erase k } : N) := ⟨rfl, rfl, rfl, fun _ _ h => h⟩
      have h2 := h1.trans (AK.of_ht (trace_ht ({ n1 with roster := n1.roster.erase k, susp := n1.susp.erase k } : N)
        (.leaseExpired k)))
      have h3 := h2.trans (AK.of_ht (pushDelta_ht e (({ n1 with roster := n1.roster.erase k, susp := n1.susp.erase k } : N).trace
        (.leaseExpired k)) now k l.rc .down))
      exact h3.trans ⟨rfl, rfl, rfl, fun _ _ h => h⟩
    · split
      · rename_i h; exact carrierWatch_ak e n1 now k (by simpa using h)
      · exact AK.refl _

/-- The first loop of `hub_tick` hands the Down delta of an expired lease to every attached hub. -/
theorem loop1_sends (e : Env) (now m : Nat) (rc : Rec) (p : Nat) :
    ∀ (ks : List Nat) (n : N) (l0 : Lease), m ∈ ks → n.roster.get? m = some l0 → l0.rc = rc →
      LEASE < now - (N.htRefresh e now m n l0).2.renewed →
      n.attached.has p = true → n.isBoot p = true → p ≠ m → n.revoked.has p = false → p ≠ n.me →
      (p, Route.session, NFrame.delta m rc .down, e.acc.has p) ∈ (forKeys ks (N.htBody1 e now) n).outSent := by
  intro ks
  induction ks with
  | nil => intro n l0 hm; simp at hm
  | cons k r ih =>
    intro n l0 hm hl hrc hx ha hb hpm hr hme
    rw [forKeys_cons]
    by_cases hk : k = m
    · subst hk
      refine sent_mem_of_ps (forKeys_ps r _ (fun k n => htBody1_ps e now k n) _) _ ?_
      rw [htBody1_some e now k n l0 hl]
      obtain ⟨-, hrc', -, -⟩ := htRefresh_spec e now k n l0 hl
      obtain ⟨f1, f2, f3, -, f5, -, -⟩ := htRefresh_fields e now k n l0
      generalize hR : N.htRefresh e now k n l0 = R at hx hrc' f1 f2 f3 f5
      obtain ⟨n1, l⟩ := R
      simp only [] at hx hrc' f1 f2 f3 f5 ⊢
      unfold N.htAfter
      rw [if_pos hx]
      simp only []
      refine sent_mem_of_ps (PS_of_sent (bc_outSent _ _)) _ ?_
      unfold N.pushDelta
      dsimp only
      refine sent_mem_of_ps (ite_ps _ _ _ _ (PS_refl _) (applyDeltaCore_ps _ _ _ _ _ _ _)) _ ?_
      rw [hrc', hrc]
      have hloop : ∀ (L : List Nat) (x : N), p ∈ L → x.revoked.has p = false → p ≠ x.me → x.isBoot p = true →
          (p, Route.session, NFrame.delta k rc .down, e.acc.has p) ∈ (forKeys L (fun q x =>
            if (q != k && (x.isBoot q || (k == x.me && x.homed.has q))) = true then N.deltaTo e x q k rc .down else x) x).outSent := by
        intro L
        induction L with
        | nil => intro x h; simp at h
        | cons q L' ihL =>
          intro x hq hrx hmx hbx
          rw [forKeys_cons]
          have hstep : ∀ y : N, (if (q != k && (y.isBoot q || (k == y.me && y.homed.has q))) = true then N.deltaTo e y q k rc .down else y).HT y :=
            fun y => by split; exact deltaTo_ht ..; exact N.HT_refl y
          rcases List.mem_cons.mp hq with h | h
          · subst h
            refine sent_mem_of_ps (forKeys_ps L' _ (fun k n => by split; exact deltaTo_ps ..; exact PS_refl n) _) _ ?_
            rw [if_pos (by simp [hpm, hbx])]
            exact tx_mem e x p .session _ hrx hmx
          · obtain ⟨-, -, -, h4, -, -, -, -, h9, h10, -⟩ := hstep x
            exact ihL _ h (by rw [h4]; exact hrx) (by rw [h9]; exact hmx) (by unfold N.isBoot at *; rw [h10]; exact hbx)
      have hmem : p ∈ (({ n1 with roster := n1.roster.erase k, susp := n1.susp.erase k } : N).trace (.leaseExpired k)).attached.keys := by
        simp only [trace_attached]; rw [f1]
        exact (AMap.has_keys _ _).mp ha
      exact hloop _ _ hmem (by simp [f5, hr]) (by simp [f3, hme]) (by unfold N.isBoot at *; simpa [f2] using hb)
    · have hk' : m ≠ k := Ne.symm hk
      have hm' : m ∈ r := by
        rcases List.mem_cons.mp hm with h | h
        · exact absurd h hk'
        · exact h
      have ho := htBody1_other e now k n m hk'
      have hak := htBody1_ak e now k n
      have hidx : (N.htRefresh e now m (N.htBody1 e now k n) l0).2 = (N.htRefresh e now m n l0).2 := by
        unfold N.htRefresh; cases e.evidence m <;> simp only [] <;> split <;> rfl
      exact ih _ l0 hm' (by rw [ho]; exact hl) hrc (by rw [hidx]; exact hx) (hak.2.2.2 p hb ha)
        (by unfold N.isBoot at *; rw [hak.2.2.1]; exact hb) hpm (by rw [hak.1]; exact hr) (by rw [hak.2.1]; exact hme)

/-- **The expired lease's Down delta goes to every attached hub (property 2, hub side).** In a `hub_tick` that finds
`m`'s lease older than `LEASE` (after the refresh from the transport's evidence), the hub hands `Delta(m, record, Down)`,
with the record of the lease, to the session of every attached hub (`e.acc.has p` says whether a session took it):
the frame is among the sends of the call. -/
theorem hubTick_hands_down (e : Env) (n : N) (now m : Nat) (l0 : Lease) (hl : n.roster.get? m = some l0)
    (hx : LEASE < now - (N.htRefresh e now m n l0).2.renewed) (p : Nat) (ha : n.attached.has p = true)
    (hb : n.isBoot p = true) (hpm : p ≠ m) (hr : n.revoked.has p = false) (hme : p ≠ n.me) :
    (p, Route.session, NFrame.delta m l0.rc .down, e.acc.has p) ∈ (N.hubTick e n now).outSent := by
  rw [hubTick_eq_cp]
  dsimp only
  refine sent_mem_of_ps (forKeys_ps _ _ (fun k n => htBody2_ps e now k n) _) _ ?_
  exact loop1_sends e now m l0.rc p n.roster.keys n l0 ((AMap.has_keys _ _).mp (AMap.get?_has _ _ _ hl)) hl rfl hx
    ha hb hpm hr hme

/-- Under `Silent t0 e m`, a lease last renewed at `t0` or earlier is older than `LEASE` after the refresh at any instant
later than `t0 + LEASE`. -/
theorem htRefresh_expired (t0 : Nat) (e : Env) (n : N) (now m : Nat) (l0 : Lease) (hs : Silent t0 e m)
    (hle : l0.renewed ≤ t0) (hd : t0 + LEASE < now) : LEASE < now - (N.htRefresh e now m n l0).2.renewed := by
  have : (N.htRefresh e now m n l0).2.renewed ≤ t0 := by
    unfold N.htRefresh
    cases hev : e.evidence m with
    | none => exact hle
    | some ev => simp only []; split
                 · exact hs.1 ev hev
                 · exact hle
  omega

/-- **The expiring tick of a run hands the Down to the hubs.** Under the hypotheses of `hub_lease_gone`, the call of
`on_timeout` at `τ ∈ (t0 + LEASE, t0 + LEASE + HUB_TICK + σ]` is a `hub_tick` from a node `s'` (the node after the
steps of the call before it) and either `s'` no longer holds `m`'s lease (an earlier call or an earlier step of this
call dropped it) or the call hands `Delta(m, record, Down)` to the session of every hub attached to `s'`. -/
theorem hub_hands_down (σ t0 m : Nat) (cs : List Call) (n : N) (ht : Timely σ n cs) (hnl : ∀ c ∈ cs, c.isLeave = false)
    (hcr : ∀ c ∈ cs, Crash t0 m c) (hhub : n.isHub = true) (hl : n.leaving = false)
    (hd : n.nextTick.getD n.born ≤ t0 + LEASE + HUB_TICK) (hh : Held t0 m n)
    (hlast : ∃ c ∈ cs, t0 + LEASE + HUB_TICK + σ < c.at) :
    ∃ pre e τ post s', cs = pre ++ Call.onTimeout e τ :: post ∧ t0 + LEASE < τ ∧ τ ≤ t0 + LEASE + HUB_TICK + σ ∧
      N.onTimeout e (runCalls pre n) τ = N.hubTick e s' τ ∧ (N.hubTick e s' τ).roster.get? m = none ∧
      (s'.roster.get? m = none ∨ ∃ l0, s'.roster.get? m = some l0 ∧ ∀ p, s'.attached.has p = true →
        s'.isBoot p = true → p ≠ m → s'.revoked.has p = false → p ≠ s'.me →
        (p, Route.session, NFrame.delta m l0.rc .down, e.acc.has p) ∈ (N.hubTick e s' τ).outSent) := by
  obtain ⟨pre, e, τ, post, h1, h2, h3, h4, h5, hdue, h6, h7⟩ := hub_lease_gone σ t0 m cs n ht hnl hcr hhub hl hd hh hlast
  have hsil : Silent t0 e m := hcr (.onTimeout e τ) (by rw [h1]; simp)
  have o1 := otPre_tm e (runCalls pre n) τ
  obtain ⟨-, o2, -, -⟩ := otTickPre_nextTick e (N.otPre e (runCalls pre n) τ) τ
  have o3 := tkPre_tm e (N.otTickPre e (N.otPre e (runCalls pre n) τ) τ) τ
  have hs'hub : (N.tkPre e (N.otTickPre e (N.otPre e (runCalls pre n) τ) τ) τ).isHub = true := by
    rw [o3.2.1, o2, o1.2.1, h4]
  have heq2 : N.onTimeout e (runCalls pre n) τ = N.hubTick e (N.tkPre e (N.otTickPre e (N.otPre e (runCalls pre n) τ) τ) τ) τ := by
    rw [(onTimeout_ticks e (runCalls pre n) τ h5 hdue).1]
    unfold N.otTick
    rw [tick_split]
    dsimp only
    rw [if_pos hs'hub]
  refine ⟨pre, e, τ, post, _, h1, h2, h3, heq2, by rw [← heq2]; exact h7, ?_⟩
  have hh' : Held t0 m (N.tkPre e (N.otTickPre e (N.otPre e (runCalls pre n) τ) τ) τ) :=
    Held.of_eq (tkPre_roster ..) (Held.of_eq (otTickPre_roster ..) (otPre_held t0 m e _ τ hsil h6))
  rcases hh' with hn | ⟨l0, hl0, hle⟩
  · left; exact hn
  · right
    refine ⟨l0, hl0, fun p ha hb hpm hr hme => ?_⟩
    exact hubTick_hands_down e _ τ m l0 hl0 (htRefresh_expired t0 e _ τ m l0 hsil hle h2) p ha hb hpm hr hme

end Vinc.Membership.Cmp

#audit_axioms Vinc.Membership.Cmp.hubTick_hands_down
#audit_axioms Vinc.Membership.Cmp.hub_hands_down
