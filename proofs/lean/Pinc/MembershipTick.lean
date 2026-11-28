import Pinc.MembershipHubRevoke
import Pinc.MembershipViewFrame

/-!
# Hub tick, part 1: the roster follows `hub_tick` (property 2, hub side)

`hub_tick` walks the roster keys (a cursor loop, the fold `forKeys`), then the held members. This file restates the
body of the first loop as small named pieces (`htPulse`, `htExpire`, `htStep`; the restatement is proved equal to the
model by `rfl`, `hubTick_eq`) and proves what each step does to the roster:

* `htStep_rm`: the step at key `m` changes only the entry of `m`, and only raises its renewal time or removes it
  (`RM`); `carrierWatch_rm`, `hubDown_roster`, `confirm_rm` are the same fact for the helpers it calls.
* `htStep_expired`: an entry whose lease (after the refresh from transport evidence) is older than `LEASE` is removed,
  its `Down` delta is pushed (`htStep_expired`) and its subscriptions are released.
* `htStep_fresh`: an entry the step keeps has been renewed within `LEASE`.
-/

set_option linter.unusedVariables false

namespace Pinc.Membership
open Pinc.MemInc

namespace AMap
variable {α : Type}

theorem get?_modify_self (m : AMap α) (k : Nat) (f : α → α) : (m.modify k f).get? k = (m.get? k).map f := by
  induction m with
  | nil => simp [modify, get?]
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    by_cases h1 : a = k
    · subst h1; simp [modify, get?, List.find?]
    · have hak : (a == k) = false := by simp; omega
      simp only [modify, get?, List.map_cons, List.find?_cons] at ih ⊢
      simp [hak, h1] at ih ⊢
      exact ih
end AMap

/-- Step `m`: other entries untouched, the entry of `m` only removed or renewed later. -/
def RM (m : Nat) (n n' : N) : Prop :=
  (∀ j, j ≠ m → n'.roster.get? j = n.roster.get? j) ∧
  ∀ l', n'.roster.get? m = some l' → ∃ l, n.roster.get? m = some l ∧ l.renewed ≤ l'.renewed

theorem RM.refl (m : Nat) (n : N) : RM m n n := ⟨fun _ _ => rfl, fun l' h => ⟨l', h, Nat.le_refl _⟩⟩

theorem RM.of_eq {m : Nat} {n n' : N} (h : n'.roster = n.roster) : RM m n n' := by
  unfold RM; rw [h]; exact ⟨fun _ _ => rfl, fun l' h => ⟨l', h, Nat.le_refl _⟩⟩

theorem RM.trans {m : Nat} {a b c : N} (h1 : RM m a b) (h2 : RM m b c) : RM m a c :=
  ⟨fun j hj => (h2.1 j hj).trans (h1.1 j hj), fun l' h => by
    obtain ⟨l, hl, hle⟩ := h2.2 l' h
    obtain ⟨l0, hl0, hle0⟩ := h1.2 l hl
    exact ⟨l0, hl0, Nat.le_trans hle0 hle⟩⟩

theorem RM.none {m : Nat} {n n' : N} (h : RM m n n') (hn : n.roster.get? m = none) : n'.roster.get? m = none := by
  cases hh : n'.roster.get? m with
  | none => rfl
  | some l' => obtain ⟨l, hl, _⟩ := h.2 l' hh; rw [hn] at hl; cases hl

/-- A roster that lost `m` (or kept it) and is otherwise as it was. -/
theorem RM.of_erase {m : Nat} {n n' : N} (h : n'.roster = n.roster.erase m) : RM m n n' := by
  unfold RM; rw [h]
  exact ⟨fun j hj => AMap.get?_erase_ne _ _ _ hj, fun l' hl' => by rw [AMap.get?_erase_self] at hl'; cases hl'⟩

theorem RM.of_modify {m : Nat} {n n' : N} (f : Lease → Lease) (hf : ∀ l, l.renewed ≤ (f l).renewed)
    (h : n'.roster = n.roster.modify m f) : RM m n n' := by
  unfold RM; rw [h]
  refine ⟨fun j hj => AMap.get?_modify_ne _ _ _ _ hj, fun l' hl' => ?_⟩
  rw [AMap.get?_modify_self] at hl'
  cases hg : n.roster.get? m with
  | none => rw [hg] at hl'; cases hl'
  | some l => rw [hg] at hl'; simp at hl'; subst hl'; exact ⟨l, rfl, hf l⟩

/-! ## `hub_down` on the roster -/

theorem hubDown_roster (e : Env) (n : N) (now member : Nat) (cause : Cause) :
    (N.hubDown e n now member cause).roster =
      (match n.roster.get? member with | none => n.roster | some _ => n.roster.erase member) := by
  cases hl : n.roster.get? member with
  | none => unfold N.hubDown; rw [hl]
  | some lease =>
    cases cause with
    | left =>
      rw [hubDown_left_eq e n now member lease hl]
      obtain ⟨p1, -⟩ := pushDelta_ht e ((n.hdPre member).bc (.release member)) now member lease.rc .left
      rw [p1]; rfl
    | remote =>
      rw [hubDown_remote_eq e n now member lease hl]
      obtain ⟨p1, -⟩ := pushDelta_ht e ((n.hdPre member).bc (.hold member)) now member lease.rc .down
      obtain ⟨g1, -⟩ := hdHold_ht (N.pushDelta e ((n.hdPre member).bc (.hold member)) now member lease.rc .down) lease member now
      rw [g1, p1]; rfl
    | confirmed pf =>
      rw [hubDown_conf_eq e n now member lease pf hl]
      dsimp only
      obtain ⟨hr, -⟩ := confirmDowns_ht e (((N.pushDelta e ((n.hdPre member).bc (.hold member)) now member lease.rc .down).hdHold lease member now).trace
        (.confirmed member)) member lease.rc.inc pf
      obtain ⟨p1, -⟩ := pushDelta_ht e ((n.hdPre member).bc (.hold member)) now member lease.rc .down
      obtain ⟨g1, -⟩ := hdHold_ht (N.pushDelta e ((n.hdPre member).bc (.hold member)) now member lease.rc .down) lease member now
      rw [hr]; simp only [trace_roster]; rw [g1, p1]; rfl

theorem hubDown_rm (e : Env) (n : N) (now m : Nat) (cause : Cause) : RM m n (N.hubDown e n now m cause) := by
  have h := hubDown_roster e n now m cause
  cases hl : n.roster.get? m with
  | none => rw [hl] at h; exact RM.of_eq h
  | some l => rw [hl] at h; exact RM.of_erase h

theorem confirm_rm (e : Env) (n : N) (now m : Nat) (sp : Susp) (l : Lease) : RM m n (N.confirm e n now m sp l) := by
  unfold N.confirm; exact hubDown_rm ..


/-! ## `carrier_watch` on the roster -/

theorem cwMain_rm (e : Env) (n : N) (now m since : Nat) (l : Lease) (ev : Option Evid) :
    RM m n (N.cwMain e n now m since l ev) := by
  have key : ∀ x : N, x.roster = n.roster → RM m n x := fun x h => RM.of_eq h
  unfold N.cwMain
  cases hs : n.susp.get? m with
  | none => exact key _ (newSusp_roster ..)
  | some sp0 =>
    simp only []
    by_cases hsi : sp0.since = since
    · simp only [hsi, beq_self_eq_true, if_true, rewatch_indep]
      cases hb : sp0.probeB with
      | none =>
        simp only [hb, Option.isNone_none, if_true, rewatch_indep]
        cases hr : n.independentRoute e now m ev with
        | none => simp only [hr, hb, rewatch_indep]; exact key _ (rewatch_roster ..)
        | some rp =>
          obtain ⟨route, path⟩ := rp
          simp only []
          by_cases hdl : max (max (since + CONFIRM) (sp0.probeA + sp0.wait)) (now + waitB sp0.wait (N.relaySrtt e route)) ≤ now
          · simp only [hr, hdl, ite_true, rewatch_indep]
            exact (key _ (by simp [rewatch_roster])).trans (confirm_rm ..)
          · simp only [hr, hdl, ite_false, rewatch_indep]
            exact key _ (by simp [scheduleConfirm_roster, rewatch_roster])
      | some tbp =>
        obtain ⟨tb, path⟩ := tbp
        simp only [hb, Option.isNone_some, Bool.false_eq_true, ite_false, rewatch_indep]
        by_cases hdl : max (max (sp0.since + CONFIRM) (sp0.probeA + sp0.wait)) (tb + waitB sp0.wait sp0.srttB) ≤ now
        · rw [if_pos hdl]; exact (key _ (rewatch_roster ..)).trans (confirm_rm ..)
        · rw [if_neg hdl]; exact key _ (by simp [scheduleConfirm_roster, rewatch_roster])
    · simp only [show (sp0.since == since) = false by simpa using hsi]
      exact key _ (newSusp_roster ..)

theorem carrierWatch_rm (e : Env) (n : N) (now m : Nat) : RM m n (N.carrierWatch e n now m) := by
  cases hl : n.roster.get? m with
  | none => rw [cw_unknown e n now m hl]; exact RM.of_eq rfl
  | some l =>
    cases hcar : e.carrier m with
    | unknown => rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hcar] at h; cases h)]; exact RM.of_eq rfl
    | open_ => rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hcar] at h; cases h)]; exact RM.of_eq rfl
    | gone since sleep =>
      by_cases hx : Excused l since sleep (e.evidence m)
      · unfold N.carrierWatch
        rw [hl]; dsimp only; simp only [hcar]
        cases hev : e.evidence m with
        | none =>
          rcases hx with h | ⟨x, hx, _⟩ | ⟨s, hs, h⟩
          · simp [h]; exact RM.of_eq rfl
          · simp [hev] at hx
          · subst hs; simp [h]; exact RM.of_eq rfl
        | some x =>
          by_cases hh : since ≤ x.rx
          · simp [hh]
            exact RM.of_modify (fun y => { y with renewed := max y.renewed x.rx }) (fun y => Nat.le_max_left _ _) rfl
          · rcases hx with h | ⟨x', hx', h'⟩ | ⟨s, hs, h⟩
            · simp [h]; split <;> first | exact RM.of_eq rfl | exact RM.of_modify (fun y => { y with renewed := max y.renewed x.rx }) (fun y => Nat.le_max_left _ _) rfl
            · simp [hev] at hx'; subst hx'; exact absurd h' hh
            · subst hs; simp [h]; split <;> first | exact RM.of_eq rfl | exact RM.of_modify (fun y => { y with renewed := max y.renewed x.rx }) (fun y => Nat.le_max_left _ _) rfl
      · rw [cw_eq_main e n now m since sleep l hl hcar hx]; exact cwMain_rm ..


/-! ## The body of the first loop of `hub_tick` -/

/-- The refresh from transport evidence: a lease not renewed for `RENEW` while the transport heard the member later
is renewed to that time (and the pulse traced). Returns the node and the lease as the expiry test sees it. -/
def N.htPulse (e : Env) (n : N) (now m : Nat) (l0 : Lease) : N × Lease :=
  match e.evidence m with
  | some ev =>
    if RENEW < now - l0.renewed && l0.renewed < ev.rx then
      (({ n with roster := n.roster.modify m (fun x => { x with renewed := ev.rx }) }).trace (.pulse m), { l0 with renewed := ev.rx })
    else (n, l0)
  | none => (n, l0)

/-- Expiry: drop the lease, push the `Down` delta, release the subscriptions. -/
def N.htExpire (e : Env) (n : N) (now m : Nat) (l : Lease) : N :=
  let n := { n with roster := n.roster.erase m, susp := n.susp.erase m }
  let n := n.trace (.leaseExpired m)
  let n := N.pushDelta e n now m l.rc .down
  n.bc (.release m)

/-- One key of the first loop. -/
def N.htStep (e : Env) (now m : Nat) (n : N) : N :=
  match n.roster.get? m with
  | none => n
  | some l0 =>
    let (n, l) : N × Lease := N.htPulse e n now m l0
    if LEASE < now - l.renewed then N.htExpire e n now m l
    else if !n.isBoot m then N.carrierWatch e n now m else n

/-- The second loop: held members are released after `LEASE` (or when listed again or revoked), restored when the
carrier is open again. -/
def N.htDown (e : Env) (now m : Nat) (n : N) : N :=
  match n.downed.get? m with
  | none => n
  | some (_, t0) =>
    if LEASE < now - t0 || n.roster.has m || n.revoked.has m then (N.bc { n with downed := n.downed.erase m } (.release m))
    else if e.carrier m == .open_ then N.carrierReturn e n now m
    else n

/-- `hub_tick` is the two loops, restated: proved equal to the model by `rfl`. -/
theorem hubTick_eq (e : Env) (n : N) (now : Nat) :
    N.hubTick e n now =
      (let n1 := forKeys n.roster.keys (N.htStep e now) n
       forKeys n1.downed.keys (N.htDown e now) n1) := rfl

theorem htPulse_spec (e : Env) (n : N) (now m : Nat) (l0 : Lease) (hl : n.roster.get? m = some l0) :
    (∀ j, j ≠ m → (N.htPulse e n now m l0).1.roster.get? j = n.roster.get? j) ∧
    (N.htPulse e n now m l0).1.roster.get? m = some (N.htPulse e n now m l0).2 ∧
    (N.htPulse e n now m l0).1.boot = n.boot ∧
    (l0.renewed ≤ (N.htPulse e n now m l0).2.renewed) ∧
    ((N.htPulse e n now m l0).2 = l0 ∨ ∃ ev, e.evidence m = some ev ∧ RENEW < now - l0.renewed ∧ l0.renewed < ev.rx ∧
        (N.htPulse e n now m l0).2 = { l0 with renewed := ev.rx }) := by
  unfold N.htPulse
  cases hev : e.evidence m with
  | none => simp [hl]
  | some ev =>
    by_cases hc : RENEW < now - l0.renewed ∧ l0.renewed < ev.rx
    · simp [hc.1, hc.2, AMap.get?_modify_self, hl]
      refine ⟨fun j hj => ?_, Nat.le_of_lt hc.2⟩
      simpa using AMap.get?_modify_ne _ _ _ _ hj
    · have : ¬ ((decide (RENEW < now - l0.renewed) && decide (l0.renewed < ev.rx)) = true) := by simpa using hc
      simp [this, hl]

theorem htPulse_bc (e : Env) (n : N) (now m : Nat) (l0 : Lease) : (N.htPulse e n now m l0).1.outBc = n.outBc := by
  unfold N.htPulse
  cases hev : e.evidence m with
  | none => rfl
  | some ev => simp only []; split <;> simp

theorem htExpire_spec (e : Env) (n : N) (now m : Nat) (l : Lease) :
    (N.htExpire e n now m l).roster = n.roster.erase m ∧ (N.htExpire e n now m l).outBc = n.outBc ++ [.release m] ∧
    (N.htExpire e n now m l).downed = n.downed := by
  unfold N.htExpire
  obtain ⟨p1, -, p2, -, -, -, -, -, -, -, -, p3, -⟩ := pushDelta_ht e (({ n with roster := n.roster.erase m, susp := n.susp.erase m } : N).trace (.leaseExpired m)) now m l.rc .down
  simp only [bc_roster, bc_outBc, bc_downed]
  refine ⟨?_, ?_, ?_⟩
  · rw [p1]; simp
  · rw [p3]; simp
  · rw [p2]; simp

theorem htStep_rm (e : Env) (now m : Nat) (n : N) : RM m n (N.htStep e now m n) := by
  unfold N.htStep
  cases hl : n.roster.get? m with
  | none => exact RM.refl _ _
  | some l0 =>
    simp only []
    obtain ⟨a1, a2, a3, a4, a5⟩ := htPulse_spec e n now m l0 hl
    generalize hP : N.htPulse e n now m l0 = P at *
    obtain ⟨n1, l⟩ := P
    simp only [] at a1 a2 a3 a4 a5 ⊢
    have h1 : RM m n n1 := ⟨a1, fun l' h => by rw [a2] at h; injection h with h; subst h; exact ⟨l0, hl, a4⟩⟩
    split
    · exact h1.trans (RM.of_erase (by obtain ⟨q, -⟩ := htExpire_spec e n1 now m l; exact q))
    · split
      · exact h1.trans (carrierWatch_rm ..)
      · exact h1

/-- A step never leaves a stale lease at its own key. -/
theorem htStep_fresh (e : Env) (now m : Nat) (n : N) :
    (N.htStep e now m n).roster.get? m = none ∨ ∃ l, (N.htStep e now m n).roster.get? m = some l ∧ now - l.renewed ≤ LEASE := by
  unfold N.htStep
  cases hl : n.roster.get? m with
  | none => left; exact hl
  | some l0 =>
    simp only []
    obtain ⟨a1, a2, a3, a4, a5⟩ := htPulse_spec e n now m l0 hl
    generalize hP : N.htPulse e n now m l0 = P at *
    obtain ⟨n1, l⟩ := P
    simp only [] at a1 a2 a3 a4 a5 ⊢
    split
    · rename_i hexp
      left; obtain ⟨q, -⟩ := htExpire_spec e n1 now m l; rw [q]; exact AMap.get?_erase_self _ _
    · rename_i hexp
      split
      · have hrm := carrierWatch_rm e n1 now m
        by_cases hn : (N.carrierWatch e n1 now m).roster.get? m = none
        · left; exact hn
        · right
          cases hg : (N.carrierWatch e n1 now m).roster.get? m with
          | none => exact absurd hg hn
          | some l' =>
            obtain ⟨l'', hl'', hle⟩ := hrm.2 l' hg
            rw [a2] at hl''; injection hl'' with hl''; subst hl''
            exact ⟨l', rfl, by omega⟩
      · right; exact ⟨l, a2, by omega⟩

/-- Property 2, hub side, one key: an entry whose lease (after the refresh from the transport's evidence) is older than
`LEASE` is removed, its subscriptions are released, and its `Down` delta is the one `push_delta` builds. -/
theorem htStep_expired (e : Env) (now m : Nat) (n : N) (l0 : Lease) (hl : n.roster.get? m = some l0)
    (hx : LEASE < now - (N.htPulse e n now m l0).2.renewed) :
    (N.htStep e now m n).roster.get? m = none ∧ (N.htStep e now m n).outBc = n.outBc ++ [.release m] ∧
    N.htStep e now m n = N.htExpire e (N.htPulse e n now m l0).1 now m (N.htPulse e n now m l0).2 := by
  unfold N.htStep
  rw [hl]
  simp only []
  have hP := htPulse_spec e n now m l0 hl
  have hq : (N.htPulse e n now m l0).2 = (N.htPulse e n now m l0).2 := rfl
  generalize hQ : N.htPulse e n now m l0 = P at *
  obtain ⟨n1, l⟩ := P
  simp only [] at hx hP ⊢
  rw [if_pos hx]
  obtain ⟨q1, q2, -⟩ := htExpire_spec e n1 now m l
  refine ⟨?_, ?_, rfl⟩
  · rw [q1]; exact AMap.get?_erase_self _ _
  · rw [q2]
    have : n1.outBc = n.outBc := by
      have := htPulse_bc e n now m l0
      rw [hQ] at this; exact this
    rw [this]

end Pinc.Membership
