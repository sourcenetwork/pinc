import Vinc.MembershipCompleteRoster

/-!
# Completeness and accuracy over timed hypotheses, part 2: the lease through `carrier_watch` and `hub_tick`

* `Silent t0 e m`: the host shows no evidence of `m` newer than `t0` and `m`'s carrier is not open.
* `carrierWatch_held`: under `Silent`, `carrier_watch` never makes a lease younger than `t0`; it only keeps it or removes it.
* `hubTick_held`: the same for the whole of `hub_tick`.
* `hubTick_expires_c` (property 2, hub side; the hypothesis `HubExpiry` of the task, proved): a lease last renewed
  at `t0` or earlier, with no evidence of the member after `t0`, is gone from the roster after a `hub_tick` at a time
  later than `t0 + LEASE`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership.Cmp
open Vinc.Membership
open Vinc.MemInc

/-- The host shows no evidence of `m` newer than `t0`, and `m`'s carrier is not open. -/
def Silent (t0 : Nat) (e : Env) (m : Nat) : Prop :=
  (∀ x, e.evidence m = some x → x.rx ≤ t0) ∧ e.carrier m ≠ .open_

/-- The transport's last hearing of `m`, 0 if none. -/
def evRx (e : Env) (m : Nat) : Nat := match e.evidence m with | some x => x.rx | none => 0

theorem evRx_le {t0 : Nat} {e : Env} {m : Nat} (h : Silent t0 e m) : evRx e m ≤ t0 := by
  unfold evRx
  cases hev : e.evidence m with
  | none => exact Nat.zero_le _
  | some x => exact h.1 x hev

theorem hubDown_roster_cp (e : Env) (n : N) (now member : Nat) (cause : Cause) :
    (N.hubDown e n now member cause).roster = n.roster.erase member := by
  cases h : n.roster.get? member with
  | none =>
    have : N.hubDown e n now member cause = n := by unfold N.hubDown; rw [h]
    rw [this, erase_of_get_none _ _ h]
  | some l =>
    cases cause with
    | left =>
      rw [hubDown_left_eq e n now member l h]; simp [N.hdPre]
    | remote =>
      rw [hubDown_remote_eq e n now member l h]
      rw [(hdHold_ht _ _ _ _).1, pushDelta_roster]; rfl
    | confirmed pf =>
      rw [hubDown_conf_eq e n now member l pf h]
      dsimp only
      refine (confirmDowns_ht e _ member l.rc.inc pf).1.trans ?_
      simp only [trace_roster]
      rw [(hdHold_ht _ _ _ _).1, pushDelta_roster]; rfl

theorem confirm_roster (e : Env) (n : N) (now m : Nat) (sp : Susp) (l : Lease) :
    (N.confirm e n now m sp l).roster = n.roster.erase m := by
  unfold N.confirm; exact hubDown_roster_cp ..

/-- What `carrier_watch` can do to the roster: nothing, drop `k`, or raise the renewal time of `k` to `x`. -/
def Shape (k x : Nat) (n n' : N) : Prop :=
  n'.roster = n.roster ∨ n'.roster = n.roster.erase k ∨
  n'.roster = n.roster.modify k (fun y => { y with renewed := max y.renewed x })

theorem cwMain_roster (e : Env) (n : N) (now m since : Nat) (l : Lease) (ev : Option Evid) :
    (N.cwMain e n now m since l ev).roster = n.roster ∨ (N.cwMain e n now m since l ev).roster = n.roster.erase m := by
  unfold N.cwMain
  cases hs : n.susp.get? m with
  | none => left; exact newSusp_roster ..
  | some sp0 =>
    simp only []
    by_cases hsi : sp0.since = since
    · simp only [hsi, beq_self_eq_true, if_true]
      cases hb : sp0.probeB with
      | none =>
        simp only [hb, Option.isNone_none, if_true]
        cases hr : n.independentRoute now m ev with
        | none => left; simp only [hr, hb]
        | some rp =>
          obtain ⟨route, path⟩ := rp
          simp only [hr]
          split
          · right; rw [confirm_roster]; simp
          · left; simp [scheduleConfirm_roster]
      | some tbp =>
        obtain ⟨tb, path⟩ := tbp
        simp only [hb, Option.isNone_some, Bool.false_eq_true, ite_false]
        split
        · right; rw [confirm_roster]
        · left; simp [scheduleConfirm_roster]
    · left
      simp only [show (sp0.since == since) = false by simpa using hsi]
      exact newSusp_roster ..
  
theorem cw_shape (e : Env) (n : N) (now m : Nat) : Shape m (evRx e m) n (N.carrierWatch e n now m) := by
  unfold Shape
  by_cases hl : ∃ l, n.roster.get? m = some l
  · obtain ⟨l, hl⟩ := hl
    cases hc : e.carrier m with
    | unknown => left; rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hc] at h; cases h)]
    | open_ => left; rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hc] at h; cases h)]
    | gone since sleep =>
      by_cases hx : Excused l since sleep (e.evidence m)
      · unfold N.carrierWatch
        rw [hl]; dsimp only; simp only [hc]
        rcases hx with h | ⟨x, hx', h⟩ | ⟨s, hs, h⟩
        · cases hev : e.evidence m with
          | none => simp [h, hev]
          | some x =>
            by_cases hh : since ≤ x.rx
            · right; right; simp [h, hev, hh, evRx]
            · left; simp [h, hev, hh]
        · right; right; simp [hx', h, evRx]
        · subst hs
          cases hev : e.evidence m with
          | none => simp [h, hev]
          | some x =>
            by_cases hh : since ≤ x.rx
            · right; right; simp [h, hev, hh, evRx]
            · left; simp [h, hev, hh]
      · rw [cw_eq_main e n now m since sleep l hl hc hx]
        rcases cwMain_roster e n now m since l (e.evidence m) with h | h
        · left; exact h
        · right; left; exact h
  · have hn : n.roster.get? m = none := by
      cases h : n.roster.get? m with
      | none => rfl
      | some l => exact absurd ⟨l, h⟩ hl
    left; rw [cw_unknown e n now m hn]

theorem Shape.other {k x : Nat} {n n' : N} (h : Shape k x n n') : Other k n n' := by
  intro j hj
  rcases h with h | h | h
  · rw [h]
  · rw [h]; exact AMap.get?_erase_ne _ _ _ hj
  · rw [h]; exact AMap.get?_modify_ne _ _ _ _ hj

theorem Shape.held {t0 k x : Nat} {n n' : N} (h : Shape k x n n') (hx : x ≤ t0) (hh : Held t0 k n) : Held t0 k n' := by
  rcases h with h | h | h
  · exact Held.of_eq h hh
  · left; rw [h]; exact AMap.get?_erase_self _ _
  · unfold Held at *
    rw [h, modify_get_self]
    rcases hh with hh | ⟨l, hl, hle⟩
    · left; rw [hh]; rfl
    · right; exact ⟨_, by rw [hl]; rfl, by simp only []; omega⟩

theorem carrierWatch_other (e : Env) (n : N) (now m : Nat) : Other m n (N.carrierWatch e n now m) := (cw_shape e n now m).other

theorem carrierWatch_held (t0 : Nat) (e : Env) (n : N) (now m : Nat) (hs : Silent t0 e m) (hh : Held t0 m n) :
    Held t0 m (N.carrierWatch e n now m) := (cw_shape e n now m).held (evRx_le hs) hh


/-! ## `carrier_return` -/

theorem carrierReturn_shape (e : Env) (n : N) (now member : Nat) :
    (N.carrierReturn e n now member).roster = n.roster ∨
    ∃ l, (N.carrierReturn e n now member).roster = n.roster.insert member l := by
  unfold N.carrierReturn
  split
  · left; simp
  · rename_i l t0 hd
    dsimp only
    split
    · left; rfl
    · split
      · left; simp
      · right; exact ⟨{ l with renewed := now }, by simp⟩

theorem carrierReturn_other (e : Env) (n : N) (now member : Nat) : Other member n (N.carrierReturn e n now member) := by
  intro j hj
  rcases carrierReturn_shape e n now member with h | ⟨l, h⟩
  · rw [h]
  · rw [h]; exact AMap.get?_insert_ne _ _ _ _ hj

/-! ## `hub_tick`, in its two loops -/

/-- The pulse refresh at the start of the visit of `m` in the first loop of `hub_tick`. -/
def N.htRefresh (e : Env) (now m : Nat) (n : N) (l0 : Lease) : N × Lease :=
  match e.evidence m with
  | some ev =>
    if RENEW < now - l0.renewed && l0.renewed < ev.rx then
      (({ n with roster := n.roster.modify m (fun x => { x with renewed := ev.rx }) }).trace (.pulse m), { l0 with renewed := ev.rx })
    else (n, l0)
  | none => (n, l0)

/-- Expire the lease (with the Down delta and the release) or watch the carrier. -/
def N.htAfter (e : Env) (now m : Nat) (n : N) (l : Lease) : N :=
  if LEASE < now - l.renewed then
    let n := { n with roster := n.roster.erase m, susp := n.susp.erase m }
    let n := n.trace (.leaseExpired m)
    let n := N.pushDelta e n now m l.rc .down
    n.bc (.release m)
  else if !n.isBoot m then N.carrierWatch e n now m else n

/-- The visit of `m` in the first loop. -/
def N.htBody1 (e : Env) (now : Nat) (m : Nat) (n : N) : N :=
  match n.roster.get? m with
  | none => n
  | some l0 => let (n, l) := N.htRefresh e now m n l0; N.htAfter e now m n l

/-- The visit of `m` in the second loop (members whose subscriptions are held). -/
def N.htBody2 (e : Env) (now : Nat) (m : Nat) (n : N) : N :=
  match n.downed.get? m with
  | none => n
  | some (_, t0) =>
    if LEASE < now - t0 || n.roster.has m || n.revoked.has m then (N.bc { n with downed := n.downed.erase m } (.release m))
    else if e.carrier m == .open_ then N.carrierReturn e n now m
    else n

theorem hubTick_eq_cp (e : Env) (n : N) (now : Nat) :
    N.hubTick e n now =
      (let n1 := forKeys n.roster.keys (N.htBody1 e now) n
       forKeys n1.downed.keys (N.htBody2 e now) n1) := rfl

theorem htRefresh_spec (e : Env) (now m : Nat) (n : N) (l0 : Lease) (hl : n.roster.get? m = some l0) :
    (N.htRefresh e now m n l0).1.roster.get? m = some (N.htRefresh e now m n l0).2 ∧
    (N.htRefresh e now m n l0).2.rc = l0.rc ∧
    ((N.htRefresh e now m n l0).2.renewed = l0.renewed ∨
      ∃ ev, e.evidence m = some ev ∧ (N.htRefresh e now m n l0).2.renewed = ev.rx) ∧
    Other m n (N.htRefresh e now m n l0).1 := by
  unfold N.htRefresh
  cases hev : e.evidence m with
  | none => exact ⟨hl, rfl, Or.inl rfl, Other.refl _ _⟩
  | some ev =>
    simp only []
    split
    · refine ⟨?_, rfl, Or.inr ⟨ev, rfl, rfl⟩, ?_⟩
      · simp only [trace_roster, modify_get_self, hl]; rfl
      · intro j hj; simp only [trace_roster]; exact AMap.get?_modify_ne _ _ _ _ hj
    · exact ⟨hl, rfl, Or.inl rfl, Other.refl _ _⟩

theorem htRefresh_fields (e : Env) (now m : Nat) (n : N) (l0 : Lease) :
    (N.htRefresh e now m n l0).1.attached = n.attached ∧ (N.htRefresh e now m n l0).1.boot = n.boot ∧
    (N.htRefresh e now m n l0).1.me = n.me ∧ (N.htRefresh e now m n l0).1.homed = n.homed ∧
    (N.htRefresh e now m n l0).1.revoked = n.revoked ∧ (N.htRefresh e now m n l0).1.outSent = n.outSent ∧
    (N.htRefresh e now m n l0).1.downed = n.downed := by
  unfold N.htRefresh
  split
  · split <;> simp
  · simp

theorem htAfter_expired (e : Env) (now m : Nat) (n : N) (l : Lease) (h : LEASE < now - l.renewed) :
    (N.htAfter e now m n l).roster = n.roster.erase m := by
  unfold N.htAfter
  rw [if_pos h]
  simp

theorem htAfter_other (e : Env) (now m : Nat) (n : N) (l : Lease) : Other m n (N.htAfter e now m n l) := by
  by_cases h : LEASE < now - l.renewed
  · intro j hj; rw [htAfter_expired e now m n l h]; exact AMap.get?_erase_ne _ _ _ hj
  · unfold N.htAfter
    rw [if_neg h]
    split
    · exact carrierWatch_other e n now m
    · exact Other.refl _ _

theorem htAfter_held (t0 : Nat) (e : Env) (now m : Nat) (n : N) (l : Lease) (hs : Silent t0 e m) (hh : Held t0 m n) :
    Held t0 m (N.htAfter e now m n l) := by
  unfold N.htAfter
  split
  · left; simp [AMap.get?_erase_self]
  · split
    · exact carrierWatch_held t0 e n now m hs hh
    · exact hh

theorem htBody1_none (e : Env) (now k : Nat) (n : N) (h : n.roster.get? k = none) : N.htBody1 e now k n = n := by
  unfold N.htBody1; rw [h]

theorem htBody1_some (e : Env) (now k : Nat) (n : N) (l0 : Lease) (h : n.roster.get? k = some l0) :
    N.htBody1 e now k n = N.htAfter e now k (N.htRefresh e now k n l0).1 (N.htRefresh e now k n l0).2 := by
  unfold N.htBody1; rw [h]; try rfl

theorem htBody1_other (e : Env) (now k : Nat) (n : N) : Other k n (N.htBody1 e now k n) := by
  cases hl : n.roster.get? k with
  | none => rw [htBody1_none e now k n hl]; exact Other.refl _ _
  | some l0 =>
    rw [htBody1_some e now k n l0 hl]
    obtain ⟨-, -, -, ho⟩ := htRefresh_spec e now k n l0 hl
    exact Other.trans ho (htAfter_other e now k _ _)

theorem htBody1_held (t0 : Nat) (e : Env) (now m : Nat) (n : N) (hs : Silent t0 e m) (hh : Held t0 m n) :
    Held t0 m (N.htBody1 e now m n) := by
  cases hl : n.roster.get? m with
  | none => rw [htBody1_none e now m n hl]; exact hh
  | some l0 =>
    rw [htBody1_some e now m n l0 hl]
    obtain ⟨hg, -, hr, -⟩ := htRefresh_spec e now m n l0 hl
    have hle : (N.htRefresh e now m n l0).2.renewed ≤ t0 := by
      rcases hr with h | ⟨ev, hev, h⟩
      · rw [h]; rcases hh with hh | ⟨l, hl', hle⟩
        · rw [hl] at hh; cases hh
        · rw [hl] at hl'; injection hl' with h2; subst h2; exact hle
      · rw [h]; exact hs.1 ev hev
    exact htAfter_held t0 e now m _ _ hs (Or.inr ⟨_, hg, hle⟩)

theorem htBody1_expires (t0 : Nat) (e : Env) (now m : Nat) (n : N) (hs : Silent t0 e m) (hh : Held t0 m n)
    (hd : t0 + LEASE < now) : (N.htBody1 e now m n).roster.get? m = none := by
  cases hl : n.roster.get? m with
  | none => rw [htBody1_none e now m n hl]; exact hl
  | some l0 =>
    rw [htBody1_some e now m n l0 hl]
    obtain ⟨hg, -, hr, -⟩ := htRefresh_spec e now m n l0 hl
    have hle : (N.htRefresh e now m n l0).2.renewed ≤ t0 := by
      rcases hr with h | ⟨ev, hev, h⟩
      · rw [h]; rcases hh with hh | ⟨l, hl', hle⟩
        · rw [hl] at hh; cases hh
        · rw [hl] at hl'; injection hl' with h2; subst h2; exact hle
      · rw [h]; exact hs.1 ev hev
    rw [htAfter_expired e now m _ _ (by omega)]
    exact AMap.get?_erase_self _ _

theorem htBody2_other (e : Env) (now k : Nat) (n : N) : Other k n (N.htBody2 e now k n) := by
  unfold N.htBody2
  split
  · exact Other.refl _ _
  · split
    · exact Other.of_eq rfl
    · split
      · exact carrierReturn_other e n now k
      · exact Other.refl _ _

theorem htBody2_roster (e : Env) (now k : Nat) (n : N) (hc : e.carrier k ≠ .open_) : (N.htBody2 e now k n).roster = n.roster := by
  unfold N.htBody2
  split
  · rfl
  · split
    · rfl
    · split
      · rename_i h; simp at h; exact absurd h hc
      · rfl

/-! ## The loops -/

theorem forKeys_held (t0 m : Nat) (ks : List Nat) (f : Nat → N → N) (h : ∀ k n, Held t0 m n → Held t0 m (f k n)) (n : N)
    (hh : Held t0 m n) : Held t0 m (forKeys ks f n) := by
  unfold forKeys
  exact foldl_inv (Held t0 m) _ _ _ (fun b a hb => h a b hb) hh

theorem forKeys_none (m : Nat) (ks : List Nat) (f : Nat → N → N) (h : ∀ k n, n.roster.get? m = none → (f k n).roster.get? m = none)
    (n : N) (hh : n.roster.get? m = none) : (forKeys ks f n).roster.get? m = none := by
  unfold forKeys
  exact foldl_inv (fun x : N => x.roster.get? m = none) _ _ _ (fun b a hb => h a b hb) hh

/-- A loop whose visit of `m` removes it and whose other visits cannot add it, with `m` among the keys. -/
theorem forKeys_expire (t0 m : Nat) (ks : List Nat) (f : Nat → N → N)
    (hheld : ∀ k n, Held t0 m n → Held t0 m (f k n))
    (hnone : ∀ k n, n.roster.get? m = none → (f k n).roster.get? m = none)
    (hexp : ∀ n, Held t0 m n → (f m n).roster.get? m = none) (hm : m ∈ ks) :
    ∀ n, Held t0 m n → (forKeys ks f n).roster.get? m = none := by
  induction ks with
  | nil => simp at hm
  | cons k r ih =>
    intro n hn
    unfold forKeys
    simp only [List.foldl_cons]
    by_cases hk : k = m
    · subst hk
      exact forKeys_none k r f hnone _ (hexp n hn)
    · have hr : m ∈ r := by
        rcases List.mem_cons.mp hm with h | h
        · exact absurd h.symm hk
        · exact h
      exact ih hr (f k n) (hheld k n hn)

theorem hubTick_held (t0 : Nat) (e : Env) (n : N) (now m : Nat) (hs : Silent t0 e m) (hh : Held t0 m n) :
    Held t0 m (N.hubTick e n now) := by
  rw [hubTick_eq_cp]
  dsimp only
  have h1 : Held t0 m (forKeys n.roster.keys (N.htBody1 e now) n) :=
    forKeys_held t0 m _ _ (fun k n hn => by
      by_cases hk : m = k
      · subst hk; exact htBody1_held t0 e now m n hs hn
      · exact Held.of_other hk (htBody1_other e now k n) hn) n hh
  exact forKeys_held t0 m _ _ (fun k n hn => by
    by_cases hk : m = k
    · subst hk; exact Held.of_eq (htBody2_roster e now m n hs.2) hn
    · exact Held.of_other hk (htBody2_other e now k n) hn) _ h1

/-- Property 2, hub side: a lease last renewed at `t0` or earlier, of a member the host shows no evidence of after
`t0`, is gone from the roster after a `hub_tick` later than `t0 + LEASE`. -/
theorem hubTick_expires_c (t0 : Nat) (e : Env) (n : N) (now m : Nat) (hs : Silent t0 e m) (hh : Held t0 m n)
    (hd : t0 + LEASE < now) : (N.hubTick e n now).roster.get? m = none := by
  rw [hubTick_eq_cp]
  dsimp only
  have hstep1 : ∀ k n, Held t0 m n → Held t0 m (N.htBody1 e now k n) := fun k n hn => by
    by_cases hk : m = k
    · subst hk; exact htBody1_held t0 e now m n hs hn
    · exact Held.of_other hk (htBody1_other e now k n) hn
  have hnone1 : ∀ k n, n.roster.get? m = none → (N.htBody1 e now k n).roster.get? m = none := fun k n hn => by
    by_cases hk : m = k
    · subst hk; rw [htBody1_none e now m n hn]; exact hn
    · rw [htBody1_other e now k n m hk]; exact hn
  have h1 : (forKeys n.roster.keys (N.htBody1 e now) n).roster.get? m = none := by
    cases hl : n.roster.get? m with
    | none => exact forKeys_none m _ _ hnone1 n hl
    | some l =>
      exact forKeys_expire t0 m _ _ hstep1 hnone1 (fun n hn => htBody1_expires t0 e now m n hs hn hd)
        ((AMap.has_keys _ _).mp (AMap.get?_has _ _ _ hl)) n hh
  refine forKeys_none m _ _ (fun k n hn => ?_) _ h1
  by_cases hk : m = k
  · subst hk; rw [htBody2_roster e now m n hs.2]; exact hn
  · rw [htBody2_other e now k n m hk]; exact hn


/-- A lease that is gone stays gone through a `hub_tick`, when `m`'s carrier is not open. -/
theorem hubTick_none (t0 : Nat) (e : Env) (n : N) (now m : Nat) (hs : Silent t0 e m) (hn : n.roster.get? m = none) :
    (N.hubTick e n now).roster.get? m = none := by
  rw [hubTick_eq_cp]
  dsimp only
  have hnone1 : ∀ k n, n.roster.get? m = none → (N.htBody1 e now k n).roster.get? m = none := fun k n hn => by
    by_cases hk : m = k
    · subst hk; rw [htBody1_none e now m n hn]; exact hn
    · rw [htBody1_other e now k n m hk]; exact hn
  have h1 := forKeys_none m n.roster.keys (N.htBody1 e now) hnone1 n hn
  refine forKeys_none m _ _ (fun k n hn => ?_) _ h1
  by_cases hk : m = k
  · subst hk; rw [htBody2_roster e now m n hs.2]; exact hn
  · rw [htBody2_other e now k n m hk]; exact hn

end Vinc.Membership.Cmp
