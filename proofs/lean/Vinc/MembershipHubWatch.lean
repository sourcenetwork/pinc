import Vinc.MembershipHubDown

/-!
# Hub theorems, part 3: confirming a dropped carrier (`carrier_watch`)

Property 3 (a, b and the independent-path rule at the hub).

* `cw_unknown`, `cw_not_gone`: a member with no lease, or whose carrier is not gone, only clears its suspicion.
* `cw_cleared`: a member that was heard from since the drop (a frame, or any transport packet: a slow member whose
  transport still answers, a lost probe whose twin or whose follow-up was answered), whose lease was renewed since
  the drop, or whose suspension was announced, is never confirmed: the roster keeps its members and nothing is sent.
* `cw_lone_new`, `cw_lone_old`: with no direct path and no other live hub, nothing is confirmed (the hub waits for the
  lease).
* `carrierWatch_keeps_unless` (with `ConfirmCond`): the roster keeps a member in `carrier_watch` unless the carrier is gone since
  `since`, the lease was not renewed since, nothing was heard since, no suspension notice excuses the drop, a
  suspicion for this very drop exists whose second probe went on a path other than the session (direct or a relay
  through another hub), and the deadline (drop + CONFIRM, each probe + its wait) has passed.
-/

set_option linter.unusedVariables false

namespace Vinc.Membership
open Vinc.MemInc

/-- Whether the drop is excused: renewed since, heard since, or announced as a suspension. -/
def Excused (l : Lease) (since : Nat) (sleep : Option Nat) (ev : Option Evid) : Prop :=
  since ≤ l.renewed ∨ (∃ x, ev = some x ∧ since ≤ x.rx) ∨ (∃ s, sleep = some s ∧ since ≤ satAdd s SLEEP_WIN)

theorem cw_unknown (e : Env) (n : N) (now m : Nat) (h : n.roster.get? m = none) :
    N.carrierWatch e n now m = { n with susp := n.susp.erase m } := by
  unfold N.carrierWatch; simp [h]

theorem cw_not_gone (e : Env) (n : N) (now m : Nat) (l : Lease) (h : n.roster.get? m = some l)
    (hc : ∀ s sl, e.carrier m ≠ .gone s sl) : N.carrierWatch e n now m = { n with susp := n.susp.erase m } := by
  unfold N.carrierWatch
  rw [h]
  dsimp only
  cases hcar : e.carrier m with
  | gone s sl => exact absurd hcar (hc s sl)
  | unknown => rfl
  | open_ => rfl

/-- An excused drop is never confirmed: no frame, no probe, the roster keeps its members and the suspicion ends. -/
theorem cw_cleared (e : Env) (n : N) (now m since : Nat) (sleep : Option Nat) (l : Lease)
    (hl : n.roster.get? m = some l) (hc : e.carrier m = .gone since sleep) (hx : Excused l since sleep (e.evidence m)) :
    (N.carrierWatch e n now m).roster.keys = n.roster.keys ∧ (N.carrierWatch e n now m).susp = n.susp.erase m ∧
    (N.carrierWatch e n now m).outSent = n.outSent ∧ (N.carrierWatch e n now m).outBc = n.outBc := by
  unfold N.carrierWatch
  rw [hl]
  dsimp only
  simp only [hc]
  rcases hx with h | ⟨x, hx, h⟩ | ⟨s, hs, h⟩
  · cases hev : e.evidence m <;> simp [h, hev] <;> (repeat' split) <;> simp
  · simp [hx, h, AMap.modify_keys]
  · subst hs
    cases hev : e.evidence m <;> simp [h, hev] <;> (repeat' split) <;> simp

/-- The test of `carrier_watch` as the code writes it. -/
def ExcusedB (l : Lease) (since : Nat) (sleep : Option Nat) (ev : Option Evid) : Bool :=
  decide (since ≤ l.renewed) || (match ev with | some x => decide (since ≤ x.rx) | none => false) ||
    (match sleep with | some s => decide (since ≤ satAdd s SLEEP_WIN) | none => false)

/-- Every suspicion whose second probe is recorded sent it on a path other than the session (1 direct, 2 relay). -/
def N.SuspOk (n : N) : Prop :=
  ∀ k sp tb path, n.susp.get? k = some sp → sp.probeB = some (tb, path) → path = 1 ∨ path = 2

theorem independentRoute_path (n : N) (now m : Nat) (ev : Option Evid) (r : Route) (path : Nat)
    (h : n.independentRoute now m ev = some (r, path)) : path = 1 ∨ path = 2 := by
  unfold N.independentRoute at h
  split at h
  · simp at h; left; exact h.2.symm
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨x, _, hx⟩ := h
    right; simp at hx; exact hx.2.symm

theorem scheduleConfirm_roster (n : N) (now at_ : Nat) : (n.scheduleConfirm now at_).roster = n.roster := by
  unfold N.scheduleConfirm; rfl

/-- `new_susp` in two stages, so that each is small: the first probe, then the second one if there is a route. -/
def N.nsFirst (e : Env) (n : N) (m : Nat) : N :=
  (N.tx e n m .session .probe).1.trace (.probeSent m 0)

def N.nsSecond (e : Env) (n : N) (now m : Nat) (ev : Option Evid) : N × Option (Nat × Nat) :=
  match n.independentRoute now m ev with
  | some (route, path) =>
    let n := (N.tx e n m route .probe).1
    (n.trace (.probeSent m path), some (now, path))
  | none => (n, none)

theorem announce_roster (n : N) (now m : Nat) (sp : Susp) : (N.announce n now m sp).roster = n.roster := by
  unfold N.announce N.emit N.scheduleConfirm
  repeat' split
  all_goals rfl

theorem announce_indep (n : N) (now m x : Nat) (sp : Susp) (ev : Option Evid) :
    (N.announce n now m sp).independentRoute x m ev = n.independentRoute x m ev := by
  unfold N.announce N.emit N.scheduleConfirm N.independentRoute N.hubUp
  repeat' split
  all_goals rfl

theorem announce_downed (n : N) (now m : Nat) (sp : Susp) : (N.announce n now m sp).downed = n.downed := by
  unfold N.announce N.emit N.scheduleConfirm
  repeat' split
  all_goals rfl

theorem announced_since (sp : Susp) (now : Nat) : (sp.announced now).since = sp.since := by
  unfold Susp.announced; split <;> rfl
theorem announced_probeA (sp : Susp) (now : Nat) : (sp.announced now).probeA = sp.probeA := by
  unfold Susp.announced; split <;> rfl
theorem announced_probeB (sp : Susp) (now : Nat) : (sp.announced now).probeB = sp.probeB := by
  unfold Susp.announced; split <;> rfl
theorem announced_wait (sp : Susp) (now : Nat) : (sp.announced now).wait = sp.wait := by
  unfold Susp.announced; split <;> rfl

theorem nsFirst_roster (e : Env) (n : N) (m : Nat) : (N.nsFirst e n m).roster = n.roster := by
  unfold N.nsFirst; simp

theorem nsSecond_roster (e : Env) (n : N) (now m : Nat) (ev : Option Evid) : (N.nsSecond e n now m ev).1.roster = n.roster := by
  unfold N.nsSecond; split <;> simp

theorem newSusp_roster (e : Env) (n : N) (now m since : Nat) (ev : Option Evid) :
    (N.newSusp e n now m since ev).roster = n.roster := by
  have h : N.newSusp e n now m since ev =
      if MAX_TABLE ≤ n.susp.len then n
      else
        let wait := max PROBE_WAIT_MIN (match ev with | some x => min (x.srtt * 3) U64MAX | none => 0)
        let n1 := N.nsFirst e n m
        let (n2, probeB) := N.nsSecond e n1 now m ev
        let sp : Susp := ⟨since, now, probeB, wait, false⟩
        let n3 := ({ n2 with susp := n2.susp.insert m sp }).scheduleConfirm now (now + wait)
        match probeB with
        | some (tb, _) => n3.scheduleConfirm now (max (max (since + CONFIRM) (now + wait)) (tb + wait))
        | none => n3.trace (.noIndependentPath m) := by
    unfold N.newSusp N.nsFirst N.nsSecond
    rfl
  rw [h]
  split
  · rfl
  · dsimp only
    generalize hq : N.nsSecond e (N.nsFirst e n m) now m ev = q
    obtain ⟨n2, pb⟩ := q
    have h2 : n2.roster = n.roster := by
      have := nsSecond_roster e (N.nsFirst e n m) now m ev
      rw [hq] at this; simp at this; rw [this, nsFirst_roster]
    cases pb with
    | none => simp [scheduleConfirm_roster, h2]
    | some p => obtain ⟨tb, pa⟩ := p; simp [scheduleConfirm_roster, h2]

/-- No second path and no earlier second probe, the member already reported suspected: the hub waits for the lease and does
nothing. (A member not yet reported is reported suspected, or its wait scheduled: `cw_lone_unannounced`.) -/
theorem cw_lone_old (e : Env) (n : N) (now m since : Nat) (sleep : Option Nat) (l : Lease) (sp : Susp)
    (hl : n.roster.get? m = some l) (hc : e.carrier m = .gone since sleep)
    (hx : ¬ Excused l since sleep (e.evidence m)) (hs : n.susp.get? m = some sp) (hsince : sp.since = since)
    (hb : sp.probeB = none) (hr : n.independentRoute now m (e.evidence m) = none) (hann : sp.ann = true) :
    N.carrierWatch e n now m = n := by
  unfold Excused at hx
  unfold N.carrierWatch
  rw [hl]; dsimp only; simp only [hc]
  cases hev : e.evidence m <;> cases sleep <;>
    simp_all [N.announce, Susp.announced] <;> (intros; exfalso; omega)

theorem cw_lone_new (e : Env) (n : N) (now m since : Nat) (sleep : Option Nat) (l : Lease)
    (hl : n.roster.get? m = some l) (hc : e.carrier m = .gone since sleep)
    (hx : ¬ Excused l since sleep (e.evidence m))
    (hs : n.susp.get? m = none ∨ ∃ sp, n.susp.get? m = some sp ∧ sp.since ≠ since) :
    (N.carrierWatch e n now m).roster = n.roster := by
  unfold Excused at hx
  unfold N.carrierWatch
  rw [hl]; dsimp only; simp only [hc]
  rcases hs with hs | ⟨sp, hs, hne⟩
  · cases hev : e.evidence m <;> cases sleep <;> simp_all [newSusp_roster] <;> (intros; exfalso; omega)
  · cases hev : e.evidence m <;> cases sleep <;> simp_all [newSusp_roster] <;> (intros; exfalso; omega)

def ConfirmCond (e : Env) (n : N) (now m : Nat) (l : Lease) : Prop :=
  ∃ since sleep sp tb path, e.carrier m = .gone since sleep ∧ ¬ Excused l since sleep (e.evidence m) ∧
    n.susp.get? m = some sp ∧ sp.since = since ∧ (path = 1 ∨ path = 2) ∧
    (sp.probeB = some (tb, path) ∨ (sp.probeB = none ∧ tb = now ∧ ∃ r, n.independentRoute now m (e.evidence m) = some (r, path))) ∧
    max (max (since + CONFIRM) (sp.probeA + sp.wait)) (tb + sp.wait) ≤ now

/-- The `else` of the excuse test in `carrier_watch`: the suspicion of this drop. -/
def N.cwMain (e : Env) (n : N) (now m since : Nat) (l : Lease) (ev : Option Evid) : N :=
  match n.susp.get? m with
  | some sp0 =>
    if sp0.since == since then
      let n := N.announce n now m sp0
      let sp0 := sp0.announced now
      let (n, sp) : N × Susp :=
        if sp0.probeB.isNone then
          match n.independentRoute now m ev with
          | some (route, path) =>
            let n := (N.tx e n m route .probe).1
            let n := n.trace (.probeSent m path)
            let sp := { sp0 with probeB := some (now, path) }
            ({ n with susp := n.susp.insert m sp }, sp)
          | none => (n, sp0)
        else (n, sp0)
      match sp.probeB with
      | some (tb, _) =>
        let dl := max (max (sp.since + CONFIRM) (sp.probeA + sp.wait)) (tb + sp.wait)
        if dl ≤ now then N.confirm e n now m sp l else n.scheduleConfirm now dl
      | none => n
    else N.newSusp e n now m since ev
  | none => N.newSusp e n now m since ev

theorem cw_eq_main (e : Env) (n : N) (now m since : Nat) (sleep : Option Nat) (l : Lease)
    (hl : n.roster.get? m = some l) (hc : e.carrier m = .gone since sleep)
    (hx : ¬ Excused l since sleep (e.evidence m)) :
    N.carrierWatch e n now m = N.cwMain e n now m since l (e.evidence m) := by
  unfold N.carrierWatch N.cwMain
  rw [hl]; dsimp only; simp only [hc]
  cases hev : e.evidence m <;> cases sleep <;>
    (rw [if_neg (by simp [Excused, hev] at hx ⊢; omega)]; rfl)

/-- The same without the report: a member not yet reported suspected is reported (or its wait scheduled), and stays on the
roster. -/
theorem cw_lone_unannounced (e : Env) (n : N) (now m since : Nat) (sleep : Option Nat) (l : Lease) (sp : Susp)
    (hl : n.roster.get? m = some l) (hc : e.carrier m = .gone since sleep)
    (hx : ¬ Excused l since sleep (e.evidence m)) (hs : n.susp.get? m = some sp) (hsince : sp.since = since)
    (hb : sp.probeB = none) (hr : n.independentRoute now m (e.evidence m) = none) :
    (N.carrierWatch e n now m).roster = n.roster := by
  rw [cw_eq_main e n now m since sleep l hl hc hx]
  unfold N.cwMain
  simp only [hs, hsince, beq_self_eq_true, if_true, announced_probeB, announced_since, announced_probeA, announced_wait,
    announce_indep, hr, hb, Option.isNone_none]
  exact announce_roster ..

theorem cwMain_keeps_unless (e : Env) (n : N) (now m since : Nat) (sleep : Option Nat) (l : Lease) (hOk : n.SuspOk)
    (hl : n.roster.get? m = some l) (hc : e.carrier m = .gone since sleep)
    (hx : ¬ Excused l since sleep (e.evidence m)) :
    (N.cwMain e n now m since l (e.evidence m)).roster.has m = true ∨ ConfirmCond e n now m l := by
  have hhas : n.roster.has m = true := AMap.get?_has _ _ _ hl
  have keep : ∀ x : N, x.roster = n.roster → x.roster.has m = true := fun x h => by rw [h]; exact hhas
  unfold N.cwMain
  cases hs : n.susp.get? m with
  | none => left; exact keep _ (newSusp_roster ..)
  | some sp0 =>
    simp only []
    by_cases hsi : sp0.since = since
    · simp only [hsi, beq_self_eq_true, if_true, announced_since, announced_probeA, announced_probeB, announced_wait,
        announce_indep]
      cases hb : sp0.probeB with
      | none =>
        simp only [hb, Option.isNone_none, if_true, announced_since, announced_probeA, announced_probeB, announced_wait, announce_indep]
        cases hr : n.independentRoute now m (e.evidence m) with
        | none => left; simp only [hr, hb, announced_since, announced_probeA, announced_probeB, announced_wait, announce_indep]; exact keep _ (announce_roster ..)
        | some rp =>
          obtain ⟨route, path⟩ := rp
          simp only [hr, announced_since, announced_probeA, announced_probeB, announced_wait, announce_indep]
          by_cases hdl : max (max (since + CONFIRM) (sp0.probeA + sp0.wait)) (now + sp0.wait) ≤ now
          · right
            exact ⟨since, sleep, sp0, now, path, hc, hx, hs, hsi, independentRoute_path n now m _ route path hr,
              Or.inr ⟨hb, rfl, route, hr⟩, hdl⟩
          · left
            simp only [hdl, if_false]
            exact keep _ (by simp [scheduleConfirm_roster, announce_roster])
      | some tbp =>
        obtain ⟨tb, path⟩ := tbp
        simp only [hb, Option.isNone_some, Bool.false_eq_true, ite_false, announced_since, announced_probeA, announced_probeB, announced_wait, announce_indep]
        by_cases hdl : max (max (sp0.since + CONFIRM) (sp0.probeA + sp0.wait)) (tb + sp0.wait) ≤ now
        · right
          exact ⟨since, sleep, sp0, tb, path, hc, hx, hs, hsi, hOk m sp0 tb path hs hb, Or.inl hb, by rw [← hsi]; exact hdl⟩
        · left
          rw [if_neg hdl]
          exact keep _ (by simp [scheduleConfirm_roster, announce_roster])
    · left
      simp only [show (sp0.since == since) = false by simpa using hsi]
      exact keep _ (newSusp_roster ..)

/-- The roster loses a member in `carrier_watch` only under `ConfirmCond`: the rule of the design. A single lost probe or a
slow member (heard from since the drop: `Excused`), a member whose second probe has no path, a first sight of the
drop, or a deadline not yet reached, all keep the member. -/
theorem carrierWatch_keeps_unless (e : Env) (n : N) (now m : Nat) (l : Lease) (hOk : n.SuspOk)
    (hl : n.roster.get? m = some l) :
    (N.carrierWatch e n now m).roster.has m = true ∨ ConfirmCond e n now m l := by
  have hhas : n.roster.has m = true := AMap.get?_has _ _ _ hl
  cases hcar : e.carrier m with
  | unknown =>
    left; rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hcar] at h; cases h)]; exact hhas
  | open_ =>
    left; rw [cw_not_gone e n now m l hl (by intro s sl h; rw [hcar] at h; cases h)]; exact hhas
  | gone since sleep =>
    by_cases hx : Excused l since sleep (e.evidence m)
    · left
      have := (cw_cleared e n now m since sleep l hl hcar hx).1
      rw [AMap.has_keys, this, ← AMap.has_keys]; exact hhas
    · rw [cw_eq_main e n now m since sleep l hl hcar hx]
      exact cwMain_keeps_unless e n now m since sleep l hOk hl hcar hx

end Vinc.Membership
