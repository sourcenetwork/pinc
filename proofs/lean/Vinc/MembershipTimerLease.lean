import Vinc.MembershipTimerRun

/-!
# Completeness over a run, part 3: the lease of a crashed member is dropped at a hub tick

* `RS[a, b]`: `b` has `a`'s roster, through the functions that do not write it (`*_rs`, `rs_tac`).
* `runCalls_held`: after a member crashed at `t0` (`Crash t0 m`: no evidence of it after `t0`, no frame from it, no
  carrier return), no call renews its lease past `t0` (the roster through every call: `RS[...]`, `onDown_held`,
  `onFrame_held`, ...).
* `hub_lease_gone` (property 2, hub side, over a run): a hub drops that lease at a tick at an instant in
  `(t0 + LEASE, t0 + LEASE + HUB_TICK + σ]`, by the timer schedule `tick_window` (`MembershipTimerRun`);
  `hub_lease_gone_start` is the same from the start of the hub.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership.Cmp
open Vinc.Membership
open Vinc.MemInc

/-! ## The roster through the functions that do not write it -/

/-- `b` has `a`'s roster. -/
notation "RS[" a ", " b "]" => N.roster b = N.roster a

theorem foldl_rs {α : Type} (f : N → α → N) (L : List α) (n : N) (h : ∀ b a, RS[b, f b a]) : RS[n, L.foldl f n] := by
  induction L generalizing n with
  | nil => simp
  | cons x r ih =>
    simp only [List.foldl_cons]
    have a1 := ih (f n x)
    have b1 := h n x
    exact a1.trans b1
theorem foldl_rs2 {α β : Type} (f : N × β → α → N × β) (L : List α) (a : N × β) (h : ∀ b x, RS[b.1, (f b x).1]) :
    RS[a.1, (L.foldl f a).1] := by
  induction L generalizing a with
  | nil => simp
  | cons x r ih =>
    simp only [List.foldl_cons]
    have a1 := ih (f a x)
    have b1 := h a x
    exact a1.trans b1
theorem foldl_rs3 {α β γ : Type} (f : N × β × γ → α → N × β × γ) (L : List α) (a : N × β × γ)
    (h : ∀ b x, RS[b.1, (f b x).1]) : RS[a.1, (L.foldl f a).1] := by
  induction L generalizing a with
  | nil => simp
  | cons x r ih =>
    simp only [List.foldl_cons]
    have a1 := ih (f a x)
    have b1 := h a x
    exact a1.trans b1
theorem forKeys_rs (ks : List Nat) (f : Nat → N → N) (n : N) (h : ∀ k b, RS[b, f k b]) : RS[n, forKeys ks f n] :=
  foldl_rs _ ks n (fun b a => h a b)
/-- `tm_tac` for the roster. -/
macro "rs_tac" : tactic => `(tactic| first
  | (simp (disch := (intro _ _; first | (simp; done) | (repeat' split; all_goals simp))) [foldl_rs, foldl_rs2, foldl_rs3, forKeys_rs]; done)
  | ((try dsimp only)
     repeat' split
     all_goals simp (disch := (intro _ _; first | (simp; done) | (repeat' split; all_goals simp))) [foldl_rs, foldl_rs2, foldl_rs3, forKeys_rs]))

@[simp] theorem trace_rs (n : N) (t : Tr) : RS[n, n.trace t] := by unfold N.trace; split <;> (try split) <;> simp
@[simp] theorem emit_rs (n : N) (e : Ev) : RS[n, n.emit e] := by unfold N.emit; split <;> simp
@[simp] theorem tx_rs (e : Env) (n : N) (p : Nat) (r : Route) (f : NFrame) : RS[n, (N.tx e n p r f).1] := by
  unfold N.tx; split <;> simp
@[simp] theorem deltaTo_rs (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : RS[n, N.deltaTo e n p m rc a] := by
  unfold N.deltaTo; simp
@[simp] theorem bc_rs (n : N) (b : Bc) : RS[n, n.bc b] := rfl
@[simp] theorem close_rs (n : N) (p : Nat) (r : CloseR) : RS[n, n.close p r] := rfl
@[simp] theorem beginQuiet_rs (n : N) (now cause : Nat) : RS[n, n.beginQuiet now cause] := by unfold N.beginQuiet; simp
@[simp] theorem bump_rs (n : N) : RS[n, n.bump] := by unfold N.bump; simp
@[simp] theorem homeDelta_rs (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : RS[n, N.homeDelta e n m rc a] := by
  unfold N.homeDelta; rs_tac
@[simp] theorem refreshLocal_rs (e : Env) (n : N) (now : Nat) : RS[n, N.refreshLocal e n now] := by
  unfold N.refreshLocal; simp
@[simp] theorem helloTo_rs (e : Env) (n : N) (peer : Nat) (snap : Bool) : RS[n, N.helloTo e n peer snap] := by
  unfold N.helloTo; split <;> simp
@[simp] theorem markHello_rs (n : N) (hub now : Nat) : RS[n, n.markHello hub now] := by unfold N.markHello; simp
@[simp] theorem bumpRecord_rs (n : N) : RS[n, n.bumpRecord] := by unfold N.bumpRecord; split <;> simp
@[simp] theorem rttSample_rs (n : N) (hub r : Nat) : RS[n, n.rttSample hub r] := by unfold N.rttSample; simp
@[simp] theorem removeFromView_rs (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (ex : Bool) :
    RS[n, (N.removeFromView e n now m cur src ex).1] := by
  unfold N.removeFromView; rs_tac
@[simp] theorem rcOldVer_rs (n : N) (m : Nat) (best : Rec) (old : Option (Nat × List Nat)) : RS[n, n.rcOldVer m best old] := by
  unfold N.rcOldVer; rs_tac
@[simp] theorem rcOldBoth_rs (n : N) (m : Nat) (best : Rec) (old : Option (Nat × List Nat)) : RS[n, n.rcOldBoth m best old] := by
  unfold N.rcOldBoth; rs_tac
@[simp] theorem rcVer_rs (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : RS[n, (n.rcVer m best c).1] := by
  unfold N.rcVer; rs_tac
@[simp] theorem rcTh_rs (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : RS[n, (n.rcTh m best c).1] := by
  unfold N.rcTh; rs_tac
@[simp] theorem rcSame_rs (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : RS[n, (n.rcSame m best c).1] := by
  unfold N.rcSame; rs_tac
@[simp] theorem rcNewer_rs (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : RS[n, (n.rcNewer m best c).1] := by
  unfold N.rcNewer; rs_tac
@[simp] theorem rcFresh_rs (n : N) (m : Nat) (best : Rec) : RS[n, (n.rcFresh m best).1] := by
  unfold N.rcFresh; rs_tac
@[simp] theorem rcArm_rs (n : N) (m : Nat) (best : Rec) (cur : Option ViewEntry) : RS[n, (n.rcArm m best cur).1] := by
  unfold N.rcArm; rs_tac
@[simp] theorem rcAfter_rs (e : Env) (n : N) (m : Nat) (best : Rec) (absent : Bool) (cur : Option ViewEntry) :
    RS[n, (N.rcAfter e n m best absent cur).1] := by
  unfold N.rcAfter N.rcSusp; rs_tac
@[simp] theorem recomputeOne_rs (e : Env) (n : N) (now m : Nat) : RS[n, (N.recomputeOne e n now m).1] := by
  rw [recomputeOne_eq]; unfold N.recomputeOneS; dsimp only; split <;> simp
@[simp] theorem recheckDue_rs (e : Env) (n : N) (now : Nat) : RS[n, N.recheckDue e n now] := recheckDue_roster e n now
@[simp] theorem adEnsure_rs (n : N) (hub : Nat) : RS[n, (n.adEnsure hub).1] := by unfold N.adEnsure; rs_tac
@[simp] theorem adEntries_rs (n : N) (hub m : Nat) (rc : Rec) (a : Alive) : RS[n, n.adEntries hub m rc a] := by
  unfold N.adEntries N.adDown; rs_tac
@[simp] theorem applyDeltaCore_rs (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) :
    RS[n, N.applyDeltaCore e n now hub m rc a] := by
  rw [applyDeltaCore_eq]; unfold N.applyDeltaCoreS; rs_tac
@[simp] theorem pushDelta_rs (e : Env) (n : N) (now m : Nat) (rc : Rec) (a : Alive) : RS[n, N.pushDelta e n now m rc a] := by
  unfold N.pushDelta; rs_tac
@[simp] theorem renew_rs (e : Env) (n : N) (now : Nat) (fs p : Bool) : RS[n, N.renew e n now fs p] := by
  unfold N.renew; rs_tac
@[simp] theorem onSelfEntry_rs (e : Env) (n : N) (now hub : Nat) (rc : Rec) (a : Alive) :
    RS[n, N.onSelfEntry e n now hub rc a] := by
  unfold N.onSelfEntry
  split
  · simp
  · dsimp only
    generalize observe (n.trace (Tr.selfDelta hub)).loc (n.trace (Tr.selfDelta hub)).inc rc.inc = r
    rcases r with x | ⟨b, i', l'⟩
    · repeat' split
      all_goals simp
    · cases b <;> (repeat' split) <;> simp
@[simp] theorem applyDelta_rs (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) :
    RS[n, N.applyDelta e n now hub m rc a] := by
  unfold N.applyDelta; rs_tac
@[simp] theorem applyDown_rs (e : Env) (n : N) (now hub member inc : Nat) : RS[n, N.applyDown e n now hub member inc] := by
  unfold N.applyDown; simp
@[simp] theorem dropGone_rs (n : N) (hub round : Nat) : RS[n, n.dropGone hub round] := by unfold N.dropGone; rs_tac
@[simp] theorem markAbsent_rs (e : Env) (n : N) (now hub round : Nat) : RS[n, (N.markAbsent e n now hub round).1] := by
  unfold N.markAbsent
  apply foldl_rs2
  intro b x
  obtain ⟨b1, b2⟩ := b
  simp only []
  repeat' split
  all_goals simp
@[simp] theorem markViewAbsent_rs (e : Env) (n : N) (now hub round : Nat) :
    RS[n, (N.markViewAbsent e n now hub round).1] := by
  unfold N.markViewAbsent
  apply foldl_rs2
  intro b x
  obtain ⟨b1, b2⟩ := b
  simp only []
  repeat' split
  all_goals simp
@[simp] theorem snapAbsent_rs (e : Env) (n : N) (now hub round : Nat) : RS[n, (N.snapAbsent e n now hub round).1] := by
  simp only [N.snapAbsent]
  split <;> simp
@[simp] theorem applySnap_rs (e : Env) (n : N) (now hub : Nat) (partial_ more : Bool) (es : List (Nat × Rec)) :
    RS[n, N.applySnap e n now hub partial_ more es] := by
  rw [applySnap_eq]
  have h2 : RS[n, (hubEnsure n hub).1] := by unfold hubEnsure; rs_tac
  rcases hE : hubEnsure n hub with ⟨n1, ok⟩
  rw [hE] at h2
  simp only [] at h2 ⊢
  by_cases hok : ok = true
  · simp only [hok, Bool.not_true, if_false, Bool.false_eq_true]
    have h3 : RS[n1, (snapRound n1 hub).1] := by unfold snapRound; rs_tac
    rcases hR : snapRound n1 hub with ⟨n2, round⟩
    rw [hR] at h3
    simp only [] at h3 ⊢
    generalize hn3 : (if (!n2.isHub && n2.primary == some hub) = true then
        ({ n2 with homeOk := some hub, homeSeen := true } : N) else n2) = n3
    have h4 : RS[n2, n3] := by rw [← hn3]; split <;> simp
    have h5 : RS[n3, (List.foldl (snapStep e now hub round) (n3, false, 0) es).1] :=
      foldl_rs3 (snapStep e now hub round) es (n3, false, 0) (fun b x => by
        obtain ⟨b1, c, k⟩ := b; unfold snapStep; dsimp only; repeat' split
        all_goals simp)
    have h6 : RS[(List.foldl (snapStep e now hub round) (n3, false, 0) es).1,
        snapFin e now hub partial_ more round (List.foldl (snapStep e now hub round) (n3, false, 0) es)] := by
      generalize List.foldl (snapStep e now hub round) (n3, false, 0) es = A
      obtain ⟨b1, c, k⟩ := A; unfold snapFin; dsimp only; repeat' split
      all_goals simp [N.bc]
    simp only [h6, h5, h4, h3, h2, and_self]
  · have : ok = false := by simpa using hok
    simp only [this, Bool.not_false, if_true]
    exact h2
@[simp] theorem sweepAbsent_rs (e : Env) (n : N) (now : Nat) : RS[n, N.sweepAbsent e n now] := by
  rw [sweepAbsent_eq]
  have h : RS[n, (n.hv.keys.foldl (swOut e now) (n, false)).1] := by
    apply foldl_rs2
    intro b hub
    unfold swOut
    apply foldl_rs2
    intro a m
    obtain ⟨n1, c1⟩ := a
    unfold swIn
    dsimp only
    repeat' split
    all_goals simp
  generalize n.hv.keys.foldl (swOut e now) (n, false) = F at h ⊢
  obtain ⟨f1, f2⟩ := F
  dsimp only at h ⊢
  split <;> simp [h]
@[simp] theorem reselect_rs (e : Env) (n : N) (now : Nat) : RS[n, N.reselect e n now] := by unfold N.reselect; rs_tac
@[simp] theorem sendSnapshot_rs (e : Env) (n : N) (now peer : Nat) : RS[n, N.sendSnapshot e n now peer] := by
  unfold N.sendSnapshot; rs_tac
@[simp] theorem sendFloor_rs (e : Env) (n : N) (peer : Nat) : RS[n, N.sendFloor e n peer] := by unfold N.sendFloor; rs_tac
@[simp] theorem hlHomed_rs (n : N) (peer : Nat) (homed : Bool) : RS[n, N.hlHomed n peer homed] := by
  unfold N.hlHomed; dsimp only; repeat' split
  all_goals simp
@[simp] theorem hlAttach_rs (e : Env) (n : N) (now peer : Nat) (snap : Bool) : RS[n, N.hlAttach e n now peer snap] := by
  unfold N.hlAttach; dsimp only; repeat' split
  all_goals simp
@[simp] theorem dropPeer_rs (e : Env) (n : N) (now peer : Nat) : RS[n, N.dropPeer e n now peer] := by
  unfold N.dropPeer; dsimp only; repeat' split
  all_goals simp
theorem rs_bumpMatch {F : N × Bool} {n0 : N} (h : RS[n0, F.1]) :
    RS[n0, match F with | (n, ch) => if ch = true then n.bump else n] := by
  obtain ⟨f1, f2⟩ := F
  dsimp only at h ⊢
  split <;> simp [h]
@[simp] theorem pulseRefresh_rs (e : Env) (n : N) (now : Nat) : RS[n, N.pulseRefresh e n now] := by
  unfold N.pulseRefresh
  apply foldl_rs
  intro b hub
  (try dsimp only)
  repeat' split
  all_goals simp
@[simp] theorem ofHub1_rs (e : Env) (n : N) (now peer : Nat) : RS[n, N.ofHub1 e n now peer] := by
  unfold N.ofHub1; dsimp only; split <;> simp
@[simp] theorem ofHub2_rs (e : Env) (n : N) (now peer : Nat) (isAckSnap : Bool) (t0 : Option Nat) :
    RS[n, N.ofHub2 e n now peer isAckSnap t0] := by
  unfold N.ofHub2; rs_tac
@[simp] theorem ofHub_rs (e : Env) (n : N) (now peer : Nat) (f : NFrame) : RS[n, N.ofHub e n now peer f] := by
  unfold N.ofHub; dsimp only; split <;> simp
@[simp] theorem sessionUp_rs (e : Env) (n : N) (now peer : Nat) (incoming : Bool) : RS[n, N.sessionUp e n now peer incoming] := by
  unfold N.sessionUp; dsimp only; repeat' split
  all_goals simp
@[simp] theorem snapshotTo_rs (e : Env) (n : N) (now peer : Nat) : RS[n, N.snapshotTo e n now peer] := by
  unfold N.snapshotTo; split <;> simp

/-! ## The lease of a crashed member through every call -/

theorem other_ite_modify (c : Prop) [Decidable c] (n : N) (peer : Nat) (g : Lease → Lease) :
    Other peer n (if c then ({ n with roster := n.roster.modify peer g } : N) else n) := by
  intro j hj
  split
  · exact AMap.get?_modify_ne _ _ _ _ hj
  · rfl

theorem ofMid_other (e : Env) (n : N) (now peer : Nat) (f : NFrame) (fromHub : Bool) :
    Other peer n (N.ofMid e n now peer f fromHub) := by
  unfold N.ofMid
  have h0 : RS[n, (if fromHub then N.ofHub e n now peer f else n)] := by split <;> simp
  generalize (if fromHub then N.ofHub e n now peer f else n) = n1 at h0 ⊢
  exact Other.trans (Other.of_eq h0) (other_ite_modify _ _ _ _)

theorem hlRoster_other (e : Env) (n : N) (now peer : Nat) (rc : Rec) : Other peer n (N.hlRoster e n now peer rc) := by
  unfold N.hlRoster
  intro j hj
  repeat' split
  all_goals simp only [deltaTo_rs, pushDelta_rs]
  all_goals first
    | rfl
    | exact AMap.get?_modify_ne _ _ _ _ hj
    | exact AMap.get?_insert_ne _ _ _ _ hj

theorem onHello_other (e : Env) (n : N) (now peer : Nat) (rc : Rec) (snap homed : Bool) :
    Other peer n (N.onHello e n now peer rc snap homed) := by
  rw [onHello_eq3]
  refine Other.trans (Other.of_eq ?_) (hlRoster_other e _ now peer rc)
  simp

/-- What `on_down` does to the roster: nothing, or raise the renewal time of `m'` to at most the transport's last
hearing of it, then possibly drop `m'`. -/
theorem onDown_cases (e : Env) (n : N) (now m' inc : Nat) (pf : Proof) :
    (N.onDown e n now m' inc pf).roster = n.roster ∨
    ∃ l r, n.roster.get? m' = some l ∧ r ≤ max l.renewed (evRx e m') ∧
      ((N.onDown e n now m' inc pf).roster = n.roster.modify m' (fun x => { x with renewed := r }) ∨
       (N.onDown e n now m' inc pf).roster = (n.roster.modify m' (fun x => { x with renewed := r })).erase m') := by
  unfold N.onDown
  dsimp only
  split
  · left; simp
  · cases hl : n.roster.get? m' with
    | none => left; simp
    | some l =>
      simp only []
      cases hev : e.evidence m' with
      | none =>
        have hr : l.renewed ≤ max l.renewed (evRx e m') := Nat.le_max_left _ _
        try dsimp only
        repeat' split
        all_goals first
          | (left; simp; done)
          | (right; exact ⟨l, l.renewed, rfl, hr, Or.inl (by simp)⟩)
          | (right; exact ⟨l, l.renewed, rfl, hr, Or.inr (by rw [hubDown_roster_cp]; simp)⟩)
          | (exfalso; simp_all; done)
      | some ev =>
        have hr : max l.renewed ev.rx ≤ max l.renewed (evRx e m') := by simp [evRx, hev]
        try dsimp only
        repeat' split
        all_goals first
          | (left; simp; done)
          | (right; exact ⟨l, max l.renewed ev.rx, rfl, hr, Or.inl (by simp)⟩)
          | (right; exact ⟨l, max l.renewed ev.rx, rfl, hr, Or.inr (by rw [hubDown_roster_cp]; simp)⟩)
          | (exfalso; simp_all; done)

/-- `on_down` never makes the lease of a silent member younger than `t0`: it raises the renewal time to the transport's
last hearing (at most `t0`), then refuses or drops the lease. -/
theorem onDown_held (t0 m : Nat) (e : Env) (n : N) (now m' inc : Nat) (pf : Proof) (hs : Silent t0 e m)
    (hh : Held t0 m n) : Held t0 m (N.onDown e n now m' inc pf) := by
  rcases onDown_cases e n now m' inc pf with h | ⟨l, r, hl, hr, h | h⟩
  · exact Held.of_eq h hh
  · by_cases hk : m = m'
    · subst hk
      have hle : r ≤ t0 := by
        rcases hh with h0 | ⟨l', hl', hle'⟩
        · rw [hl] at h0; cases h0
        · rw [hl] at hl'; injection hl' with hl'; subst hl'
          have := evRx_le hs; omega
      right; refine ⟨{ l with renewed := r }, ?_, hle⟩
      rw [h, modify_get_self, hl]; rfl
    · unfold Held; rw [h, AMap.get?_modify_ne _ _ _ _ hk]; exact hh
  · by_cases hk : m = m'
    · subst hk; left; rw [h]; exact AMap.get?_erase_self _ _
    · unfold Held; rw [h, AMap.get?_erase_ne _ _ _ hk, AMap.get?_modify_ne _ _ _ _ hk]; exact hh

theorem ofDisp_held (t0 m : Nat) (e : Env) (n : N) (now peer : Nat) (f : NFrame) (fromHub : Bool)
    (hs : Silent t0 e m) (hp : peer ≠ m) (hh : Held t0 m n) : Held t0 m (N.ofDisp e n now peer f fromHub) := by
  unfold N.ofDisp
  cases f with
  | hello rc snap homed =>
    dsimp only; split
    · exact Held.of_other (Ne.symm hp) (onHello_other e n now peer rc snap homed) hh
    · exact hh
  | down m' inc pf =>
    dsimp only; split
    · exact onDown_held t0 m e n now m' inc pf hs hh
    · split
      · exact Held.of_eq (by simp) hh
      · exact hh
  | _ => dsimp only; (repeat' split) <;> exact Held.of_eq (by simp) hh

theorem onFrame_held (t0 m : Nat) (e : Env) (n : N) (now peer : Nat) (f : NFrame) (hs : Silent t0 e m) (hp : peer ≠ m)
    (hh : Held t0 m n) : Held t0 m (N.onFrame e n now peer f) := by
  rw [onFrame_eq]
  split
  · exact hh
  · dsimp only
    refine ofDisp_held t0 m e _ now peer f _ hs hp ?_
    refine Held.of_other (Ne.symm hp) (ofMid_other e _ now peer f _) ?_
    exact Held.of_eq (by simp) hh

theorem onBytes_held (t0 m : Nat) (e : Env) (n : N) (now peer : Nat) (fs : List NFrame) (bad : Bool) (hs : Silent t0 e m)
    (hp : peer ≠ m) (hh : Held t0 m n) : Held t0 m (N.onBytes e n now peer fs bad) := by
  unfold N.onBytes
  have h : ∀ (L : List NFrame) (x : N), Held t0 m x → Held t0 m (L.foldl (fun n f => N.onFrame e n now peer f) x) := by
    intro L
    induction L with
    | nil => intro x hx; exact hx
    | cons f r ih => intro x hx; exact ih _ (onFrame_held t0 m e x now peer f hs hp hx)
  dsimp only
  split
  · exact Held.of_eq (by simp) (h (fs.take MAX_FRAMES_PER_CALL) n hh)
  · exact h (fs.take MAX_FRAMES_PER_CALL) n hh

theorem sessionDown_held (t0 m : Nat) (e : Env) (n : N) (now peer code : Nat) (hh : Held t0 m n) :
    Held t0 m (N.sessionDown e n now peer code) := by
  unfold N.sessionDown
  split
  · exact hh
  · dsimp only
    refine Held.of_eq (dropPeer_rs ..) ?_
    split
    · rw [Held, hubDown_roster_cp]
      by_cases hk : m = peer
      · subst hk; left; exact AMap.get?_erase_self _ _
      · rw [AMap.get?_erase_ne _ _ _ hk]; simp only [trace_rs]; exact hh
    · exact hh

theorem revoke_held (t0 m : Nat) (e : Env) (n n' : N) (now member : Nat) (h : N.revoke e n now member = some n')
    (hh : Held t0 m n) : Held t0 m n' := by
  have hc : ¬ (n.revoked.has member = false ∧ MAX_TABLE ≤ n.revoked.len) := by
    intro hh; rw [(revoke_none_iff e n now member).2 hh] at h; cases h
  rw [revoke_eq e n now member hc] at h
  injection h with h; subst h
  have h1 : RS[n, n.rvPre member] := by unfold N.rvPre; simp
  have h2 : RS[n.rvPre member, N.rvMembers e (n.rvPre member) now member] := by
    unfold N.rvMembers; split
    · dsimp only; split <;> simp
    · rfl
  have h4 : ∀ x : N, RS[x, x.rvEnd member] := by intro x; unfold N.rvEnd; dsimp only; split <;> simp
  dsimp only
  refine Held.of_eq (h4 _) ?_
  generalize hx : N.rvMembers e (n.rvPre member) now member = x at h2
  have hx' : Held t0 m x := Held.of_eq (h2.trans h1) hh
  unfold N.rvRoster
  split
  · rename_i l hl
    rw [Held, pushDelta_rs]
    simp only []
    by_cases hk : m = member
    · subst hk; left; exact AMap.get?_erase_self _ _
    · rw [AMap.get?_erase_ne _ _ _ hk]; exact hx'
  · exact hx'

theorem carrierGone_held (t0 m : Nat) (e : Env) (n : N) (now member : Nat) (hs : Silent t0 e m) (hh : Held t0 m n) :
    Held t0 m (N.carrierGone e n now member) := by
  unfold N.carrierGone
  split
  · have h1 : Held t0 m (n.trace (.carrierGone member)) := Held.of_eq (by simp) hh
    by_cases hk : m = member
    · subst hk; exact carrierWatch_held t0 e _ now m hs h1
    · exact Held.of_other hk (carrierWatch_other e _ now member) h1
  · exact hh

theorem leave_rs (n : N) : RS[n, n.leave] := by
  unfold N.leave
  exact forKeys_rs n.up.keys (fun p n => n.close p .leave) { n with leaving := true } (fun k b => by simp)

/-- What the host shows a node after member `m` crashed at `t0`: in every call that reads the transport, no evidence of
`m` newer than `t0` and no open carrier of `m` (`Silent`); no frame from `m`; no `carrier_return` of `m`. -/
def Crash (t0 m : Nat) : Call → Prop
  | .onBytes e _ peer _ _ => Silent t0 e m ∧ peer ≠ m
  | .onFrame e _ peer _ => Silent t0 e m ∧ peer ≠ m
  | .onTimeout e _ => Silent t0 e m
  | .carrierReturn _ _ member => member ≠ m
  | .carrierGone e _ _ => Silent t0 e m
  | _ => True

/-- No call after the crash renews the lease of the crashed member. -/
theorem step_held (t0 m : Nat) (c : Call) (n : N) (hc : Crash t0 m c) (hh : Held t0 m n) : Held t0 m (c.step n) := by
  cases c with
  | onBytes e now peer fs bad => exact onBytes_held t0 m e n now peer fs bad hc.1 hc.2 hh
  | onFrame e now peer f => exact onFrame_held t0 m e n now peer f hc.1 hc.2 hh
  | onTimeout e now => exact onTimeout_held t0 m e n now hc hh
  | sessionUp e now peer incoming => exact Held.of_eq (sessionUp_rs ..) hh
  | sessionDown e now peer code => exact sessionDown_held t0 m e n now peer code hh
  | leave now => exact Held.of_eq (leave_rs n) hh
  | revoke e now member =>
    simp only [Call.step]
    cases hr : N.revoke e n now member with
    | none => exact hh
    | some n' => exact revoke_held t0 m e n n' now member hr hh
  | addressChanged now => exact hh
  | snapshotTo e now peer => exact Held.of_eq (snapshotTo_rs ..) hh
  | setMaxFrame now mb => exact hh
  | carrierReturn e now member => exact Held.of_other (Ne.symm hc) (carrierReturn_other e n now member) hh
  | carrierGone e now member => exact carrierGone_held t0 m e n now member hc hh
  | drained now => exact hh

theorem runCalls_held (t0 m : Nat) (cs : List Call) (n : N) (hc : ∀ c ∈ cs, Crash t0 m c) (hh : Held t0 m n) :
    Held t0 m (runCalls cs n) := by
  induction cs generalizing n with
  | nil => exact hh
  | cons c r ih =>
    rw [runCalls_cons]
    exact ih _ (fun c' h => hc c' (List.mem_cons_of_mem _ h)) (step_held t0 m c n (hc c (List.mem_cons_self ..)) hh)

/-- **Property 2, hub side, over a run.** A hub whose host keeps its obligation (`Timely σ`), that does not leave, and
whose tick deadline is at most one tick after `t0 + LEASE` (a hub that started by then), drops the lease of a member
that crashed at `t0` (`Crash t0 m`: no evidence of it after `t0`, no frame from it, no carrier return) at a call of
`on_timeout` at an instant `τ` with `t0 + LEASE < τ ≤ t0 + LEASE + HUB_TICK + σ`, provided the run goes on past that
instant. The only hypotheses about timing are the host's (`Timely σ`); the tick schedule is `tick_window` and the
expiry in that call is `onTimeout_expires`. -/
theorem hub_lease_gone (σ t0 m : Nat) (cs : List Call) (n : N) (ht : Timely σ n cs) (hnl : ∀ c ∈ cs, c.isLeave = false)
    (hcr : ∀ c ∈ cs, Crash t0 m c) (hhub : n.isHub = true) (hl : n.leaving = false)
    (hd : n.nextTick.getD n.born ≤ t0 + LEASE + HUB_TICK) (hh : Held t0 m n)
    (hlast : ∃ c ∈ cs, t0 + LEASE + HUB_TICK + σ < c.at) :
    ∃ pre e τ post, cs = pre ++ Call.onTimeout e τ :: post ∧ t0 + LEASE < τ ∧ τ ≤ t0 + LEASE + HUB_TICK + σ ∧
      (runCalls pre n).isHub = true ∧ (runCalls pre n).leaving = false ∧ (runCalls pre n).nextTick.getD 0 ≤ τ ∧
      Held t0 m (runCalls pre n) ∧ (N.onTimeout e (runCalls pre n) τ).roster.get? m = none := by
  have hp : period n = HUB_TICK := by unfold period; rw [hhub]; rfl
  obtain ⟨pre, e, τ, post, h1, h2, h3, h4, h5, h6⟩ :=
    tick_window σ (t0 + LEASE) cs n ht hnl hl (by rw [hp]; omega) (by rw [hp]; obtain ⟨c, hc, h⟩ := hlast; exact ⟨c, hc, by omega⟩)
  rw [hp] at h3
  have hpre : ∀ c ∈ pre, Crash t0 m c := fun c hc => hcr c (by rw [h1]; exact List.mem_append_left _ hc)
  have hsil : Silent t0 e m := hcr (.onTimeout e τ) (by rw [h1]; simp)
  have hh' := runCalls_held t0 m pre n hpre hh
  refine ⟨pre, e, τ, post, h1, h2, by omega, h5.trans hhub, h4, h6, hh', ?_⟩
  have o1 := otPre_tm e (runCalls pre n) τ
  obtain ⟨-, o2, -, -⟩ := otTickPre_nextTick e (N.otPre e (runCalls pre n) τ) τ
  have o3 := tkPre_tm e (N.otTickPre e (N.otPre e (runCalls pre n) τ) τ) τ
  exact onTimeout_expires t0 m e _ τ hsil hh' h2 h4 (by rw [o1.1]; exact h6)
    (by rw [o3.2.1, o2, o1.2.1, h5, hhub])

/-- The node `Membership::start` returns has no tick deadline yet, starts at the instant it is given, is not leaving
and holds no lease. -/
theorem start_timer {e : Env} {me : Nat} {isHub : Bool} {hubs : List Nat} {tracing : Bool} {now wall floor : Nat} {n : N}
    (h : N.start e me isHub hubs tracing now wall floor = .ok n) :
    n.nextTick = none ∧ n.born = now ∧ n.leaving = false ∧ n.isHub = isHub ∧ n.roster = [] := by
  unfold N.start at h
  dsimp only at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  all_goals
    simp only [Except.ok.injEq] at h
    subst h
    simp

/-- `hub_lease_gone` from the start of the hub: a hub started at `ts ≤ t0 + LEASE + HUB_TICK`. -/
theorem hub_lease_gone_start (σ t0 m : Nat) (cs : List Call) {e : Env} {me : Nat} {hubs : List Nat} {tracing : Bool}
    {ts wall floor : Nat} {n : N} (hs : N.start e me true hubs tracing ts wall floor = .ok n)
    (hts : ts ≤ t0 + LEASE + HUB_TICK) (ht : Timely σ n cs) (hnl : ∀ c ∈ cs, c.isLeave = false)
    (hcr : ∀ c ∈ cs, Crash t0 m c) (hlast : ∃ c ∈ cs, t0 + LEASE + HUB_TICK + σ < c.at) :
    ∃ pre e τ post, cs = pre ++ Call.onTimeout e τ :: post ∧ t0 + LEASE < τ ∧ τ ≤ t0 + LEASE + HUB_TICK + σ ∧
      (N.onTimeout e (runCalls pre n) τ).roster.get? m = none := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := start_timer hs
  obtain ⟨pre, e, τ, post, h1, h2, h3, -, -, -, -, h7⟩ := hub_lease_gone σ t0 m cs n ht hnl hcr s4 s3
    (by rw [s1, s2]; exact hts) (Or.inl (by rw [s5]; rfl)) hlast
  exact ⟨pre, e, τ, post, h1, h2, h3, h7⟩

end Vinc.Membership.Cmp

#audit_axioms Vinc.Membership.Cmp.runCalls_held
#audit_axioms Vinc.Membership.Cmp.hub_lease_gone
#audit_axioms Vinc.Membership.Cmp.hub_lease_gone_start
