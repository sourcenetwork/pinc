import Pinc.MembershipTimerDown

/-!
# Completeness over a run, part 5: a heal and a late tick at a member

* `heal_keeps_waiting`, `heal_then_removed`, `heal_then_gone` (#284): a member that hears a hub again after longer
  than the host's give-up bound for it opens the quiet window again but leaves every waiting removal at its own instant
  and grace state, so a removal a window deferred is out of the view at its own instant plus the one extra look,
  whatever window the heal opened: `awareness_budget`'s link `q ≤ taud + QUIET` needs nothing of later heals.
* `late_tick_reopens`: a member's tick later than `WAKE_GAP` after its deadline opens the window and defers every
  waiting removal to its end (the reference model's rule), so the host's slack at a member must stay within
  `WAKE_GAP` between the Down and the removal. `QU[a, b]` (`b` has `a`'s quiet window and grace flag) carries the
  window through `renew`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Pinc.Membership.Cmp
open Pinc.Membership
open Pinc.MemInc

/-! ## A heal after the Down: the removal keeps its own instant (#284) -/

/-- **A heal leaves every waiting removal at its own instant.** A member that hears a hub `peer` again after longer
than the host's give-up bound for it (the first step of `on_frame` for a frame from a hub, `ofHub1`) opens the quiet
window again, `QUIET` from that instant, with the window's grace dropped, and leaves the recheck table as it was: every
waiting removal keeps its instant and its grace state (`beginQuiet_heal`; `session_up` and the PULSE refresh open the
window through the same `begin_quiet`). Before #284 a heal deferred the waiting removals again: a heal at the member at
least every `QUIET` kept a removal waiting for ever (the witness `MembershipSys_w_healwait.cfg`). -/
theorem heal_keeps_waiting (e : Env) (n : N) (now peer t : Nat) (hm : n.isHub = false) (hh : n.heard.get? peer = some t)
    (hs : e.giveUp peer < now - t) :
    (N.ofHub1 e n now peer).quietUntil = satAdd now QUIET ∧ (N.ofHub1 e n now peer).regrace = false ∧
    (N.ofHub1 e n now peer).recheck = n.recheck := by
  have hq := ofHub1_heal e n now peer t hm hh hs
  have hr : (N.ofHub1 e n now peer).regrace = false := by
    unfold N.ofHub1
    simp only [hh, hs, hm, decide_true, Bool.not_false, Bool.true_and, if_true]
    exact (beginQuiet_window n now 1).2
  have hrc : (N.ofHub1 e n now peer).recheck = n.recheck := by
    unfold N.ofHub1
    simp only [hh, hs, hm, decide_true, Bool.not_false, Bool.true_and, if_true]
    exact beginQuiet_heal n now
  exact ⟨hq, hr, hrc⟩

/-- **A heal does not defer again a removal an earlier window deferred** (#284). A member waiting under `(d, true)` (its
extra look ran) whose node then hears a hub again after a long silence is out of the view after the tick at any
`t' ≥ d`, though the window the heal opened lasts until `now + QUIET`, when no eligible copy lists it and nothing holds
removals. -/
theorem heal_then_removed (e : Env) (n : N) (now peer t m d t' : Nat) (hm : n.isHub = false)
    (hh : n.heard.get? peer = some t) (hs : e.giveUp peer < now - t) (hw : n.recheck.get? m = some (d, true))
    (hd : d ≤ t')
    (hc : ((N.ofHub1 e n now peer).candidates t' ((N.ofHub1 e n now peer).source t') m).1 = none)
    (hold : ((N.ofHub1 e n now peer).source t').hold = false) :
    (N.recheckDue e (N.ofHub1 e n now peer) t').members.has m = false := by
  obtain ⟨-, -, hrc⟩ := heal_keeps_waiting e n now peer t hm hh hs
  exact recheckDue_removes e _ t' m d (by rw [hrc]; exact hw) hd hc hold

/-- The same for a removal whose extra look has not begun: after the heal it gets the look at the first tick `t1 ≥ d`
and is out of the view at the next tick `t2 ≥ t1 + RECHECK_GAP`, whatever window the heal opened. -/
theorem heal_then_gone (e : Env) (n : N) (now peer t m d t1 t2 : Nat) (hm : n.isHub = false)
    (hh : n.heard.get? peer = some t) (hs : e.giveUp peer < now - t) (hw : n.recheck.get? m = some (d, false))
    (hd : d ≤ t1) (hdue : satAdd t1 RECHECK_GAP ≤ t2)
    (hc : ((N.ofHub1 e n now peer).candidates t2 ((N.ofHub1 e n now peer).source t2) m).1 = none)
    (hold : ((N.ofHub1 e n now peer).source t2).hold = false) :
    (N.recheckDue e (N.recheckDue e (N.ofHub1 e n now peer) t1) t2).members.has m = false := by
  obtain ⟨-, -, hrc⟩ := heal_keeps_waiting e n now peer t hm hh hs
  exact deferred_removal e _ t1 t2 m d (by rw [hrc]; exact hw) hd hdue hc hold

/-! ## A late tick at a member opens the quiet window -/

@[simp] theorem ite_quietUntil (c : Prop) [Decidable c] (a b : N) :
    (if c then a else b).quietUntil = if c then a.quietUntil else b.quietUntil := by split <;> rfl
@[simp] theorem ite_regrace (c : Prop) [Decidable c] (a b : N) :
    (if c then a else b).regrace = if c then a.regrace else b.regrace := by split <;> rfl

/-- `b` has `a`'s quiet window and grace flag. -/
notation "QU[" a ", " b "]" => N.quietUntil b = N.quietUntil a ∧ N.regrace b = N.regrace a

theorem foldl_qu {α : Type} (f : N → α → N) (L : List α) (n : N) (h : ∀ b a, QU[b, f b a]) : QU[n, L.foldl f n] := by
  induction L generalizing n with
  | nil => simp
  | cons x r ih =>
    simp only [List.foldl_cons]
    obtain ⟨a1, a2⟩ := ih (f n x)
    obtain ⟨b1, b2⟩ := h n x
    exact ⟨a1.trans b1, a2.trans b2⟩
theorem foldl_qu2 {α β : Type} (f : N × β → α → N × β) (L : List α) (a : N × β) (h : ∀ b x, QU[b.1, (f b x).1]) :
    QU[a.1, (L.foldl f a).1] := by
  induction L generalizing a with
  | nil => simp
  | cons x r ih =>
    simp only [List.foldl_cons]
    obtain ⟨a1, a2⟩ := ih (f a x)
    obtain ⟨b1, b2⟩ := h a x
    exact ⟨a1.trans b1, a2.trans b2⟩
theorem foldl_qu3 {α β γ : Type} (f : N × β × γ → α → N × β × γ) (L : List α) (a : N × β × γ)
    (h : ∀ b x, QU[b.1, (f b x).1]) : QU[a.1, (L.foldl f a).1] := by
  induction L generalizing a with
  | nil => simp
  | cons x r ih =>
    simp only [List.foldl_cons]
    obtain ⟨a1, a2⟩ := ih (f a x)
    obtain ⟨b1, b2⟩ := h a x
    exact ⟨a1.trans b1, a2.trans b2⟩
theorem forKeys_qu (ks : List Nat) (f : Nat → N → N) (n : N) (h : ∀ k b, QU[b, f k b]) : QU[n, forKeys ks f n] :=
  foldl_qu _ ks n (fun b a => h a b)
/-- `tm_tac` for the quiet window. -/
macro "qu_tac" : tactic => `(tactic| first
  | (simp (disch := (intro _ _; first | (simp; done) | (repeat' split; all_goals simp))) [foldl_qu, foldl_qu2, foldl_qu3, forKeys_qu]; done)
  | ((try dsimp only)
     repeat' split
     all_goals simp (disch := (intro _ _; first | (simp; done) | (repeat' split; all_goals simp))) [foldl_qu, foldl_qu2, foldl_qu3, forKeys_qu]))

@[simp] theorem trace_qu (n : N) (t : Tr) : QU[n, n.trace t] := by unfold N.trace; split <;> (try split) <;> simp
@[simp] theorem emit_qu (n : N) (e : Ev) : QU[n, n.emit e] := by unfold N.emit; split <;> simp
@[simp] theorem tx_qu (e : Env) (n : N) (p : Nat) (r : Route) (f : NFrame) : QU[n, (N.tx e n p r f).1] := by
  unfold N.tx; split <;> simp
@[simp] theorem deltaTo_qu (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : QU[n, N.deltaTo e n p m rc a] := by
  unfold N.deltaTo; simp
@[simp] theorem bc_qu (n : N) (b : Bc) : QU[n, n.bc b] := ⟨rfl, rfl⟩
@[simp] theorem close_qu (n : N) (p : Nat) (r : CloseR) : QU[n, n.close p r] := ⟨rfl, rfl⟩
@[simp] theorem bump_qu (n : N) : QU[n, n.bump] := by unfold N.bump; simp
@[simp] theorem homeDelta_qu (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : QU[n, N.homeDelta e n m rc a] := by
  unfold N.homeDelta; qu_tac
@[simp] theorem refreshLocal_qu (e : Env) (n : N) (now : Nat) : QU[n, N.refreshLocal e n now] := by
  unfold N.refreshLocal; simp
@[simp] theorem helloTo_qu (e : Env) (n : N) (peer : Nat) (snap : Bool) : QU[n, N.helloTo e n peer snap] := by
  unfold N.helloTo; split <;> simp
@[simp] theorem markHello_qu (n : N) (hub now : Nat) : QU[n, n.markHello hub now] := by unfold N.markHello; simp
@[simp] theorem bumpRecord_qu (n : N) : QU[n, n.bumpRecord] := by unfold N.bumpRecord; split <;> simp
@[simp] theorem rttSample_qu (n : N) (hub r : Nat) : QU[n, n.rttSample hub r] := by unfold N.rttSample; simp
@[simp] theorem removeFromView_qu (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (ex : Bool) :
    QU[n, (N.removeFromView e n now m cur src ex).1] := by
  unfold N.removeFromView; qu_tac
@[simp] theorem rcOldVer_qu (n : N) (m : Nat) (best : Rec) (old : Option (Nat × List Nat)) : QU[n, n.rcOldVer m best old] := by
  unfold N.rcOldVer; qu_tac
@[simp] theorem rcOldBoth_qu (n : N) (m : Nat) (best : Rec) (old : Option (Nat × List Nat)) : QU[n, n.rcOldBoth m best old] := by
  unfold N.rcOldBoth; qu_tac
@[simp] theorem rcVer_qu (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : QU[n, (n.rcVer m best c).1] := by
  unfold N.rcVer; qu_tac
@[simp] theorem rcTh_qu (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : QU[n, (n.rcTh m best c).1] := by
  unfold N.rcTh; qu_tac
@[simp] theorem rcSame_qu (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : QU[n, (n.rcSame m best c).1] := by
  unfold N.rcSame; qu_tac
@[simp] theorem rcNewer_qu (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : QU[n, (n.rcNewer m best c).1] := by
  unfold N.rcNewer; qu_tac
@[simp] theorem rcFresh_qu (n : N) (m : Nat) (best : Rec) : QU[n, (n.rcFresh m best).1] := by
  unfold N.rcFresh; qu_tac
@[simp] theorem rcArm_qu (n : N) (m : Nat) (best : Rec) (cur : Option ViewEntry) : QU[n, (n.rcArm m best cur).1] := by
  unfold N.rcArm; qu_tac
@[simp] theorem rcAfter_qu (e : Env) (n : N) (m : Nat) (best : Rec) (absent : Bool) (cur : Option ViewEntry) :
    QU[n, (N.rcAfter e n m best absent cur).1] := by
  unfold N.rcAfter N.rcSusp; qu_tac
@[simp] theorem recomputeOne_qu (e : Env) (n : N) (now m : Nat) : QU[n, (N.recomputeOne e n now m).1] := by
  rw [recomputeOne_eq]; unfold N.recomputeOneS; dsimp only; split <;> simp
@[simp] theorem adEnsure_qu (n : N) (hub : Nat) : QU[n, (n.adEnsure hub).1] := by unfold N.adEnsure; qu_tac
@[simp] theorem adEntries_qu (n : N) (hub m : Nat) (rc : Rec) (a : Alive) : QU[n, n.adEntries hub m rc a] := by
  unfold N.adEntries N.adDown; qu_tac
@[simp] theorem applyDeltaCore_qu (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) :
    QU[n, N.applyDeltaCore e n now hub m rc a] := by
  rw [applyDeltaCore_eq]; unfold N.applyDeltaCoreS; qu_tac
@[simp] theorem pushDelta_qu (e : Env) (n : N) (now m : Nat) (rc : Rec) (a : Alive) : QU[n, N.pushDelta e n now m rc a] := by
  unfold N.pushDelta; qu_tac
@[simp] theorem renew_qu (e : Env) (n : N) (now : Nat) (fs p : Bool) : QU[n, N.renew e n now fs p] := by
  unfold N.renew; qu_tac

theorem bumpRecord_recheck (n : N) : n.bumpRecord.recheck = n.recheck := by
  unfold N.bumpRecord; split <;> simp

theorem rnStep_recheck (e : Env) (now : Nat) (fs p : Bool) (n : N) (hub : Nat) :
    (rnStep e now fs p n hub).recheck = n.recheck := by
  unfold rnStep
  split
  · rfl
  · dsimp only
    split
    · simp
    · unfold N.helloTo; split <;> simp [N.markHello]

/-- A member's `renew` leaves the recheck table (only a hub's renewal pushes a delta). -/
theorem renew_recheck_member (e : Env) (n : N) (now : Nat) (fs p : Bool) (hm : n.isHub = false) :
    (N.renew e n now fs p).recheck = n.recheck := by
  rw [renew_eq']
  have hb : ∀ (c : Prop) [Decidable c], (if c then n.bumpRecord else n).recheck = n.recheck ∧
      (if c then n.bumpRecord else n).isHub = false := by
    intro c _
    by_cases h : c
    · rw [if_pos h]; exact ⟨bumpRecord_recheck n, (bumpRecord_tm n).2.1.trans hm⟩
    · rw [if_neg h]; exact ⟨rfl, hm⟩
  have e1 : (rnPre n p).1.recheck = n.recheck ∧ (rnPre n p).1.isHub = false := by
    unfold rnPre
    dsimp only
    exact hb _
  have e2 : rnPush e (rnPre n p).1 now = (rnPre n p).1 := by
    unfold rnPush
    simp [e1.2]
  rw [e2]
  exact foldl_inv (fun (y : N) => y.recheck = n.recheck) (rnStep e now fs (rnPre n p).2) (rnPre n p).1.boot (rnPre n p).1
    (fun b a hb => by rw [rnStep_recheck]; exact hb) e1.1

/-- **A late tick at a member opens the quiet window and defers every waiting removal again.** A member whose tick
comes later than `WAKE_GAP` after its deadline reads it as a suspension: the window opens, `QUIET` from the call, the
window's grace is dropped, and every waiting removal is due at the window's end with its extra look not begun (the
reference model's rule, kept by #284). So a host slack above `WAKE_GAP` at every tick keeps a member's removals
waiting (`recheckDue_waits`): the late-host hypothesis of the awareness bound. -/
theorem late_tick_reopens (e : Env) (n : N) (now t : Nat) (hm : n.isHub = false) (ht : n.nextTick = some t)
    (hlate : WAKE_GAP < now - t) :
    (N.otTickPre e n now).quietUntil = satAdd now QUIET ∧ (N.otTickPre e n now).regrace = false ∧
    (N.otTickPre e n now).recheck =
      n.recheck.map (fun (p : Nat × (Nat × Bool)) => (p.1, (satAdd now QUIET, false))) := by
  unfold N.otTickPre
  simp only [ht, hm, Bool.not_false, decide_true, Bool.true_and, hlate, if_true]
  have h := renew_qu e (n.beginQuiet now 0) now true false
  have hr := renew_recheck_member e (n.beginQuiet now 0) now true false ((beginQuiet_tm n now 0).2.1.trans hm)
  refine ⟨?_, ?_, ?_⟩
  · rw [h.1]; exact (beginQuiet_window n now 0).1
  · rw [h.2]; exact (beginQuiet_window n now 0).2
  · rw [hr]; exact beginQuiet_late n now

end Pinc.Membership.Cmp

#audit_axioms Pinc.Membership.Cmp.heal_keeps_waiting
#audit_axioms Pinc.Membership.Cmp.heal_then_removed
#audit_axioms Pinc.Membership.Cmp.heal_then_gone
#audit_axioms Pinc.Membership.Cmp.late_tick_reopens
