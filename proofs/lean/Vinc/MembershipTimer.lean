import Vinc.MembershipWindow
import Vinc.MembershipSuspAll
import Vinc.MembershipCurrent

/-!
# Completeness over a run: the timer schedule, the hub's lease expiry and its Down delta

The host asks `poll_timeout` for the next deadline and calls `on_timeout`; the tick runs in the call that finds its
deadline `next_tick` passed. This file proves, over any sequence of the host's calls (`Call`, `runCalls`), the hub side
of the awareness chain of `awareness_budget`, with one hypothesis about timing, the host's:

* `*_tm`: no call but `on_timeout` writes `next_tick`, no call writes `is_hub` or `born`, and no call but `leave`
  writes `leaving` (`step_tm`, `step_fields`). So no input postpones a tick.
* `pollTimeout_le`: the deadline `poll_timeout` returns is never later than the tick deadline.
* `onTimeout_ticks`: a call of `on_timeout` at or after the tick deadline (on a node that is not leaving) runs the tick
  and sets the next deadline one tick period (`HUB_TICK` for a hub, `NODE_TICK` for a member) after the call;
  `onTimeout_waits`: an earlier call leaves the deadline as it is.
* `tick_window` (the timer schedule): under the host's one obligation (`Timely σ`: each call comes no later than `σ`
  after the deadline `poll_timeout` returned before it), a node that does not leave runs its tick in every window
  `(T, T + period + σ]` that the run outlasts.
* `runCalls_held`: after a member crashed at `t0` (`Crash t0 m`: no evidence of it after `t0`, no frame from it, no
  carrier return), no call renews its lease past `t0` (the roster through every call: `RS[...]`, `onDown_held`,
  `onFrame_held`, ...).
* `hub_lease_gone` (property 2, hub side, over a run): a hub drops that lease at a tick at an instant in
  `(t0 + LEASE, t0 + LEASE + HUB_TICK + σ]`; `hub_hands_down`: that call hands `Delta(m, record, Down)` to the session
  of every attached hub (`hubTick_hands_down`), unless the lease was dropped before.
* `heal_postpones`: what the chain still needs. A member that hears a hub again after longer than the host's give-up
  bound for it opens the quiet window again, and a removal the window deferred waits for its end: `awareness_budget`'s
  link `q ≤ taud + QUIET` holds only when no quiet window opens at the member after the Down arrives.
  `late_tick_reopens`: a member's tick later than `WAKE_GAP` after its deadline opens the window too, so the host's
  slack at a member must stay within `WAKE_GAP`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership.Cmp
open Vinc.Membership
open Vinc.MemInc

/-! ## The timer fields through every function -/

@[simp] theorem ite_nextTick (c : Prop) [Decidable c] (a b : N) :
    (if c then a else b).nextTick = if c then a.nextTick else b.nextTick := by split <;> rfl
@[simp] theorem ite_leaving (c : Prop) [Decidable c] (a b : N) :
    (if c then a else b).leaving = if c then a.leaving else b.leaving := by split <;> rfl
@[simp] theorem ite_born' (c : Prop) [Decidable c] (a b : N) :
    (if c then a else b).born = if c then a.born else b.born := by split <;> rfl

/-- `b` has `a`'s tick deadline, role, leave flag and start time (a conjunction, so that `simp` uses each part). -/
notation "TM[" a ", " b "]" => N.nextTick b = N.nextTick a ∧ N.isHub b = N.isHub a ∧ N.leaving b = N.leaving a ∧ N.born b = N.born a

theorem foldl_tm {α : Type} (f : N → α → N) (L : List α) (n : N) (h : ∀ b a, TM[b, f b a]) : TM[n, L.foldl f n] := by
  induction L generalizing n with
  | nil => simp
  | cons x r ih =>
    simp only [List.foldl_cons]
    obtain ⟨a1, a2, a3, a4⟩ := ih (f n x)
    obtain ⟨b1, b2, b3, b4⟩ := h n x
    exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4⟩

theorem foldl_tm2 {α β : Type} (f : N × β → α → N × β) (L : List α) (a : N × β) (h : ∀ b x, TM[b.1, (f b x).1]) :
    TM[a.1, (L.foldl f a).1] := by
  induction L generalizing a with
  | nil => simp
  | cons x r ih =>
    simp only [List.foldl_cons]
    obtain ⟨a1, a2, a3, a4⟩ := ih (f a x)
    obtain ⟨b1, b2, b3, b4⟩ := h a x
    exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4⟩

theorem foldl_tm3 {α β γ : Type} (f : N × β × γ → α → N × β × γ) (L : List α) (a : N × β × γ)
    (h : ∀ b x, TM[b.1, (f b x).1]) : TM[a.1, (L.foldl f a).1] := by
  induction L generalizing a with
  | nil => simp
  | cons x r ih =>
    simp only [List.foldl_cons]
    obtain ⟨a1, a2, a3, a4⟩ := ih (f a x)
    obtain ⟨b1, b2, b3, b4⟩ := h a x
    exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4⟩

theorem forKeys_tm (ks : List Nat) (f : Nat → N → N) (n : N) (h : ∀ k b, TM[b, f k b]) : TM[n, forKeys ks f n] :=
  foldl_tm _ ks n (fun b a => h a b)

/-- Close a goal `TM[n, f ...]` after unfolding `f`: `simp` with the lemmas already proved, splitting the `if`s and
`match`es it cannot see through, with the loops discharged by the same tactic on their body. -/
macro "tm_tac" : tactic => `(tactic| first
  | (simp (disch := (intro _ _; first | (simp; done) | (repeat' split; all_goals simp))) [foldl_tm, foldl_tm2, foldl_tm3, forKeys_tm]; done)
  | ((try dsimp only)
     repeat' split
     all_goals simp (disch := (intro _ _; first | (simp; done) | (repeat' split; all_goals simp))) [foldl_tm, foldl_tm2, foldl_tm3, forKeys_tm]))

@[simp] theorem trace_tm (n : N) (t : Tr) : TM[n, n.trace t] := by unfold N.trace; split <;> (try split) <;> simp
@[simp] theorem emit_tm (n : N) (e : Ev) : TM[n, n.emit e] := by unfold N.emit; split <;> simp
@[simp] theorem tx_tm (e : Env) (n : N) (p : Nat) (r : Route) (f : NFrame) : TM[n, (N.tx e n p r f).1] := by
  unfold N.tx; split <;> simp
@[simp] theorem deltaTo_tm (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : TM[n, N.deltaTo e n p m rc a] := by
  unfold N.deltaTo; simp
@[simp] theorem bc_tm (n : N) (b : Bc) : TM[n, n.bc b] := ⟨rfl, rfl, rfl, rfl⟩
@[simp] theorem close_tm (n : N) (p : Nat) (r : CloseR) : TM[n, n.close p r] := ⟨rfl, rfl, rfl, rfl⟩
@[simp] theorem beginQuiet_tm (n : N) (now cause : Nat) : TM[n, n.beginQuiet now cause] := by unfold N.beginQuiet; simp
@[simp] theorem bump_tm (n : N) : TM[n, n.bump] := by unfold N.bump; simp
@[simp] theorem homeDelta_tm (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : TM[n, N.homeDelta e n m rc a] := by
  unfold N.homeDelta; tm_tac
@[simp] theorem refreshLocal_tm (e : Env) (n : N) (now : Nat) : TM[n, N.refreshLocal e n now] := by
  unfold N.refreshLocal; simp
@[simp] theorem helloTo_tm (e : Env) (n : N) (peer : Nat) (snap : Bool) : TM[n, N.helloTo e n peer snap] := by
  unfold N.helloTo; split <;> simp
@[simp] theorem markHello_tm (n : N) (hub now : Nat) : TM[n, n.markHello hub now] := by unfold N.markHello; simp
@[simp] theorem bumpRecord_tm (n : N) : TM[n, n.bumpRecord] := by unfold N.bumpRecord; split <;> simp
@[simp] theorem rttSample_tm (n : N) (hub r : Nat) : TM[n, n.rttSample hub r] := by unfold N.rttSample; simp

/-! ### The view -/

@[simp] theorem removeFromView_tm (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (ex : Bool) :
    TM[n, (N.removeFromView e n now m cur src ex).1] := by
  unfold N.removeFromView; tm_tac

@[simp] theorem rcOldVer_tm (n : N) (m : Nat) (best : Rec) (old : Option (Nat × List Nat)) : TM[n, n.rcOldVer m best old] := by
  unfold N.rcOldVer; tm_tac
@[simp] theorem rcOldBoth_tm (n : N) (m : Nat) (best : Rec) (old : Option (Nat × List Nat)) : TM[n, n.rcOldBoth m best old] := by
  unfold N.rcOldBoth; tm_tac
@[simp] theorem rcVer_tm (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : TM[n, (n.rcVer m best c).1] := by
  unfold N.rcVer; tm_tac
@[simp] theorem rcTh_tm (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : TM[n, (n.rcTh m best c).1] := by
  unfold N.rcTh; tm_tac
@[simp] theorem rcSame_tm (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : TM[n, (n.rcSame m best c).1] := by
  unfold N.rcSame; tm_tac
@[simp] theorem rcNewer_tm (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : TM[n, (n.rcNewer m best c).1] := by
  unfold N.rcNewer; tm_tac
@[simp] theorem rcFresh_tm (n : N) (m : Nat) (best : Rec) : TM[n, (n.rcFresh m best).1] := by
  unfold N.rcFresh; tm_tac
@[simp] theorem rcArm_tm (n : N) (m : Nat) (best : Rec) (cur : Option ViewEntry) : TM[n, (n.rcArm m best cur).1] := by
  unfold N.rcArm; tm_tac
@[simp] theorem rcAfter_tm (e : Env) (n : N) (m : Nat) (best : Rec) (absent : Bool) (cur : Option ViewEntry) :
    TM[n, (N.rcAfter e n m best absent cur).1] := by
  unfold N.rcAfter N.rcSusp; tm_tac
@[simp] theorem recomputeOne_tm (e : Env) (n : N) (now m : Nat) : TM[n, (N.recomputeOne e n now m).1] := by
  rw [recomputeOne_eq]; unfold N.recomputeOneS; dsimp only; split <;> simp
@[simp] theorem recheckNow_tm (e : Env) (n : N) (now : Nat) : TM[n, N.recheckNow e n now] := by
  unfold N.recheckNow; tm_tac
@[simp] theorem adEnsure_tm (n : N) (hub : Nat) : TM[n, (n.adEnsure hub).1] := by unfold N.adEnsure; tm_tac
@[simp] theorem adEntries_tm (n : N) (hub m : Nat) (rc : Rec) (a : Alive) : TM[n, n.adEntries hub m rc a] := by
  unfold N.adEntries N.adDown; tm_tac
@[simp] theorem applyDeltaCore_tm (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) :
    TM[n, N.applyDeltaCore e n now hub m rc a] := by
  rw [applyDeltaCore_eq]; unfold N.applyDeltaCoreS; tm_tac
@[simp] theorem pushDelta_tm (e : Env) (n : N) (now m : Nat) (rc : Rec) (a : Alive) : TM[n, N.pushDelta e n now m rc a] := by
  unfold N.pushDelta; tm_tac
@[simp] theorem renew_tm (e : Env) (n : N) (now : Nat) (fs p : Bool) : TM[n, N.renew e n now fs p] := by
  unfold N.renew; tm_tac

@[simp] theorem onSelfEntry_tm (e : Env) (n : N) (now hub : Nat) (rc : Rec) (a : Alive) :
    TM[n, N.onSelfEntry e n now hub rc a] := by
  unfold N.onSelfEntry
  split
  · simp
  · dsimp only
    generalize observe (n.trace (Tr.selfDelta hub)).loc (n.trace (Tr.selfDelta hub)).inc rc.inc = r
    rcases r with x | ⟨b, i', l'⟩
    · repeat' split
      all_goals simp
    · cases b <;> (repeat' split) <;> simp
@[simp] theorem applyDelta_tm (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) :
    TM[n, N.applyDelta e n now hub m rc a] := by
  unfold N.applyDelta; tm_tac
@[simp] theorem applyDown_tm (e : Env) (n : N) (now hub member inc : Nat) : TM[n, N.applyDown e n now hub member inc] := by
  unfold N.applyDown; simp
@[simp] theorem dropGone_tm (n : N) (hub round : Nat) : TM[n, n.dropGone hub round] := by unfold N.dropGone; tm_tac
@[simp] theorem markAbsent_tm (e : Env) (n : N) (now hub round : Nat) : TM[n, (N.markAbsent e n now hub round).1] := by
  unfold N.markAbsent
  apply foldl_tm2
  intro b x
  obtain ⟨b1, b2⟩ := b
  simp only []
  repeat' split
  all_goals simp
@[simp] theorem markViewAbsent_tm (e : Env) (n : N) (now hub round : Nat) :
    TM[n, (N.markViewAbsent e n now hub round).1] := by
  unfold N.markViewAbsent
  apply foldl_tm2
  intro b x
  obtain ⟨b1, b2⟩ := b
  simp only []
  repeat' split
  all_goals simp
@[simp] theorem snapAbsent_tm (e : Env) (n : N) (now hub round : Nat) : TM[n, (N.snapAbsent e n now hub round).1] := by
  simp only [N.snapAbsent]
  split <;> simp
@[simp] theorem applySnap_tm (e : Env) (n : N) (now hub : Nat) (partial_ more : Bool) (es : List (Nat × Rec)) :
    TM[n, N.applySnap e n now hub partial_ more es] := by
  rw [applySnap_eq]
  have h2 : TM[n, (hubEnsure n hub).1] := by unfold hubEnsure; tm_tac
  rcases hE : hubEnsure n hub with ⟨n1, ok⟩
  rw [hE] at h2
  simp only [] at h2 ⊢
  by_cases hok : ok = true
  · simp only [hok, Bool.not_true, if_false, Bool.false_eq_true]
    have h3 : TM[n1, (snapRound n1 hub).1] := by unfold snapRound; tm_tac
    rcases hR : snapRound n1 hub with ⟨n2, round⟩
    rw [hR] at h3
    simp only [] at h3 ⊢
    generalize hn3 : (if (!n2.isHub && n2.primary == some hub) = true then
        ({ n2 with homeOk := some hub, homeSeen := true } : N) else n2) = n3
    have h4 : TM[n2, n3] := by rw [← hn3]; split <;> simp
    have h5 : TM[n3, (List.foldl (snapStep e now hub round) (n3, false, 0) es).1] :=
      foldl_tm3 (snapStep e now hub round) es (n3, false, 0) (fun b x => by
        obtain ⟨b1, c, k⟩ := b; unfold snapStep; dsimp only; repeat' split
        all_goals simp)
    have h6 : TM[(List.foldl (snapStep e now hub round) (n3, false, 0) es).1,
        snapFin e now hub partial_ more round (List.foldl (snapStep e now hub round) (n3, false, 0) es)] := by
      generalize List.foldl (snapStep e now hub round) (n3, false, 0) es = A
      obtain ⟨b1, c, k⟩ := A; unfold snapFin; dsimp only; repeat' split
      all_goals simp [N.bc]
    simp only [h6, h5, h4, h3, h2, and_self]
  · have : ok = false := by simpa using hok
    simp only [this, Bool.not_false, if_true]
    exact h2
@[simp] theorem sweepAbsent_tm (e : Env) (n : N) (now : Nat) : TM[n, N.sweepAbsent e n now] := by
  rw [sweepAbsent_eq]
  have h : TM[n, (n.hv.keys.foldl (swOut e now) (n, false)).1] := by
    apply foldl_tm2
    intro b hub
    unfold swOut
    apply foldl_tm2
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
@[simp] theorem reselect_tm (e : Env) (n : N) (now : Nat) : TM[n, N.reselect e n now] := by unfold N.reselect; tm_tac

/-! ### The hub -/

@[simp] theorem sendSnapshot_tm (e : Env) (n : N) (now peer : Nat) : TM[n, N.sendSnapshot e n now peer] := by
  unfold N.sendSnapshot; tm_tac
@[simp] theorem sendFloor_tm (e : Env) (n : N) (peer : Nat) : TM[n, N.sendFloor e n peer] := by unfold N.sendFloor; tm_tac
/-- `on_hello` in three pieces: the homed set and the held subscriptions, the attachment and the answer, the roster. -/
def N.hlHomed (n : N) (peer : Nat) (homed : Bool) : N :=
  let n := if homed && !n.isBoot peer then
      (if n.homed.len < MAX_TABLE then { n with homed := n.homed.ins peer } else n)
    else { n with homed := n.homed.del peer }
  if n.downed.has peer then (N.bc { n with downed := n.downed.erase peer } (.restore peer)) else n

def N.hlAttach (e : Env) (n : N) (now peer : Nat) (snap : Bool) : N :=
  let newAttach := !n.attached.has peer
  let n := if newAttach && n.attached.len < MAX_TABLE then { n with attached := n.attached.ins peer } else n
  let n := if newAttach then N.sendFloor e (n.trace (.attached peer)) peer else n
  if snap || newAttach then N.sendSnapshot e n now peer else (N.tx e n peer .session .ack).1

def N.hlRoster (e : Env) (n : N) (now peer : Nat) (rc : Rec) : N :=
  match n.roster.get? peer with
  | some held =>
    if rc.inc < held.rc.inc then
      let n := { n with roster := n.roster.modify peer (fun l => { l with renewed := now }) }
      N.deltaTo e n peer peer held.rc .alive
    else if held.rc == rc then
      { n with roster := n.roster.modify peer (fun l => { l with renewed := now }) }
    else if MAX_TABLE ≤ n.roster.len && !n.roster.has peer then n
    else
      let n := { n with roster := n.roster.insert peer ⟨rc, now⟩ }
      N.pushDelta e n now peer rc .alive
  | none =>
    if MAX_TABLE ≤ n.roster.len then n
    else
      let n := { n with roster := n.roster.insert peer ⟨rc, now⟩ }
      N.pushDelta e n now peer rc .alive

theorem onHello_eq3 (e : Env) (n : N) (now peer : Nat) (rc : Rec) (snap homed : Bool) :
    N.onHello e n now peer rc snap homed = N.hlRoster e (N.hlAttach e (N.hlHomed n peer homed) now peer snap) now peer rc := rfl

@[simp] theorem hlHomed_tm (n : N) (peer : Nat) (homed : Bool) : TM[n, N.hlHomed n peer homed] := by
  unfold N.hlHomed; dsimp only; repeat' split
  all_goals simp
@[simp] theorem hlAttach_tm (e : Env) (n : N) (now peer : Nat) (snap : Bool) : TM[n, N.hlAttach e n now peer snap] := by
  unfold N.hlAttach; dsimp only; repeat' split
  all_goals simp
@[simp] theorem hlRoster_tm (e : Env) (n : N) (now peer : Nat) (rc : Rec) : TM[n, N.hlRoster e n now peer rc] := by
  unfold N.hlRoster; tm_tac
@[simp] theorem onHello_tm (e : Env) (n : N) (now peer : Nat) (rc : Rec) (snap homed : Bool) :
    TM[n, N.onHello e n now peer rc snap homed] := by
  rw [onHello_eq3]; simp
@[simp] theorem hubDown_tm (e : Env) (n : N) (now member : Nat) (cause : Cause) : TM[n, N.hubDown e n now member cause] := by
  unfold N.hubDown; tm_tac
@[simp] theorem onDown_tm (e : Env) (n : N) (now m inc : Nat) (pf : Proof) : TM[n, N.onDown e n now m inc pf] := by
  unfold N.onDown; tm_tac
@[simp] theorem carrierReturn_tm (e : Env) (n : N) (now member : Nat) : TM[n, N.carrierReturn e n now member] := by
  unfold N.carrierReturn; tm_tac
@[simp] theorem scheduleConfirm_tm (n : N) (now at_ : Nat) : TM[n, n.scheduleConfirm now at_] := by
  unfold N.scheduleConfirm; simp
@[simp] theorem confirm_tm (e : Env) (n : N) (now m : Nat) (sp : Susp) (l : Lease) : TM[n, N.confirm e n now m sp l] := by
  unfold N.confirm; simp
@[simp] theorem rewatch_tm (n : N) (now : Nat) (sp : Susp) : TM[n, n.rewatch now sp] := by unfold N.rewatch; tm_tac
@[simp] theorem newSusp_tm (e : Env) (n : N) (now m since : Nat) (ev : Option Evid) : TM[n, N.newSusp e n now m since ev] := by
  unfold N.newSusp; tm_tac
@[simp] theorem carrierWatch_tm (e : Env) (n : N) (now m : Nat) : TM[n, N.carrierWatch e n now m] := by
  unfold N.carrierWatch; tm_tac
@[simp] theorem carrierGone_tm (e : Env) (n : N) (now member : Nat) : TM[n, N.carrierGone e n now member] := by
  unfold N.carrierGone; tm_tac
@[simp] theorem hubTick_tm (e : Env) (n : N) (now : Nat) : TM[n, N.hubTick e n now] := by
  rw [hubTick_eq_cp]; dsimp only
  have h1 : TM[n, forKeys n.roster.keys (N.htBody1 e now) n] := by
    apply forKeys_tm; intro k b; unfold N.htBody1 N.htRefresh N.htAfter; tm_tac
  generalize forKeys n.roster.keys (N.htBody1 e now) n = n1 at h1 ⊢
  have h2 : TM[n1, forKeys n1.downed.keys (N.htBody2 e now) n1] := by
    apply forKeys_tm; intro k b; unfold N.htBody2; tm_tac
  simp only [h2, h1, and_self]

/-! ### Timers, frames, sessions -/

@[simp] theorem dropPeer_tm (e : Env) (n : N) (now peer : Nat) : TM[n, N.dropPeer e n now peer] := by
  unfold N.dropPeer; dsimp only; repeat' split
  all_goals simp
theorem tm_bumpMatch {F : N × Bool} {n0 : N} (h : TM[n0, F.1]) :
    TM[n0, match F with | (n, ch) => if ch = true then n.bump else n] := by
  obtain ⟨f1, f2⟩ := F
  dsimp only at h ⊢
  split <;> simp [h]

@[simp] theorem pulseRefresh_tm (e : Env) (n : N) (now : Nat) : TM[n, N.pulseRefresh e n now] := by
  unfold N.pulseRefresh
  apply foldl_tm
  intro b hub
  (try dsimp only)
  repeat' split
  all_goals simp
@[simp] theorem sampleSessionRtts_tm (e : Env) (n : N) (now : Nat) : TM[n, N.sampleSessionRtts e n now] := by
  rw [sampleSessionRtts_eq]
  have h : TM[n, N.ssFold e n now] := by
    unfold N.ssFold
    apply foldl_tm
    intro b hub
    repeat' split
    all_goals simp
  dsimp only
  split <;> simp [h]
@[simp] theorem dropStaleHubs_tm (e : Env) (n : N) (now : Nat) : TM[n, N.dropStaleHubs e n now] := by
  unfold N.dropStaleHubs
  dsimp only
  split
  · simp
  · refine tm_bumpMatch (foldl_tm2 _ _ _ (fun b x => ?_))
    obtain ⟨b1, c1⟩ := b
    dsimp only
    split
    · simp
    · split
      · simp
      · refine (fun h => ?_) (foldl_tm2 (fun (b : N × Bool) m => let (n', c) := N.recomputeOne e b.1 now m; (n', b.2 || c))
          (match b1.hv.get? x with | some c => c.entries.keys | none => []) (b1, c1) (fun b x => by simp))
        rename_i copy hc
        have h3 := foldl_tm2 (fun (b : N × Bool) m => let (n', c) := N.recomputeOne e b.1 now m; (n', b.2 || c))
          copy.entries.keys
          ((if (({ b1 with hv := b1.hv.erase x } : N).trace (.hubStale x)).up.has x &&
              decide (HUB_STALE ≤ now - ((({ b1 with hv := b1.hv.erase x } : N).trace (.hubStale x)).heard.get? x).getD 0) then
              (({ b1 with hv := b1.hv.erase x } : N).trace (.hubStale x)).close x .stale
            else ({ b1 with hv := b1.hv.erase x } : N).trace (.hubStale x)), c1) (fun b x => by simp)
        simp only [] at h3 ⊢
        refine ⟨h3.1.trans ?_, h3.2.1.trans ?_, h3.2.2.1.trans ?_, h3.2.2.2.trans ?_⟩ <;> split <;> simp
@[simp] theorem stHello_tm (e : Env) (now : Nat) (n : N) : TM[n, N.stHello e now n] := by
  unfold N.stHello; apply forKeys_tm; intro k b; tm_tac
@[simp] theorem slowTick_tm (e : Env) (n : N) (now : Nat) : TM[n, N.slowTick e n now] := by
  rw [slowTick_eq]; dsimp only; split <;> simp
@[simp] theorem tickRecheck_tm (e : Env) (n : N) (now : Nat) : TM[n, N.tickRecheck e n now] := by
  unfold N.tickRecheck; tm_tac
@[simp] theorem tickMid_tm (e : Env) (n : N) (now : Nat) : TM[n, N.tickMid e n now] := by
  unfold N.tickMid
  have h := tickRecheck_tm e n now
  generalize N.tickRecheck e n now = n1 at h ⊢
  repeat' split
  all_goals simp [h]
@[simp] theorem tick_tm (e : Env) (n : N) (now : Nat) : TM[n, N.tick e n now] := by
  rw [tick_eq']; dsimp only; split <;> simp
@[simp] theorem otA_tm (e : Env) (n : N) (now : Nat) : TM[n, N.otA e n now] := by
  unfold N.otA; dsimp only; split <;> simp
@[simp] theorem otB_tm (e : Env) (n : N) (now : Nat) : TM[n, N.otB e n now] := by
  unfold N.otB; tm_tac
@[simp] theorem otPre_tm (e : Env) (n : N) (now : Nat) : TM[n, N.otPre e n now] := by
  unfold N.otPre; tm_tac
@[simp] theorem tkPre_tm (e : Env) (n : N) (now : Nat) : TM[n, N.tkPre e n now] := by
  unfold N.tkPre N.tkRecheck
  have h : TM[n, (if !n.recheck.isEmpty && n.quietUntil ≤ now then
      (if n.regrace then N.recheckNow e { n with regrace := false } now
       else { n with regrace := true, quietUntil := satAdd now RECHECK_GAP }) else n)] := by
    repeat' split
    all_goals simp
  generalize (if !n.recheck.isEmpty && n.quietUntil ≤ now then _ else n) = n1 at h ⊢
  dsimp only
  repeat' split
  all_goals simp [h]

@[simp] theorem ofHub1_tm (e : Env) (n : N) (now peer : Nat) : TM[n, N.ofHub1 e n now peer] := by
  unfold N.ofHub1; dsimp only; split <;> simp
@[simp] theorem ofHub2_tm (e : Env) (n : N) (now peer : Nat) (isAckSnap : Bool) (t0 : Option Nat) :
    TM[n, N.ofHub2 e n now peer isAckSnap t0] := by
  unfold N.ofHub2; tm_tac
@[simp] theorem ofHub_tm (e : Env) (n : N) (now peer : Nat) (f : NFrame) : TM[n, N.ofHub e n now peer f] := by
  unfold N.ofHub; dsimp only; split <;> simp
@[simp] theorem ofMid_tm (e : Env) (n : N) (now peer : Nat) (f : NFrame) (fromHub : Bool) :
    TM[n, N.ofMid e n now peer f fromHub] := by
  unfold N.ofMid; dsimp only; repeat' split
  all_goals simp
@[simp] theorem ofDisp_tm (e : Env) (n : N) (now peer : Nat) (f : NFrame) (fromHub : Bool) :
    TM[n, N.ofDisp e n now peer f fromHub] := by
  unfold N.ofDisp; cases f <;> dsimp only <;> repeat' split
  all_goals simp
@[simp] theorem onFrame_tm (e : Env) (n : N) (now peer : Nat) (f : NFrame) : TM[n, N.onFrame e n now peer f] := by
  rw [onFrame_eq]; split
  · simp
  · dsimp only; simp
@[simp] theorem onBytes_tm (e : Env) (n : N) (now peer : Nat) (fs : List NFrame) (bad : Bool) :
    TM[n, N.onBytes e n now peer fs bad] := by
  unfold N.onBytes
  have h := foldl_tm (fun n f => N.onFrame e n now peer f) (fs.take MAX_FRAMES_PER_CALL) n (fun b a => by simp)
  dsimp only
  split <;> simp [h]
@[simp] theorem sessionUp_tm (e : Env) (n : N) (now peer : Nat) (incoming : Bool) : TM[n, N.sessionUp e n now peer incoming] := by
  unfold N.sessionUp; dsimp only; repeat' split
  all_goals simp
@[simp] theorem sessionDown_tm (e : Env) (n : N) (now peer code : Nat) : TM[n, N.sessionDown e n now peer code] := by
  unfold N.sessionDown; dsimp only; repeat' split
  all_goals simp
@[simp] theorem snapshotTo_tm (e : Env) (n : N) (now peer : Nat) : TM[n, N.snapshotTo e n now peer] := by
  unfold N.snapshotTo; split <;> simp
@[simp] theorem setMaxFrame_tm (n : N) (mb : Nat) : TM[n, n.setMaxFrame mb] := ⟨rfl, rfl, rfl, rfl⟩
@[simp] theorem addressChanged_tm (n : N) (now : Nat) : TM[n, n.addressChanged now] := ⟨rfl, rfl, rfl, rfl⟩
@[simp] theorem drained_tm (n : N) : TM[n, n.drained] := ⟨rfl, rfl, rfl, rfl⟩

theorem revoke_tm (e : Env) (n n' : N) (now member : Nat) (h : N.revoke e n now member = some n') : TM[n, n'] := by
  have hc : ¬ (n.revoked.has member = false ∧ MAX_TABLE ≤ n.revoked.len) := by
    intro hh; rw [(revoke_none_iff e n now member).2 hh] at h; cases h
  rw [revoke_eq e n now member hc] at h
  injection h with h; subst h
  have h1 : TM[n, n.rvPre member] := by unfold N.rvPre; simp
  have h2 : TM[n.rvPre member, N.rvMembers e (n.rvPre member) now member] := by unfold N.rvMembers; tm_tac
  have h3 : TM[N.rvMembers e (n.rvPre member) now member,
      N.rvRoster e (N.rvMembers e (n.rvPre member) now member) now member] := by unfold N.rvRoster; tm_tac
  have h4 : ∀ x : N, TM[x, x.rvEnd member] := by intro x; unfold N.rvEnd; dsimp only; split <;> simp
  dsimp only
  simp only [h4, h3, h2, h1, and_self]

/-- `leave` only raises the leave flag. -/
theorem leave_tm (n : N) : n.leave.nextTick = n.nextTick ∧ n.leave.isHub = n.isHub ∧ n.leave.born = n.born ∧
    n.leave.leaving = true := by
  unfold N.leave
  have := forKeys_tm n.up.keys (fun p n => n.close p .leave) { n with leaving := true } (fun k b => by simp)
  exact ⟨this.1, this.2.1, this.2.2.2, this.2.2.1⟩

/-! ## `on_timeout` and `poll_timeout` -/

/-- The tick period of a node. -/
def period (n : N) : Nat := if n.isHub then HUB_TICK else NODE_TICK

theorem otTickPre_nextTick (e : Env) (n : N) (now : Nat) :
    (N.otTickPre e n now).nextTick = some (satAdd now (period n)) ∧
    (N.otTickPre e n now).isHub = n.isHub ∧ (N.otTickPre e n now).leaving = n.leaving ∧
    (N.otTickPre e n now).born = n.born := by
  unfold N.otTickPre period
  repeat' split
  all_goals simp_all

/-- `on_timeout` writes none of the role, the start time and the leave flag. -/
theorem onTimeout_fields (e : Env) (n : N) (now : Nat) :
    (N.onTimeout e n now).isHub = n.isHub ∧ (N.onTimeout e n now).born = n.born ∧ (N.onTimeout e n now).leaving = n.leaving := by
  rw [onTimeout_split]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · dsimp only
    have h1 := otPre_tm e n now
    split
    · unfold N.otTick
      have h2 := tick_tm e (N.otTickPre e (N.otPre e n now) now) now
      obtain ⟨-, h3, h4, h5⟩ := otTickPre_nextTick e (N.otPre e n now) now
      exact ⟨h2.2.1.trans (h3.trans h1.2.1), h2.2.2.2.trans (h5.trans h1.2.2.2), h2.2.2.1.trans (h4.trans h1.2.2.1)⟩
    · exact ⟨h1.2.1, h1.2.2.2, h1.2.2.1⟩

/-- **The tick runs when its deadline has passed.** A call of `on_timeout` at or after the tick deadline, on a node that
is not leaving, is the tick branch of the code, and the next deadline is one tick period after the call. -/
theorem onTimeout_ticks (e : Env) (n : N) (now : Nat) (hl : n.leaving = false) (hd : n.nextTick.getD 0 ≤ now) :
    N.onTimeout e n now = N.otTick e (N.otPre e n now) now ∧
    (N.onTimeout e n now).nextTick = some (satAdd now (period n)) := by
  have h1 := otPre_tm e n now
  have heq : N.onTimeout e n now = N.otTick e (N.otPre e n now) now := by
    rw [onTimeout_split, if_neg (by simp [hl])]
    dsimp only
    rw [if_pos (by rw [h1.1]; exact hd)]
  refine ⟨heq, ?_⟩
  rw [heq]
  unfold N.otTick
  have h2 := tick_tm e (N.otTickPre e (N.otPre e n now) now) now
  obtain ⟨h3, -⟩ := otTickPre_nextTick e (N.otPre e n now) now
  rw [h2.1, h3]
  unfold period
  rw [h1.2.1]

/-- A call of `on_timeout` before the tick deadline leaves the deadline as it is. -/
theorem onTimeout_waits (e : Env) (n : N) (now : Nat) (hd : now < n.nextTick.getD 0) :
    TM[n, N.onTimeout e n now] := by
  rw [onTimeout_split]
  split
  · simp
  · dsimp only
    have h1 := otPre_tm e n now
    rw [if_neg (by rw [h1.1]; omega)]
    exact h1

/-- The deadline `poll_timeout` returns is never later than the tick deadline (the start time before the first tick). -/
theorem pollTimeout_le (n : N) : N.pollTimeout n ≤ n.nextTick.getD n.born := by
  unfold N.pollTimeout
  dsimp only
  split <;> omega

/-! ## A run of the host's calls -/

/-- A call of the host into the machine, with the instant of the host's clock when it is made. -/
inductive Call where
  | onBytes (e : Env) (now peer : Nat) (fs : List NFrame) (bad : Bool)
  | onFrame (e : Env) (now peer : Nat) (f : NFrame)
  | onTimeout (e : Env) (now : Nat)
  | sessionUp (e : Env) (now peer : Nat) (incoming : Bool)
  | sessionDown (e : Env) (now peer code : Nat)
  | leave (now : Nat)
  | revoke (e : Env) (now member : Nat)
  | addressChanged (now : Nat)
  | snapshotTo (e : Env) (now peer : Nat)
  | setMaxFrame (now mb : Nat)
  | carrierReturn (e : Env) (now member : Nat)
  | carrierGone (e : Env) (now member : Nat)
  | drained (now : Nat)

/-- The instant of a call. -/
def Call.at : Call → Nat
  | .onBytes _ now .. => now
  | .onFrame _ now .. => now
  | .onTimeout _ now => now
  | .sessionUp _ now .. => now
  | .sessionDown _ now .. => now
  | .leave now => now
  | .revoke _ now .. => now
  | .addressChanged now => now
  | .snapshotTo _ now .. => now
  | .setMaxFrame now _ => now
  | .carrierReturn _ now .. => now
  | .carrierGone _ now .. => now
  | .drained now => now

/-- The node after the call (a `revoke` that returns `TableFull` changes nothing). -/
def Call.step : Call → N → N
  | .onBytes e now peer fs bad, n => N.onBytes e n now peer fs bad
  | .onFrame e now peer f, n => N.onFrame e n now peer f
  | .onTimeout e now, n => N.onTimeout e n now
  | .sessionUp e now peer incoming, n => N.sessionUp e n now peer incoming
  | .sessionDown e now peer code, n => N.sessionDown e n now peer code
  | .leave _, n => n.leave
  | .revoke e now member, n => (N.revoke e n now member).getD n
  | .addressChanged now, n => n.addressChanged now
  | .snapshotTo e now peer, n => N.snapshotTo e n now peer
  | .setMaxFrame _ mb, n => n.setMaxFrame mb
  | .carrierReturn e now member, n => N.carrierReturn e n now member
  | .carrierGone e now member, n => N.carrierGone e n now member
  | .drained _, n => n.drained

def Call.isLeave : Call → Bool
  | .leave _ => true
  | _ => false

/-- The node after a sequence of calls. -/
def runCalls (cs : List Call) (n : N) : N := cs.foldl (fun n c => c.step n) n

theorem runCalls_cons (c : Call) (cs : List Call) (n : N) : runCalls (c :: cs) n = runCalls cs (c.step n) := rfl
theorem runCalls_append (a b : List Call) (n : N) : runCalls (a ++ b) n = runCalls b (runCalls a n) := by
  unfold runCalls; rw [List.foldl_append]

/-- **The host's obligation.** Each call comes no later than `σ` after the deadline `poll_timeout` returned after the
previous call: when nothing else happens by then, the host calls `on_timeout`. `σ` is the host's scheduling slack. -/
def Timely (σ : Nat) : N → List Call → Prop
  | _, [] => True
  | n, c :: cs => c.at ≤ N.pollTimeout n + σ ∧ Timely σ (c.step n) cs

theorem Timely.append {σ : Nat} {n : N} {a b : List Call} (h : Timely σ n (a ++ b)) : Timely σ (runCalls a n) b := by
  induction a generalizing n with
  | nil => exact h
  | cons c r ih => exact ih h.2

/-- Every call but `on_timeout` and `leave` keeps the four timer fields. -/
theorem step_tm (c : Call) (n : N) (h1 : ∀ e t, c ≠ .onTimeout e t) (h2 : c.isLeave = false) : TM[n, c.step n] := by
  cases c with
  | onTimeout e t => exact absurd rfl (h1 e t)
  | leave t => simp [Call.isLeave] at h2
  | revoke e now member =>
    simp only [Call.step]
    cases hr : N.revoke e n now member with
    | none => simp
    | some n' => simp only [Option.getD_some]; exact revoke_tm e n n' now member hr
  | _ => simp [Call.step]

/-- Every call but `leave` keeps the role, the start time and the leave flag. -/
theorem step_fields (c : Call) (n : N) (h2 : c.isLeave = false) :
    (c.step n).isHub = n.isHub ∧ (c.step n).born = n.born ∧ (c.step n).leaving = n.leaving := by
  cases c with
  | onTimeout e t => exact onTimeout_fields e n t
  | leave t => simp [Call.isLeave] at h2
  | _ =>
    have := step_tm _ n (fun _ _ h => by cases h) h2
    exact ⟨this.2.1, this.2.2.2, this.2.2.1⟩

theorem runCalls_fields (cs : List Call) (n : N) (h : ∀ c ∈ cs, c.isLeave = false) :
    (runCalls cs n).isHub = n.isHub ∧ (runCalls cs n).born = n.born ∧ (runCalls cs n).leaving = n.leaving := by
  induction cs generalizing n with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons c r ih =>
    rw [runCalls_cons]
    obtain ⟨a1, a2, a3⟩ := ih (c.step n) (fun c' hc => h c' (List.mem_cons_of_mem _ hc))
    obtain ⟨b1, b2, b3⟩ := step_fields c n (h c (List.mem_cons_self ..))
    exact ⟨a1.trans b1, a2.trans b2, a3.trans b3⟩

/-- **The timer schedule over a run.** Along any sequence of calls on which the host keeps its obligation (`Timely σ`)
and the node does not leave, a node whose tick deadline (its start time before the first tick) is at most one tick
period after an instant `T` runs its tick at a call of `on_timeout` at an instant in `(T, T + period + σ]`, provided
the run goes on past that window. No input postpones the tick: every call but `on_timeout` keeps the deadline
(`step_tm`), the deadline `poll_timeout` returns is never later (`pollTimeout_le`), and `on_timeout` at the deadline
runs the tick (`onTimeout_ticks`). The calls before the tick leave a node that is not leaving, has the same role and
whose deadline has passed. -/
theorem tick_window (σ T : Nat) : ∀ (cs : List Call) (n : N), Timely σ n cs → (∀ c ∈ cs, c.isLeave = false) →
    n.leaving = false → n.nextTick.getD n.born ≤ T + period n → (∃ c ∈ cs, T + period n + σ < c.at) →
    ∃ pre e τ post, cs = pre ++ Call.onTimeout e τ :: post ∧ T < τ ∧ τ ≤ T + period n + σ ∧
      (runCalls pre n).leaving = false ∧ (runCalls pre n).isHub = n.isHub ∧ (runCalls pre n).nextTick.getD 0 ≤ τ := by
  intro cs
  induction cs with
  | nil => intro n _ _ _ _ hc; obtain ⟨c, hc, -⟩ := hc; simp at hc
  | cons c cs ih =>
    intro n ht hnl hl hd hc
    obtain ⟨hat, ht'⟩ := ht
    have hpoll := pollTimeout_le n
    have hcat : c.at ≤ T + period n + σ := by omega
    have hrest : ∃ c ∈ cs, T + period n + σ < c.at := by
      obtain ⟨c', hc', hlt⟩ := hc
      rcases List.mem_cons.mp hc' with h | h
      · subst h; omega
      · exact ⟨c', h, hlt⟩
    have hnl' : ∀ c ∈ cs, c.isLeave = false := fun c hc => hnl c (List.mem_cons_of_mem _ hc)
    -- a call that keeps the timer fields: the window carries over to the rest of the run
    have keep : TM[n, c.step n] → ∃ pre e τ post, c :: cs = pre ++ Call.onTimeout e τ :: post ∧ T < τ ∧
        τ ≤ T + period n + σ ∧ (runCalls pre n).leaving = false ∧ (runCalls pre n).isHub = n.isHub ∧
        (runCalls pre n).nextTick.getD 0 ≤ τ := by
      intro htm
      have hp : period (c.step n) = period n := by unfold period; rw [htm.2.1]
      obtain ⟨pre, e, τ, post, h1, h2, h3, h4, h5, h6⟩ := ih (c.step n) ht' hnl' (by rw [htm.2.2.1]; exact hl)
        (by rw [htm.1, htm.2.2.2, hp]; exact hd) (by rw [hp]; exact hrest)
      refine ⟨c :: pre, e, τ, post, by rw [h1]; rfl, h2, by rw [← hp]; exact h3, h4, ?_, h6⟩
      rw [runCalls_cons, h5]; exact htm.2.1
    cases c with
    | onTimeout e t =>
      by_cases hdue : n.nextTick.getD 0 ≤ t
      · by_cases hT : T < t
        · exact ⟨[], e, t, cs, rfl, hT, hcat, hl, rfl, hdue⟩
        · -- the tick ran at or before `T`: the next deadline is within one period of `T`
          obtain ⟨-, hnt⟩ := onTimeout_ticks e n t hl hdue
          obtain ⟨f1, f2, f3⟩ := onTimeout_fields e n t
          have hp : period (N.onTimeout e n t) = period n := by unfold period; rw [f1]
          have hd' : (N.onTimeout e n t).nextTick.getD (N.onTimeout e n t).born ≤ T + period (N.onTimeout e n t) := by
            rw [hnt, hp]
            simp only [Option.getD_some, satAdd]
            omega
          obtain ⟨pre, e', τ, post, h1, h2, h3, h4, h5, h6⟩ := ih (N.onTimeout e n t) ht' hnl'
            (by rw [f3]; exact hl) hd' (by rw [hp]; exact hrest)
          refine ⟨.onTimeout e t :: pre, e', τ, post, by rw [h1]; rfl, h2, by rw [← hp]; exact h3, h4, ?_, h6⟩
          rw [runCalls_cons]; simp only [Call.step]; rw [h5]; exact f1
      · exact keep (onTimeout_waits e n t (by omega))
    | leave t => simp [Call.isLeave] at hnl
    | _ => exact keep (step_tm _ n (fun _ _ h => by cases h) rfl)

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
@[simp] theorem recheckNow_rs (e : Env) (n : N) (now : Nat) : RS[n, N.recheckNow e n now] := by
  unfold N.recheckNow; rs_tac
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
        cases hr : n.independentRoute now m ev with
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
        cases hr : n.independentRoute now m ev with
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

/-! ## What the 145 s chain still needs: no quiet window at the node after the Down -/

/-- **A heal after the Down postpones the deferred removal.** A member whose removal of `m` a quiet window deferred
hears a hub `peer` again after longer than the host's give-up bound for it (the first step of `on_frame` for a frame
from a hub, `ofHub1`): the window opens again, `QUIET` from that instant, the grace is dropped, and the recheck of the
tick at every instant before the new window ends leaves `m` in the view. So a heal at the member at least every `QUIET`
keeps `m` in its view for ever, and the link `q ≤ taud + QUIET` of `awareness_budget` (the window in force when the Down
arrives is the last one) holds only when no quiet window opens at the member between the Down and the removal. -/
theorem heal_postpones (e : Env) (n : N) (now peer t m : Nat) (hm : n.isHub = false) (hh : n.heard.get? peer = some t)
    (hs : e.giveUp peer < now - t) (hin : n.members.has m = true) (t' : Nat) (ht : t' < satAdd now QUIET) :
    (N.ofHub1 e n now peer).quietUntil = satAdd now QUIET ∧ (N.ofHub1 e n now peer).regrace = false ∧
    (N.tickRecheck e (N.ofHub1 e n now peer) t').members.has m = true := by
  have hq := ofHub1_heal e n now peer t hm hh hs
  have hr : (N.ofHub1 e n now peer).regrace = false := by
    unfold N.ofHub1
    simp only [hh, hs, hm, decide_true, Bool.not_false, Bool.true_and, if_true]
    unfold N.beginQuiet N.trace
    split <;> (try split) <;> rfl
  have hmem : (N.ofHub1 e n now peer).members = n.members := by
    unfold N.ofHub1; dsimp only; split <;> simp [N.beginQuiet]
  refine ⟨hq, hr, ?_⟩
  rw [tickRecheck_early e _ t' (by rw [hq]; exact ht), hmem]
  exact hin

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

/-- **A late tick at a member opens the quiet window.** A member whose tick comes later than `WAKE_GAP` after its
deadline reads it as a suspension: the window opens, `QUIET` from the call, and the grace is dropped. So a host slack
above `WAKE_GAP` at every tick keeps a member's window open and a deferred removal waiting (`tickRecheck_early`). -/
theorem late_tick_reopens (e : Env) (n : N) (now t : Nat) (hm : n.isHub = false) (ht : n.nextTick = some t)
    (hlate : WAKE_GAP < now - t) :
    (N.otTickPre e n now).quietUntil = satAdd now QUIET ∧ (N.otTickPre e n now).regrace = false := by
  unfold N.otTickPre
  simp only [ht, hm, Bool.not_false, decide_true, Bool.true_and, hlate, if_true]
  have h := renew_qu e (n.beginQuiet now 0) now true false
  rw [h.1, h.2]
  exact beginQuiet_window n now 0

end Vinc.Membership.Cmp

#audit_axioms Vinc.Membership.Cmp.step_tm
#audit_axioms Vinc.Membership.Cmp.pollTimeout_le
#audit_axioms Vinc.Membership.Cmp.onTimeout_ticks
#audit_axioms Vinc.Membership.Cmp.tick_window
#audit_axioms Vinc.Membership.Cmp.runCalls_held
#audit_axioms Vinc.Membership.Cmp.hub_lease_gone
#audit_axioms Vinc.Membership.Cmp.hub_lease_gone_start
#audit_axioms Vinc.Membership.Cmp.hubTick_hands_down
#audit_axioms Vinc.Membership.Cmp.hub_hands_down
#audit_axioms Vinc.Membership.Cmp.heal_postpones
#audit_axioms Vinc.Membership.Cmp.late_tick_reopens
