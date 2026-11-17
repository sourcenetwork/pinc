import Vinc.MembershipWindow
import Vinc.MembershipSuspAll
import Vinc.MembershipCurrent

/-!
# Completeness over a run, part 1: the timer fields through every function

The hub side of the awareness chain of `awareness_budget` is proved over any sequence of the host's calls in five
files, each importing the one before: the timer fields (this file), the timer schedule (`MembershipTimerRun`), the
lease of a crashed member (`MembershipTimerLease`), the Down delta of that lease (`MembershipTimerDown`), and a heal or
a late tick at a member (`MembershipTimerQuiet`).

* `TM[a, b]`: `b` has `a`'s tick deadline, role, leave flag and start time. `*_tm` proves it for every function the
  calls are built from and for every call but `on_timeout` and `leave` (`tm_tac` closes most of them; `leave_tm`:
  `leave` only raises the leave flag), so no call but `on_timeout` writes `next_tick`, no call writes `is_hub` or
  `born`, and no call but `leave` writes `leaving`.
* `onHello_eq3`: `on_hello` in three pieces (`hlHomed`, `hlAttach`, `hlRoster`), which these lemmas and the roster
  lemmas of `MembershipTimerLease` take one at a time.
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
@[simp] theorem recheckFold_tm (e : Env) (n : N) (now : Nat) (ks : List Nat) : TM[n, (N.recheckFold e n now ks).1] := by
  unfold N.recheckFold; tm_tac
@[simp] theorem recheckDue_tm (e : Env) (n : N) (now : Nat) : TM[n, N.recheckDue e n now] := by
  unfold N.recheckDue N.recheckRun N.recheckArm; tm_tac
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
@[simp] theorem onLeft_tm (e : Env) (n : N) (now m : Nat) (rc : Rec) : TM[n, N.onLeft e n now m rc] := by
  unfold N.onLeft; tm_tac
@[simp] theorem ofDelta_tm (e : Env) (n : N) (now peer m : Nat) (rc : Rec) (a : Alive) :
    TM[n, N.ofDelta e n now peer m rc a] := by
  unfold N.ofDelta; dsimp only; simp
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
@[simp] theorem tickMid_tm (e : Env) (n : N) (now : Nat) : TM[n, N.tickMid e n now] := by
  unfold N.tickMid
  have h := recheckDue_tm e n now
  generalize N.recheckDue e n now = n1 at h ⊢
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
  have h := recheckDue_tm e n now
  generalize N.recheckDue e n now = n1 at h ⊢
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

end Vinc.Membership.Cmp
