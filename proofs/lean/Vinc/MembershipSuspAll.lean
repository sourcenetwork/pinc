import Vinc.MembershipTickLoop
import Vinc.MembershipSweep
import Vinc.MembershipQuiet

/-!
# `SuspOk` through every call (property 3, hub side)

Only a few functions write the suspicion table (`MembershipTickSusp.lean`): `new_susp`, `carrier_watch`, `hub_down`,
`hub_tick`, `revoke`. Every other function of the machine leaves it as it is; this file proves that
(`*_susp` theorems: `(f ...).susp = n.susp`) and then that each public call keeps `SuspOk`. With `start` (empty table)
this makes `SuspOk` an invariant of every reachable state (`Reach.suspOk`), and `carrierWatch_keeps_unless_reach`
is the unconditional form of `carrierWatch_keeps_unless`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.MemInc

/-- Folding a step that keeps the table keeps it. -/
theorem foldl_su {α : Type} (f : N → α → N) (L : List α) (n : N) (h : ∀ b a, (f b a).susp = b.susp) :
    (L.foldl f n).susp = n.susp := by
  induction L generalizing n with
  | nil => rfl
  | cons x r ih => simp only [List.foldl_cons]; rw [ih, h]

theorem foldl_su2 {α β : Type} (f : N × β → α → N × β) (L : List α) (a : N × β) (h : ∀ b x, (f b x).1.susp = b.1.susp) :
    (L.foldl f a).1.susp = a.1.susp := by
  induction L generalizing a with
  | nil => rfl
  | cons x r ih => simp only [List.foldl_cons]; rw [ih, h]

theorem foldl_su2' {α β : Type} (f : N × β → α → N × β) (L : List α) (a : N × β)
    (h : ∀ (n : N) (c : β) x, (f (n, c) x).1.susp = n.susp) : (L.foldl f a).1.susp = a.1.susp := by
  induction L generalizing a with
  | nil => rfl
  | cons x r ih => simp only [List.foldl_cons]; rw [ih]; obtain ⟨n1, c1⟩ := a; exact h n1 c1 x

theorem forKeys_su (ks : List Nat) (f : Nat → N → N) (n : N) (h : ∀ k b, (f k b).susp = b.susp) : (forKeys ks f n).susp = n.susp :=
  foldl_su _ ks n (fun b a => h a b)

@[simp] theorem close_susp'' (n : N) (p : Nat) (r : CloseR) : (n.close p r).susp = n.susp := rfl
@[simp] theorem recomputeOne_susp (e : Env) (n : N) (now m : Nat) : (N.recomputeOne e n now m).1.susp = n.susp :=
  (recomputeOne_ht e n now m).2.1
@[simp] theorem applyDeltaCore_susp (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) :
    (N.applyDeltaCore e n now hub m rc a).susp = n.susp := (applyDeltaCore_ht e n now hub m rc a).2.1
@[simp] theorem sendSnapshot_susp (e : Env) (n : N) (now peer : Nat) : (N.sendSnapshot e n now peer).susp = n.susp :=
  (sendSnapshot_ht e n now peer).2.1
@[simp] theorem sendFloor_susp (e : Env) (n : N) (peer : Nat) : (N.sendFloor e n peer).susp = n.susp :=
  (sendFloor_ht e n peer).2.1
@[simp] theorem beginQuiet_susp (n : N) (now cause : Nat) : (n.beginQuiet now cause).susp = n.susp := by
  unfold N.beginQuiet; simp
@[simp] theorem helloTo_susp (e : Env) (n : N) (peer : Nat) (snap : Bool) : (N.helloTo e n peer snap).susp = n.susp := by
  unfold N.helloTo; simp
@[simp] theorem bumpRecord_susp (n : N) : n.bumpRecord.susp = n.susp := by
  unfold N.bumpRecord; split <;> simp
@[simp] theorem rttSample_susp (n : N) (hub r : Nat) : (n.rttSample hub r).susp = n.susp := by
  unfold N.rttSample; simp
@[simp] theorem refreshLocal_susp (e : Env) (n : N) (now : Nat) : (N.refreshLocal e n now).susp = n.susp := by
  unfold N.refreshLocal; simp

attribute [local simp] foldl_su foldl_su2' forKeys_su N.markHello

theorem pushDelta_susp'' (e : Env) (n : N) (now m : Nat) (rc : Rec) (a : Alive) : (N.pushDelta e n now m rc a).susp = n.susp :=
  pushDelta_susp' e n now m rc a

@[simp] theorem renew_susp (e : Env) (n : N) (now : Nat) (fs p : Bool) : (N.renew e n now fs p).susp = n.susp := by
  unfold N.renew
  simp

@[simp] theorem onSelfEntry_susp (e : Env) (n : N) (now hub : Nat) (rc : Rec) (a : Alive) :
    (N.onSelfEntry e n now hub rc a).susp = n.susp := by
  unfold N.onSelfEntry
  split
  · rfl
  · dsimp only
    split
    · split
      · simp [renew_susp]
      · simp
      · simp
    · split <;> simp

@[simp] theorem applyDelta_susp (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) :
    (N.applyDelta e n now hub m rc a).susp = n.susp := by
  unfold N.applyDelta
  split
  · exact onSelfEntry_susp ..
  · simp

@[simp] theorem applyDown_susp (e : Env) (n : N) (now hub member inc : Nat) : (N.applyDown e n now hub member inc).susp = n.susp := by
  unfold N.applyDown; exact applyDelta_susp ..

@[simp] theorem markAbsent_susp (e : Env) (n : N) (now hub round : Nat) : (N.markAbsent e n now hub round).1.susp = n.susp := by
  unfold N.markAbsent
  apply foldl_su2
  intro b x
  obtain ⟨b1, b2⟩ := b
  simp only []
  repeat' split
  all_goals simp

theorem susp_bump_match {F : N × Bool} {n0 : N} (h : F.1.susp = n0.susp) :
    (match F with | (n, ch) => if ch = true then n.bump else n).susp = n0.susp := by
  obtain ⟨f1, f2⟩ := F
  by_cases hc : f2 = true <;> simp [hc] at h ⊢ <;> exact h

macro "su_tac" : tactic => `(tactic| first | (simp; done) | (repeat' split; all_goals simp))
macro "su_fold" : tactic => `(tactic| (apply foldl_su; intro b a; repeat' split; all_goals simp))
macro "su_all" : tactic => `(tactic| simp (disch := (intro b a; repeat' split; all_goals simp)) [foldl_su])

@[simp] theorem recheckNow_susp (e : Env) (n : N) (now : Nat) : (N.recheckNow e n now).susp = n.susp := by
  unfold N.recheckNow
  su_tac

@[simp] theorem reselect_susp (e : Env) (n : N) (now : Nat) : (N.reselect e n now).susp = n.susp := by
  unfold N.reselect
  su_tac

@[simp] theorem onHello_susp (e : Env) (n : N) (now peer : Nat) (rc : Rec) (snap homed : Bool) :
    (N.onHello e n now peer rc snap homed).susp = n.susp := by
  unfold N.onHello
  su_tac

@[simp] theorem dropPeer_susp (e : Env) (n : N) (now peer : Nat) : (N.dropPeer e n now peer).susp = n.susp := by
  unfold N.dropPeer
  su_tac

@[simp] theorem pulseRefresh_susp (e : Env) (n : N) (now : Nat) : (N.pulseRefresh e n now).susp = n.susp := by
  unfold N.pulseRefresh
  su_fold

/-- `sample_session_rtts` in two pieces: the loop, then the test for a better hub. -/
def N.ssFold (e : Env) (n : N) (now : Nat) : N :=
  n.boot.foldl
    (fun n hub =>
      if hub == n.me then n
      else match e.evidence hub with
        | some ev =>
          if n.up.has hub && 0 < ev.srtt && now - ev.rx < PULSE_FRESH && ev.inf ≤ RTT_QUIET then n.rttSample hub ev.srtt else n
        | none => n) n

def N.ssBetter (n : N) (now : Nat) : Bool :=
  let cur := n.primary.bind (fun p => n.hrtt.get? p)
  n.boot.any (fun x =>
    x != n.me && n.primary != some x && n.hubUp now x &&
      (match n.hrtt.get? x with
       | some r => (match cur with | none => true | some c => decide (min (r + HYST_ABS) U64MAX < c * 2 / 3))
       | none => false))

theorem sampleSessionRtts_eq (e : Env) (n : N) (now : Nat) :
    N.sampleSessionRtts e n now = (let n1 := N.ssFold e n now; if n1.ssBetter now then N.reselect e n1 now else n1) := rfl

@[simp] theorem sampleSessionRtts_susp (e : Env) (n : N) (now : Nat) : (N.sampleSessionRtts e n now).susp = n.susp := by
  rw [sampleSessionRtts_eq]
  have h : (N.ssFold e n now).susp = n.susp := by
    unfold N.ssFold; su_fold
  dsimp only
  split
  · rw [reselect_susp, h]
  · exact h

@[simp] theorem dropStaleHubs_susp (e : Env) (n : N) (now : Nat) : (N.dropStaleHubs e n now).susp = n.susp := by
  unfold N.dropStaleHubs
  dsimp only
  split
  · rfl
  · refine susp_bump_match ?_
    apply foldl_su2'
    intro n1 c hub
    repeat' split
    all_goals first
      | (refine (foldl_su2 _ _ _ (fun b x => by simp)).trans ?_; simp)
      | simp

theorem swIn_susp (e : Env) (now hub : Nat) (a : N × Bool) (m : Nat) : (swIn e now hub a m).1.susp = a.1.susp := by
  obtain ⟨n1, c1⟩ := a
  unfold swIn
  dsimp only
  repeat' split
  all_goals simp

theorem swOut_susp (e : Env) (now : Nat) (a : N × Bool) (hub : Nat) : (swOut e now a hub).1.susp = a.1.susp := by
  unfold swOut
  exact foldl_su2 _ _ _ (fun b x => swIn_susp e now hub b x)

@[simp] theorem sweepAbsent_susp (e : Env) (n : N) (now : Nat) : (N.sweepAbsent e n now).susp = n.susp := by
  rw [sweepAbsent_eq]
  refine susp_bump_match ?_
  exact foldl_su2 _ _ _ (fun b x => swOut_susp e now b x)

/-- The first loop of `slow_tick`: sessions whose HELLO was not acknowledged are closed. -/
def N.stHello (e : Env) (now : Nat) (n : N) : N :=
  forKeys n.helloAt.keys
    (fun hub n =>
      match n.helloAt.timeAt hub with
      | none => n
      | some t0 =>
        let opened := (n.up.get? hub).getD now
        if ACK_WAIT < now - t0 && HS_GRACE < now - opened then
          let skip := match e.evidence hub with
            | some ev =>
              let wt := max ACK_WAIT (min (ev.srtt * 4) U64MAX)
              decide (now - t0 ≤ wt) || decide (now - ev.rx < wt / 2)
            | none => false
          if skip then n
          else
            let n := { n with helloAt := n.helloAt.unset hub }
            if n.up.has hub then N.dropPeer e (n.close hub .noack) now hub else n
        else n) n

theorem slowTick_eq (e : Env) (n : N) (now : Nat) :
    N.slowTick e n now =
      (let n := N.stHello e now n
       let n := if !n.isHub then N.sampleSessionRtts e n now else n
       let n := N.dropStaleHubs e n now
       let n := N.sweepAbsent e n now
       let primaryDown := match n.primary with | none => true | some p => !n.hubUp now p
       if primaryDown then N.reselect e n now else n) := rfl

theorem stHello_susp (e : Env) (now : Nat) (n : N) : (N.stHello e now n).susp = n.susp := by
  unfold N.stHello
  apply forKeys_su
  intro k b
  repeat' split
  all_goals simp

@[simp] theorem slowTick_susp (e : Env) (n : N) (now : Nat) : (N.slowTick e n now).susp = n.susp := by
  rw [slowTick_eq]
  dsimp only
  split <;> simp [stHello_susp]

theorem hubEnsure_su (n : N) (hub : Nat) : (hubEnsure n hub).1.susp = n.susp := by
  unfold hubEnsure; repeat' split <;> simp

theorem snapRound_su (n : N) (hub : Nat) : (snapRound n hub).1.susp = n.susp := by
  unfold snapRound; repeat' split <;> simp_all

theorem snapStep_su (e : Env) (now hub round : Nat) (a : N × Bool × Nat) (p : Nat × Rec) :
    (snapStep e now hub round a p).1.susp = a.1.susp := by
  obtain ⟨n, c, k⟩ := a
  unfold snapStep
  dsimp only
  repeat' split
  all_goals simp

theorem snapFin_su (e : Env) (now hub : Nat) (partial_ more : Bool) (round : Nat) (a : N × Bool × Nat) :
    (snapFin e now hub partial_ more round a).susp = a.1.susp := by
  obtain ⟨n, c, k⟩ := a
  unfold snapFin
  dsimp only
  repeat' split
  all_goals simp [N.bc]

@[simp] theorem applySnap_susp (e : Env) (n : N) (now hub : Nat) (partial_ more : Bool) (es : List (Nat × Rec)) :
    (N.applySnap e n now hub partial_ more es).susp = n.susp := by
  rw [applySnap_eq]
  have h2 := hubEnsure_su n hub
  rcases hE : hubEnsure n hub with ⟨n1, ok⟩
  rw [hE] at h2
  change n1.susp = n.susp at h2
  simp only []
  by_cases hok : ok = true
  · simp only [hok, Bool.not_true, if_false, Bool.false_eq_true]
    have h3 := snapRound_su n1 hub
    rcases hR : snapRound n1 hub with ⟨n2, round⟩
    rw [hR] at h3
    change n2.susp = n1.susp at h3
    simp only []
    generalize hn3 : (if (!n2.isHub && n2.primary == some hub) = true then
        ({ n2 with homeOk := some hub, homeSeen := true } : N) else n2) = n3
    have h4 : n3.susp = n2.susp := by rw [← hn3]; split <;> rfl
    have h5 : (List.foldl (snapStep e now hub round) (n3, false, 0) es).1.susp = n3.susp :=
      foldl_su2 (snapStep e now hub round) es (n3, false, 0) (fun b x => snapStep_su e now hub round b x)
    have h6 := snapFin_su e now hub partial_ more round (List.foldl (snapStep e now hub round) (n3, false, 0) es)
    rw [h6, h5, h4, h3, h2]
  · have : ok = false := by simpa using hok
    simp only [this, Bool.not_false, if_true]
    exact h2

/-! ## The calls that reach a writer -/

theorem so_ite (c : Prop) [Decidable c] {a b : N} (ha : a.SuspOk) (hb : b.SuspOk) : (if c then a else b).SuspOk := by
  split <;> assumption

theorem forKeys_so (ks : List Nat) (f : Nat → N → N) (h : ∀ k b, b.SuspOk → (f k b).SuspOk) (n : N) (hn : n.SuspOk) :
    (forKeys ks f n).SuspOk := by
  unfold forKeys
  induction ks generalizing n with
  | nil => exact hn
  | cons k r ih => exact ih _ (h k n hn)

/-- `tick` up to the last step, which is the only one that can touch the suspicion table. -/
def N.tickMid (e : Env) (n : N) (now : Nat) : N :=
  let n := N.tickRecheck e n now
  let n := if n.sent != some (n.ver, n.th) then N.renew e n now false false else n
  if n.isHub || n.nextSlow ≤ now then
    N.slowTick e (if !n.isHub then { n with nextSlow := satAdd now SLOW_TICK } else n) now
  else n

theorem tick_eq' (e : Env) (n : N) (now : Nat) :
    N.tick e n now = (let n := N.tickMid e n now; if n.isHub then N.hubTick e n now else n) := rfl

theorem tickRecheck_susp (e : Env) (n : N) (now : Nat) : (N.tickRecheck e n now).susp = n.susp := by
  unfold N.tickRecheck
  repeat' split
  all_goals simp

theorem tickMid_susp (e : Env) (n : N) (now : Nat) : (N.tickMid e n now).susp = n.susp := by
  unfold N.tickMid
  have h := tickRecheck_susp e n now
  generalize N.tickRecheck e n now = n1 at h ⊢
  repeat' split
  all_goals simp [h]

theorem tick_so (e : Env) (n : N) (now : Nat) (hs : n.SuspOk) : (N.tick e n now).SuspOk := by
  rw [tick_eq']
  dsimp only
  have h := SuspOk.of_eq (tickMid_susp e n now) hs
  split
  · exact hubTick_susp e _ now h
  · exact h

theorem hubDown_so (e : Env) (n : N) (now m : Nat) (cause : Cause) (hs : n.SuspOk) : (N.hubDown e n now m cause).SuspOk :=
  (hubDown_susp e n now m cause).1 hs

theorem onDown_so (e : Env) (n : N) (now m inc : Nat) (pf : Proof) (hs : n.SuspOk) : (N.onDown e n now m inc pf).SuspOk := by
  unfold N.onDown
  dsimp only
  repeat' split
  all_goals first
    | exact (hubDown_susp _ _ _ _ _).1 (SuspOk.of_eq (by simp) hs)
    | exact SuspOk.of_eq (by simp) hs

theorem carrierGone_so (e : Env) (n : N) (now member : Nat) (hs : n.SuspOk) : (N.carrierGone e n now member).SuspOk := by
  unfold N.carrierGone
  split
  · exact (carrierWatch_cw2 e _ now member).1 (SuspOk.of_eq (by simp) hs)
  · exact hs

theorem carrierReturn_so (e : Env) (n : N) (now member : Nat) (hs : n.SuspOk) : (N.carrierReturn e n now member).SuspOk :=
  (carrierReturn_cw2 e n now member).1 hs

theorem sessionDown_so (e : Env) (n : N) (now peer code : Nat) (hs : n.SuspOk) : (N.sessionDown e n now peer code).SuspOk := by
  unfold N.sessionDown
  split
  · exact hs
  · dsimp only
    refine SuspOk.of_eq (dropPeer_susp e _ now peer).symm.symm ?_
    split
    · exact (hubDown_susp _ _ _ _ _).1 (SuspOk.of_eq (by simp) (SuspOk.of_eq rfl hs))
    · exact SuspOk.of_eq rfl hs

@[simp] theorem sessionUp_susp (e : Env) (n : N) (now peer : Nat) (incoming : Bool) : (N.sessionUp e n now peer incoming).susp = n.susp := by
  unfold N.sessionUp
  su_tac

@[simp] theorem leave_susp (n : N) : n.leave.susp = n.susp := by
  unfold N.leave
  apply forKeys_su
  intro k b
  simp

@[simp] theorem addressChanged_susp (n : N) (now : Nat) : (n.addressChanged now).susp = n.susp := by
  unfold N.addressChanged; rfl

/-! ### `on_timeout` -/

def N.otA (e : Env) (n : N) (now : Nat) : N :=
  let n := N.pulseRefresh e n now
  let n := N.refreshLocal e n now
  if n.nextRenew ≤ now then N.renew e n now false true else n

def N.confDue (n : N) (now : Nat) : Bool := match n.nextConf with | some c => decide (c ≤ now) | none => false

def N.otB (e : Env) (n : N) (now : Nat) : N :=
  if n.confDue now then
    let n := { n with nextConf := none }
    if n.isHub then forKeys n.susp.keys (fun m n => N.carrierWatch e n now m) n else n
  else n

def N.otC (e : Env) (n : N) (now : Nat) : N :=
  if (n.nextTick.getD 0) ≤ now then
    let n := match n.nextTick with
      | some t => if !n.isHub && WAKE_GAP < now - t then N.renew e (n.beginQuiet now 0) now true false else n
      | none => n
    let n := { n with nextTick := some (satAdd now (if n.isHub then HUB_TICK else NODE_TICK)) }
    N.tick e n now
  else n

theorem onTimeout_eq (e : Env) (n : N) (now : Nat) :
    N.onTimeout e n now = (if n.leaving then n else N.otC e (N.otB e (N.otA e n now) now) now) := rfl

theorem otA_susp (e : Env) (n : N) (now : Nat) : (N.otA e n now).susp = n.susp := by
  unfold N.otA; dsimp only; split <;> simp

theorem otB_so (e : Env) (n : N) (now : Nat) (hs : n.SuspOk) : (N.otB e n now).SuspOk := by
  unfold N.otB
  split
  · dsimp only
    split
    · exact forKeys_so _ _ (fun k b hb => (carrierWatch_cw2 e b now k).1 hb) _ (SuspOk.of_eq rfl hs)
    · exact SuspOk.of_eq rfl hs
  · exact hs

theorem otC_so (e : Env) (n : N) (now : Nat) (hs : n.SuspOk) : (N.otC e n now).SuspOk := by
  unfold N.otC
  split
  · dsimp only
    apply tick_so
    refine SuspOk.of_eq ?_ hs
    repeat' split
    all_goals simp
  · exact hs

theorem onTimeout_so (e : Env) (n : N) (now : Nat) (hs : n.SuspOk) : (N.onTimeout e n now).SuspOk := by
  rw [onTimeout_eq]
  split
  · exact hs
  · exact otC_so e _ now (otB_so e _ now (SuspOk.of_eq (otA_susp e n now) hs))

/-! ### `on_frame` -/

/-- The first steps of the hub part of `on_frame`: silence detection and the hearing time. -/
def N.ofHub1 (e : Env) (n : N) (now peer : Nat) : N :=
  let silent := match n.heard.get? peer with | some t => decide (e.giveUp peer < now - t) | none => false
  let n := if !n.isHub && silent then n.beginQuiet now 1 else n
  { n with heard := n.heard.insert peer now, helloAt := n.helloAt.unset peer }

/-- The round trip sample of an acknowledged HELLO and the primary choice it can trigger. -/
def N.ofHub2 (e : Env) (n : N) (now peer : Nat) (isAckSnap : Bool) (t0 : Option Nat) : N :=
  match t0 with
  | some t0 =>
    if isAckSnap && now - t0 < RTT_SAMPLE_MAX then
      let n := n.rttSample peer (now - t0)
      match n.primary with
      | some p =>
        if !n.isHub && p != peer then
          let cur := n.hrtt.get? p
          let new := (n.hrtt.get? peer).getD U64MAX
          if n.hubUp now peer && (match cur with | none => true | some c => decide (min (new + HYST_ABS) U64MAX < c * 3 / 4)) then
            N.reselect e n now
          else n
        else n
      | none => n
    else n
  | none => n

/-- The part of `on_frame` for a frame from a hub: silence detection, round trip samples, primary choice. -/
def N.ofHub (e : Env) (n : N) (now peer : Nat) (f : NFrame) : N :=
  let n := N.ofHub1 e n now peer
  let isAckSnap := match f with | .ack => true | .snap .. => true | _ => false
  let t0 := n.hsent.timeAt peer
  let n := if isAckSnap then { n with hsent := n.hsent.unset peer } else n
  let n := N.ofHub2 e n now peer isAckSnap t0
  if n.primary.isNone then N.reselect e n now else n

def N.ofMid (e : Env) (n : N) (now peer : Nat) (f : NFrame) (fromHub : Bool) : N :=
  let n := if fromHub then N.ofHub e n now peer f else n
  let isHello := match f with | .hello .. => true | _ => false
  if n.isHub && !isHello && n.roster.has peer then
    { n with roster := n.roster.modify peer (fun l => { l with renewed := now }) } else n

def N.ofDisp (e : Env) (n : N) (now peer : Nat) (f : NFrame) (fromHub : Bool) : N :=
  match f with
  | .hello rc snap homed => if n.isHub then N.onHello e n now peer rc snap homed else n
  | .probe => if fromHub && !n.isHub then N.helloTo e n peer false else n
  | .down m inc pf =>
    if n.isHub && fromHub then N.onDown e n now m inc pf
    else if fromHub then N.applyDown e n now peer m inc
    else n
  | .delta m rc a => if fromHub then N.applyDelta e n now peer m rc a else n
  | .snap part more es => if fromHub then N.applySnap e n now peer part more es else n
  | .ack => n
  | .other ty topic rest => n.bc (.frame peer ty topic rest)

theorem onFrame_eq (e : Env) (n : N) (now peer : Nat) (f : NFrame) :
    N.onFrame e n now peer f =
      (if n.revoked.has peer || n.leaving then n
       else
         let n := n.trace (.frameIn peer f.ty)
         let n := N.pulseRefresh e n now
         let fromHub := n.isBoot peer
         N.ofDisp e (N.ofMid e n now peer f fromHub) now peer f fromHub) := rfl

theorem susp_ite (c : Prop) [Decidable c] {a b : N} {s : AMap Susp} (ha : a.susp = s) (hb : b.susp = s) : (if c then a else b).susp = s := by
  split <;> assumption

theorem ofHub1_susp (e : Env) (n : N) (now peer : Nat) : (N.ofHub1 e n now peer).susp = n.susp := by
  unfold N.ofHub1; dsimp only; split <;> simp

theorem ofHub2_susp (e : Env) (n : N) (now peer : Nat) (isAckSnap : Bool) (t0 : Option Nat) :
    (N.ofHub2 e n now peer isAckSnap t0).susp = n.susp := by
  unfold N.ofHub2
  split
  · refine susp_ite _ ?_ rfl
    dsimp only
    split
    · refine susp_ite _ ?_ (by simp)
      exact susp_ite _ (by simp) (by simp)
    · simp
  · rfl

theorem ofHub_susp (e : Env) (n : N) (now peer : Nat) (f : NFrame) : (N.ofHub e n now peer f).susp = n.susp := by
  unfold N.ofHub
  dsimp only
  split <;> simp [ofHub1_susp, ofHub2_susp]

theorem ofMid_susp (e : Env) (n : N) (now peer : Nat) (f : NFrame) (fromHub : Bool) : (N.ofMid e n now peer f fromHub).susp = n.susp := by
  unfold N.ofMid
  dsimp only
  repeat' split
  all_goals simp [ofHub_susp]

theorem ofDisp_so (e : Env) (n : N) (now peer : Nat) (f : NFrame) (fromHub : Bool) (hs : n.SuspOk) :
    (N.ofDisp e n now peer f fromHub).SuspOk := by
  unfold N.ofDisp
  cases f <;> dsimp only <;> repeat' split
  all_goals first
    | exact onDown_so _ _ _ _ _ _ hs
    | exact SuspOk.of_eq (by simp) hs
    | exact hs

theorem onFrame_so (e : Env) (n : N) (now peer : Nat) (f : NFrame) (hs : n.SuspOk) : (N.onFrame e n now peer f).SuspOk := by
  rw [onFrame_eq]
  split
  · exact hs
  · dsimp only
    exact ofDisp_so e _ now peer f _ (SuspOk.of_eq (by rw [ofMid_susp]; simp) hs)

theorem onBytes_so (e : Env) (n : N) (now peer : Nat) (fs : List NFrame) (bad : Bool) (hs : n.SuspOk) :
    (N.onBytes e n now peer fs bad).SuspOk := by
  unfold N.onBytes
  have h : ∀ (L : List NFrame) (x : N), x.SuspOk → (L.foldl (fun n f => N.onFrame e n now peer f) x).SuspOk := by
    intro L
    induction L with
    | nil => intro x hx; exact hx
    | cons f r ih => intro x hx; exact ih _ (onFrame_so e x now peer f hx)
  split
  · exact SuspOk.of_eq (by simp) (h (fs.take MAX_FRAMES_PER_CALL) n hs)
  · exact h (fs.take MAX_FRAMES_PER_CALL) n hs

theorem revoke_susp (e : Env) (n n' : N) (now member : Nat) (h : N.revoke e n now member = some n') :
    n'.susp = n.susp.erase member := by
  have hc : ¬ (n.revoked.has member = false ∧ MAX_TABLE ≤ n.revoked.len) := by
    intro hh; rw [(revoke_none_iff e n now member).2 hh] at h; cases h
  rw [revoke_eq e n now member hc] at h
  injection h with h; subst h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := rvMembers_ht e (n.rvPre member) now member
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := rvRoster_spec e (N.rvMembers e (n.rvPre member) now member) now member
  have a_su : (n.rvPre member).susp = n.susp.erase member := rfl
  have e_su : (N.rvRoster e (N.rvMembers e (n.rvPre member) now member) now member).susp = n.susp.erase member := by
    rw [c4, b2, a_su]
  unfold N.rvEnd
  dsimp only
  split <;> simp [e_su]

theorem revoke_so (e : Env) (n n' : N) (now member : Nat) (h : N.revoke e n now member = some n') (hs : n.SuspOk) : n'.SuspOk :=
  SuspOk.erase member (revoke_susp e n n' now member h) hs

theorem start_so (e : Env) (me : Nat) (isHub : Bool) (hubs : List Nat) (tr : Bool) (now wall floor : Nat) (n : N)
    (h : N.start e me isHub hubs tr now wall floor = .ok n) : n.SuspOk := by
  unfold N.start at h
  dsimp only at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  all_goals
    simp only [Except.ok.injEq] at h
    subst h
    intro k sp tb path hk
    simp [N.trace, AMap.get?] at hk

end Vinc.Membership
