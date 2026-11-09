import Vinc.MembershipViewUnion

/-!
# Membership view: the view epoch only increases (property 1, view side)

`bump` is the only writer of `epoch`: it adds one and emits `ViewChanged` with the new epoch (`bump_epoch`,
`MembershipModelLemmas.lean`). Every other function of the view leaves it alone (`recomputeOne_keeps2`), so every
function that can call `bump` has an epoch at least the old one:

`applyDeltaCore_epoch`, `pushDelta_epoch`, `renew_epoch`, `onSelfEntry_epoch`, `applyDelta_epoch`, `markAbsent_epoch`,
`applySnap_epoch`, `sweepAbsent_epoch`, `recheckNow_epoch`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.MemInc

/-- A fold whose step preserves a property. -/
theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) (L : List α) (b : β)
    (h : ∀ b a, P b → P (f b a)) (hb : P b) : P (L.foldl f b) := by
  induction L generalizing b with
  | nil => exact hb
  | cons x r ih => exact ih _ (h b x hb)

@[simp] theorem ite_epoch (c : Prop) [Decidable c] (a b : N) : (if c then a else b).epoch = if c then a.epoch else b.epoch := by
  split <;> rfl

@[simp] theorem ite_fst_v (c : Prop) [Decidable c] (a b : N × Bool) : (if c then a else b).1 = if c then a.1 else b.1 := by
  split <;> rfl

/-- The epoch does not go down from `n0` to `n`. -/
def EpGe (n0 n : N) : Prop := n0.epoch ≤ n.epoch

theorem EpGe.trans {a b c : N} (h1 : EpGe a b) (h2 : EpGe b c) : EpGe a c := Nat.le_trans h1 h2
theorem EpGe.refl (n : N) : EpGe n n := Nat.le_refl _

theorem bump_ge (n : N) : EpGe n n.bump := by unfold EpGe; rw [bump_epoch]; omega

theorem ite_bump_ge (n : N) (c : Bool) : EpGe n (if c = true then n.bump else n) := by
  by_cases h : c = true
  · simp [h]; exact bump_ge n
  · simp [h]; exact EpGe.refl n

theorem recomputeOne_ep (e : Env) (n : N) (now m : Nat) : (N.recomputeOne e n now m).1.epoch = n.epoch :=
  (recomputeOne_keeps2 e n now m).1.2.1

/-! ## `apply_delta` in pieces -/

/-- Make sure a copy for `hub` exists (refused when there are `MAX_HUBS` already). -/
def hubEnsure (n : N) (hub : Nat) : N × Bool :=
  if !n.hv.has hub then
    if MAX_HUBS ≤ n.hv.len then (n, false)
    else ({ n with hv := n.hv.insert hub ⟨[], 0, false⟩ }, true)
  else (n, true)

/-- The change to the hub's copy and to the `left` set. -/
def adcUpd (n : N) (hub m : Nat) (rc : Rec) (a : Alive) : N :=
  match n.hv.get? hub with
  | none => n
  | some c =>
    match a with
    | .alive =>
      if c.entries.len < MAX_TABLE || c.entries.has m then
        { n with hv := n.hv.insert hub { c with entries := c.entries.insert m ⟨rc, c.round, none⟩ }, left := n.left.del m }
      else n
    | .down | .left =>
      match c.entries.get? m with
      | some x =>
        if x.rc.inc / 65536 ≤ rc.inc / 65536 then
          let n := { n with hv := n.hv.insert hub { c with entries := c.entries.erase m } }
          if a == .left && n.left.len < MAX_TABLE then { n with left := n.left.ins m } else n
        else n
      | none => n

theorem applyDeltaCore_eq_v (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) :
    N.applyDeltaCore e n now hub m rc a =
      (if n.revoked.has m then n
       else
        let (n, ok) := hubEnsure n hub
        if !ok then n
        else
          let n := adcUpd n hub m rc a
          let (n, ch) := N.recomputeOne e n now m
          if ch then n.bump else n) := rfl

theorem hubEnsure_ep (n : N) (hub : Nat) : (hubEnsure n hub).1.epoch = n.epoch := by
  unfold hubEnsure; simp; repeat' split <;> simp_all

theorem adcUpd_ep (n : N) (hub m : Nat) (rc : Rec) (a : Alive) : (adcUpd n hub m rc a).epoch = n.epoch := by
  unfold adcUpd; repeat' split
  all_goals simp_all
  all_goals (try split) <;> simp

theorem ite_ge_bump (n0 n : N) (ch : Bool) (h : EpGe n0 n) : EpGe n0 (if ch = true then n.bump else n) := by
  by_cases hc : ch = true
  · simp [hc]; exact h.trans (bump_ge n)
  · simp [hc]; exact h

theorem applyDeltaCore_epoch (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) :
    EpGe n (N.applyDeltaCore e n now hub m rc a) := by
  rw [applyDeltaCore_eq_v]
  by_cases h1 : n.revoked.has m = true
  · simp [h1]; exact EpGe.refl n
  · simp only [h1, if_false, Bool.false_eq_true]
    have h2 := hubEnsure_ep n hub
    rcases hE : hubEnsure n hub with ⟨n1, ok⟩
    rw [hE] at h2
    change n1.epoch = n.epoch at h2
    simp only []
    by_cases hok : ok = true
    · simp only [hok, Bool.not_true, if_false, Bool.false_eq_true]
      have h3 := adcUpd_ep n1 hub m rc a
      have h4 := recomputeOne_ep e (adcUpd n1 hub m rc a) now m
      rcases hR : N.recomputeOne e (adcUpd n1 hub m rc a) now m with ⟨n2, ch⟩
      rw [hR] at h4
      change n2.epoch = _ at h4
      simp only []
      apply ite_ge_bump
      unfold EpGe; omega
    · have : ok = false := by simpa using hok
      simp only [this, Bool.not_false, if_true]
      unfold EpGe; omega


theorem deltaTo_ep (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : (N.deltaTo e n p m rc a).epoch = n.epoch :=
  deltaTo_epoch n e p m rc a

theorem pushDelta_epoch (e : Env) (n : N) (now m : Nat) (rc : Rec) (a : Alive) :
    EpGe n (N.pushDelta e n now m rc a) := by
  unfold N.pushDelta
  have h : ∀ (ks : List Nat) (x : N), x.epoch = n.epoch →
      (forKeys ks (fun p n => if p != m && (n.isBoot p || (m == n.me && n.homed.has p)) then N.deltaTo e n p m rc a else n) x).epoch = n.epoch := by
    intro ks
    unfold forKeys
    induction ks with
    | nil => intro x hx; exact hx
    | cons k r ih =>
      intro x hx
      simp only [List.foldl_cons]
      apply ih
      split
      · rw [deltaTo_ep]; exact hx
      · exact hx
  have h1 := h n.attached.keys n rfl
  generalize forKeys n.attached.keys (fun p n => if p != m && (n.isBoot p || (m == n.me && n.homed.has p)) then N.deltaTo e n p m rc a else n) n = x at h1 ⊢
  by_cases hm : (m == x.me) = true
  · simp only [hm, if_true]; unfold EpGe; omega
  · simp only [hm, Bool.false_eq_true, if_false]
    have := applyDeltaCore_epoch e x now x.me m rc a
    unfold EpGe at this ⊢; omega

/-- The step of the loop over the hubs in `renew`. -/
def rnStep (e : Env) (now : Nat) (forceSnap periodic : Bool) (n : N) (hub : Nat) : N :=
  if hub == n.me || !n.up.has hub then n
  else
    let snap := forceSnap || !n.hv.has hub
    if periodic && !snap && (n.primary != some hub || n.homeOk == some hub) && N.pulseFresh e now hub then
      n.trace (.helloSuppressed hub)
    else
      N.helloTo e (n.markHello hub now) hub snap

def rnPre (n : N) (periodic : Bool) : N × Bool :=
  let n := if (match n.sent with | some s => decide (s ≠ (n.ver, n.th)) | none => false) then n.bumpRecord else n
  let periodic := if n.sent != some (n.ver, n.th) then false else periodic
  ({ n with sent := some (n.ver, n.th) }, periodic)

def rnPush (e : Env) (n : N) (now : Nat) : N :=
  let cur : Rec := ⟨n.inc.word, n.ver, n.th⟩
  if n.isHub && decide (n.own ≠ cur) then N.pushDelta e { n with own := cur } now n.me cur .alive else n

theorem renew_eq (e : Env) (n : N) (now : Nat) (forceSnap periodic : Bool) :
    N.renew e n now forceSnap periodic =
      (let (n, periodic) := rnPre n periodic
       let n := rnPush e n now
       let n := n.boot.foldl (rnStep e now forceSnap periodic) n
       { n with nextRenew := satAdd now RENEW }) := rfl

theorem bumpRecord_ep (n : N) : n.bumpRecord.epoch = n.epoch := by
  unfold N.bumpRecord; split <;> simp

theorem rnStep_ep (e : Env) (now : Nat) (fs p : Bool) (n : N) (hub : Nat) : (rnStep e now fs p n hub).epoch = n.epoch := by
  unfold rnStep N.helloTo
  repeat' split
  all_goals simp_all [N.markHello]

theorem rnPre_ep (n : N) (p : Bool) : (rnPre n p).1.epoch = n.epoch := by
  unfold rnPre; dsimp only; split <;> simp [bumpRecord_ep]

theorem rnPush_ge (e : Env) (n : N) (now : Nat) : EpGe n (rnPush e n now) := by
  unfold rnPush
  by_cases h : (n.isHub && decide (n.own ≠ ⟨n.inc.word, n.ver, n.th⟩)) = true
  · simp only [h, if_true]
    have := pushDelta_epoch e { n with own := ⟨n.inc.word, n.ver, n.th⟩ } now n.me ⟨n.inc.word, n.ver, n.th⟩ .alive
    exact this
  · simp only [h, if_false]; exact EpGe.refl n

theorem renew_epoch (e : Env) (n : N) (now : Nat) (fs p : Bool) : EpGe n (N.renew e n now fs p) := by
  rw [renew_eq]
  rcases hP : rnPre n p with ⟨n1, p1⟩
  have e1 : n1.epoch = n.epoch := by have := rnPre_ep n p; rw [hP] at this; exact this
  simp only []
  have e2 := rnPush_ge e n1 now
  have e3 : (List.foldl (rnStep e now fs p1) (rnPush e n1 now) (rnPush e n1 now).boot).epoch = (rnPush e n1 now).epoch :=
    foldl_inv (fun (x : N) => x.epoch = (rnPush e n1 now).epoch) _ _ _ (fun b a hb => by rw [rnStep_ep]; exact hb) rfl
  unfold EpGe at e2 ⊢
  show n.epoch ≤ (List.foldl (rnStep e now fs p1) (rnPush e n1 now) (rnPush e n1 now).boot).epoch
  omega


theorem onSelfEntry_epoch (e : Env) (n : N) (now hub : Nat) (rc : Rec) (a : Alive) : EpGe n (N.onSelfEntry e n now hub rc a) := by
  unfold N.onSelfEntry
  by_cases h0 : (hub == n.me) = true
  · simp only [h0, if_true]; exact EpGe.refl n
  · simp only [h0, Bool.false_eq_true, if_false]
    have e1 : (n.trace (.selfDelta hub)).epoch = n.epoch := trace_epoch n _
    generalize n.trace (.selfDelta hub) = n1 at e1 ⊢
    by_cases h1 : (a == .alive && n1.inc.word < rc.inc) = true
    · simp only [h1, if_true]
      rcases hO : observe n1.loc n1.inc rc.inc with err | ⟨ch, i', l'⟩
      · unfold EpGe; simp [e1, trace_epoch]
      · cases ch
        · unfold EpGe; show n.epoch ≤ n1.epoch; omega
        · refine EpGe.trans ?_ (renew_epoch _ _ _ _ _)
          unfold EpGe; simp [e1, trace_epoch]
    · simp only [h1, if_false]
      by_cases h2 : (a != .alive || rc.inc < n1.inc.word) = true
      · simp only [h2, if_true]; unfold EpGe; simp [e1, N.helloTo]
      · simp only [h2, if_false]; unfold EpGe; simp [e1, N.bc]

theorem applyDelta_epoch (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) : EpGe n (N.applyDelta e n now hub m rc a) := by
  unfold N.applyDelta
  split
  · exact onSelfEntry_epoch ..
  · exact applyDeltaCore_epoch ..

/-- The fold of `recompute_one` over members keeps the epoch (it never bumps). -/
theorem markAbsent_epoch (e : Env) (n : N) (now hub round : Nat) : (N.markAbsent e n now hub round).1.epoch = n.epoch := by
  unfold N.markAbsent
  refine foldl_inv (fun (a : N × Bool) => a.1.epoch = n.epoch) _ _ _ ?_ rfl
  intro a m ha
  obtain ⟨n1, c1⟩ := a
  simp only at ha ⊢
  repeat' split
  all_goals simp_all [recomputeOne_ep]


/-! ## `apply_snap` in pieces -/

def snapRound (n : N) (hub : Nat) : N × Nat :=
  match n.hv.get? hub with
  | some c =>
    let c := if !c.open_ then { c with round := c.round + 1, open_ := true } else c
    ({ n with hv := n.hv.insert hub c }, c.round)
  | none => (n, 0)

def snapStep (e : Env) (now hub round : Nat) (a : N × Bool × Nat) (p : Nat × Rec) : N × Bool × Nat :=
  let (n, changed, cnt) := a
  let cnt := cnt + 1
  let (m, rc) := p
  if m == n.me then (N.onSelfEntry e n now hub rc .alive, changed, cnt)
  else if n.revoked.has m then (n, changed, cnt)
  else
    match n.hv.get? hub with
    | some c =>
      if MAX_TABLE ≤ c.entries.len && !c.entries.has m then (n, changed, cnt)
      else
        let n := { n with hv := n.hv.insert hub { c with entries := c.entries.insert m ⟨rc, round, none⟩ } }
        let n := { n with left := n.left.del m }
        let (n, ch) := N.recomputeOne e n now m
        (n, changed || ch, cnt)
    | none =>
      let n := { n with left := n.left.del m }
      let (n, ch) := N.recomputeOne e n now m
      (n, changed || ch, cnt)

def snapFin (e : Env) (now hub : Nat) (partial_ more : Bool) (round : Nat) (a : N × Bool × Nat) : N :=
  let (n, changed, cnt) := a
  let n := n.trace (.snapApplied hub cnt more)
  let (n, changed) : N × Bool :=
    if !more then
      let n := match n.hv.get? hub with
        | some c => { n with hv := n.hv.insert hub { c with open_ := false } }
        | none => n
      let (n, changed) := if !partial_ then
          let (n', ch) := N.markAbsent e n now hub round
          (n', changed || ch)
        else (n, changed)
      let n := if n.primary == some hub then n.bc (.resub hub) else n
      (n, changed)
    else (n, changed)
  if changed then n.bump else n

theorem applySnap_eq (e : Env) (n : N) (now hub : Nat) (partial_ more : Bool) (es : List (Nat × Rec)) :
    N.applySnap e n now hub partial_ more es =
      (let (n, ok) := hubEnsure n hub
       if !ok then n
       else
         let (n, round) := snapRound n hub
         let n := if !n.isHub && n.primary == some hub then { n with homeOk := some hub, homeSeen := true } else n
         snapFin e now hub partial_ more round (es.foldl (snapStep e now hub round) (n, false, 0))) := rfl

theorem snapRound_ep (n : N) (hub : Nat) : (snapRound n hub).1.epoch = n.epoch := by
  unfold snapRound; repeat' split <;> simp_all

theorem snapStep_ep (e : Env) (now hub round : Nat) (a : N × Bool × Nat) (p : Nat × Rec) :
    EpGe a.1 (snapStep e now hub round a p).1 := by
  obtain ⟨n, c, k⟩ := a
  unfold snapStep
  dsimp only
  by_cases h1 : (p.1 == n.me) = true
  · simp only [h1, if_true]; exact onSelfEntry_epoch ..
  · simp only [h1, Bool.false_eq_true, if_false]
    by_cases h2 : n.revoked.has p.1 = true
    · simp only [h2, if_true]; exact EpGe.refl n
    · simp only [h2, Bool.false_eq_true, if_false]
      cases hg : n.hv.get? hub with
      | none =>
        simp only []
        unfold EpGe; simp [recomputeOne_ep]
      | some c =>
        simp only []
        by_cases h3 : (decide (MAX_TABLE ≤ c.entries.len) && !c.entries.has p.1) = true
        · simp only [h3, if_true]; exact EpGe.refl n
        · simp only [h3, Bool.false_eq_true, if_false]
          unfold EpGe; simp [recomputeOne_ep]

theorem snapFin_ep (e : Env) (now hub : Nat) (partial_ more : Bool) (round : Nat) (a : N × Bool × Nat) :
    EpGe a.1 (snapFin e now hub partial_ more round a) := by
  obtain ⟨n, c, k⟩ := a
  unfold snapFin
  dsimp only
  apply ite_ge_bump
  repeat' split
  all_goals (unfold EpGe; simp [trace_epoch, N.bc, markAbsent_epoch])


theorem applySnap_epoch (e : Env) (n : N) (now hub : Nat) (partial_ more : Bool) (es : List (Nat × Rec)) :
    EpGe n (N.applySnap e n now hub partial_ more es) := by
  rw [applySnap_eq]
  have h2 := hubEnsure_ep n hub
  rcases hE : hubEnsure n hub with ⟨n1, ok⟩
  rw [hE] at h2
  change n1.epoch = n.epoch at h2
  simp only []
  by_cases hok : ok = true
  · simp only [hok, Bool.not_true, if_false, Bool.false_eq_true]
    have h3 := snapRound_ep n1 hub
    rcases hR : snapRound n1 hub with ⟨n2, round⟩
    rw [hR] at h3
    change n2.epoch = n1.epoch at h3
    simp only []
    generalize hn3 : (if (!n2.isHub && n2.primary == some hub) = true then
        ({ n2 with homeOk := some hub, homeSeen := true } : N) else n2) = n3
    have h4 : n3.epoch = n2.epoch := by rw [← hn3]; split <;> rfl
    have h5 : EpGe n3 (List.foldl (snapStep e now hub round) (n3, false, 0) es).1 := by
      have := foldl_inv (fun (a : N × Bool × Nat) => EpGe n3 a.1) (snapStep e now hub round) es (n3, false, 0)
        (fun b a hb => hb.trans (snapStep_ep e now hub round b a)) (EpGe.refl n3)
      exact this
    have h6 := snapFin_ep e now hub partial_ more round (List.foldl (snapStep e now hub round) (n3, false, 0) es)
    unfold EpGe at h5 h6 ⊢
    omega
  · have : ok = false := by simpa using hok
    simp only [this, Bool.not_false, if_true]
    unfold EpGe; omega

theorem sweepAbsent_epoch (e : Env) (n : N) (now : Nat) : EpGe n (N.sweepAbsent e n now) := by
  unfold N.sweepAbsent
  dsimp only
  apply ite_ge_bump
  unfold EpGe
  refine Nat.le_of_eq (Eq.symm (foldl_inv (fun (a : N × Bool) => a.1.epoch = n.epoch) _ n.hv.keys (n, false) ?_ rfl))
  · intro a hub ha
    refine foldl_inv (fun (a : N × Bool) => a.1.epoch = n.epoch) _ _ a ?_ ha
    intro b m hb
    obtain ⟨n1, c1⟩ := b
    simp only at hb ⊢
    repeat' split
    all_goals first | exact hb | skip
    all_goals simp_all [recomputeOne_ep]

theorem recheckNow_epoch (e : Env) (n : N) (now : Nat) : EpGe n (N.recheckNow e n now) := by
  unfold N.recheckNow
  dsimp only
  apply ite_ge_bump
  unfold EpGe
  refine Nat.le_of_eq (Eq.symm (foldl_inv (fun (a : N × Bool) => a.1.epoch = n.epoch) _ n.recheck.keys ({ n with recheck := [] }, false) ?_ rfl))
  · intro b m hb
    obtain ⟨n1, c1⟩ := b
    simp only at hb ⊢
    rcases hr : N.recomputeOne e n1 now m with ⟨n2, ch⟩
    have := recomputeOne_ep e n1 now m
    rw [hr] at this
    simp only; change n2.epoch = n.epoch; change n2.epoch = n1.epoch at this; omega

end Vinc.Membership
