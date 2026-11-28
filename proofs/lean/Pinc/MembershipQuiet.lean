import Pinc.MembershipViewPrimary

/-!
# Membership view: the quiet-window schedule (property 4)

After a late timer or a heal the node opens a quiet window (`begin_quiet`): a removal found inside it is deferred, the
member queued in the `recheck` table with its own instant (the end of the window then open) and its own grace state
(#284). The first block of `tick` (`recheck_due`) then drives each queued removal on its own schedule:

* `beginQuiet_window`: the window lasts `QUIET` from the call and clears the window's grace flag;
  `beginQuiet_heal`: a heal leaves every waiting removal at its own instant and grace state;
  `beginQuiet_late`: a late timer defers every waiting removal to the new window's end, its extra look not begun.
* `recomputeOne_defers`: a removal found inside the window changes nothing in the view and queues the member at the
  window's end with the window's grace state (a member already waiting keeps its own entry).
* `recheckDue_waits`: a tick before a removal's instant leaves its entry as it is.
* `recheckDue_arms`: the first tick at or after its instant, with its extra look not begun, gives it the look: the
  entry moves to `RECHECK_GAP` after the tick with the look begun, and the window lasts at least as long.
* `recheckDue_removes` (`MembershipWindow.lean`): the first tick at or after its instant, with its look run,
  recomputes it with no window open, so a member no eligible copy lists, with no hold, is out of the view whatever
  window a heal has opened since.
* `removeFromView_holds`: a removal found while the source is held (no confirmed home view) queues the member, the
  view untouched.
* `recheckDue_clears`: with the source not held, the recompute queues none of the removals it runs again.
* `recheckDue_keeps_listed`: a member in the view that some eligible hub copy still lists is in the view after
  `recheck_due` (a member that is back is never reported); `recomputeOne_removes`: one that no copy lists, with the
  window over, is removed.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Pinc.Membership
open Pinc.MemInc

/-! ## The recheck table -/

namespace AMap
variable {α : Type}

theorem pair_mem_of_get? (m : AMap α) (k : Nat) (v : α) (h : m.get? k = some v) : (k, v) ∈ m := by
  induction m with
  | nil => simp [get?] at h
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    by_cases hk : a = k
    · subst hk
      have hv : b = v := by simpa [get?] using h
      subst hv
      simp
    · have hr : AMap.get? r k = some v := by simpa [get?, hk] using h
      exact List.mem_cons_of_mem _ (ih hr)

theorem key_mem_of_get? (m : AMap α) (k : Nat) (v : α) (h : m.get? k = some v) : k ∈ m.keys :=
  List.mem_map.2 ⟨(k, v), pair_mem_of_get? m k v h, rfl⟩

/-- An entry the filter keeps is found in the filtered table. -/
theorem get?_filter_of (m : AMap α) (g : Nat × α → Bool) (k : Nat) (v : α) (h : m.get? k = some v)
    (hg : g (k, v) = true) : AMap.get? (m.filter g) k = some v := by
  induction m with
  | nil => simp [get?] at h
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    by_cases hk : a = k
    · subst hk
      have hv : b = v := by simpa [get?] using h
      subst hv
      simp [List.filter_cons, hg, get?]
    · have hr : AMap.get? r k = some v := by simpa [get?, hk] using h
      have ih' := ih hr
      by_cases hgp : g (a, b) = true
      · simpa [List.filter_cons, hgp, get?, hk] using ih'
      · simpa [List.filter_cons, hgp] using ih'

/-- A table whose values change and whose keys stay: the entry of `k` is the changed one. -/
theorem get?_map_keys {β : Type} (m : AMap α) (f : Nat × α → Nat × β) (hf : ∀ p, (f p).1 = p.1) (k : Nat) :
    AMap.get? (m.map f) k = (m.get? k).map (fun v => (f (k, v)).2) := by
  induction m with
  | nil => simp [get?]
  | cons p r ih =>
    obtain ⟨a, b⟩ := p
    by_cases hk : a = k
    · subst hk
      simp [get?, hf]
    · simpa [get?, hf, hk] using ih

theorem get?_orIns_of (m : AMap α) (j k : Nat) (w v : α) (h : m.get? k = some v) : (m.orIns j w).get? k = some v := by
  unfold orIns
  split
  · exact h
  · rename_i hj
    by_cases hk : k = j
    · subst hk
      rw [has_iff_get, h] at hj
      simp at hj
    · rw [get?_insert_ne _ _ _ _ hk]; exact h

theorem get?_orIns_self (m : AMap α) (k : Nat) (w : α) : (m.orIns k w).get? k = some ((m.get? k).getD w) := by
  unfold orIns
  split
  · rename_i hk
    rw [has_iff_get] at hk
    cases hg : m.get? k with
    | none => rw [hg] at hk; simp at hk
    | some v => rfl
  · rename_i hk
    rw [get?_insert_self]
    rw [has_iff_get] at hk
    cases hg : m.get? k with
    | none => rfl
    | some v => rw [hg] at hk; simp at hk
end AMap

/-! ## `begin_quiet` and the deferral -/

theorem tick_eq (e : Env) (n : N) (now : Nat) :
    N.tick e n now =
      (let n := N.recheckDue e n now
       let n := if n.absentDue now then N.sweepAbsent e n now else n
       let n := if n.sent != some (n.ver, n.th) then N.renew e n now false false else n
       let n := if n.isHub || n.nextSlow ≤ now then
           N.slowTick e (if !n.isHub then { n with nextSlow := satAdd now SLOW_TICK } else n) now
         else n
       if n.isHub then N.hubTick e n now else n) := rfl

theorem beginQuiet_window (n : N) (now cause : Nat) :
    (n.beginQuiet now cause).quietUntil = satAdd now QUIET ∧ (n.beginQuiet now cause).regrace = false := by
  unfold N.beginQuiet N.trace
  dsimp only
  constructor <;> (repeat' split) <;> rfl

/-- **A heal leaves every waiting removal at its own instant and grace state** (#284): `begin_quiet` for a heal
(`cause = 1`) does not touch the recheck table. -/
theorem beginQuiet_heal (n : N) (now : Nat) : (n.beginQuiet now 1).recheck = n.recheck := by
  unfold N.beginQuiet
  simp

/-- **A late timer defers every waiting removal to the new window's end**, its extra look not begun (`cause = 0`, the
reference model's rule). -/
theorem beginQuiet_late (n : N) (now : Nat) :
    (n.beginQuiet now 0).recheck = n.recheck.map (fun (p : Nat × (Nat × Bool)) => (p.1, (satAdd now QUIET, false))) := by
  unfold N.beginQuiet
  simp

/-- A removal found inside the quiet window is deferred: the member waits at the window's end with the window's grace
state, or under the entry it already had. -/
theorem recomputeOne_defers (e : Env) (n : N) (now m : Nat) (hin : n.members.has m = true)
    (hc : (n.candidates now (n.source now) m).1 = none) (hold : (n.source now).hold = false)
    (hq : now < n.quietUntil) (hr : n.recheck.len < MAX_TABLE) :
    (N.recomputeOne e n now m).1.members = n.members ∧
    (N.recomputeOne e n now m).1.recheck = n.recheck.orIns m (n.quietUntil, n.regrace) ∧
    (N.recomputeOne e n now m).2 = false := by
  rw [recomputeOne_none e n now m hc]
  obtain ⟨c, hcur⟩ : ∃ c, n.members.get? m = some c := by
    rw [AMap.has_iff_get] at hin
    cases h : n.members.get? m with
    | none => rw [h] at hin; simp at hin
    | some c => exact ⟨c, rfl⟩
  rw [hcur]
  exact removeFromView_defers e n now m c _ _ hold hq hr

/-! ## What `remove_from_view` and `recompute_one` do to the table -/

/-- A removal found while the source is held (no confirmed home view) changes nothing in the view and queues the member for
a second look, as a removal inside the quiet window does (commit 6355d7d): no hub copy lists the member to bring it back. -/
theorem removeFromView_holds (e : Env) (n : N) (now m : Nat) (c : ViewEntry) (src : Source) (x : Bool)
    (hh : src.hold = true) (hr : n.recheck.len < MAX_TABLE) :
    N.removeFromView e n now m (some c) src x =
      ({ n with recheck := n.recheck.orIns m (n.quietUntil, n.regrace),
                held := if n.recheck.has m then n.held else n.held.ins m }, false) := by
  unfold N.removeFromView
  by_cases hq : n.recheck.has m = true <;> simp [hh, hr, hq]

/-- Whatever it decides, `remove_from_view` leaves the table, or queues `m` under the window's end and grace state
unless it already waits. -/
theorem removeFromView_recheck_or (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (x : Bool) :
    (N.removeFromView e n now m cur src x).1.recheck = n.recheck ∨
      (N.removeFromView e n now m cur src x).1.recheck = n.recheck.orIns m (n.quietUntil, n.regrace) := by
  unfold N.removeFromView
  split
  · exact Or.inl rfl
  · split
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl
    · split
      · exact Or.inr (trace_recheck _ _)
      · left
        by_cases hh : n.isHub = true <;> by_cases hg : (n.goneVer.len < MAX_TABLE ∨ n.goneVer.has m = true) <;>
          by_cases hl : n.left.has m = true <;> by_cases hx : x = true <;> simp [hh, hg, hl, hx]

theorem removeFromView_recheck (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (x : Bool)
    (hq : ¬ now < n.quietUntil) (hh : src.hold = false) : (N.removeFromView e n now m cur src x).1.recheck = n.recheck := by
  unfold N.removeFromView
  split
  · rfl
  · split
    · rename_i h; rw [hh] at h; cases h
    · split
      · rename_i h; simp at h; omega
      · by_cases hh : n.isHub = true <;> by_cases hg : (n.goneVer.len < MAX_TABLE ∨ n.goneVer.has m = true) <;>
          by_cases hl : n.left.has m = true <;> by_cases hx : x = true <;> simp [hh, hg, hl, hx]

theorem rcKnown_recheck (e : Env) (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : (rcKnown e n m best c).1.recheck = n.recheck := by
  unfold rcKnown
  by_cases h1 : best.inc / 65536 = c.rc.inc / 65536 <;> by_cases h2 : (best.inc / 65536 == c.rc.inc / 65536 && decide (c.rc.inc ≤ best.inc)) = true <;>
    by_cases h3 : (best.ver != c.rc.ver) = true <;> by_cases h4 : (best.th != c.rc.th) = true <;>
    by_cases h5 : (match (some (c.rc.ver, c.rc.th)).orElse (fun _ => (n.emit (.joined m)).goneVer.get? m) with | some (ver, th) => ver != best.ver | none => false) = true <;>
    simp [h1, h2, h3, h4, h5] <;> split <;> simp_all

theorem rcNew_recheck (e : Env) (n : N) (m : Nat) (best : Rec) : (rcNew e n m best).1.recheck = n.recheck := by
  unfold rcNew
  split
  · rfl
  · dsimp only
    repeat' split
    all_goals simp_all

theorem rcTail_recheck (n : N) (m : Nat) (absent changed : Bool) : (rcTail n m absent changed).1.recheck = n.recheck := by
  rfl

theorem recomputeOne_recheck (e : Env) (n : N) (now m : Nat) (hq : ¬ now < n.quietUntil)
    (hh : (n.source now).hold = false) :
    (N.recomputeOne e n now m).1.recheck = n.recheck := by
  rw [recomputeOne_eq_v]
  dsimp only
  split
  · exact removeFromView_recheck e n now m _ _ _ hq hh
  · rename_i b0 a0 hb
    have hm : (if (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0))) = true then
        N.homeDelta e n m b0 .alive else n).recheck = n.recheck := by
      by_cases hc : (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0))) = true
      · rw [if_pos hc]; exact homeDelta_recheck n e m b0 .alive
      · rw [if_neg hc]
    generalize (if (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0))) = true then
        N.homeDelta e n m b0 .alive else n) = n1 at hm ⊢
    split
    · rename_i c hc
      have k1 := rcKnown_recheck e n1 m b0 c
      generalize rcKnown e n1 m b0 c = R at k1 ⊢
      obtain ⟨r1, r2, r3⟩ := R
      simp only [] at k1 ⊢
      split
      · simp [k1, hm]
      · rw [rcTail_recheck]; simp [k1, hm]
    · rename_i hc
      have k1 := rcNew_recheck e n1 m b0
      generalize rcNew e n1 m b0 = R at k1 ⊢
      obtain ⟨r1, r2, r3⟩ := R
      simp only [] at k1 ⊢
      split
      · simp [k1, hm]
      · rw [rcTail_recheck]; simp [k1, hm]


/-- `recompute_one` leaves the table, or queues `m` as `remove_from_view` does. -/
theorem recomputeOne_recheck_or (e : Env) (n : N) (now m : Nat) :
    (N.recomputeOne e n now m).1.recheck = n.recheck ∨
      (N.recomputeOne e n now m).1.recheck = n.recheck.orIns m (n.quietUntil, n.regrace) := by
  rw [recomputeOne_eq_v]
  dsimp only
  split
  · exact removeFromView_recheck_or e n now m _ _ _
  · left
    rename_i b0 a0 hb
    have hm : (if (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0))) = true then
        N.homeDelta e n m b0 .alive else n).recheck = n.recheck := by
      by_cases hc : (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0))) = true
      · rw [if_pos hc]; exact homeDelta_recheck n e m b0 .alive
      · rw [if_neg hc]
    generalize (if (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0))) = true then
        N.homeDelta e n m b0 .alive else n) = n1 at hm ⊢
    split
    · rename_i c hc
      have k1 := rcKnown_recheck e n1 m b0 c
      generalize rcKnown e n1 m b0 c = R at k1 ⊢
      obtain ⟨r1, r2, r3⟩ := R
      simp only [] at k1 ⊢
      split
      · simp [k1, hm]
      · rw [rcTail_recheck]; simp [k1, hm]
    · rename_i hc
      have k1 := rcNew_recheck e n1 m b0
      generalize rcNew e n1 m b0 = R at k1 ⊢
      obtain ⟨r1, r2, r3⟩ := R
      simp only [] at k1 ⊢
      split
      · simp [k1, hm]
      · rw [rcTail_recheck]; simp [k1, hm]

/-- `recompute_one` never changes the entry of a member already waiting. -/
theorem recomputeOne_recheck_get (e : Env) (n : N) (now m k : Nat) (v : Nat × Bool) (h : n.recheck.get? k = some v) :
    (N.recomputeOne e n now m).1.recheck.get? k = some v := by
  rcases recomputeOne_recheck_or e n now m with h1 | h1
  · rw [h1]; exact h
  · rw [h1]; exact AMap.get?_orIns_of _ _ _ _ _ h

theorem bump_recheck (n : N) : n.bump.recheck = n.recheck := by unfold N.bump; simp
theorem bump_quietUntil (n : N) : n.bump.quietUntil = n.quietUntil := by unfold N.bump; simp

theorem Keeps.hubUp {n n' : N} (h : Keeps n n') (now x : Nat) : n'.hubUp now x = n.hubUp now x := by
  obtain ⟨-, -, -, hme, -, -, -, hup, hhe, -⟩ := h
  unfold N.hubUp; rw [hme, hup, hhe]

theorem Keeps.source {n n' : N} (h : Keeps n n') (now : Nat) : n'.source now = n.source now := by
  have hu := h.hubUp
  obtain ⟨hv, -, -, hme, hhub, -, -, hup, hhe, hpr, hho, -⟩ := h
  unfold N.source
  rw [hpr, hhub, hho, hv]
  simp only [hu]


/-- What the source and the candidates read: the hub copies, the node's identity and role, the sessions, the times
heard and the home. -/
def SrcEq (n n' : N) : Prop :=
  n'.hv = n.hv ∧ n'.me = n.me ∧ n'.isHub = n.isHub ∧ n'.up = n.up ∧ n'.heard = n.heard ∧ n'.primary = n.primary ∧
    n'.homeOk = n.homeOk

theorem SrcEq.refl (n : N) : SrcEq n n := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SrcEq.trans {a b c : N} (h1 : SrcEq a b) (h2 : SrcEq b c) : SrcEq a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7⟩

theorem SrcEq.hubUp {n n' : N} (h : SrcEq n n') (now x : Nat) : n'.hubUp now x = n.hubUp now x := by
  obtain ⟨-, hme, -, hup, hhe, -, -⟩ := h
  unfold N.hubUp; rw [hme, hup, hhe]

theorem SrcEq.source {n n' : N} (h : SrcEq n n') (now : Nat) : n'.source now = n.source now := by
  have hu := h.hubUp
  obtain ⟨hv, -, hhub, -, -, hpr, hho⟩ := h
  unfold N.source
  rw [hpr, hhub, hho, hv]
  simp only [hu]

theorem SrcEq.candidates {n n' : N} (h : SrcEq n n') (now m : Nat) :
    n'.candidates now (n'.source now) m = n.candidates now (n.source now) m := by
  rw [h.source now]
  exact candidates_congr n n' now _ m h.1 (h.hubUp now)

theorem Keeps.srcEq {n n' : N} (h : Keeps n n') : SrcEq n n' := by
  obtain ⟨hv, -, -, hme, hhub, -, -, hup, hhe, hpr, hho, -⟩ := h
  exact ⟨hv, hme, hhub, hup, hhe, hpr, hho⟩

theorem bump_srcEq (n : N) : SrcEq n n.bump := by
  unfold N.bump N.emit
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## `recheck_due` -/

theorem recheckArm_recheck (n : N) (now : Nat) :
    (N.recheckArm n now).recheck = (n.recheck.filter (fun p => !recheckReady now p)).map (recheckStep now) := by
  unfold N.recheckArm; dsimp only; split <;> rfl

theorem recheckArm_members (n : N) (now : Nat) : (N.recheckArm n now).members = n.members := by
  unfold N.recheckArm; dsimp only; split <;> rfl

theorem recheckArm_srcEq (n : N) (now : Nat) : SrcEq n ({ N.recheckArm n now with regrace := false } : N) := by
  unfold N.recheckArm; dsimp only; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The first part of `recheck_due` on a waiting removal whose extra look has not run by `now`. -/
theorem recheckArm_get (n : N) (now k : Nat) (v : Nat × Bool) (h : n.recheck.get? k = some v)
    (hr : recheckReady now (k, v) = false) :
    (N.recheckArm n now).recheck.get? k = some (recheckStep now (k, v)).2 := by
  rw [recheckArm_recheck, AMap.get?_map_keys _ (recheckStep now) (fun p => by unfold recheckStep; split <;> rfl),
    AMap.get?_filter_of _ (fun p => !recheckReady now p) _ _ h (by simp [hr])]
  rfl

theorem recheckFold_keeps (e : Env) (n : N) (now : Nat) (ks : List Nat) : Keeps n (N.recheckFold e n now ks).1 := by
  unfold N.recheckFold
  refine foldl_inv (fun (a : N × Bool) => Keeps n a.1) _ ks (n, false) ?_ (Keeps.refl n)
  intro b j hb
  obtain ⟨n1, c1⟩ := b
  simp only at hb ⊢
  rcases hr : N.recomputeOne e n1 now j with ⟨n2, ch⟩
  have := (recomputeOne_keeps2 e n1 now j).1
  rw [hr] at this
  exact Keeps.trans hb this

theorem recheckFold_get (e : Env) (n : N) (now : Nat) (ks : List Nat) (k : Nat) (v : Nat × Bool)
    (h : n.recheck.get? k = some v) : (N.recheckFold e n now ks).1.recheck.get? k = some v := by
  unfold N.recheckFold
  refine foldl_inv (fun (a : N × Bool) => a.1.recheck.get? k = some v) _ ks (n, false) ?_ h
  intro b j hb
  obtain ⟨n1, c1⟩ := b
  simp only at hb ⊢
  rcases hr : N.recomputeOne e n1 now j with ⟨n2, ch⟩
  have := recomputeOne_recheck_get e n1 now j k v hb
  rw [hr] at this
  exact this

theorem recheckRun_srcEq (e : Env) (n : N) (now : Nat) (ks : List Nat) : SrcEq n (N.recheckRun e n now ks) := by
  have hk := (recheckFold_keeps e { n with quietUntil := 0 } now ks).srcEq
  unfold N.recheckRun
  dsimp only
  split
  · exact SrcEq.trans hk (bump_srcEq _)
  · exact hk

/-- `recheck_due` leaves what the source and the candidates read. -/
theorem recheckDue_srcEq (e : Env) (n : N) (now : Nat) : SrcEq n (N.recheckDue e n now) := by
  rw [recheckDue_eq]
  split
  · unfold N.recheckArm; dsimp only; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact SrcEq.trans (recheckArm_srcEq n now) (recheckRun_srcEq e _ now _)

/-- An entry the recompute does not run keeps its value through it and through the window put back. -/
theorem recheckRun_get (e : Env) (n : N) (now : Nat) (ks : List Nat) (k : Nat) (v : Nat × Bool)
    (h : n.recheck.get? k = some v) : (N.recheckRun e n now ks).recheck.get? k = some v := by
  unfold N.recheckRun
  dsimp only
  split
  · rw [bump_recheck]; exact recheckFold_get e { n with quietUntil := 0 } now ks k v h
  · exact recheckFold_get e { n with quietUntil := 0 } now ks k v h

theorem recheckRun_quietUntil (e : Env) (n : N) (now : Nat) (ks : List Nat) :
    (N.recheckRun e n now ks).quietUntil = n.quietUntil := by
  unfold N.recheckRun
  dsimp only
  split
  · rw [bump_quietUntil]
  · rfl

/-- **A tick before a removal's instant leaves it as it is.** -/
theorem recheckDue_waits (e : Env) (n : N) (now m d : Nat) (g : Bool) (hw : n.recheck.get? m = some (d, g))
    (hd : now < d) : (N.recheckDue e n now).recheck.get? m = some (d, g) := by
  have hr : recheckReady now (m, (d, g)) = false := by simp [recheckReady, Nat.not_le.mpr hd]
  have hg := recheckArm_get n now m (d, g) hw hr
  have hs : (recheckStep now (m, (d, g))).2 = (d, g) := by simp [recheckStep, recheckLook, Nat.not_le.mpr hd]
  rw [hs] at hg
  rw [recheckDue_eq]
  split
  · exact hg
  · exact recheckRun_get e ({ N.recheckArm n now with regrace := false } : N) now _ m _ hg

/-- **The first tick at or after a removal's instant gives it its extra look** when it has not begun: the removal then
waits until `RECHECK_GAP` after the tick, its look begun, and the window lasts at least as long. -/
theorem recheckDue_arms (e : Env) (n : N) (now m d : Nat) (hw : n.recheck.get? m = some (d, false)) (hd : d ≤ now) :
    (N.recheckDue e n now).recheck.get? m = some (satAdd now RECHECK_GAP, true) ∧
    satAdd now RECHECK_GAP ≤ (N.recheckDue e n now).quietUntil := by
  have hr : recheckReady now (m, (d, false)) = false := by simp [recheckReady]
  have hl : recheckLook now (m, (d, false)) = true := by simp [recheckLook, hd]
  have hg := recheckArm_get n now m (d, false) hw hr
  have hs : (recheckStep now (m, (d, false))).2 = (satAdd now RECHECK_GAP, true) := by simp [recheckStep, hl]
  rw [hs] at hg
  have hany : n.recheck.any (recheckLook now) = true :=
    List.any_eq_true.2 ⟨(m, (d, false)), AMap.pair_mem_of_get? _ _ _ hw, hl⟩
  have hq : satAdd now RECHECK_GAP ≤ (N.recheckArm n now).quietUntil := by
    unfold N.recheckArm
    dsimp only
    rw [if_pos hany]
    exact Nat.le_max_right _ _
  rw [recheckDue_eq]
  split
  · exact ⟨hg, hq⟩
  · refine ⟨recheckRun_get e ({ N.recheckArm n now with regrace := false } : N) now _ m _ hg, ?_⟩
    rw [recheckRun_quietUntil]
    exact hq

/-- With the source not held, the recompute of `recheck_due` queues none of the removals it runs again: the table is
what the first part left (no window is open during the recompute). While the source is held a removal is queued again
(`removeFromView_holds`). -/
theorem recheckFold_recheck (e : Env) (n : N) (now : Nat) (ks : List Nat) (hq : ¬ now < n.quietUntil)
    (hh : (n.source now).hold = false) : (N.recheckFold e n now ks).1.recheck = n.recheck := by
  unfold N.recheckFold
  have key : ∀ (ks : List Nat) (a : N × Bool), Keeps n a.1 → a.1.recheck = n.recheck →
      (ks.foldl (fun (a : N × Bool) m => let (n', c) := N.recomputeOne e a.1 now m; (n', a.2 || c)) a).1.recheck
        = n.recheck := by
    intro ks
    induction ks with
    | nil => intro a _ h; exact h
    | cons k r ih =>
      intro a h1 h2
      simp only [List.foldl_cons]
      apply ih
      · exact Keeps.trans h1 (recomputeOne_keeps2 e a.1 now k).1
      · have hq' : ¬ now < a.1.quietUntil := by rw [h1.2.2.2.2.2.2.2.2.2.2.2]; exact hq
        have hh' : (a.1.source now).hold = false := by rw [h1.source now]; exact hh
        exact (recomputeOne_recheck e a.1 now k hq' hh').trans h2
  exact key ks (n, false) (Keeps.refl n) rfl

theorem recheckDue_clears (e : Env) (n : N) (now : Nat) (hh : (n.source now).hold = false) :
    (N.recheckDue e n now).recheck = (N.recheckArm n now).recheck := by
  rw [recheckDue_eq]
  split
  · rfl
  · have hs := recheckArm_srcEq n now
    unfold N.recheckRun
    dsimp only
    have h0 : SrcEq ({ N.recheckArm n now with regrace := false } : N)
        ({ ({ N.recheckArm n now with regrace := false } : N) with quietUntil := 0 } : N) :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hf := recheckFold_recheck e ({ ({ N.recheckArm n now with regrace := false } : N) with quietUntil := 0 } : N) now
      (AMap.keys (n.recheck.filter (recheckReady now))) (Nat.not_lt_zero now)
      (by rw [h0.source now, hs.source now]; exact hh)
    split
    · rw [bump_recheck]; exact hf
    · exact hf

theorem Keeps.candidates {n n' : N} (h : Keeps n n') (now m : Nat) :
    n'.candidates now (n'.source now) m = n.candidates now (n.source now) m := by
  rw [h.source now]
  exact candidates_congr n n' now _ m h.1 (h.hubUp now)


theorem recheckFold_keeps_listed (e : Env) (n : N) (now m : Nat) (ks : List Nat) (hin : n.members.has m = true)
    (hc : (n.candidates now (n.source now) m).1 ≠ none) : (N.recheckFold e n now ks).1.members.has m = true := by
  unfold N.recheckFold
  have key : ∀ (ks : List Nat) (a : N × Bool), Keeps n a.1 → a.1.members.has m = true →
      (Keeps n (ks.foldl (fun (a : N × Bool) m => let (n', c) := N.recomputeOne e a.1 now m; (n', a.2 || c)) a).1 ∧
       (ks.foldl (fun (a : N × Bool) m => let (n', c) := N.recomputeOne e a.1 now m; (n', a.2 || c)) a).1.members.has m = true) := by
    intro ks
    induction ks with
    | nil => intro a h1 h2; exact ⟨h1, h2⟩
    | cons k r ih =>
      intro a h1 h2
      simp only [List.foldl_cons]
      apply ih
      · exact Keeps.trans h1 (recomputeOne_keeps2 e a.1 now k).1
      · simp only []
        by_cases hk : k = m
        · subst hk
          have hcand : (a.1.candidates now (a.1.source now) k).1 ≠ none := by
            rw [h1.candidates now k]; exact hc
          rcases recomputeOne_listed_stays e a.1 now k hcand with h | ⟨h, -⟩
          · exact h
          · rw [h] at h2; cases h2
        · have := (recomputeOne_keeps2 e a.1 now k).2 m (Ne.symm hk)
          rw [AMap.has_iff_get] at h2 ⊢
          rw [this]; exact h2
  exact (key ks (n, false) (Keeps.refl _) hin).2

/-- A member in the view that some eligible hub copy still lists is in the view after `recheck_due`: a member that is
back is never reported down. -/
theorem recheckDue_keeps_listed (e : Env) (n : N) (now m : Nat) (hin : n.members.has m = true)
    (hc : (n.candidates now (n.source now) m).1 ≠ none) : (N.recheckDue e n now).members.has m = true := by
  rw [recheckDue_eq]
  split
  · rw [recheckArm_members]; exact hin
  · have hs := recheckArm_srcEq n now
    have h0 : SrcEq ({ N.recheckArm n now with regrace := false } : N)
        ({ ({ N.recheckArm n now with regrace := false } : N) with quietUntil := 0 } : N) :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hf := recheckFold_keeps_listed e ({ ({ N.recheckArm n now with regrace := false } : N) with quietUntil := 0 } : N)
      now m (AMap.keys (n.recheck.filter (recheckReady now))) (by rw [← recheckArm_members n now] at hin; exact hin)
      (by rw [h0.candidates now m, hs.candidates now m]; exact hc)
    unfold N.recheckRun
    dsimp only
    split
    · rw [bump_members]; exact hf
    · exact hf

/-- With no copy listing the member, no hold on removals and the window over, the member is removed. -/
theorem recomputeOne_removes (e : Env) (n : N) (now m : Nat) (hin : n.members.has m = true)
    (hc : (n.candidates now (n.source now) m).1 = none) (hold : (n.source now).hold = false)
    (hq : ¬ now < n.quietUntil) : (N.recomputeOne e n now m).1.members.has m = false := by
  rw [recomputeOne_none e n now m hc]
  obtain ⟨c, hcur⟩ : ∃ c, n.members.get? m = some c := by
    rw [AMap.has_iff_get] at hin
    cases h : n.members.get? m with
    | none => rw [h] at hin; simp at hin
    | some c => exact ⟨c, rfl⟩
  rw [hcur]
  unfold N.removeFromView
  simp only [hold, Bool.false_eq_true, if_false]
  have : ¬ (decide (now < n.quietUntil) && decide (n.recheck.len < MAX_TABLE)) = true := by simp [hq]
  rw [if_neg this]
  by_cases hh : n.isHub = true <;> by_cases hg : (n.goneVer.len < MAX_TABLE ∨ n.goneVer.has m = true) <;>
    by_cases hl : n.left.has m = true <;> by_cases hx : (n.candidates now (n.source now) m).2 = true <;>
    simp [hh, hg, hl, hx, AMap.has_erase_self]

end Pinc.Membership
