import Pinc.MembershipCompleteRoster

/-!
# Completeness and accuracy over timed hypotheses, part 7: `slow_tick` leaves the roster alone

`slow_tick` (the ACK wait, the round trip samples, the stale hub copies, the omission sweep, the primary) works on the
member view and the sessions; it never touches the lease table. The loops are restated as named steps (`stHello`,
`dshStep`, `saStep`, `saInner`), proved equal to the model by `rfl`, and each step is shown to keep the roster.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Pinc.Membership.Cmp
open Pinc.Membership
open Pinc.MemInc

theorem foldl_roster {α : Type} (L : List α) (f : N → α → N) (n : N) (h : ∀ b a, b.roster = n.roster → (f b a).roster = n.roster) :
    (L.foldl f n).roster = n.roster := foldl_inv (fun x : N => x.roster = n.roster) f L n h rfl

theorem rcFold_roster (e : Env) (now : Nat) (ks : List Nat) (a : N × Bool) :
    (ks.foldl (fun (b : N × Bool) m => let (n', c) := N.recomputeOne e b.1 now m; (n', b.2 || c)) a).1.roster = a.1.roster := by
  refine foldl_inv (fun x : N × Bool => x.1.roster = a.1.roster) _ _ _ (fun b k hb => ?_) rfl
  generalize hR : N.recomputeOne e b.1 now k = R
  have h := recomputeOne_roster e b.1 now k
  rw [hR] at h
  obtain ⟨n', c⟩ := R
  simp only [] at h ⊢
  rw [h]; exact hb

theorem sampleSessionRtts_roster (e : Env) (n : N) (now : Nat) : (N.sampleSessionRtts e n now).roster = n.roster := by
  unfold N.sampleSessionRtts
  dsimp only
  rw [ite_roster, reselect_roster, ite_self]
  apply foldl_roster
  intro b a hb
  repeat' split
  all_goals first | exact hb | (simp; exact hb) | simp [hb]

/-- The visit of `hub` in the first loop of `slow_tick`. -/
def stHello (e : Env) (now : Nat) (hub : Nat) (n : N) : N :=
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
    else n

/-- The visit of `hub` in `drop_stale_hubs`. -/
def dshStep (e : Env) (now : Nat) (a : N × Bool) (hub : Nat) : N × Bool :=
  let (n, changed) := a
  if n.hubUp now hub then a
  else match n.hv.get? hub with
    | none => a
    | some copy =>
      let n := { n with hv := n.hv.erase hub }
      let n := n.trace (.hubStale hub)
      let n := if n.up.has hub && HUB_STALE ≤ now - (n.heard.get? hub).getD 0 then n.close hub .stale else n
      copy.entries.keys.foldl (fun (b : N × Bool) m => let (n', c) := N.recomputeOne e b.1 now m; (n', b.2 || c)) (n, changed)

/-- Whether the omission of `m` in the copy of `hub` has lasted a full lease. -/
def saExpired (now hub m : Nat) (n : N) : Bool :=
  match (n.hv.get? hub).bind (fun c => c.entries.get? m) with
  | some ce => (match ce.absentSince with | some t => decide (LEASE ≤ now - t) | none => false)
  | none => false

/-- The visit of `m` in the inner loop of `sweep_absent` for `hub`. -/
def saInner (e : Env) (now hub : Nat) (a : N × Bool) (m : Nat) : N × Bool :=
  let (n, changed) := a
  let expired := saExpired now hub m n
  if expired then
    let (n, ch) := N.recomputeOne e n now m
    let n := match n.hv.get? hub with
      | some c => { n with hv := n.hv.insert hub { c with entries := c.entries.erase m } }
      | none => n
    (n, changed || ch)
  else (n.keepAbsent hub m, changed)

/-- The visit of `hub` in `sweep_absent`. -/
def saStep (e : Env) (now : Nat) (a : N × Bool) (hub : Nat) : N × Bool :=
  let ks := match a.1.hv.get? hub with | some c => c.entries.keys | none => []
  ks.foldl (saInner e now hub) a

theorem sweepAbsent_eq_c (e : Env) (n : N) (now : Nat) :
    N.sweepAbsent e n now =
      (let n0 : N := { n with nextAbsent := none }
       let (n, changed) := n0.hv.keys.foldl (saStep e now) (n0, false)
       if changed then n.bump else n) := rfl

theorem dropStaleHubs_eq (e : Env) (n : N) (now : Nat) :
    N.dropStaleHubs e n now =
      (let stale := (n.hv.keys.filter (fun k => !n.hubUp now k)).length
       if stale == 0 || n.hv.len ≤ stale then n
       else
         let (n, changed) := n.hv.keys.foldl (dshStep e now) (n, false)
         if changed then n.bump else n) := rfl

theorem slowTick_eq_c (e : Env) (n : N) (now : Nat) :
    N.slowTick e n now =
      (let n := forKeys n.helloAt.keys (stHello e now) n
       let n := if !n.isHub then N.sampleSessionRtts e n now else n
       let n := N.dropStaleHubs e n now
       let n := N.sweepAbsent e n now
       let primaryDown := match n.primary with | none => true | some p => !n.hubUp now p
       if primaryDown then N.reselect e n now else n) := rfl

theorem stHello_roster (e : Env) (now hub : Nat) (n : N) : (stHello e now hub n).roster = n.roster := by
  unfold stHello
  repeat' split
  all_goals first | rfl | simp [dropPeer_roster] | simp_all [dropPeer_roster]

theorem dshStep_roster (e : Env) (now : Nat) (a : N × Bool) (hub : Nat) : (dshStep e now a hub).1.roster = a.1.roster := by
  obtain ⟨n, ch⟩ := a
  unfold dshStep
  dsimp only
  split
  · rfl
  · split
    · rfl
    · rename_i copy _
      refine (rcFold_roster e now copy.entries.keys _).trans ?_
      dsimp only
      split <;> simp

theorem saInner_roster (e : Env) (now hub : Nat) (a : N × Bool) (m : Nat) : (saInner e now hub a m).1.roster = a.1.roster := by
  obtain ⟨n, ch⟩ := a
  unfold saInner
  dsimp only
  split
  · generalize hR : N.recomputeOne e n now m = R
    have h := recomputeOne_roster e n now m
    rw [hR] at h
    obtain ⟨n', c⟩ := R
    simp only [] at h ⊢
    split <;> simp [h]
  · rfl

theorem saStep_roster (e : Env) (now : Nat) (a : N × Bool) (hub : Nat) : (saStep e now a hub).1.roster = a.1.roster := by
  unfold saStep
  exact foldl_inv (fun x : N × Bool => x.1.roster = a.1.roster) _ _ _ (fun b k hb => by rw [saInner_roster]; exact hb) rfl

theorem dropStaleHubs_roster (e : Env) (n : N) (now : Nat) : (N.dropStaleHubs e n now).roster = n.roster := by
  rw [dropStaleHubs_eq]
  dsimp only
  split
  · rfl
  · have hX : (n.hv.keys.foldl (dshStep e now) (n, false)).1.roster = n.roster :=
      foldl_inv (fun x : N × Bool => x.1.roster = n.roster) _ _ _ (fun b a hb => by rw [dshStep_roster]; exact hb) rfl
    generalize n.hv.keys.foldl (dshStep e now) (n, false) = Y at hX ⊢
    obtain ⟨n1, ch⟩ := Y
    simp only [] at hX ⊢
    split <;> simp [hX]

theorem sweepAbsent_roster (e : Env) (n : N) (now : Nat) : (N.sweepAbsent e n now).roster = n.roster := by
  rw [sweepAbsent_eq_c]
  dsimp only
  have hX : (n.hv.keys.foldl (saStep e now) ({ n with nextAbsent := none }, false)).1.roster = n.roster :=
    foldl_inv (fun x : N × Bool => x.1.roster = n.roster) _ _ _ (fun b a hb => by rw [saStep_roster]; exact hb) rfl
  generalize n.hv.keys.foldl (saStep e now) ({ n with nextAbsent := none }, false) = Y at hX ⊢
  obtain ⟨n1, ch⟩ := Y
  simp only [] at hX ⊢
  split <;> simp [hX]

theorem slowTick_roster (e : Env) (n : N) (now : Nat) : (N.slowTick e n now).roster = n.roster := by
  rw [slowTick_eq_c]
  dsimp only
  have h1 : (forKeys n.helloAt.keys (stHello e now) n).roster = n.roster :=
    forKeys_roster _ _ (fun k n => stHello_roster e now k n) n
  generalize forKeys n.helloAt.keys (stHello e now) n = n1 at h1 ⊢
  have h2 : (if !n1.isHub then N.sampleSessionRtts e n1 now else n1).roster = n1.roster := by
    split
    · exact sampleSessionRtts_roster ..
    · rfl
  generalize (if !n1.isHub then N.sampleSessionRtts e n1 now else n1) = n2 at h2 ⊢
  simp only [ite_roster, reselect_roster, sweepAbsent_roster, dropStaleHubs_roster, h2, h1, ite_self]

end Pinc.Membership.Cmp
