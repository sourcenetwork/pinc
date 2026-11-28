import Pinc.MembershipCompleteRoster

/-!
# Completeness and accuracy over timed hypotheses, part 3: the frames a call hands to the sessions only accumulate

`outSent` is the list of every `Session::send` of the current call, in order. `PS a b` says that `a`'s list is `b`'s with
more frames appended. Every function of the model that can send does so through `tx`, which appends, and no function
removes: this file proves it for the roster rules (`hub_down`, `push_delta` with `apply_delta`, `recompute_one`,
`remove_from_view`, `home_delta`, `carrier_watch`, `carrier_return`), so that a frame handed to a session at one point of a
call is in the list the host takes at the end of the call (`sent_mem_of_ps`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Pinc.Membership.Cmp
open Pinc.Membership
open Pinc.MemInc

/-- `a`'s frames to the sessions are `b`'s with more appended. -/
def PS (a b : N) : Prop := ∃ s, a.outSent = b.outSent ++ s

theorem PS_refl (n : N) : PS n n := ⟨[], by simp⟩
theorem PS_trans {a b c : N} (h1 : PS a b) (h2 : PS b c) : PS a c := by
  obtain ⟨s, hs⟩ := h1; obtain ⟨t, ht⟩ := h2
  exact ⟨t ++ s, by rw [hs, ht, List.append_assoc]⟩
theorem PS_of_sent {a b : N} (h : a.outSent = b.outSent) : PS a b := ⟨[], by simp [h]⟩

theorem sent_mem_of_ps {a b : N} (h : PS a b) (x : Sent) (hx : x ∈ b.outSent) : x ∈ a.outSent := by
  obtain ⟨s, hs⟩ := h; rw [hs]; exact List.mem_append_left _ hx

@[simp] theorem trace_outSent_c (n : N) (t : Tr) : (n.trace t).outSent = n.outSent := by
  unfold N.trace; split <;> (try split) <;> rfl
@[simp] theorem emit_outSent_c (n : N) (e : Ev) : (n.emit e).outSent = n.outSent := by
  unfold N.emit; split <;> rfl
@[simp] theorem bc_outSent (n : N) (b : Bc) : (n.bc b).outSent = n.outSent := rfl
@[simp] theorem ite_outSent (c : Prop) [Decidable c] (a b : N) : (if c then a else b).outSent = if c then a.outSent else b.outSent := by
  split <;> rfl

theorem tx_ps (e : Env) (n : N) (p : Nat) (r : Route) (f : NFrame) : PS (N.tx e n p r f).1 n := by
  unfold N.tx
  split
  · exact PS_refl n
  · exact ⟨[(p, r, f, e.acc.has p)], by simp⟩

theorem tx_mem (e : Env) (n : N) (p : Nat) (r : Route) (f : NFrame) (h1 : n.revoked.has p = false) (h2 : p ≠ n.me) :
    (p, r, f, e.acc.has p) ∈ (N.tx e n p r f).1.outSent := by
  unfold N.tx
  have : (n.revoked.has p || p == n.me) = false := by simp [h1, h2]
  rw [if_neg (by simp [this])]
  simp

theorem deltaTo_ps (e : Env) (n : N) (p m : Nat) (rc : Rec) (a : Alive) : PS (N.deltaTo e n p m rc a) n := tx_ps ..

theorem forKeys_ps (ks : List Nat) (f : Nat → N → N) (h : ∀ k n, PS (f k n) n) (n : N) : PS (forKeys ks f n) n := by
  unfold forKeys
  induction ks generalizing n with
  | nil => exact PS_refl n
  | cons k r ih => simp only [List.foldl_cons]; exact PS_trans (ih (f k n)) (h k n)

theorem bump_ps (n : N) : PS n.bump n := by unfold N.bump; exact PS_of_sent (by simp)

theorem homeDelta_ps (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) : PS (N.homeDelta e n m rc a) n := by
  unfold N.homeDelta
  exact forKeys_ps _ _ (fun k n => by split; exact deltaTo_ps ..; exact PS_refl n) n

theorem ite_ps (c : Prop) [Decidable c] (a b n : N) (h1 : PS a n) (h2 : PS b n) : PS (if c then a else b) n := by
  split <;> assumption

theorem rfvDo_ps (e : Env) (n : N) (now m : Nat) (c : ViewEntry) (x : Bool) : PS (rfvDo e n now m c x).1 n := by
  unfold rfvDo
  dsimp only
  exact ite_ps _ _ _ _ (homeDelta_ps ..) (PS_of_sent (by simp)) |> fun h => PS_trans h (PS_of_sent (by simp))

theorem removeFromView_ps (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (ex : Bool) :
    PS (N.removeFromView e n now m cur src ex).1 n := by
  cases cur with
  | none => unfold N.removeFromView; exact PS_refl n
  | some c =>
    by_cases hh : src.hold = true
    · unfold N.removeFromView; simp [hh]; split
      · exact PS_of_sent (by simp)
      · exact PS_refl n
    · by_cases hq : now < n.quietUntil ∧ n.recheck.len < MAX_TABLE
      · unfold N.removeFromView; simp [hq.1, hq.2]; exact PS_of_sent (by simp)
      · rw [removeFromView_eq e n now m c src ex (by simpa using hh) hq]; exact rfvDo_ps ..

/-! ## `recompute_one` -/

theorem rcOldVer_sent (n : N) (m : Nat) (best : Rec) (old : Option (Nat × List Nat)) : (n.rcOldVer m best old).outSent = n.outSent := by
  unfold N.rcOldVer; repeat' split
  all_goals simp
theorem rcOldBoth_sent (n : N) (m : Nat) (best : Rec) (old : Option (Nat × List Nat)) : (n.rcOldBoth m best old).outSent = n.outSent := by
  unfold N.rcOldBoth; repeat' split
  all_goals simp
theorem rcSusp_sent (n : N) (m : Nat) (a c : Bool) : (n.rcSusp m a c).1.outSent = n.outSent := by
  unfold N.rcSusp; repeat' split
  all_goals simp
theorem rcVer_sent (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : (n.rcVer m best c).1.outSent = n.outSent := by
  unfold N.rcVer; split <;> simp
theorem rcTh_sent (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : (n.rcTh m best c).1.outSent = n.outSent := by
  unfold N.rcTh; split <;> simp
theorem rcSame_sent (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : (n.rcSame m best c).1.outSent = n.outSent := by
  unfold N.rcSame
  dsimp only
  generalize hn : ({ n with members := n.members.modify m (fun x => { x with rc := { x.rc with inc := best.inc } }) } : N) = n1
  have h1 : n1.outSent = n.outSent := by rw [← hn]
  have h2 := rcVer_sent n1 m best c
  have h3 := rcTh_sent (n1.rcVer m best c).1 m best c
  exact h3.trans (h2.trans h1)
theorem rcNewer_sent (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : (n.rcNewer m best c).1.outSent = n.outSent := by
  unfold N.rcNewer
  dsimp only
  simp [rcOldVer_sent]
theorem rcFresh_sent (n : N) (m : Nat) (best : Rec) : (n.rcFresh m best).1.outSent = n.outSent := by
  unfold N.rcFresh
  split
  · rfl
  · dsimp only
    simp [rcOldBoth_sent]
theorem rcArm_sent (n : N) (m : Nat) (best : Rec) (cur : Option ViewEntry) : (n.rcArm m best cur).1.outSent = n.outSent := by
  unfold N.rcArm
  cases cur with
  | none => exact rcFresh_sent n m best
  | some c =>
    dsimp only
    split
    · split
      · exact rcSame_sent n m best c
      · rfl
    · exact rcNewer_sent n m best c

theorem rcAfter_ps (e : Env) (n : N) (m : Nat) (best : Rec) (absent : Bool) (cur : Option ViewEntry) :
    PS (N.rcAfter e n m best absent cur).1 n := by
  unfold N.rcAfter
  dsimp only
  generalize hn : (if n.isHub && (match cur with | none => true | some c => decide (c.rc ≠ best)) then N.homeDelta e n m best .alive else n) = n1
  have h1 : PS n1 n := hn ▸ (ite_ps _ _ _ _ (homeDelta_ps ..) (PS_refl n))
  have h2 := rcArm_sent n1 m best cur
  generalize hr : n1.rcArm m best cur = r
  obtain ⟨n2, ch, early⟩ := r
  rw [hr] at h2
  split
  · exact PS_trans (PS_of_sent h2) h1
  · have h3 := rcSusp_sent n2 m absent ch
    exact PS_trans (PS_of_sent (h3.trans h2)) h1

theorem recomputeOne_ps (e : Env) (n : N) (now m : Nat) : PS (N.recomputeOne e n now m).1 n := by
  rw [recomputeOne_eq]
  unfold N.recomputeOneS
  dsimp only
  split
  · exact removeFromView_ps ..
  · exact rcAfter_ps ..

/-! ## `apply_delta` and `push_delta` -/

theorem adEnsure_sent (n : N) (hub : Nat) : (n.adEnsure hub).1.outSent = n.outSent := by
  unfold N.adEnsure; repeat' split
  all_goals simp
theorem adDown_sent (n : N) (hub m : Nat) (rc : Rec) (a : Alive) (c : HubCopy) : (n.adDown hub m rc a c).outSent = n.outSent := by
  unfold N.adDown; repeat' split
  all_goals simp
theorem adEntries_sent (n : N) (hub m : Nat) (rc : Rec) (a : Alive) : (n.adEntries hub m rc a).outSent = n.outSent := by
  unfold N.adEntries; repeat' split
  all_goals simp [adDown_sent]

theorem applyDeltaCore_ps (e : Env) (n : N) (now hub m : Nat) (rc : Rec) (a : Alive) :
    PS (N.applyDeltaCore e n now hub m rc a) n := by
  rw [applyDeltaCore_eq]
  unfold N.applyDeltaCoreS
  split
  · exact PS_refl n
  · dsimp only
    generalize hE : n.adEnsure hub = r
    obtain ⟨n1, ok⟩ := r
    have h1 : n1.outSent = n.outSent := by have := adEnsure_sent n hub; rw [hE] at this; exact this
    split
    · exact PS_of_sent h1
    · generalize hR : N.recomputeOne e (n1.adEntries hub m rc a) now m = r2
      obtain ⟨n2, ch⟩ := r2
      have h2 : PS n2 n1 := by
        have := recomputeOne_ps e (n1.adEntries hub m rc a) now m
        rw [hR] at this
        exact PS_trans this (PS_of_sent (adEntries_sent ..))
      dsimp only
      split
      · exact PS_trans (PS_trans (bump_ps _) h2) (PS_of_sent h1)
      · exact PS_trans h2 (PS_of_sent h1)

theorem pushDelta_ps (e : Env) (n : N) (now m : Nat) (rc : Rec) (a : Alive) : PS (N.pushDelta e n now m rc a) n := by
  unfold N.pushDelta
  dsimp only
  have h1 : PS (forKeys n.attached.keys
      (fun p n => if p != m && (n.isBoot p || (m == n.me && n.homed.has p)) then N.deltaTo e n p m rc a else n) n) n :=
    forKeys_ps _ _ (fun k n => by split; exact deltaTo_ps ..; exact PS_refl n) n
  split
  · exact h1
  · exact PS_trans (applyDeltaCore_ps ..) h1

/-- `recompute_one`'s arm for a member the view lists whose best eligible record is of another epoch, an older one
included: the view takes that record, so it never keeps a later life that no eligible copy holds. -/
theorem rcArm_other_epoch (n : N) (m : Nat) (best : Rec) (c : ViewEntry) (h : best.inc / 65536 ≠ c.rc.inc / 65536) :
    (n.rcArm m best (some c)).1.members.get? m = some ⟨best⟩ := by
  unfold N.rcArm N.rcNewer N.rcOldVer
  dsimp only
  rw [if_neg h]
  first
    | (simp [Pinc.Membership.AMap.get?_insert_self]; done)
    | (repeat' split) <;> simp [Pinc.Membership.AMap.get?_insert_self]

end Pinc.Membership.Cmp
