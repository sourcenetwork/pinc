import Vinc.MembershipViewCand

/-!
# Membership view: who is in the view (properties 3, 4, 7)

`recompute_one` decides each member's place. Built on `MembershipViewCand.lean` (the candidate of the eligible copies):

* `recomputeOne_listed_stays`: a member that an eligible copy lists with a live omission state is in the view after the
  recomputation (or the view table is full and it was not in the view): **a snapshot, which only lists members or marks
  them omitted, never removes one**;
* `recomputeOne_removal_requires`: a member leaves the view only if no eligible copy lists it, the source does not hold
  removals, and no quiet window defers it;
* `removeFromView_event_left`, `removeFromView_event_down` (and `rfvDo_events_left`, `rfvDo_events_down`): the removal
  raises the event `left` exactly when a hub reported a leave and the event `down` otherwise, never a failure for a
  leave (property 7), or is counted as a lost event when the queue is full; that the trace names a lease expiry only
  when a full lease of omission passed is not proved in Lean yet.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.MemInc

theorem rcKnown_has (e : Env) (n : N) (m : Nat) (best : Rec) (c : ViewEntry) (h : n.members.has m = true) :
    (rcKnown e n m best c).1.members.has m = true := by
  unfold rcKnown
  by_cases h1 : best.inc / 65536 ≤ c.rc.inc / 65536 <;> by_cases h2 : (best.inc / 65536 == c.rc.inc / 65536 && decide (c.rc.inc ≤ best.inc)) = true <;>
    by_cases h3 : (best.ver != c.rc.ver) = true <;> by_cases h4 : (best.th != c.rc.th) = true <;>
    simp [h1, h2, h3, h4, AMap.has_modify, AMap.has_insert_self, h] <;> repeat' split
  all_goals simp_all [AMap.has_modify, AMap.has_insert_self]

theorem rcNew_has (e : Env) (n : N) (m : Nat) (best : Rec) :
    (rcNew e n m best).2.2 = false → (rcNew e n m best).1.members.has m = true := by
  unfold rcNew
  by_cases h1 : n.members.len ≥ MAX_TABLE
  · simp [h1]
  · simp [h1]
    repeat' split
    all_goals simp_all [AMap.has_insert_self]

theorem rcNew_early (e : Env) (n : N) (m : Nat) (best : Rec) :
    (rcNew e n m best).2.2 = true → MAX_TABLE ≤ n.members.len := by
  unfold rcNew
  by_cases h1 : n.members.len ≥ MAX_TABLE
  · intro _; exact h1
  · simp [h1]
    repeat' split
    all_goals simp_all

theorem rcTail_has (n : N) (m : Nat) (absent changed : Bool) (h : n.members.has m = true) :
    (rcTail n m absent changed).1.members.has m = true := by
  unfold rcTail
  repeat' split
  all_goals simp_all [AMap.has_modify]

theorem removeFromView_members_eq (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (x : Bool)
    (h : src.hold = true ∨ (now < n.quietUntil ∧ n.recheck.len < MAX_TABLE)) :
    (N.removeFromView e n now m cur src x).1.members = n.members := by
  unfold N.removeFromView
  split
  · rfl
  · by_cases hh : src.hold = true
    · simp [hh]; split <;> rfl
    · have h2 : now < n.quietUntil ∧ n.recheck.len < MAX_TABLE := by
        rcases h with h | h
        · exact absurd h hh
        · exact h
      simp [hh, h2.1, h2.2]


theorem rcKnown_not_early (e : Env) (n : N) (m : Nat) (best : Rec) (c : ViewEntry) : (rcKnown e n m best c).2.2 = false := by
  unfold rcKnown
  repeat' split
  all_goals simp_all

theorem hdIf_members (e : Env) (n : N) (m : Nat) (b0 : Rec) (c : Bool) :
    (if c = true then N.homeDelta e n m b0 .alive else n).members = n.members := by
  by_cases h : c = true <;> simp [h]

/-- **A snapshot never removes a member on its own** (view side). If an eligible hub copy lists the member and its
omission, if any, has not lasted a full lease, then recomputing the member keeps it in the view (or the view table is
full and the member was not in it: a full table refuses a new member and evicts nobody). `applySnap` only inserts
entries into the sender's copy, marks the omitted entries of members the view lists, and drops the omitted entries of
members it does not list (`MembershipViewSnap.lean`); an omission that has just been marked is not expired, so a
snapshot alone cannot make a listed member leave. -/
theorem recomputeOne_listed_stays (e : Env) (n : N) (now m : Nat)
    (h : (n.candidates now (n.source now) m).1 ≠ none) :
    (N.recomputeOne e n now m).1.members.has m = true ∨ (n.members.has m = false ∧ MAX_TABLE ≤ n.members.len) := by
  rw [recomputeOne_eq_v]
  dsimp only
  split
  · rename_i hb; exact absurd (by rw [hb]) h
  · rename_i b0 a0 hb
    have hm := hdIf_members e n m b0 (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0)))
    generalize (if (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0))) = true then
        N.homeDelta e n m b0 .alive else n) = n1 at hm ⊢
    split
    · rename_i c hc
      have hhas : n1.members.has m = true := by rw [hm, AMap.has_iff_get, hc]; rfl
      have h1 := rcKnown_has e n1 m b0 c hhas
      have hne := rcKnown_not_early e n1 m b0 c
      left
      rw [hne]
      simp only [Bool.false_eq_true, if_false]
      exact rcTail_has _ _ _ _ h1
    · rename_i hc
      by_cases he : (rcNew e n1 m b0).2.2 = true
      · right
        refine ⟨?_, ?_⟩
        · rw [AMap.has_iff_get, hc]; rfl
        · have := rcNew_early e n1 m b0 he
          rw [hm] at this; exact this
      · left
        have hf : (rcNew e n1 m b0).2.2 = false := by simpa using he
        simp only [hf, Bool.false_eq_true, if_false]
        exact rcTail_has _ _ _ _ (rcNew_has e n1 m b0 hf)

theorem recomputeOne_none (e : Env) (n : N) (now m : Nat) (h : (n.candidates now (n.source now) m).1 = none) :
    N.recomputeOne e n now m =
      N.removeFromView e n now m (n.members.get? m) (n.source now) (n.candidates now (n.source now) m).2 := by
  rw [recomputeOne_eq_v]
  dsimp only
  split
  · rfl
  · rename_i b0 a0 hb; rw [hb] at h; exact absurd h (by simp)

/-- A member leaves the view only if no eligible copy lists it with a live omission state, the source does not hold
removals, and no quiet window defers the removal (`now < quiet_until` with room in the recheck table). -/
theorem recomputeOne_removal_requires (e : Env) (n : N) (now m : Nat) (hin : n.members.has m = true)
    (hout : (N.recomputeOne e n now m).1.members.has m = false) :
    (∀ p ∈ n.hv, ∀ ce, ¬ Live n now (n.source now) m p ce) ∧ (n.source now).hold = false ∧
      (n.quietUntil ≤ now ∨ MAX_TABLE ≤ n.recheck.len) := by
  have hcand : (n.candidates now (n.source now) m).1 = none := by
    apply Classical.byContradiction
    intro hne
    rcases recomputeOne_listed_stays e n now m hne with h | h
    · rw [hout] at h; exact absurd h (by simp)
    · rw [hin] at h; exact absurd h.1 (by simp)
  have hr := recomputeOne_none e n now m hcand
  refine ⟨(candidates_none_iff n now _ m).mp hcand, ?_, ?_⟩
  · apply Classical.byContradiction
    intro hh
    have hh' : (n.source now).hold = true := by simpa using hh
    have := removeFromView_members_eq e n now m (n.members.get? m) (n.source now) (n.candidates now (n.source now) m).2 (Or.inl hh')
    rw [hr, this] at hout
    rw [hin] at hout; exact absurd hout (by simp)
  · apply Classical.byContradiction
    intro hh
    have hh' : now < n.quietUntil ∧ n.recheck.len < MAX_TABLE := by
      simp only [not_or] at hh; omega
    have := removeFromView_members_eq e n now m (n.members.get? m) (n.source now) (n.candidates now (n.source now) m).2 (Or.inr hh')
    rw [hr, this] at hout
    rw [hin] at hout; exact absurd hout (by simp)


/-! ## Leave is reported as a leave (property 7, view side) -/

@[simp] theorem trace_events (n : N) (t : Tr) : (n.trace t).events = n.events ∧ (n.trace t).lostEvents = n.lostEvents := by
  unfold N.trace; split <;> (try split) <;> simp

@[simp] theorem tx_events (e : Env) (n : N) (p : Nat) (r : Route) (f : NFrame) :
    (N.tx e n p r f).1.events = n.events ∧ (N.tx e n p r f).1.lostEvents = n.lostEvents := by
  unfold N.tx; split
  · simp
  · simp

theorem homeDelta_events (e : Env) (n : N) (m : Nat) (rc : Rec) (a : Alive) :
    (N.homeDelta e n m rc a).events = n.events ∧ (N.homeDelta e n m rc a).lostEvents = n.lostEvents := by
  unfold N.homeDelta forKeys
  suffices ∀ (ks : List Nat) (n0 : N), n0.events = n.events → n0.lostEvents = n.lostEvents →
      (ks.foldl (fun n p => if p != m then N.deltaTo e n p m rc a else n) n0).events = n.events ∧
      (ks.foldl (fun n p => if p != m then N.deltaTo e n p m rc a else n) n0).lostEvents = n.lostEvents from
    this _ n rfl rfl
  intro ks
  induction ks with
  | nil => intro n0 h1 h2; exact ⟨h1, h2⟩
  | cons k r ih =>
    intro n0 h1 h2
    simp only [List.foldl_cons]
    apply ih
    · split
      · unfold N.deltaTo; rw [(tx_events _ _ _ _ _).1]; exact h1
      · exact h1
    · split
      · unfold N.deltaTo; rw [(tx_events _ _ _ _ _).2]; exact h2
      · exact h2

theorem emit_cases (n : N) (e : Ev) :
    (n.emit e).events = n.events ++ [e] ∨ ((n.emit e).events = n.events ∧ (n.emit e).lostEvents = n.lostEvents + 1) := by
  unfold N.emit; split
  · right; simp
  · left; simp

/-- The removing branch of `remove_from_view`. -/
def rfvDo (e : Env) (n : N) (now m : Nat) (c : ViewEntry) (expired : Bool) : N × Bool :=
  let n := { n with members := n.members.erase m }
  let n := if n.goneVer.len < MAX_TABLE || n.goneVer.has m then
      { n with goneVer := n.goneVer.insert m (c.rc.ver, c.rc.th) } else n
  let wasLeft := n.left.has m
  let n := { n with left := n.left.del m }
  let (why, a) : Removal × Alive := if wasLeft then (.left, .left) else if expired then (.leaseExpired, .down) else (.reported, .down)
  let n := n.trace (.removed m why.toNat)
  let n := n.emit (if wasLeft then .left m else .down m)
  let n := if n.isHub then N.homeDelta e n m c.rc a else n
  (n, true)

theorem removeFromView_eq (e : Env) (n : N) (now m : Nat) (c : ViewEntry) (src : Source) (x : Bool)
    (hold : src.hold = false) (hq : ¬(now < n.quietUntil ∧ n.recheck.len < MAX_TABLE)) :
    N.removeFromView e n now m (some c) src x = rfvDo e n now m c x := by
  have hq' : ¬ ((decide (now < n.quietUntil) && decide (n.recheck.len < MAX_TABLE)) = true) := by
    simp; intro h; exact Nat.le_of_not_lt (fun h2 => hq ⟨h, h2⟩)
  unfold N.removeFromView
  simp only [hold, hq', Bool.false_eq_true, if_false]
  rfl

theorem tail_events (n nn : N) (t : Tr) (ev : Ev) (e : Env) (m : Nat) (rc : Rec) (a : Alive)
    (h1 : nn.events = n.events) (h2 : nn.lostEvents = n.lostEvents) :
    (if ((nn.trace t).emit ev).isHub = true then N.homeDelta e ((nn.trace t).emit ev) m rc a else (nn.trace t).emit ev).events
        = n.events ++ [ev] ∨
    ((if ((nn.trace t).emit ev).isHub = true then N.homeDelta e ((nn.trace t).emit ev) m rc a else (nn.trace t).emit ev).events
        = n.events ∧
     (if ((nn.trace t).emit ev).isHub = true then N.homeDelta e ((nn.trace t).emit ev) m rc a else (nn.trace t).emit ev).lostEvents
        = n.lostEvents + 1) := by
  have ht := trace_events nn t
  have hc := emit_cases (nn.trace t) ev
  rw [ht.1, ht.2] at hc
  have hc' : ((nn.trace t).emit ev).events = n.events ++ [ev] ∨
      (((nn.trace t).emit ev).events = n.events ∧ ((nn.trace t).emit ev).lostEvents = n.lostEvents + 1) := by
    rcases hc with hc | hc
    · left; rw [hc, h1]
    · right; rw [h1, h2] at hc; exact hc
  by_cases hh : ((nn.trace t).emit ev).isHub = true
  · simp only [hh, if_true]
    have hd := homeDelta_events e ((nn.trace t).emit ev) m rc a
    rw [hd.1, hd.2]
    exact hc'
  · simp only [hh, if_false]
    exact hc'

theorem rfvDo_events_left (e : Env) (n : N) (now m : Nat) (c : ViewEntry) (x : Bool) (hl : n.left.has m = true) :
    (rfvDo e n now m c x).1.events = n.events ++ [Ev.left m] ∨
    ((rfvDo e n now m c x).1.events = n.events ∧ (rfvDo e n now m c x).1.lostEvents = n.lostEvents + 1) := by
  unfold rfvDo
  dsimp only
  by_cases hg : (n.goneVer.len < MAX_TABLE || n.goneVer.has m) = true
  · simp only [hg, hl, if_true, if_false, Bool.false_eq_true, ite_true, ite_false, Bool.or_true, Bool.true_or]
    refine tail_events n _ _ _ e m c.rc _ ?_ ?_ <;> rfl
  · simp only [hg, hl, if_true, if_false, Bool.false_eq_true, ite_true, ite_false, Bool.or_true, Bool.true_or]
    refine tail_events n _ _ _ e m c.rc _ ?_ ?_ <;> rfl

theorem rfvDo_events_down (e : Env) (n : N) (now m : Nat) (c : ViewEntry) (x : Bool) (hl : n.left.has m = false) :
    (rfvDo e n now m c x).1.events = n.events ++ [Ev.down m] ∨
    ((rfvDo e n now m c x).1.events = n.events ∧ (rfvDo e n now m c x).1.lostEvents = n.lostEvents + 1) := by
  unfold rfvDo
  dsimp only
  by_cases hg : (n.goneVer.len < MAX_TABLE || n.goneVer.has m) = true
  · simp only [hg, hl, if_true, if_false, Bool.false_eq_true, ite_true, ite_false, Bool.or_true, Bool.true_or]
    refine tail_events n _ _ _ e m c.rc _ ?_ ?_ <;> rfl
  · simp only [hg, hl, if_true, if_false, Bool.false_eq_true, ite_true, ite_false, Bool.or_true, Bool.true_or]
    refine tail_events n _ _ _ e m c.rc _ ?_ ?_ <;> rfl

/-- **Leave is reported as a leave (property 7, view side).** The removal of a member a hub reported leaving emits
`MemberLeft`, and any other removal emits `MemberConfirmedDown`; a full event queue drops the event and counts it. -/
theorem removeFromView_event_left (e : Env) (n : N) (now m : Nat) (c : ViewEntry) (src : Source) (x : Bool)
    (hold : src.hold = false) (hq : ¬(now < n.quietUntil ∧ n.recheck.len < MAX_TABLE)) (hl : n.left.has m = true) :
    (N.removeFromView e n now m (some c) src x).1.events = n.events ++ [Ev.left m] ∨
    ((N.removeFromView e n now m (some c) src x).1.events = n.events ∧
      (N.removeFromView e n now m (some c) src x).1.lostEvents = n.lostEvents + 1) := by
  rw [removeFromView_eq e n now m c src x hold hq]; exact rfvDo_events_left e n now m c x hl

theorem removeFromView_event_down (e : Env) (n : N) (now m : Nat) (c : ViewEntry) (src : Source) (x : Bool)
    (hold : src.hold = false) (hq : ¬(now < n.quietUntil ∧ n.recheck.len < MAX_TABLE)) (hl : n.left.has m = false) :
    (N.removeFromView e n now m (some c) src x).1.events = n.events ++ [Ev.down m] ∨
    ((N.removeFromView e n now m (some c) src x).1.events = n.events ∧
      (N.removeFromView e n now m (some c) src x).1.lostEvents = n.lostEvents + 1) := by
  rw [removeFromView_eq e n now m c src x hold hq]; exact rfvDo_events_down e n now m c x hl

end Vinc.Membership
