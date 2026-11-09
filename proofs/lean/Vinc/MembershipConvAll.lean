import Vinc.MembershipWindow

/-!
# Convergence of the whole view

`recompute_one` changes the entry of one member and no other (`recomputeOne_keeps2`), and lists a new member only
when the view has room. Here the view's length grows by at most one per call (`recomputeOne_len_le`), so a list of
`k` calls on a view with room for `k` more never refuses (`recomputeAll_len_le`). Then
`recomputeAll_agree`: two nodes with the same hub copies and the same freshness, no hold and no quiet window, that
recompute every member of a duplicate-free list of members listed in no more than the room allows, list exactly the
same members of the list afterwards, and `recomputeAll_view_agree` states it for the whole view: if both views start
inside the list, they end with the same set of members.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Vinc.Membership
open Vinc.Membership.Cmp

theorem rcKnown_len (e : Env) (n : N) (m : Nat) (best : Rec) (c : ViewEntry) :
    (rcKnown e n m best c).1.members.len ≤ n.members.len + 1 := by
  have hi := AMap.insert_length_le n.members m ⟨best, false⟩
  unfold rcKnown
  by_cases h1 : best.inc / 65536 ≤ c.rc.inc / 65536 <;> by_cases h2 : (best.inc / 65536 == c.rc.inc / 65536 && decide (c.rc.inc ≤ best.inc)) = true <;>
    by_cases h3 : (best.ver != c.rc.ver) = true <;> by_cases h4 : (best.th != c.rc.th) = true <;>
    by_cases h5 : (match (some (c.rc.ver, c.rc.th)).orElse (fun _ => (n.emit (.joined m)).goneVer.get? m) with | some (ver, th) => ver != best.ver | none => false) = true <;>
    simp [h1, h2, h3, h4, h5, AMap.len, AMap.length_modify] <;> first | omega | (split <;> simp_all [AMap.len, AMap.length_modify] <;> omega) | skip

theorem rcNew_len (e : Env) (n : N) (m : Nat) (best : Rec) :
    (rcNew e n m best).1.members.len ≤ n.members.len + 1 := by
  have hi := AMap.insert_length_le n.members m ⟨best, false⟩
  unfold rcNew
  by_cases h1 : n.members.len ≥ MAX_TABLE
  · rw [if_pos h1]; exact Nat.le_succ _
  · simp [h1, AMap.len]
    repeat' split
    all_goals simp_all [AMap.len] <;> omega

theorem rcTail_len (n : N) (m : Nat) (absent changed : Bool) :
    (rcTail n m absent changed).1.members.len ≤ n.members.len := by
  unfold rcTail
  repeat' split
  all_goals simp [AMap.len, AMap.length_modify]
  all_goals split <;> simp [AMap.len, AMap.length_modify]

theorem removeFromView_len (e : Env) (n : N) (now m : Nat) (cur : Option ViewEntry) (src : Source) (x : Bool) :
    (N.removeFromView e n now m cur src x).1.members.len ≤ n.members.len := by
  have h := AMap.erase_length_le n.members m
  unfold N.removeFromView
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · split
      · simp [AMap.len]
      · by_cases hh : n.isHub = true <;> by_cases hg : (n.goneVer.len < MAX_TABLE ∨ n.goneVer.has m = true) <;>
          by_cases hl : n.left.has m = true <;> by_cases hx : x = true <;> simp [AMap.len, hh, hg, hl, hx] <;> omega

/-- **A view grows by at most one member per `recompute_one`.** -/
theorem recomputeOne_len_le (e : Env) (n : N) (now m : Nat) :
    (N.recomputeOne e n now m).1.members.len ≤ n.members.len + 1 := by
  rw [recomputeOne_eq_v]
  dsimp only
  split
  · exact Nat.le_trans (removeFromView_len _ _ _ _ _ _ _) (Nat.le_succ _)
  · rename_i b0 a0 hb
    have hm := hdIf_members e n m b0 (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0)))
    generalize (if (n.isHub && (match n.members.get? m with | none => true | some c => decide (c.rc ≠ b0))) = true then
        N.homeDelta e n m b0 .alive else n) = n1 at hm ⊢
    have h2 : ∀ (r : N × Bool × Bool), r.1.members.len ≤ n.members.len + 1 →
        (if r.2.2 = true then (r.1, false) else rcTail r.1 m a0 r.2.1).1.members.len ≤ n.members.len + 1 := by
      intro r hr
      by_cases he : r.2.2 = true
      · simp only [he, if_true]; exact hr
      · simp only [he, if_false]; exact Nat.le_trans (rcTail_len _ _ _ _) hr
    split
    · rename_i c hc
      refine h2 _ ?_
      have := rcKnown_len e n1 m b0 c
      unfold AMap.len at this ⊢; rw [hm] at this; exact this
    · refine h2 _ ?_
      have := rcNew_len e n1 m b0
      unfold AMap.len at this ⊢; rw [hm] at this; exact this

/-- `recompute_one` over a list of members, in order. -/
def recomputeAll (e : Env) (now : Nat) (ks : List Nat) (n : N) : N :=
  ks.foldl (fun n m => (N.recomputeOne e n now m).1) n

@[simp] theorem recomputeAll_nil (e : Env) (now : Nat) (n : N) : recomputeAll e now [] n = n := rfl
theorem recomputeAll_cons (e : Env) (now k : Nat) (r : List Nat) (n : N) :
    recomputeAll e now (k :: r) n = recomputeAll e now r (N.recomputeOne e n now k).1 := rfl

theorem recomputeAll_keeps (e : Env) (now : Nat) (ks : List Nat) (n : N) : Keeps n (recomputeAll e now ks n) := by
  induction ks generalizing n with
  | nil => exact Keeps.refl n
  | cons k r ih => rw [recomputeAll_cons]; exact Keeps.trans (recomputeOne_keeps2 e n now k).1 (ih _)

/-- The view grows by at most one member per member recomputed. -/
theorem recomputeAll_len_le (e : Env) (now : Nat) (ks : List Nat) (n : N) :
    (recomputeAll e now ks n).members.len ≤ n.members.len + ks.length := by
  induction ks generalizing n with
  | nil => simp
  | cons k r ih =>
    rw [recomputeAll_cons]
    have h1 := recomputeOne_len_le e n now k
    have h2 := ih (N.recomputeOne e n now k).1
    simp only [List.length_cons]; omega

/-- A member that is not recomputed keeps its entry. -/
theorem recomputeAll_notin (e : Env) (now : Nat) (ks : List Nat) (n : N) (m : Nat) (hm : m ∉ ks) :
    (recomputeAll e now ks n).members.get? m = n.members.get? m := by
  induction ks generalizing n with
  | nil => rfl
  | cons k r ih =>
    rw [recomputeAll_cons]
    have hk : m ≠ k := fun h => hm (h ▸ List.mem_cons_self)
    rw [ih _ (fun h => hm (List.mem_cons_of_mem _ h))]
    exact (recomputeOne_keeps2 e n now k).2 m hk

/-- Two nodes that see the same hub copies in the same way, with no hold and no quiet window. -/
structure Sync (now : Nat) (n1 n2 : N) : Prop where
  hv : n2.hv = n1.hv
  up : ∀ h, n2.hubUp now h = n1.hubUp now h
  src : n2.source now = n1.source now
  hold : (n1.source now).hold = false
  q1 : ¬ now < n1.quietUntil
  q2 : ¬ now < n2.quietUntil

theorem Sync.step {now : Nat} {n1 n2 : N} (h : Sync now n1 n2) (e1 e2 : Env) (k : Nat) :
    Sync now (N.recomputeOne e1 n1 now k).1 (N.recomputeOne e2 n2 now k).1 := by
  have a1 := (recomputeOne_keeps2 e1 n1 now k).1
  have a2 := (recomputeOne_keeps2 e2 n2 now k).1
  refine ⟨?_, fun x => ?_, ?_, ?_, ?_, ?_⟩
  · rw [a2.1, a1.1]; exact h.hv
  · rw [a2.hubUp, a1.hubUp]; exact h.up x
  · rw [a2.source, a1.source]; exact h.src
  · rw [a1.source]; exact h.hold
  · rw [a1.2.2.2.2.2.2.2.2.2.2.2]; exact h.q1
  · rw [a2.2.2.2.2.2.2.2.2.2.2.2]; exact h.q2

theorem Sync.all {now : Nat} {n1 n2 : N} (h : Sync now n1 n2) (e1 e2 : Env) (ks : List Nat) :
    Sync now (recomputeAll e1 now ks n1) (recomputeAll e2 now ks n2) := by
  induction ks generalizing n1 n2 with
  | nil => exact h
  | cons k r ih => rw [recomputeAll_cons, recomputeAll_cons]; exact ih (h.step e1 e2 k)

/-- **Two nodes with the same hub copies agree on every recomputed member.** Two nodes that hold the same copies of
the fresh hubs, with no hold and no quiet window, recompute a duplicate-free list of members; when each view has room
for the whole list, they list exactly the same members of it afterwards. -/
theorem recomputeAll_agree (e1 e2 : Env) (now : Nat) (ks : List Nat) :
    ∀ (n1 n2 : N), Sync now n1 n2 → ks.Nodup → n1.members.len + ks.length ≤ MAX_TABLE →
      n2.members.len + ks.length ≤ MAX_TABLE →
      ∀ m ∈ ks, (recomputeAll e1 now ks n1).members.has m = (recomputeAll e2 now ks n2).members.has m := by
  induction ks with
  | nil => intro n1 n2 _ _ _ _ m hm; exact absurd hm List.not_mem_nil
  | cons k r ih =>
    intro n1 n2 hs hnd c1 c2 m hm
    rw [recomputeAll_cons, recomputeAll_cons]
    have hnd' := List.nodup_cons.1 hnd
    simp only [List.length_cons] at c1 c2
    rcases List.mem_cons.1 hm with rfl | hr
    · have e1' : (recomputeAll e1 now r (N.recomputeOne e1 n1 now m).1).members.has m = (N.recomputeOne e1 n1 now m).1.members.has m := by
        rw [AMap.has_iff_get, AMap.has_iff_get, recomputeAll_notin _ _ _ _ _ hnd'.1]
      have e2' : (recomputeAll e2 now r (N.recomputeOne e2 n2 now m).1).members.has m = (N.recomputeOne e2 n2 now m).1.members.has m := by
        rw [AMap.has_iff_get, AMap.has_iff_get, recomputeAll_notin _ _ _ _ _ hnd'.1]
      rw [e1', e2']
      exact views_merge_key e1 e2 n1 n2 now m hs.hv hs.up hs.src hs.hold hs.q1 hs.q2
        (fun h => by have := h.2; omega) (fun h => by have := h.2; omega)
    · refine ih _ _ (hs.step e1 e2 k) hnd'.2 ?_ ?_ m hr
      · have := recomputeOne_len_le e1 n1 now k; omega
      · have := recomputeOne_len_le e2 n2 now k; omega

/-- **Convergence of the whole view.** If every member either view lists is in the list, the two views list exactly
the same members after the recompute: one statement over every member of two nodes with the same hub copies. -/
theorem recomputeAll_view_agree (e1 e2 : Env) (now : Nat) (ks : List Nat) (n1 n2 : N) (hs : Sync now n1 n2)
    (hnd : ks.Nodup) (c1 : n1.members.len + ks.length ≤ MAX_TABLE) (c2 : n2.members.len + ks.length ≤ MAX_TABLE)
    (hcov : ∀ m, (n1.members.has m = true ∨ n2.members.has m = true) → m ∈ ks) (m : Nat) :
    (recomputeAll e1 now ks n1).members.has m = (recomputeAll e2 now ks n2).members.has m := by
  by_cases hm : m ∈ ks
  · exact recomputeAll_agree e1 e2 now ks n1 n2 hs hnd c1 c2 m hm
  · have h1 : n1.members.has m = false := by
      cases hb : n1.members.has m
      · rfl
      · exact absurd (hcov m (Or.inl hb)) hm
    have h2 : n2.members.has m = false := by
      cases hb : n2.members.has m
      · rfl
      · exact absurd (hcov m (Or.inr hb)) hm
    rw [AMap.has_iff_get, AMap.has_iff_get, recomputeAll_notin _ _ _ _ _ hm, recomputeAll_notin _ _ _ _ _ hm]
    rw [AMap.has_iff_get] at h1 h2
    rw [h1, h2]

end Vinc.Membership
