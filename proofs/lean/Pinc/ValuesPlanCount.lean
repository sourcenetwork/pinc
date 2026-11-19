import Pinc.ValuesPlanRef

/-!
# The pair counts of `plan.rs`

`parents_in`, `parents_in_suffix` and `parents_before` of `crates/pinc-values/src/plan.rs`, written on `Nat`
(the loops as tail-recursive functions with the running sum), and their meaning against the reference of
`ValuesPlanRef`:

* `parentsIn_eq`: `parents_in(lo, hi, a, b)` is the number of parent steps of the encoder for the groups
  `[a, b)` (so `range_pairs`, which `fetch/wt.rs` checks a proof against, is the pair count of `RangeEncoder`).
* `sufGo_eq`: the loop of `parents_in_suffix` is `parents_in` of the groups from `s` on.
* `pbGo_eq`: `parents_before` is the number of parent steps that precede the data of the group in the stream.
* `parentsBefore_sum`, `pendLen_diff`, `parentsIn_sum` (in `ValuesPlanFrames`): the pair counts of the frames sum, frame
  by frame, to `parents_before`, so the pair count of a frame is the difference of two `parents_before` and the pairs of
  all the frames are the parents of the range.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesPlan
open Pinc.Layout Pinc.Encode

/-- `parents_in(lo, hi, a, b)`. -/
def parentsIn (a b : Nat) (lo hi : Nat) : Nat :=
  if h : hi - lo < 2 ∨ b ≤ lo ∨ hi ≤ a then 0
  else if a ≤ lo ∧ hi ≤ b then hi - lo - 1
  else
    have h1 := leftGroups_pos (hi - lo) (by omega)
    have h2 := leftGroups_lt (hi - lo) (by omega)
    1 + parentsIn a b lo (lo + leftGroups (hi - lo)) + parentsIn a b (lo + leftGroups (hi - lo)) hi
termination_by hi - lo

theorem parentsIn_stop (a b lo hi : Nat) (h : hi - lo < 2 ∨ b ≤ lo ∨ hi ≤ a) : parentsIn a b lo hi = 0 := by
  rw [parentsIn]; simp [h]

theorem parentsIn_full (a b lo hi : Nat) (h : ¬ (hi - lo < 2 ∨ b ≤ lo ∨ hi ≤ a)) (hc : a ≤ lo ∧ hi ≤ b) :
    parentsIn a b lo hi = hi - lo - 1 := by
  rw [parentsIn]; simp only [h, hc, dite_false, and_self, ite_true]

theorem parentsIn_rec (a b lo hi : Nat) (h : ¬ (hi - lo < 2 ∨ b ≤ lo ∨ hi ≤ a)) (hc : ¬ (a ≤ lo ∧ hi ≤ b)) :
    parentsIn a b lo hi = 1 + parentsIn a b lo (lo + leftGroups (hi - lo)) +
      parentsIn a b (lo + leftGroups (hi - lo)) hi := by
  rw [parentsIn]; simp only [h, hc, dite_false, ite_false]

theorem parentsIn_covered (a b lo hi : Nat) (hlh : lo < hi) (ha : a ≤ lo) (hb : hi ≤ b) :
    parentsIn a b lo hi = hi - lo - 1 := by
  by_cases h : hi - lo < 2
  · rw [parentsIn_stop _ _ _ _ (Or.inl h)]; omega
  · exact parentsIn_full _ _ _ _ (by omega) ⟨ha, hb⟩

/-- The parent steps of a step list. -/
def np : List Step → Nat
  | [] => 0
  | .parent _ :: t => np t + 1
  | .group _ _ :: t => np t

theorem np_append (A B : List Step) : np (A ++ B) = np A + np B := by
  induction A with
  | nil => simp [np]
  | cons s T ih => cases s <;> simp [np, ih] <;> omega

/-- A node that lies inside the range has `hi - lo - 1` parents in the reference. -/
theorem np_full (len log a b : Nat) :
    ∀ (n lo hi idx : Nat), hi - lo = n → lo < hi → a ≤ lo → hi ≤ b → np (ref len log a b lo hi idx) = hi - lo - 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi idx hn hlh ha hb
    by_cases h2 : hi - lo ≥ 2
    · have h1 := leftGroups_pos (hi - lo) h2
      have h3 := leftGroups_lt (hi - lo) h2
      rw [ref_node _ _ _ _ _ _ _ h2]
      have hl : a < lo + leftGroups (hi - lo) := by omega
      have hr : lo + leftGroups (hi - lo) < b := by omega
      simp only [hl, hr, ite_true, np, np_append]
      rw [ih (leftGroups (hi - lo)) (by omega) lo _ (idx + 1) (by omega) (by omega) ha (by omega),
        ih (hi - (lo + leftGroups (hi - lo))) (by omega) _ hi _ (by omega) (by omega) (by omega) hb]
      omega
    · rw [ref_leaf _ _ _ _ _ _ _ h2]; simp [np]; omega

/-- `parents_in` counts the parent steps of the encoder. -/
theorem parentsIn_eq (len log a b : Nat) :
    ∀ (n lo hi idx : Nat), hi - lo = n → lo < hi → lo < b → a < hi → a < b →
      parentsIn a b lo hi = np (ref len log a b lo hi idx) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi idx hn hlh hlb hah hab
    by_cases h2 : hi - lo ≥ 2
    · have h1 := leftGroups_pos (hi - lo) h2
      have h3 := leftGroups_lt (hi - lo) h2
      by_cases hc : a ≤ lo ∧ hi ≤ b
      · rw [parentsIn_full _ _ _ _ (by omega) hc, np_full len log a b _ lo hi idx rfl hlh hc.1 hc.2]
      · rw [parentsIn_rec _ _ _ _ (by omega) hc, ref_node _ _ _ _ _ _ _ h2]
        by_cases hl : a < lo + leftGroups (hi - lo) <;> by_cases hr : lo + leftGroups (hi - lo) < b
        · simp only [hl, hr, ite_true, np, np_append]
          rw [ih (leftGroups (hi - lo)) (by omega) lo _ (idx + 1) (by omega) (by omega) hlb hl hab,
            ih (hi - (lo + leftGroups (hi - lo))) (by omega) _ hi (idx + leftGroups (hi - lo)) (by omega) (by omega) hr hah hab]
          omega
        · simp only [hl, hr, ite_true, ite_false, np, np_append, List.append_nil]
          rw [ih (leftGroups (hi - lo)) (by omega) lo _ (idx + 1) (by omega) (by omega) hlb hl hab,
            parentsIn_stop _ _ _ _ (by omega)]
          omega
        · simp only [hl, hr, ite_true, ite_false, np, np_append, List.nil_append]
          rw [ih (hi - (lo + leftGroups (hi - lo))) (by omega) _ hi (idx + leftGroups (hi - lo)) (by omega) (by omega) (by omega) hah hab,
            parentsIn_stop _ _ _ _ (by omega)]
          omega
        · omega
    · rw [parentsIn_stop _ _ _ _ (by omega), ref_leaf _ _ _ _ _ _ _ h2]; simp [np]

/-- The loop of `parents_in_suffix`, with the running sum. -/
def sufGo (s : Nat) (lo hi sum : Nat) : Nat :=
  if h : hi - lo ≥ 2 ∧ s < hi then
    have h1 := leftGroups_pos (hi - lo) h.1
    have h2 := leftGroups_lt (hi - lo) h.1
    if s ≤ lo then sum + (hi - lo - 1)
    else if s < lo + leftGroups (hi - lo) then
      sufGo s lo (lo + leftGroups (hi - lo)) (sum + 1 + (hi - (lo + leftGroups (hi - lo)) - 1))
    else sufGo s (lo + leftGroups (hi - lo)) hi (sum + 1)
  else sum
termination_by hi - lo

/-- The suffix loop is `parents_in` from `s` on, for any end beyond the node. -/
theorem sufGo_eq (s B : Nat) :
    ∀ (n lo hi sum : Nat), hi - lo = n → hi ≤ B → sufGo s lo hi sum = sum + parentsIn s B lo hi := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi sum hn hB
    rw [sufGo]
    by_cases hc : hi - lo ≥ 2 ∧ s < hi
    · have h1 := leftGroups_pos (hi - lo) hc.1
      have h3 := leftGroups_lt (hi - lo) hc.1
      simp only [hc, and_self, dite_true]
      by_cases hs : s ≤ lo
      · simp only [hs, ite_true]
        rw [parentsIn_full _ _ _ _ (by omega) ⟨hs, hB⟩]
      · simp only [hs, ite_false]
        rw [parentsIn_rec _ _ _ _ (by omega) (by omega)]
        by_cases hm : s < lo + leftGroups (hi - lo)
        · simp only [hm, ite_true]
          rw [ih (leftGroups (hi - lo)) (by omega) lo _ _ (by omega) (by omega),
            parentsIn_covered _ _ _ _ (by omega) (by omega) hB]
          omega
        · simp only [hm, ite_false]
          rw [ih (hi - (lo + leftGroups (hi - lo))) (by omega) _ hi _ (by omega) hB,
            parentsIn_stop _ _ lo _ (by omega)]
          omega
    · simp only [hc, dite_false]
      rw [parentsIn_stop _ _ _ _ (by omega)]; rfl

/-- `parents_in_suffix(lo, hi, s)`. -/
def parentsInSuffix (lo hi s : Nat) : Nat := sufGo s lo hi 0

/-- The loop of `parents_before` from the node `[lo, hi)` with the running sum. -/
def pbGo (a x : Nat) (lo hi sum : Nat) : Nat :=
  if h : hi - lo ≥ 2 then
    have h1 := leftGroups_pos (hi - lo) h
    have h2 := leftGroups_lt (hi - lo) h
    if x < lo + leftGroups (hi - lo) then pbGo a x lo (lo + leftGroups (hi - lo)) (sum + 1)
    else pbGo a x (lo + leftGroups (hi - lo)) hi (sum + 1 + parentsInSuffix lo (lo + leftGroups (hi - lo)) a)
  else sum
termination_by hi - lo

/-- `parents_before(n, a, x)`. -/
def parentsBefore (n a x : Nat) : Nat := pbGo a x 0 n 0

/-! ## The stream position of a group -/

/-- The value offsets of the groups of a step list, in order. -/
def groupOffs : List Step → List Nat
  | [] => []
  | .parent _ :: t => groupOffs t
  | .group o _ :: t => o :: groupOffs t

/-- The parent steps before the group at value offset `off`. -/
def bef : List Step → Nat → Nat
  | [], _ => 0
  | .parent _ :: t, off => bef t off + 1
  | .group o _ :: t, off => if o = off then 0 else bef t off

theorem bef_append (A B : List Step) (off : Nat) :
    bef (A ++ B) off = if off ∈ groupOffs A then bef A off else np A + bef B off := by
  induction A with
  | nil => simp [bef, groupOffs, np]
  | cons s T ih =>
    cases s with
    | parent o =>
      simp only [List.cons_append, bef, groupOffs, np, ih]
      by_cases h : off ∈ groupOffs T <;> simp [h] <;> omega
    | group o l =>
      simp only [List.cons_append, bef, groupOffs, np, ih, List.mem_cons]
      by_cases h1 : o = off
      · simp [h1]
      · by_cases h : off ∈ groupOffs T <;> simp [h1, h, Ne.symm h1]

theorem groupLen_inj (log x y : Nat) (h : x * groupLen log = y * groupLen log) : x = y :=
  Nat.eq_of_mul_eq_mul_right (groupLen_pos log) h

/-- The groups of the reference of a node are the groups of the node that meet the range. -/
theorem mem_groupOffs_ref (len log a b : Nat) :
    ∀ (n lo hi idx : Nat), hi - lo = n → lo < hi → lo < b → a < hi → ∀ x,
      x * groupLen log ∈ groupOffs (ref len log a b lo hi idx) ↔ (lo ≤ x ∧ x < hi ∧ a ≤ x ∧ x < b) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi idx hn hlh hlb hah x
    by_cases h2 : hi - lo ≥ 2
    · have h1 := leftGroups_pos (hi - lo) h2
      have h3 := leftGroups_lt (hi - lo) h2
      rw [ref_node _ _ _ _ _ _ _ h2]
      have gl : ∀ (A B : List Step), groupOffs (.parent (idx * 64) :: (A ++ B)) = groupOffs A ++ groupOffs B := by
        intro A B
        induction A with
        | nil => simp [groupOffs]
        | cons s T ih => cases s <;> simp_all [groupOffs]
      rw [gl]
      by_cases hl : a < lo + leftGroups (hi - lo) <;> by_cases hr : lo + leftGroups (hi - lo) < b
      · simp only [hl, hr, ite_true, List.mem_append]
        rw [ih (leftGroups (hi - lo)) (by omega) lo _ (idx + 1) (by omega) (by omega) hlb hl x,
          ih (hi - (lo + leftGroups (hi - lo))) (by omega) _ hi (idx + leftGroups (hi - lo)) (by omega) (by omega) hr hah x]
        omega
      · simp only [hl, hr, ite_true, ite_false, groupOffs, List.append_nil]
        rw [ih (leftGroups (hi - lo)) (by omega) lo _ (idx + 1) (by omega) (by omega) hlb hl x]
        omega
      · simp only [hl, hr, ite_true, ite_false, groupOffs, List.nil_append]
        rw [ih (hi - (lo + leftGroups (hi - lo))) (by omega) _ hi (idx + leftGroups (hi - lo)) (by omega) (by omega) (by omega) hah x]
        omega
      · simp only [hl, hr, ite_false, groupOffs, List.append_nil, List.not_mem_nil]
        exact ⟨fun h => h.elim, fun h => by omega⟩
    · rw [ref_leaf _ _ _ _ _ _ _ h2]
      simp only [groupOffs, List.mem_singleton]
      constructor
      · intro h; have := groupLen_inj log _ _ h; omega
      · intro h; have : x = lo := by omega
        rw [this]

/-- `parents_before` is the number of parent steps before the group. -/
theorem pbGo_eq (len log a b : Nat) :
    ∀ (n lo hi idx : Nat) (x sum : Nat), hi - lo = n → lo ≤ x → x < hi → a ≤ x → x < b →
      pbGo a x lo hi sum = sum + bef (ref len log a b lo hi idx) (x * groupLen log) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi idx x sum hn hlx hxh hax hxb
    rw [pbGo]
    by_cases h2 : hi - lo ≥ 2
    · have h1 := leftGroups_pos (hi - lo) h2
      have h3 := leftGroups_lt (hi - lo) h2
      simp only [h2, dite_true]
      rw [ref_node _ _ _ _ _ _ _ h2]
      have hl : a < lo + leftGroups (hi - lo) ∨ ¬ a < lo + leftGroups (hi - lo) := by omega
      by_cases hxm : x < lo + leftGroups (hi - lo)
      · simp only [hxm, ite_true]
        have hl : a < lo + leftGroups (hi - lo) := by omega
        simp only [hl, ite_true, bef, bef_append]
        have hm := (mem_groupOffs_ref len log a b _ lo (lo + leftGroups (hi - lo)) (idx + 1) rfl (by omega) (by omega) hl x).2
          ⟨hlx, hxm, hax, hxb⟩
        simp only [hm, ite_true]
        rw [ih (leftGroups (hi - lo)) (by omega) lo _ (idx + 1) x _ (by omega) hlx hxm hax hxb]
        omega
      · simp only [hxm, ite_false]
        have hr : lo + leftGroups (hi - lo) < b := by omega
        by_cases hl : a < lo + leftGroups (hi - lo)
        · simp only [hl, hr, ite_true, bef, bef_append]
          have hm : ¬ x * groupLen log ∈ groupOffs (ref len log a b lo (lo + leftGroups (hi - lo)) (idx + 1)) := by
            rw [mem_groupOffs_ref len log a b _ lo _ (idx + 1) rfl (by omega) (by omega) hl x]; omega
          simp only [hm, ite_false]
          rw [ih (hi - (lo + leftGroups (hi - lo))) (by omega) _ hi (idx + leftGroups (hi - lo)) x _ (by omega) (by omega) hxh hax hxb,
            parentsInSuffix, sufGo_eq a b _ lo _ 0 rfl (by omega),
            parentsIn_eq len log a b _ lo _ (idx + 1) rfl (by omega) (by omega) hl (by omega)]
          omega
        · simp only [hl, hr, ite_true, ite_false, List.nil_append, bef, bef_append, groupOffs, List.not_mem_nil, np,
            Nat.zero_add]
          rw [ih (hi - (lo + leftGroups (hi - lo))) (by omega) _ hi (idx + leftGroups (hi - lo)) x _ (by omega) (by omega) hxh hax hxb,
            parentsInSuffix, sufGo_eq a b _ lo _ 0 rfl (by omega),
            parentsIn_stop _ _ _ _ (by omega)]
          omega
    · simp only [h2, dite_false]
      rw [ref_leaf _ _ _ _ _ _ _ h2]
      have : x = lo := by omega
      subst this
      simp [bef]

end Pinc.ValuesPlan
