import Pinc.Axioms

/-!
# Tree layout

The arithmetic of `pinc-dag/src/tree/layout.rs` and the pre-order index of `preorder_index`: `left_groups`,
`Layout::groups`, `Layout::group_range` and the parent numbering of the outboard.

Everything is `Nat`; the Rust code is `u64` arithmetic that cannot overflow for the supported group sizes
(`log <= 20`), so the two agree.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false

namespace Pinc.Layout

/-- `left_groups`: the left subtree of a node of `count >= 2` groups holds the largest power of two strictly
below `count`; 0 when `count < 2`. -/
def leftGroups (count : Nat) : Nat := if count ≥ 2 then 2 ^ Nat.log2 (count - 1) else 0

theorem leftGroups_pos (c : Nat) (h : 2 ≤ c) : 0 < leftGroups c := by
  simp only [leftGroups, h, ite_true]; exact Nat.two_pow_pos _

theorem leftGroups_lt (c : Nat) (h : 2 ≤ c) : leftGroups c < c := by
  have := @Nat.log2_self_le (c - 1) (by omega)
  simp [leftGroups, h]; omega

theorem le_two_leftGroups (c : Nat) (h : 2 ≤ c) : c ≤ 2 * leftGroups c := by
  have := @Nat.lt_log2_self (c - 1)
  simp only [leftGroups, h, ite_true]
  rw [Nat.pow_succ] at this
  omega

/-- The left subtree is a power of two. -/
theorem leftGroups_pow (c : Nat) (h : 2 ≤ c) : ∃ k, leftGroups c = 2 ^ k :=
  ⟨Nat.log2 (c - 1), by simp [leftGroups, h]⟩

/-- It is the largest power of two strictly below `c`. -/
theorem leftGroups_max (c : Nat) (h : 2 ≤ c) (j : Nat) (hj : 2 ^ j < c) : 2 ^ j ≤ leftGroups c := by
  have : j ≤ Nat.log2 (c - 1) := (Nat.le_log2 (by omega)).2 (by omega)
  simp only [leftGroups, h, ite_true]
  exact Nat.pow_le_pow_right (by omega) this

/-- The parent nodes of the subtree `[lo, hi)` in pre-order: the order of the outboard. -/
def pre (lo hi : Nat) : List (Nat × Nat) :=
  if h : hi - lo ≥ 2 then
    have h1 := leftGroups_pos (hi - lo) h
    have h2 := leftGroups_lt (hi - lo) h
    (lo, hi) :: (pre lo (lo + leftGroups (hi - lo)) ++ pre (lo + leftGroups (hi - lo)) hi)
  else []
termination_by hi - lo

theorem pre_unfold (lo hi : Nat) (h : hi - lo ≥ 2) :
    pre lo hi = (lo, hi) :: (pre lo (lo + leftGroups (hi - lo)) ++ pre (lo + leftGroups (hi - lo)) hi) := by
  rw [pre]; simp [h]

theorem pre_small (lo hi : Nat) (h : ¬ hi - lo ≥ 2) : pre lo hi = [] := by
  rw [pre]; simp [h]

/-- A tree of `n` groups has `n - 1` parents (the outboard holds `groups - 1` pairs). -/
theorem pre_length (lo hi : Nat) : (pre lo hi).length = hi - lo - 1 := by
  generalize hn : hi - lo = n
  induction n using Nat.strongRecOn generalizing lo hi with
  | _ n ih =>
    by_cases h : n ≥ 2
    · rw [pre_unfold lo hi (by omega)]
      have h1 := leftGroups_pos (hi - lo) (by omega)
      have h2 := leftGroups_lt (hi - lo) (by omega)
      simp only [List.length_cons, List.length_append]
      rw [ih (leftGroups (hi - lo)) (by omega) lo (lo + leftGroups (hi - lo)) (by omega),
        ih (n - leftGroups (hi - lo)) (by omega) (lo + leftGroups (hi - lo)) hi (by omega)]
      omega
    · rw [pre_small lo hi (by omega)]; simp; omega

/-- The right child of the parent `[lo, hi)`, when it is a parent, sits at pre-order position `left_groups`
within the node's own subtree: the `idx + left` step of `preorder_index`. -/
theorem right_child_index (lo hi : Nat) (h : hi - lo ≥ 2) (hc : hi - (lo + leftGroups (hi - lo)) ≥ 2) :
    (pre lo hi)[leftGroups (hi - lo)]? = some (lo + leftGroups (hi - lo), hi) := by
  have h1 := leftGroups_pos (hi - lo) h
  have h2 := leftGroups_lt (hi - lo) h
  have hlen := pre_length lo (lo + leftGroups (hi - lo))
  rw [pre_unfold lo hi h]
  generalize leftGroups (hi - lo) = L1 at *
  obtain ⟨L, rfl⟩ : ∃ L, L1 = L + 1 := ⟨L1 - 1, by omega⟩
  simp only [List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by omega), show L - (pre lo (lo + (L + 1))).length = 0 by omega]
  rw [pre_unfold _ _ hc]; simp

/-- The left child of the parent `[lo, hi)`, when it is a parent, sits right after it: the `idx + 1` step. -/
theorem left_child_index (lo hi : Nat) (h : hi - lo ≥ 2) (hc : leftGroups (hi - lo) ≥ 2) :
    (pre lo hi)[1]? = some (lo, lo + leftGroups (hi - lo)) := by
  have h1 := leftGroups_pos (hi - lo) h
  have h2 := leftGroups_lt (hi - lo) h
  have : (lo + leftGroups (hi - lo)) - lo ≥ 2 := by omega
  rw [pre_unfold lo hi h]
  simp only [List.getElem?_cons_succ]
  rw [pre_unfold _ _ this]; simp

/-- `(lo, hi)` is a node of the tree rooted at `(nlo, nhi)`. -/
inductive Sub : Nat → Nat → Nat → Nat → Prop where
  | refl (nlo nhi : Nat) : Sub nlo nhi nlo nhi
  | left {nlo nhi lo hi : Nat} : nhi - nlo ≥ 2 → Sub nlo (nlo + leftGroups (nhi - nlo)) lo hi → Sub nlo nhi lo hi
  | right {nlo nhi lo hi : Nat} : nhi - nlo ≥ 2 → Sub (nlo + leftGroups (nhi - nlo)) nhi lo hi → Sub nlo nhi lo hi

theorem Sub.bounds {a b lo hi : Nat} (h : Sub a b lo hi) : a ≤ lo ∧ hi ≤ b ∧ (a < b → lo < hi) := by
  induction h with
  | refl => exact ⟨Nat.le_refl _, Nat.le_refl _, id⟩
  | left h _ ih =>
    have := leftGroups_pos _ h
    have := leftGroups_lt _ h
    obtain ⟨i1, i2, i3⟩ := ih
    exact ⟨i1, by omega, fun _ => i3 (by omega)⟩
  | right h _ ih =>
    have := leftGroups_pos _ h
    have := leftGroups_lt _ h
    obtain ⟨i1, i2, i3⟩ := ih
    exact ⟨by omega, i2, fun _ => i3 (by omega)⟩

/-- `preorder_index`: the loop, with the running node `[nlo, nhi)` and the index so far. -/
def preorderGo (lo hi : Nat) (nlo nhi idx : Nat) : Nat :=
  if h : (nlo ≠ lo ∨ nhi ≠ hi) ∧ nhi - nlo ≥ 2 then
    have h1 := leftGroups_pos (nhi - nlo) h.2
    have h2 := leftGroups_lt (nhi - nlo) h.2
    if hi ≤ nlo + leftGroups (nhi - nlo) then preorderGo lo hi nlo (nlo + leftGroups (nhi - nlo)) (idx + 1)
    else preorderGo lo hi (nlo + leftGroups (nhi - nlo)) nhi (idx + leftGroups (nhi - nlo))
  else idx
termination_by nhi - nlo

/-- `preorder_index(groups, lo, hi)`. -/
def preorderIndex (groups lo hi : Nat) : Nat := preorderGo lo hi 0 groups 0

theorem preorderGo_stop (lo hi nlo nhi idx : Nat) (h : ¬ ((nlo ≠ lo ∨ nhi ≠ hi) ∧ nhi - nlo ≥ 2)) :
    preorderGo lo hi nlo nhi idx = idx := by
  rw [preorderGo, dif_neg h]

theorem preorderGo_step (lo hi nlo nhi idx : Nat) (h : (nlo ≠ lo ∨ nhi ≠ hi) ∧ nhi - nlo ≥ 2) :
    preorderGo lo hi nlo nhi idx =
      if hi ≤ nlo + leftGroups (nhi - nlo) then preorderGo lo hi nlo (nlo + leftGroups (nhi - nlo)) (idx + 1)
      else preorderGo lo hi (nlo + leftGroups (nhi - nlo)) nhi (idx + leftGroups (nhi - nlo)) := by
  rw [preorderGo, dif_pos h]

/-- `preorder_index` lands on the node's position in the pre-order of the parents. -/
theorem preorderGo_correct {nlo nhi lo hi : Nat} (hs : Sub nlo nhi lo hi) (hn : nlo < nhi) (hp : hi - lo ≥ 2) :
    ∀ idx, idx ≤ preorderGo lo hi nlo nhi idx ∧
      (pre nlo nhi)[preorderGo lo hi nlo nhi idx - idx]? = some (lo, hi) := by
  induction hs with
  | refl =>
    intro idx
    rw [preorderGo_stop _ _ _ _ _ (by simp)]
    refine ⟨Nat.le_refl _, ?_⟩
    rw [pre_unfold _ _ hp]; simp
  | @left nlo nhi lo hi h hsub ih =>
    intro idx
    have h1 := leftGroups_pos _ h
    have h2 := leftGroups_lt _ h
    obtain ⟨b1, b2, b3⟩ := hsub.bounds
    have hne : (nlo ≠ lo ∨ nhi ≠ hi) ∧ nhi - nlo ≥ 2 := ⟨Or.inr (by omega), h⟩
    have hc : hi ≤ nlo + leftGroups (nhi - nlo) := by omega
    rw [preorderGo_step _ _ _ _ _ hne]
    simp only [hc, ite_true]
    obtain ⟨i1, i2⟩ := ih (by omega) hp (idx + 1)
    refine ⟨by omega, ?_⟩
    rw [pre_unfold _ _ h]
    obtain ⟨d, hd⟩ : ∃ d, preorderGo lo hi nlo (nlo + leftGroups (nhi - nlo)) (idx + 1) - idx = d + 1 :=
      ⟨preorderGo lo hi nlo (nlo + leftGroups (nhi - nlo)) (idx + 1) - idx - 1, by omega⟩
    rw [hd]
    have : preorderGo lo hi nlo (nlo + leftGroups (nhi - nlo)) (idx + 1) - (idx + 1) = d := by omega
    rw [this] at i2
    simp only [List.getElem?_cons_succ]
    rw [List.getElem?_append_left (by
      have := (List.getElem?_eq_some_iff.1 i2).1; exact this)]
    exact i2
  | @right nlo nhi lo hi h hsub ih =>
    intro idx
    have h1 := leftGroups_pos _ h
    have h2 := leftGroups_lt _ h
    obtain ⟨b1, b2, b3⟩ := hsub.bounds
    have hlt : lo < hi := by omega
    have hne : (nlo ≠ lo ∨ nhi ≠ hi) ∧ nhi - nlo ≥ 2 := ⟨Or.inl (by omega), h⟩
    have hc : ¬ hi ≤ nlo + leftGroups (nhi - nlo) := by omega
    rw [preorderGo_step _ _ _ _ _ hne]
    simp only [hc, ite_false]
    obtain ⟨i1, i2⟩ := ih (by omega) hp (idx + leftGroups (nhi - nlo))
    refine ⟨by omega, ?_⟩
    have hlen := pre_length nlo (nlo + leftGroups (nhi - nlo))
    rw [pre_unfold _ _ h]
    generalize preorderGo lo hi (nlo + leftGroups (nhi - nlo)) nhi (idx + leftGroups (nhi - nlo)) = R at *
    generalize leftGroups (nhi - nlo) = L1 at *
    obtain ⟨L, rfl⟩ : ∃ L, L1 = L + 1 := ⟨L1 - 1, by omega⟩
    obtain ⟨d, rfl⟩ : ∃ d, R = idx + (L + 1) + d := ⟨R - (idx + (L + 1)), by omega⟩
    rw [show idx + (L + 1) + d - idx = (L + d) + 1 by omega]
    simp only [List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by omega), show L + d - (pre nlo (nlo + (L + 1))).length = d by omega]
    rw [show idx + (L + 1) + d - (idx + (L + 1)) = d by omega] at i2
    exact i2

/-- (c) `preorder_index` of a parent node of the tree of `groups` leaves is its position in the pre-order of
all `groups - 1` parents. -/
theorem preorderIndex_correct {groups lo hi : Nat} (hs : Sub 0 groups lo hi) (hp : hi - lo ≥ 2) :
    (pre 0 groups)[preorderIndex groups lo hi]? = some (lo, hi) := by
  have := hs.bounds
  have := (preorderGo_correct hs (by omega) hp 0).2
  simpa [preorderIndex] using this

/-! ## Groups and byte ranges -/

/-- `group_len`: `CHUNK_LEN << log`. -/
def groupLen (log : Nat) : Nat := 1024 <<< log

theorem groupLen_pos (log : Nat) : 0 < groupLen log := by
  unfold groupLen; rw [Nat.shiftLeft_eq]
  have := Nat.two_pow_pos log
  omega

/-- `Layout::groups`. -/
def groups (len log : Nat) : Nat :=
  len / groupLen log + if len % groupLen log = 0 then 0 else 1

/-- Group `k` exists exactly when it starts inside the value. -/
theorem lt_groups_iff (len log k : Nat) : k < groups len log ↔ k * groupLen log < len := by
  have hg := groupLen_pos log
  unfold groups
  generalize groupLen log = g at hg ⊢
  have hdm := Nat.div_add_mod len g
  have hml := Nat.mod_lt len hg
  have hc := Nat.mul_comm g (len / g)
  generalize len / g = q at *
  generalize len % g = r at *
  by_cases hr : r = 0
  · simp only [hr, ite_true, Nat.add_zero]
    constructor
    · intro h
      have := Nat.mul_le_mul_right g (show k + 1 ≤ q by omega)
      rw [Nat.succ_mul] at this
      omega
    · intro h
      refine Classical.byContradiction fun hk => ?_
      have := Nat.mul_le_mul_right g (show q ≤ k by omega)
      omega
  · simp only [hr, ite_false]
    constructor
    · intro h
      have := Nat.mul_le_mul_right g (show k ≤ q by omega)
      omega
    · intro h
      refine Classical.byContradiction fun hk => ?_
      have := Nat.mul_le_mul_right g (show q + 1 ≤ k by omega)
      rw [Nat.succ_mul] at this
      omega

/-- `Layout::group_range`: `none` is `RangeOutOfBounds`. -/
def groupRange (len log s e : Nat) : Option (Nat × Nat) :=
  if s > e ∨ e > len then none
  else if s = e then some (0, 0)
  else some (s / groupLen log, (e - 1) / groupLen log + 1)


theorem groupRange_none (len log s e : Nat) :
    groupRange len log s e = none ↔ s > e ∨ e > len := by
  unfold groupRange
  by_cases h : s > e ∨ e > len
  · simp [h]
  · by_cases h2 : s = e <;> simp [h, h2]

theorem groupRange_empty (len log s : Nat) (h : s ≤ len) : groupRange len log s s = some (0, 0) := by
  simp [groupRange]; omega

/-- (c) `group_range` is the minimal covering group interval: group `k` is in the range exactly when its bytes
`[k * group_len, (k + 1) * group_len)` intersect the requested bytes, and the range stays within the groups. -/
theorem groupRange_spec (len log s e : Nat) (hse : s < e) (hel : e ≤ len) :
    ∃ a b, groupRange len log s e = some (a, b) ∧ a < b ∧ b ≤ groups len log ∧
      ∀ k, (a ≤ k ∧ k < b) ↔ (k * groupLen log < e ∧ s < (k + 1) * groupLen log) := by
  have hg := groupLen_pos log
  refine ⟨s / groupLen log, (e - 1) / groupLen log + 1, ?_, ?_, ?_, ?_⟩
  · unfold groupRange
    have : ¬ (s > e ∨ e > len) := by omega
    have h2 : s ≠ e := by omega
    simp [this, h2]
  · have := Nat.div_le_div_right (c := groupLen log) (show s ≤ e - 1 by omega)
    omega
  · have h1 := Nat.div_mul_le_self (e - 1) (groupLen log)
    have := (lt_groups_iff len log ((e - 1) / groupLen log)).2 (by omega)
    omega
  · intro k
    have h1 := Nat.div_lt_iff_lt_mul (x := s) (k := groupLen log) (y := k + 1) hg
    have h2 := Nat.le_div_iff_mul_le (x := k) (y := e - 1) (k := groupLen log) hg
    constructor
    · rintro ⟨a, b⟩
      constructor
      · omega
      · exact h1.1 (by omega)
    · rintro ⟨a, b⟩
      constructor
      · have := h1.2 b; omega
      · omega

end Pinc.Layout

#audit_axioms Pinc.Layout.pre_length
#audit_axioms Pinc.Layout.right_child_index
#audit_axioms Pinc.Layout.preorderIndex_correct
#audit_axioms Pinc.Layout.groupRange_spec
#audit_axioms Pinc.Layout.leftGroups_max
