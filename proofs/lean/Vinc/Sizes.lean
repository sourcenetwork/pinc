import Vinc.Layout

/-!
# Sizes: depth, outboard size, group size

The arithmetic of `Layout::depth`, `Layout::outboard_size` and `Layout::group_size` in
`vinc-dag/src/tree/layout.rs`, tied to the tree they describe:

* `depth` is the height of the tree over the groups (`ht`), where `u64::leading_zeros` is specified by the
  position of the top set bit (`IsLz`);
* `outboard_size` is 64 bytes for every parent, `groups - 1` of them (the length of `pre`);
* `group_size` is the number of bytes of the value whose group is that index.

It also proves the bound that sizes every fixed stack: a value of at most `2^64 - 1` bytes has at most `2^54`
groups, for every group size log (the log is at least 0, so groups are at least 1024 bytes).

The Rust code does its arithmetic in `u64` with a saturating multiply (`group_size`), a checked subtraction
(`outboard_size`) and a checked-free product `(groups - 1) * 64` (`outboard_size`); the theorems below show the
`Nat` model agrees with the saturating form and that the product stays below `2^64`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false

namespace Vinc.Layout

/-- `u64::MAX`. -/
def u64Max : Nat := 2 ^ 64 - 1

/-- The height of a group tree of `c` groups: the number of parent levels, `ceil(log2 c)`. -/
def hh (c : Nat) : Nat := if c ≤ 1 then 0 else Nat.log2 (c - 1) + 1

theorem hh_leftGroups (c : Nat) (h : 2 ≤ c) : hh (leftGroups c) + 1 = hh c := by
  have hc : hh c = Nat.log2 (c - 1) + 1 := by simp [hh]; omega
  rw [hc]
  simp only [leftGroups, h, ite_true]
  generalize Nat.log2 (c - 1) = m
  cases m with
  | zero => simp [hh]
  | succ m =>
    have h1 : ¬ 2 ^ (m + 1) ≤ 1 := by
      have := Nat.two_pow_pos m
      rw [Nat.pow_succ]; omega
    simp only [hh, h1, ite_false]
    have : Nat.log2 (2 ^ (m + 1) - 1) = m := by
      rw [Nat.log2_eq_iff (by have := Nat.two_pow_pos m; rw [Nat.pow_succ]; omega)]
      have := Nat.two_pow_pos m
      rw [Nat.pow_succ]
      constructor <;> omega
    rw [this]

theorem hh_mono {a b : Nat} (h : a ≤ b) : hh a ≤ hh b := by
  by_cases ha : a ≤ 1
  · simp [hh, ha]
  · have hb : ¬ b ≤ 1 := by omega
    simp only [hh, ha, hb, ite_false]
    have : Nat.log2 (a - 1) ≤ Nat.log2 (b - 1) :=
      (Nat.le_log2 (by omega)).2 (Nat.le_trans (Nat.log2_self_le (by omega)) (by omega))
    omega

/-- The right child is strictly lower than the node. -/
theorem hh_right (c : Nat) (h : 2 ≤ c) : hh (c - leftGroups c) + 1 ≤ hh c := by
  have h1 := le_two_leftGroups c h
  have h2 := hh_leftGroups c h
  have := hh_mono (show c - leftGroups c ≤ leftGroups c by omega)
  omega

/-- The height of the subtree `[lo, hi)`, from its recursive shape. -/
def ht (lo hi : Nat) : Nat :=
  if h : hi - lo ≥ 2 then
    have h1 := leftGroups_pos (hi - lo) h
    have h2 := leftGroups_lt (hi - lo) h
    1 + max (ht lo (lo + leftGroups (hi - lo))) (ht (lo + leftGroups (hi - lo)) hi)
  else 0
termination_by hi - lo

theorem ht_unfold (lo hi : Nat) (h : hi - lo ≥ 2) :
    ht lo hi = 1 + max (ht lo (lo + leftGroups (hi - lo))) (ht (lo + leftGroups (hi - lo)) hi) := by
  rw [ht]; simp [h]

theorem ht_eq (lo hi : Nat) : ht lo hi = hh (hi - lo) := by
  generalize hn : hi - lo = n
  induction n using Nat.strongRecOn generalizing lo hi with
  | _ n ih =>
    by_cases h : n ≥ 2
    · have h1 := leftGroups_pos (hi - lo) (by omega)
      have h2 := leftGroups_lt (hi - lo) (by omega)
      rw [ht_unfold lo hi (by omega)]
      rw [ih (leftGroups (hi - lo)) (by omega) lo (lo + leftGroups (hi - lo)) (by omega),
        ih (n - leftGroups (hi - lo)) (by omega) (lo + leftGroups (hi - lo)) hi (by omega)]
      have := hh_leftGroups n (by omega)
      have := hh_right n (by omega)
      subst hn
      omega
    · rw [ht, dif_neg (by omega)]
      simp [hh]; omega

/-- `u64::leading_zeros(x) = z`: the top set bit of `x` is bit `63 - z`. -/
def IsLz (x z : Nat) : Prop := z ≤ 63 ∧ 2 ^ (63 - z) ≤ x ∧ x < 2 ^ (64 - z)

/-- `Layout::depth`: `0` for at most one group, `64 - leading_zeros(groups - 1)` otherwise, equals the height of
the tree over `n` groups. -/
theorem depth_eq (n z : Nat) (hn : 2 ≤ n) (hz : IsLz (n - 1) z) : 64 - z = ht 0 n := by
  obtain ⟨h1, h2, h3⟩ := hz
  rw [ht_eq]
  have : Nat.log2 (n - 1) = 63 - z := by
    rw [Nat.log2_eq_iff (by omega)]
    exact ⟨h2, by rw [show 63 - z + 1 = 64 - z by omega]; exact h3⟩
  have hc : hh (n - 0) = Nat.log2 (n - 1) + 1 := by simp [hh]; omega
  omega

theorem depth_small (n : Nat) (hn : n ≤ 1) : ht 0 n = 0 := by
  rw [ht_eq]; simp [hh]; omega

/-- `Layout::outboard_size`: `checked_sub(1)` on the group count, then 64 bytes per parent. -/
def outboardSize (len log : Nat) : Nat :=
  match groups len log with
  | 0 => 0
  | n + 1 => n * 64

/-- The outboard holds one 64-byte pair per parent of the tree. -/
theorem outboardSize_eq (len log : Nat) : outboardSize len log = 64 * (pre 0 (groups len log)).length := by
  rw [pre_length]
  unfold outboardSize
  rcases groups len log with _ | n <;> simp [Nat.mul_comm]

/-- A value of at most `2^64 - 1` bytes has at most `2^54` groups, whatever the group size. -/
theorem groups_le (len log : Nat) (hlen : len ≤ u64Max) : groups len log ≤ 2 ^ 54 := by
  refine Classical.byContradiction fun h => ?_
  have hk := (lt_groups_iff len log (2 ^ 54)).1 (by omega)
  have hg : 1024 ≤ groupLen log := by
    unfold groupLen; rw [Nat.shiftLeft_eq]
    have := Nat.two_pow_pos log
    omega
  have := Nat.mul_le_mul_left (2 ^ 54) hg
  have e : (2 : Nat) ^ 54 * 1024 = 2 ^ 64 := by decide
  unfold u64Max at hlen
  omega

/-- `(groups - 1) * 64` does not overflow `u64`. -/
theorem outboardSize_lt (len log : Nat) (hlen : len ≤ u64Max) : outboardSize len log < 2 ^ 64 := by
  have := groups_le len log hlen
  have e : (2 : Nat) ^ 54 * 64 < 2 ^ 64 := by decide
  unfold outboardSize
  generalize groups len log = m at this ⊢
  rcases m with _ | n
  · simp
  · simp only []; omega

/-- `Layout::group_size`, with the saturating multiply of `u64` made explicit. -/
def groupSize (len log i : Nat) : Nat :=
  let start := min (i * groupLen log) u64Max
  if start ≥ len then 0 else if len - start < groupLen log then len - start else groupLen log

/-- The saturating form is the plain one: 0 from the first byte of the group on the value's end, otherwise the
group size or the remainder. -/
theorem groupSize_eq (len log i : Nat) (hlen : len ≤ u64Max) :
    groupSize len log i = if i * groupLen log ≥ len then 0 else min (groupLen log) (len - i * groupLen log) := by
  unfold groupSize
  generalize i * groupLen log = p
  generalize groupLen log = g
  unfold u64Max at *
  simp only []
  by_cases h : p ≥ len
  · have : min p (2 ^ 64 - 1) ≥ len := by omega
    simp [h, this]
  · have : ¬ min p (2 ^ 64 - 1) ≥ len := by omega
    have h2 : min p (2 ^ 64 - 1) = p := by omega
    simp only [h, ite_false, h2]
    by_cases h3 : len - p < g <;> simp [h3] <;> omega

/-- `group_size` counts exactly the bytes of the value that belong to group `i`. -/
theorem groupSize_spec (len log i : Nat) (hlen : len ≤ u64Max) (b : Nat) :
    (i * groupLen log ≤ b ∧ b < i * groupLen log + groupSize len log i) ↔ (b < len ∧ b / groupLen log = i) := by
  have hg := groupLen_pos log
  rw [groupSize_eq len log i hlen]
  have h1 := Nat.div_lt_iff_lt_mul (x := b) (k := groupLen log) (y := i + 1) hg
  have h2 := Nat.le_div_iff_mul_le (x := i) (y := b) (k := groupLen log) hg
  have h3 : b / groupLen log = i ↔ i ≤ b / groupLen log ∧ b / groupLen log < i + 1 := by omega
  rw [h3, h2, h1, Nat.succ_mul]
  generalize i * groupLen log = p
  generalize groupLen log = g
  by_cases h : p ≥ len <;> simp only [h, ite_true, ite_false] <;> constructor <;> intro hh <;> omega

/-- Group `i` has bytes exactly when it exists. -/
theorem groupSize_pos_iff (len log i : Nat) (hlen : len ≤ u64Max) :
    0 < groupSize len log i ↔ i < groups len log := by
  rw [lt_groups_iff, groupSize_eq len log i hlen]
  have hg := groupLen_pos log
  generalize i * groupLen log = p
  generalize groupLen log = g at hg
  by_cases h : p ≥ len <;> simp only [h, ite_true, ite_false] <;> omega

/-- A group never reads past the value. -/
theorem groupSize_le (len log i : Nat) (hlen : len ≤ u64Max) :
    i * groupLen log + groupSize len log i ≤ len ∨ groupSize len log i = 0 := by
  rw [groupSize_eq len log i hlen]
  generalize i * groupLen log = p
  generalize groupLen log = g
  by_cases h : p ≥ len
  · simp [h]
  · simp only [h, ite_false]; omega

/-- A group is at most one group long. -/
theorem groupSize_le_len (len log i : Nat) (hlen : len ≤ u64Max) : groupSize len log i ≤ groupLen log := by
  rw [groupSize_eq len log i hlen]
  generalize i * groupLen log = p
  generalize groupLen log = g
  by_cases h : p ≥ len <;> simp only [h, ite_true, ite_false] <;> omega

end Vinc.Layout

#audit_axioms Vinc.Layout.ht_eq
#audit_axioms Vinc.Layout.depth_eq
#audit_axioms Vinc.Layout.outboardSize_eq
#audit_axioms Vinc.Layout.outboardSize_lt
#audit_axioms Vinc.Layout.groups_le
#audit_axioms Vinc.Layout.groupSize_spec
