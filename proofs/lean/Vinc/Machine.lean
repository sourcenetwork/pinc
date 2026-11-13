import Vinc.Encode

/-!
# Machine integers

The tree arithmetic of `vinc-dag/src/tree/layout.rs` as the code writes it, on `u64` (and `usize`, which is
32 or 64 bits wide), not on unbounded naturals.

Each operation returns `none` where Rust would overflow, underflow, divide by zero or shift out of range:
that is a panic in a debug build and a silent wrap in a release build, so the code is correct only if it never
happens. A function `fooM` is the code of `foo` written with these operations, in the order the code evaluates
them, and a theorem named after it with the suffix `eq` (`groupsM_eq`, `depthM_eq`, `outboardSizeM_eq`, `groupSizeM_eq`, `groupRangeM_eq`,
`leftGroupsM_eq`, `preorderIndexM_eq`, ...) says it returns `some` of the unbounded model that the rest of the package proves
correct: no step of the code overflows, for every length up to `u64::MAX` and every supported group log. Where the
code uses a saturating operation the model uses `satMul`, and where it narrows with `try_from` the model uses
`tryFrom`, which fails instead of truncating.

Assumed, as hypotheses of the theorems (never as axioms): `u64::leading_zeros` and `u64::ilog2` are specified by
the position of the top set bit (`Layout.IsLz`, `IsIlog2`). The other core integer operations are the ones
defined here, which are their documented meanings.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Vinc.Machine
open Vinc.Layout Vinc.Encode

/-! ## Operations of a `w`-bit unsigned integer -/

/-- `a + b`; `none` on overflow. -/
def add (w a b : Nat) : Option Nat := if a + b < 2 ^ w then some (a + b) else none

/-- `a * b`; `none` on overflow. -/
def mul (w a b : Nat) : Option Nat := if a * b < 2 ^ w then some (a * b) else none

/-- `a - b`; `none` on underflow. -/
def sub (w a b : Nat) : Option Nat := if b ≤ a then some (a - b) else none

/-- `a.saturating_mul(b)`. -/
def satMul (w a b : Nat) : Nat := min (a * b) (2 ^ w - 1)

/-- `a << s`: a shift by `w` or more is a panic; bits shifted out are lost. -/
def shl (w a s : Nat) : Option Nat := if s < w then some (a * 2 ^ s % 2 ^ w) else none

/-- `a / b`; `none` for a zero divisor. -/
def div (a b : Nat) : Option Nat := if b = 0 then none else some (a / b)

/-- `T::try_from(x)` into a `w`-bit integer: `none` when `x` does not fit, never a truncation. -/
def tryFrom (w x : Nat) : Option Nat := if x < 2 ^ w then some x else none

/-- `u64::ilog2` is specified by the top set bit: `2^z <= x < 2^(z+1)`. -/
def IsIlog2 (x z : Nat) : Prop := 2 ^ z ≤ x ∧ x < 2 ^ (z + 1)

theorem ilog2_eq {x z : Nat} (hx : 0 < x) (h : IsIlog2 x z) : z = Nat.log2 x := by
  have := (Nat.log2_eq_iff (n := x) (k := z) (by omega)).2 h
  omega

theorem two_pow_lt_64 (k : Nat) (h : k < 64) : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) h

/-! ## Layout -/

/-- `CHUNK_LEN << log`. -/
def groupLenM (log : Nat) : Option Nat := shl 64 1024 log

theorem groupLen_le (log : Nat) (h : log ≤ 20) : groupLen log ≤ 2 ^ 30 := by
  unfold groupLen; rw [Nat.shiftLeft_eq]
  have := Nat.pow_le_pow_right (show 0 < 2 by omega) h
  have e : (2 : Nat) ^ 30 = 1024 * 2 ^ 20 := by decide
  omega

theorem groupLen_ge (log : Nat) : 1024 ≤ groupLen log := by
  unfold groupLen; rw [Nat.shiftLeft_eq]
  have := Nat.two_pow_pos log
  omega

theorem groupLenM_eq (log : Nat) (h : log ≤ 20) : groupLenM log = some (groupLen log) := by
  have h1 := groupLen_le log h
  have h2 : groupLen log < 2 ^ 64 := Nat.lt_of_le_of_lt h1 (by decide)
  have hg : groupLen log = 1024 * 2 ^ log := by unfold groupLen; rw [Nat.shiftLeft_eq]
  simp only [groupLenM, shl, show log < 64 by omega, ite_true]
  rw [← hg, Nat.mod_eq_of_lt h2]

/-- `Layout::groups`. -/
def groupsM (len log : Nat) : Option Nat := do
  let g ← groupLenM log
  let q ← div len g
  add 64 q (if len % g = 0 then 0 else 1)

theorem groupsM_eq (len log : Nat) (hlen : len < 2 ^ 64) (hlog : log ≤ 20) :
    groupsM len log = some (groups len log) := by
  have hg := groupLen_pos log
  have hb := groups_le len log (by unfold u64Max; omega)
  have hlt : groups len log < 2 ^ 64 := Nat.lt_of_le_of_lt hb (by decide)
  simp only [groupsM, groupLenM_eq log hlog, div, Option.bind_some, Option.bind_eq_bind, show groupLen log ≠ 0 by omega, ite_false,
    add]
  unfold groups at hlt ⊢
  simp [hlt]

/-- `Layout::depth`, with `u64::leading_zeros` as a function `lz`. -/
def depthM (lz : Nat → Nat) (len log : Nat) : Option Nat := do
  let n ← groupsM len log
  if n ≤ 1 then some 0 else do
    let m ← sub 64 n 1
    sub 32 64 (lz m)

theorem depthM_eq (lz : Nat → Nat) (hlz : ∀ x, 0 < x → x < 2 ^ 64 → IsLz x (lz x)) (len log : Nat)
    (hlen : len < 2 ^ 64) (hlog : log ≤ 20) : depthM lz len log = some (ht 0 (groups len log)) := by
  have hb := groups_le len log (by unfold u64Max; omega)
  simp only [depthM, groupsM_eq len log hlen hlog, Option.bind_some, Option.bind_eq_bind]
  by_cases hn : groups len log ≤ 1
  · simp only [hn, ite_true]; rw [depth_small _ hn]
  · simp only [hn, ite_false, sub, show 1 ≤ groups len log by omega, ite_true]
    have hlt : groups len log - 1 < 2 ^ 64 := Nat.lt_of_le_of_lt (by omega) (Nat.lt_of_le_of_lt hb (by decide))
    have hz := hlz (groups len log - 1) (by omega) hlt
    have := depth_eq (groups len log) _ (by omega) hz
    obtain ⟨h1, _, _⟩ := hz
    simp [this, show lz (groups len log - 1) ≤ 64 by omega]

/-- `Layout::outboard_size`. -/
def outboardSizeM (len log : Nat) : Option Nat := do
  let n ← groupsM len log
  match n with
  | 0 => some 0
  | k + 1 => mul 64 k 64

theorem outboardSizeM_eq (len log : Nat) (hlen : len < 2 ^ 64) (hlog : log ≤ 20) :
    outboardSizeM len log = some (outboardSize len log) := by
  have hlt := outboardSize_lt len log (by unfold u64Max; omega)
  simp only [outboardSizeM, groupsM_eq len log hlen hlog, Option.bind_some, Option.bind_eq_bind]
  unfold outboardSize at hlt ⊢
  generalize groups len log = m at hlt ⊢
  rcases m with _ | k
  · rfl
  · simp only [mul]; simp at hlt; simp [hlt]

/-- `Layout::group_size`. -/
def groupSizeM (len log i : Nat) : Option Nat := do
  let g ← groupLenM log
  let start := satMul 64 i g
  if start ≥ len then some 0 else do
    let rest ← sub 64 len start
    if rest < g then some rest else some g

theorem groupSizeM_eq (len log i : Nat) (hlog : log ≤ 20) :
    groupSizeM len log i = some (groupSize len log i) := by
  simp only [groupSizeM, groupLenM_eq log hlog, Option.bind_some, Option.bind_eq_bind]
  unfold groupSize satMul u64Max
  by_cases h : min (i * groupLen log) (2 ^ 64 - 1) ≥ len
  · simp [h]
  · have hle : min (i * groupLen log) (2 ^ 64 - 1) ≤ len := by omega
    simp [h, sub, hle]
    split <;> rfl

/-- `Layout::group_range`: the outer `none` is an overflow, the inner one `RangeOutOfBounds`. -/
def groupRangeM (len log s e : Nat) : Option (Option (Nat × Nat)) :=
  if s > e ∨ e > len then some none
  else if s = e then some (some (0, 0))
  else do
    let g ← groupLenM log
    let a ← div s g
    let t ← sub 64 e 1
    let q ← div t g
    let b ← add 64 q 1
    some (some (a, b))

theorem groupRangeM_eq (len log s e : Nat) (hlen : len < 2 ^ 64) (hlog : log ≤ 20) :
    groupRangeM len log s e = some (groupRange len log s e) := by
  have hg := groupLen_pos log
  have hg1 := groupLen_ge log
  unfold groupRangeM groupRange
  by_cases h : s > e ∨ e > len
  · simp [h]
  · by_cases h2 : s = e
    · subst h2
      have : ¬ (s > len) := by omega
      simp [this]
    · have hq : (e - 1) / groupLen log < 2 ^ 54 := by
        have : (e - 1) / groupLen log ≤ (e - 1) / 1024 := Nat.div_le_div_left hg1 (by omega)
        have : (e - 1) / 1024 < 2 ^ 54 := by omega
        omega
      have hq2 : (e - 1) / groupLen log + 1 < 2 ^ 64 := Nat.lt_of_le_of_lt (by omega) (show 2 ^ 54 < 2 ^ 64 by decide)
      simp only [h, h2, ite_false, groupLenM_eq log hlog, div, show groupLen log ≠ 0 by omega, Option.bind_some, Option.bind_eq_bind,
        sub, show 1 ≤ e by omega, ite_true, add, hq2]

/-! ## `left_groups` and `preorder_index` -/

/-- `left_groups`, with `u64::ilog2` as a function `il`. -/
def leftGroupsM (il : Nat → Nat) (count : Nat) : Option Nat :=
  if count = 0 then some 0 else if count - 1 > 0 then shl 64 1 (il (count - 1)) else some 0

theorem leftGroupsM_eq (il : Nat → Nat) (hil : ∀ x, 0 < x → x < 2 ^ 64 → IsIlog2 x (il x)) (count : Nat)
    (hc : count < 2 ^ 64) : leftGroupsM il count = some (leftGroups count) := by
  unfold leftGroupsM leftGroups
  by_cases h0 : count = 0
  · simp [h0]
  · by_cases h1 : count - 1 > 0
    · have hz := ilog2_eq h1 (hil (count - 1) h1 (by omega))
      have hl : Nat.log2 (count - 1) < 64 := by
        have := Nat.log2_lt (n := count - 1) (k := 64) (by omega)
        exact this.2 (by omega)
      have hp := two_pow_lt_64 _ hl
      simp only [h0, h1, ite_false, ite_true, shl, hz, hl, show count ≥ 2 by omega, Nat.one_mul]
      rw [Nat.mod_eq_of_lt hp]
    · simp [h0, h1, show ¬ count ≥ 2 by omega]

/-- The loop of `preorder_index`, with `fuel` bounding the iterations (a proof device: the theorem shows that
`nhi - nlo` iterations are enough, so the loop terminates). -/
def preorderGoM (il : Nat → Nat) (lo hi : Nat) : (fuel nlo nhi idx : Nat) → Option Nat
  | 0, nlo, nhi, idx => if (nlo ≠ lo ∨ nhi ≠ hi) ∧ nhi - nlo ≥ 2 then none else some idx
  | f + 1, nlo, nhi, idx =>
    if (nlo ≠ lo ∨ nhi ≠ hi) ∧ nhi - nlo ≥ 2 then do
      let c ← sub 64 nhi nlo
      let left ← leftGroupsM il c
      let mid ← add 64 nlo left
      if hi ≤ mid then do
        let idx' ← add 64 idx 1
        preorderGoM il lo hi f nlo mid idx'
      else do
        let idx' ← add 64 idx left
        preorderGoM il lo hi f mid nhi idx'
    else some idx

/-- `preorder_index(groups, lo, hi)`. -/
def preorderIndexM (il : Nat → Nat) (groups lo hi : Nat) : Option Nat := preorderGoM il lo hi groups 0 groups 0

/-- Along the walk the running node stays inside the tree and `idx + size` never grows, so `idx` never exceeds
the group count: no addition overflows, for any `lo` and `hi`, node or not. -/
theorem preorderGoM_eq (il : Nat → Nat) (hil : ∀ x, 0 < x → x < 2 ^ 64 → IsIlog2 x (il x)) (lo hi G : Nat)
    (hG : G ≤ 2 ^ 54) :
    ∀ (fuel nlo nhi idx : Nat), nhi - nlo ≤ fuel → nlo ≤ nhi → nhi ≤ G → idx + (nhi - nlo) ≤ G →
      preorderGoM il lo hi fuel nlo nhi idx = some (preorderGo lo hi nlo nhi idx) := by
  intro fuel
  induction fuel with
  | zero =>
    intro nlo nhi idx hf hn hh hi'
    have : ¬ ((nlo ≠ lo ∨ nhi ≠ hi) ∧ nhi - nlo ≥ 2) := by omega
    rw [preorderGo_stop _ _ _ _ _ this]
    simp [preorderGoM, this]
  | succ f ih =>
    intro nlo nhi idx hf hn hh hi'
    by_cases hc : (nlo ≠ lo ∨ nhi ≠ hi) ∧ nhi - nlo ≥ 2
    · have h2 : nhi - nlo ≥ 2 := hc.2
      have h1 := leftGroups_pos _ h2
      have h3 := leftGroups_lt _ h2
      have hG' : nhi - nlo < 2 ^ 64 := Nat.lt_of_le_of_lt (by omega) (Nat.lt_of_le_of_lt hG (by decide))
      have hl := leftGroupsM_eq il hil _ hG'
      rw [preorderGo_step _ _ _ _ _ hc]
      simp only [preorderGoM, hc, and_self, ite_true, sub, show nlo ≤ nhi from hn, hl, Option.bind_some, Option.bind_eq_bind, add]
      have hG2 : G < 2 ^ 64 := Nat.lt_of_le_of_lt hG (by decide)
      have hmid : nlo + leftGroups (nhi - nlo) < 2 ^ 64 := by omega
      simp only [hmid, ite_true]
      by_cases hhi : hi ≤ nlo + leftGroups (nhi - nlo)
      · have hidx : idx + 1 < 2 ^ 64 := by omega
        simp only [hhi, ite_true, hidx, Option.bind_some, Option.bind_eq_bind]
        exact ih _ _ _ (by omega) (by omega) (by omega) (by omega)
      · have hidx : idx + leftGroups (nhi - nlo) < 2 ^ 64 := by omega
        simp only [hhi, ite_false, hidx, Option.bind_some, Option.bind_eq_bind]
        exact ih _ _ _ (by omega) (by omega) (by omega) (by omega)
    · rw [preorderGo_stop _ _ _ _ _ hc]
      simp [preorderGoM, hc]

/-- `preorder_index` of any `[lo, hi)` in the tree of `groups <= 2^54` leaves runs without an overflow or an
underflow, and returns the model's index. -/
theorem preorderIndexM_eq (il : Nat → Nat) (hil : ∀ x, 0 < x → x < 2 ^ 64 → IsIlog2 x (il x)) (groups lo hi : Nat)
    (hG : groups ≤ 2 ^ 54) : preorderIndexM il groups lo hi = some (preorderIndex groups lo hi) :=
  preorderGoM_eq il hil lo hi groups hG groups 0 groups 0 (by omega) (by omega) (by omega) (by omega)

/-- `preorder_index(..) * PARENT_LEN`: the outboard offset. For a node of the tree the index is below
`groups - 1`, so the product is below `2^60`. -/
theorem preorderOffset_lt (groups lo hi : Nat) (hG : groups ≤ 2 ^ 54) (hs : Sub 0 groups lo hi) (hp : hi - lo ≥ 2) :
    preorderIndex groups lo hi < groups - 1 ∧ 64 * preorderIndex groups lo hi + 64 ≤ 64 * (groups - 1) := by
  have h := preorderIndex_correct hs hp
  have hl := (List.getElem?_eq_some_iff.1 h).1
  rw [pre_length] at hl
  simp only [Nat.sub_zero] at hl
  omega


/-- `Layout::for_group_bytes`: `some log` for an accepted group buffer size, `none` for `InvalidGroupSize`. `tz`
is `usize::trailing_zeros`, and `is_power_of_two` is "nonzero and equal to `2 ^ log2`". The conversion
`Layout::new(len, chunks.trailing_zeros())` rejects a log above 20. -/
def forGroupBytesM (tz : Nat → Nat) (gb : Nat) : Option Nat :=
  if gb % 1024 ≠ 0 ∨ gb / 1024 = 0 ∨ gb / 1024 ≠ 2 ^ Nat.log2 (gb / 1024) then none
  else if tz (gb / 1024) > 20 then none else some (tz (gb / 1024))

/-- A group buffer size of `GROUP` bytes is accepted, on a 32-bit or a 64-bit `usize`, exactly when it is
`1024 << log` for a supported `log`, and then the layout's group length is `GROUP`, so the verifier's buffer
holds a whole group. -/
theorem forGroupBytesM_iff (tz : Nat → Nat) (htz : ∀ k, tz (2 ^ k) = k) (gb log : Nat) :
    forGroupBytesM tz gb = some log ↔ log ≤ 20 ∧ gb = groupLen log := by
  have hg : ∀ l, groupLen l = 1024 * 2 ^ l := by intro l; unfold groupLen; rw [Nat.shiftLeft_eq]
  unfold forGroupBytesM
  constructor
  · intro h
    by_cases hc : gb % 1024 ≠ 0 ∨ gb / 1024 = 0 ∨ gb / 1024 ≠ 2 ^ Nat.log2 (gb / 1024)
    · rw [if_pos hc] at h; cases h
    · rw [if_neg hc] at h
      have hc' : gb % 1024 = 0 ∧ gb / 1024 = 2 ^ Nat.log2 (gb / 1024) := by omega
      rw [hc'.2, htz] at h
      by_cases h20 : Nat.log2 (gb / 1024) > 20
      · simp [h20] at h
      · simp only [h20, ite_false, Option.some.injEq] at h
        subst h
        refine ⟨by omega, ?_⟩
        rw [hg, ← hc'.2]; omega
  · rintro ⟨h20, rfl⟩
    rw [hg]
    have e : 1024 * 2 ^ log / 1024 = 2 ^ log := by omega
    have e2 : 1024 * 2 ^ log % 1024 = 0 := by omega
    have hp := Nat.two_pow_pos log
    rw [e, e2, Nat.log2_two_pow, htz]
    simp [show ¬ log > 20 by omega, show 2 ^ log ≠ 0 by omega]

end Vinc.Machine

#audit_axioms Vinc.Machine.groupsM_eq
#audit_axioms Vinc.Machine.depthM_eq
#audit_axioms Vinc.Machine.outboardSizeM_eq
#audit_axioms Vinc.Machine.groupSizeM_eq
#audit_axioms Vinc.Machine.groupRangeM_eq
#audit_axioms Vinc.Machine.leftGroupsM_eq
#audit_axioms Vinc.Machine.preorderIndexM_eq
#audit_axioms Vinc.Machine.preorderOffset_lt
#audit_axioms Vinc.Machine.forGroupBytesM_iff

