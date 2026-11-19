import Pinc.ValuesPlanMain

/-!
# The size of a range-proof frame (`server.rs proof_k`)

`proof_k(ln)` picks the groups per proof frame: the largest of 16, 8, 4, 2, 1 whose proof bound `cost(k)` fits
the 1100 proof bytes `WT_PMAX`, `None` (the tree is too deep, no write-through) unless that is at least 4.

* `protoK_deep_iff`: a value gets no write-through proofs exactly when it is over `2^30` bytes (1 GiB), i.e. when
  its tree is more than 16 levels deep.
* `protoK_pow`: the frame size is 16, 8 or 4 groups, a power of two.
* `parentsIn_aligned`: the parents of any group range inside an aligned block of `k = 2^m` groups number at most
  `(k - 1) + (height - m)`: the parents inside the block's subtree plus one per level above it.
* `proof_bytes_le`: so the proof of a frame is at most `cost(k) - 8 < 1100` bytes, and with its 30-byte head
  at most `PROOF_BODY_MAX = 1130`: `build_proof` never runs out of body.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesPlan
open Pinc.Layout Pinc.Encode

/-- `x.checked_ilog2().map_or(0, |b| b + 1)`. -/
def bits (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

/-- `WT_PMAX`. -/
abbrev PMAX : Nat := 1100
/-- `WT_MIN_K`, `WT_MAX_K`, `WT_MAXF`. -/
abbrev MINK : Nat := 4
abbrev MAXK : Nat := 16
abbrev MAXF : Nat := 48

/-- The bound on the proof bytes of a frame of `k` aligned groups in a tree `dep` levels deep. -/
def cost (dep k : Nat) : Nat := 64 * (k - 1) + 64 * (dep - bits (k - 1)) + 8

/-- The halving loop. -/
def kLoop (dep : Nat) (k : Nat) : Nat :=
  if 1 < k ∧ PMAX < cost dep k then kLoop dep (k / 2) else k
termination_by k
decreasing_by omega

/-- The depth of the tree of a value of `ln` bytes. -/
def depOf (ln : Nat) : Nat := bits ((ln + G - 1) / G - 1)

/-- `proof_k`. -/
def protoK (ln : Nat) : Option Nat :=
  let k := kLoop (depOf ln) MAXK
  if cost (depOf ln) k ≤ PMAX ∧ MINK ≤ k then some k else none

theorem kLoop_stop (dep k : Nat) (h : ¬ (1 < k ∧ PMAX < cost dep k)) : kLoop dep k = k := by
  rw [kLoop]; simp [h]

theorem kLoop_step (dep k : Nat) (h : 1 < k ∧ PMAX < cost dep k) : kLoop dep k = kLoop dep (k / 2) := by
  rw [kLoop]; simp [h]

theorem bits_pow (m : Nat) : bits (2 ^ m - 1) = m := by
  unfold bits
  cases m with
  | zero => simp
  | succ m =>
    have h1 : 0 < 2 ^ m := Nat.two_pow_pos m
    have h2 : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ ..
    have : 2 ^ (m + 1) - 1 ≠ 0 := by omega
    simp only [this, ite_false]
    have : Nat.log2 (2 ^ (m + 1) - 1) = m := by
      rw [Nat.log2_eq_iff (by omega)]
      constructor <;> omega
    omega

theorem bits_ge (x n : Nat) : n ≤ bits x ↔ (n = 0 ∨ 2 ^ (n - 1) ≤ x) := by
  unfold bits
  by_cases hx : x = 0
  · subst hx; simp
  · simp only [hx, ite_false]
    by_cases hn : n = 0
    · subst hn; simp
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have := Nat.le_log2 (n := x) (k := n') hx
      simp only [Nat.add_sub_cancel]
      constructor
      · intro h; exact Or.inr (this.1 (by omega))
      · intro h; rcases h with h | h
        · omega
        · have := this.2 h; omega

/-- The frame size is the largest of 16, 8, 4, 2, 1 whose bound fits. -/
theorem kLoop_pow (dep : Nat) : ∀ k, (∃ m, k = 2 ^ m) → ∃ m, kLoop dep k = 2 ^ m := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro ⟨m, hm⟩
    by_cases h : 1 < k ∧ PMAX < cost dep k
    · rw [kLoop_step dep k h]
      cases m with
      | zero => simp at hm; omega
      | succ m => exact ih (k / 2) (by omega) ⟨m, by rw [hm, Nat.pow_succ]; omega⟩
    · rw [kLoop_stop dep k h]; exact ⟨m, hm⟩

theorem kLoop_fits (dep : Nat) : ∀ k, 1 ≤ k → (kLoop dep k = 1 ∨ cost dep (kLoop dep k) ≤ PMAX) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    by_cases h : 1 < k ∧ PMAX < cost dep k
    · rw [kLoop_step dep k h]; exact ih (k / 2) (by omega) (by omega)
    · rw [kLoop_stop dep k h]
      by_cases h1 : 1 < k
      · right; omega
      · left; omega

theorem kLoop_le (dep : Nat) : ∀ k, kLoop dep k ≤ k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases h : 1 < k ∧ PMAX < cost dep k
    · rw [kLoop_step dep k h]; have := ih (k / 2) (by omega); omega
    · rw [kLoop_stop dep k h]; exact Nat.le_refl _

/-- The k is 16, 8 or 4, or there are no proofs. -/
theorem protoK_pow (ln k : Nat) (h : protoK ln = some k) :
    ∃ m, k = 2 ^ m ∧ MINK ≤ k ∧ k ≤ MAXK ∧ cost (depOf ln) k ≤ PMAX := by
  unfold protoK at h
  simp only [] at h
  by_cases hc : cost (depOf ln) (kLoop (depOf ln) MAXK) ≤ PMAX ∧ MINK ≤ kLoop (depOf ln) MAXK
  · simp only [hc, and_self, ite_true, Option.some.injEq] at h
    subst h
    obtain ⟨m, hm⟩ := kLoop_pow (depOf ln) MAXK ⟨4, by decide⟩
    exact ⟨m, hm, hc.2, kLoop_le _ _, hc.1⟩
  · simp [hc] at h

theorem bits3 : bits 3 = 2 := bits_pow 2
theorem bits7 : bits 7 = 3 := bits_pow 3
theorem bits15 : bits 15 = 4 := bits_pow 4
theorem bits1 : bits 1 = 1 := by unfold bits; simp
theorem bits0 : bits 0 = 0 := by unfold bits; simp

/-- Over 16 levels no frame of 4 groups fits: the loop ends below 4. -/
theorem kLoop_deep (dep : Nat) (h : 17 ≤ dep) : kLoop dep MAXK ≤ 2 := by
  have c16 : PMAX < cost dep 16 := by unfold cost PMAX; simp only [show 16 - 1 = 15 by rfl, bits15]; omega
  have c8 : PMAX < cost dep 8 := by unfold cost PMAX; simp only [show 8 - 1 = 7 by rfl, bits7]; omega
  have c4 : PMAX < cost dep 4 := by unfold cost PMAX; simp only [show 4 - 1 = 3 by rfl, bits3]; omega
  unfold MAXK
  rw [kLoop_step dep 16 ⟨by decide, c16⟩, show 16 / 2 = 8 from rfl, kLoop_step dep 8 ⟨by decide, c8⟩,
    show 8 / 2 = 4 from rfl, kLoop_step dep 4 ⟨by decide, c4⟩, show 4 / 2 = 2 from rfl]
  by_cases h2 : 1 < 2 ∧ PMAX < cost dep 2
  · rw [kLoop_step dep 2 h2, show 2 / 2 = 1 from rfl, kLoop_stop dep 1 (by omega)]; omega
  · rw [kLoop_stop dep 2 h2]; exact Nat.le_refl _

/-- Up to 16 levels a frame of at least 4 groups fits. -/
theorem kLoop_shallow (dep : Nat) (h : dep ≤ 16) : 4 ≤ kLoop dep MAXK ∧ cost dep (kLoop dep MAXK) ≤ PMAX := by
  have c4 : ¬ PMAX < cost dep 4 := by unfold cost PMAX; simp only [show 4 - 1 = 3 by rfl, bits3]; omega
  unfold MAXK
  by_cases c16 : PMAX < cost dep 16
  · rw [kLoop_step dep 16 ⟨by decide, c16⟩, show 16 / 2 = 8 from rfl]
    by_cases c8 : PMAX < cost dep 8
    · rw [kLoop_step dep 8 ⟨by decide, c8⟩, show 8 / 2 = 4 from rfl, kLoop_stop dep 4 (by omega)]
      exact ⟨Nat.le_refl _, by omega⟩
    · rw [kLoop_stop dep 8 (by omega)]; exact ⟨by decide, by omega⟩
  · rw [kLoop_stop dep 16 (by omega)]; exact ⟨by decide, by omega⟩

/-- No proofs for a value whose tree is more than 16 levels deep, exactly. -/
theorem protoK_deep_iff (ln : Nat) (h0 : 0 < ln) : protoK ln = none ↔ 2 ^ 30 < ln := by
  have hGe : G = 16384 := G_eq
  have hdep : 17 ≤ depOf ln ↔ 2 ^ 30 < ln := by
    unfold depOf
    rw [bits_ge]
    simp only [show (17 : Nat) ≠ 0 by omega, false_or, show 17 - 1 = 16 by rfl]
    rw [hGe]
    omega
  rw [← hdep]
  unfold protoK
  simp only []
  by_cases hd : 17 ≤ depOf ln
  · have := kLoop_deep _ hd
    have h4 : ¬ (cost (depOf ln) (kLoop (depOf ln) MAXK) ≤ PMAX ∧ MINK ≤ kLoop (depOf ln) MAXK) := by
      intro h; unfold MINK at h; omega
    simp [h4, hd]
  · obtain ⟨a, b⟩ := kLoop_shallow (depOf ln) (by omega)
    simp [MINK, a, b, hd]

/-- `k` divides the left subtree size of a node bigger than `k` (a power of two). -/
theorem dvd_left (m : Nat) (s : Nat) (h : 2 ^ m < s) : 2 ^ m ∣ leftGroups s ∧ m + 1 ≤ hh s := by
  have h2 : 2 ≤ s := by have := Nat.two_pow_pos m; omega
  have hj : m ≤ Nat.log2 (s - 1) := (Nat.le_log2 (by omega)).2 (by omega)
  constructor
  · simp only [leftGroups, h2, ite_true]
    exact Nat.pow_dvd_pow 2 hj
  · have : hh s = Nat.log2 (s - 1) + 1 := by simp [hh]; omega
    omega

/-- The parents of a group range inside an aligned block of `2^m` groups: the block's own, plus one per level above. -/
theorem parentsIn_aligned (m A a b : Nat) (hA : 2 ^ m ∣ A) (hAa : A ≤ a) (hbA : b ≤ A + 2 ^ m) :
    ∀ (n lo hi : Nat), hi - lo = n → (2 ^ m < hi - lo → 2 ^ m ∣ lo) →
      parentsIn a b lo hi ≤ (2 ^ m - 1) + (hh (hi - lo) - m) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi hn hlo
    have hpos := Nat.two_pow_pos m
    by_cases h : hi - lo < 2 ∨ b ≤ lo ∨ hi ≤ a
    · rw [parentsIn_stop _ _ _ _ h]; omega
    · have hle := parentsIn_le a b _ lo hi rfl
      by_cases hc : a ≤ lo ∧ hi ≤ b
      · rw [parentsIn_full _ _ _ _ h hc]; omega
      · have h2 : hi - lo ≥ 2 := by omega
        by_cases hsk : hi - lo ≤ 2 ^ m
        · omega
        · have hk := dvd_left m (hi - lo) (by omega)
          have h1 := leftGroups_pos (hi - lo) h2
          have h3 := leftGroups_lt (hi - lo) h2
          have hlo := hlo (by omega)
          have hmid : 2 ^ m ∣ lo + leftGroups (hi - lo) := Nat.dvd_add hlo hk.1
          have hl := hh_leftGroups (hi - lo) h2
          have hr := hh_right (hi - lo) h2
          rw [parentsIn_rec _ _ _ _ h hc]
          by_cases ha : a < lo + leftGroups (hi - lo)
          · -- the block is inside the left subtree
            obtain ⟨x, hx⟩ := hA
            obtain ⟨y, hy⟩ := hmid
            have hxy : x < y := by
              have : 2 ^ m * x < 2 ^ m * y := by omega
              exact Nat.lt_of_mul_lt_mul_left this
            have : 2 ^ m * (x + 1) ≤ 2 ^ m * y := Nat.mul_le_mul_left _ hxy
            rw [Nat.mul_add, Nat.mul_one] at this
            rw [parentsIn_stop a b (lo + leftGroups (hi - lo)) hi (Or.inr (Or.inl (by omega)))]
            have iL := ih (leftGroups (hi - lo)) (by omega) lo (lo + leftGroups (hi - lo)) (by omega) (fun _ => hlo)
            rw [show lo + leftGroups (hi - lo) - lo = leftGroups (hi - lo) by omega] at iL
            omega
          · rw [parentsIn_stop a b lo (lo + leftGroups (hi - lo)) (Or.inr (Or.inr (by omega)))]
            have iR := ih (hi - (lo + leftGroups (hi - lo))) (by omega) (lo + leftGroups (hi - lo)) hi rfl (fun _ => hmid)
            rw [show hi - (lo + leftGroups (hi - lo)) = hi - lo - leftGroups (hi - lo) by omega] at iR
            omega

theorem hh_eq_bits (n : Nat) : hh n = bits (n - 1) := by
  unfold hh bits
  by_cases h : n ≤ 1
  · have : n - 1 = 0 := by omega
    simp [h, this]
  · have : n - 1 ≠ 0 := by omega
    simp [h, this]

/-- A frame of an aligned block fits the proof bound: its pairs are at most `cost(k) - 8` bytes. -/
theorem proof_bytes_le (ln k m A a b : Nat) (hk : k = 2 ^ m) (hA : k ∣ A) (hAa : A ≤ a) (hbA : b ≤ A + k) :
    parentsIn a b 0 ((ln + G - 1) / G) * 64 + 8 ≤ cost (depOf ln) k := by
  subst hk
  have := parentsIn_aligned m A a b hA hAa hbA ((ln + G - 1) / G) 0 ((ln + G - 1) / G) (Nat.sub_zero _)
    (fun _ => Nat.dvd_zero _)
  rw [Nat.sub_zero] at this
  unfold cost depOf
  rw [bits_pow, ← hh_eq_bits]
  omega

end Pinc.ValuesPlan

#audit_axioms Pinc.ValuesPlan.protoK_deep_iff
#audit_axioms Pinc.ValuesPlan.protoK_pow
#audit_axioms Pinc.ValuesPlan.parentsIn_aligned
#audit_axioms Pinc.ValuesPlan.proof_bytes_le
