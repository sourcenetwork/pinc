import Vinc.Axioms

/-!
# `slice::partition_point`

The Rust standard library computes `partition_point` as a branchless binary search over `[base, base + size)`.
`ppGo` is that loop. For a slice partitioned by the predicate (a prefix where it holds, then a suffix where it
does not) the result is the index of the first element where it fails; `partitionPoint_eq` proves it.
-/

namespace Vinc.PP

variable {α : Type} [Inhabited α]

theorem get_bang (l : List α) (i : Nat) (h : i < l.length) : l[i]! = l[i] := by
  simp [getElem!_pos, h]

/-- The binary search loop: `size` candidates starting at `base`. -/
def ppGo (p : α → Bool) (l : List α) (base size : Nat) : Nat :=
  if size > 1 then
    let half := size / 2
    let mid := base + half
    ppGo p l (if p l[mid]! then mid else base) (size - half)
  else if p l[base]! then base + 1 else base
termination_by size
decreasing_by omega

/-- `slice::partition_point`. -/
def partitionPoint (p : α → Bool) (l : List α) : Nat :=
  if l.length = 0 then 0 else ppGo p l 0 l.length

/-- `k` is the index of the first element failing `p`, or the length when none does. -/
structure FirstFalse (p : α → Bool) (l : List α) (k : Nat) : Prop where
  le : k ≤ l.length
  pre : ∀ i (h : i < l.length), i < k → p l[i] = true
  suf : ∀ i (h : i < l.length), k ≤ i → p l[i] = false

/-- The slice is partitioned: `p` holds on a prefix. -/
def Partitioned (p : α → Bool) (l : List α) : Prop :=
  ∀ i j (hi : i < l.length) (hj : j < l.length), i < j → p l[j] = true → p l[i] = true

theorem ppGo_eq (p : α → Bool) (l : List α) (k : Nat) (hk : FirstFalse p l k) :
    ∀ size base, 1 ≤ size → base + size ≤ l.length → base ≤ k → k ≤ base + size →
      ppGo p l base size = k := by
  intro size
  induction size using Nat.strongRecOn with
  | _ size ih =>
    intro base h1 hlen hb hk2
    rw [ppGo]
    by_cases hs : size > 1
    · simp only [hs, ite_true]
      have hmid : base + size / 2 < l.length := by omega
      rw [get_bang l _ hmid]
      cases hp : p l[base + size / 2]
      · simp only [Bool.false_eq_true, ite_false]
        have : k ≤ base + size / 2 := by
          by_cases hc : base + size / 2 < k
          · have := hk.pre _ hmid hc; simp_all
          · omega
        exact ih (size - size / 2) (by omega) _ (by omega) (by omega) (by omega) (by omega)
      · simp only [ite_true]
        have : base + size / 2 < k := by
          by_cases hc : k ≤ base + size / 2
          · have := hk.suf _ hmid hc; simp_all
          · omega
        exact ih (size - size / 2) (by omega) _ (by omega) (by omega) (by omega) (by omega)
    · simp only [hs, ite_false]
      have hbl : base < l.length := by omega
      rw [get_bang l _ hbl]
      cases hp : p l[base]
      · simp only [Bool.false_eq_true, ite_false]
        have : k ≤ base := by
          by_cases hc : base < k
          · have := hk.pre _ hbl hc; simp_all
          · omega
        omega
      · simp only [ite_true]
        have : base < k := by
          by_cases hc : k ≤ base
          · have := hk.suf _ hbl hc; simp_all
          · omega
        omega

/-- On a partitioned slice, `partition_point` is the first index where the predicate fails. -/
theorem partitionPoint_eq (p : α → Bool) (l : List α) (k : Nat) (hk : FirstFalse p l k) :
    partitionPoint p l = k := by
  unfold partitionPoint
  by_cases h0 : l.length = 0
  · have := hk.le; simp [h0]; omega
  · simp only [h0, ite_false]
    exact ppGo_eq p l k hk l.length 0 (by omega) (by omega) (by omega) (by have := hk.le; omega)

omit [Inhabited α] in
/-- A partitioned slice has a first failing index. -/
theorem exists_firstFalse (p : α → Bool) (l : List α) (h : Partitioned p l) : ∃ k, FirstFalse p l k := by
  induction l with
  | nil => exact ⟨0, ⟨by simp, by simp, by simp⟩⟩
  | cons a t ih =>
    by_cases ha : p a = true
    · have ht : Partitioned p t := by
        intro i j hi hj hij hp
        have := h (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega) (by simpa using hp)
        simpa using this
      obtain ⟨k, hk⟩ := ih ht
      refine ⟨k + 1, ⟨by simp [hk.le], ?_, ?_⟩⟩
      · intro i hi hik
        cases i with
        | zero => simpa using ha
        | succ i => simpa using hk.pre i (by simp at hi; omega) (by omega)
      · intro i hi hik
        cases i with
        | zero => omega
        | succ i => simpa using hk.suf i (by simp at hi; omega) (by omega)
    · refine ⟨0, ⟨by simp, by intro i _ h0; omega, ?_⟩⟩
      intro i hi _
      cases i with
      | zero => simpa using ha
      | succ i =>
        by_cases hp : p (a :: t)[i + 1] = true
        · have := h 0 (i + 1) (by simp) hi (by omega) hp
          simp_all
        · simpa using hp

end Vinc.PP

#audit_axioms Vinc.PP.partitionPoint_eq
