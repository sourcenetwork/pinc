import Pinc.Axioms
import Pinc.CoreHeap

/-!
# The deadline heap, part 1: the invariant and its helpers

What the model proves about `DeadlineHeap`, for any capacity `n`, any deadlines (the largest `u64` included) and any
run of calls, is in four files, each importing the one before: the invariant (this file), the sifts (`CoreHeapSift`),
`set` (`CoreHeapSet`) and the root and the pops (`CoreHeapPop`).

- `Le`, `Lt`: the order of the pairs `(deadline, id)`, the lower id first on a tie; what `put` changes.
- `Inv`: the position index and the heap are inverse on the ids present (`pa`, `pb`), every id in the heap is below
  `n`, the heap order holds (each element is not earlier than its parent, the lower id first on a tie: `Ord`), and so
  an id is held at most once and the heap never holds more than `n` items (`len_le`); the empty heap has it
  (`init_inv`).
- `HS`: a heap with one hole, through which the sifts are proved, as the code's loops are; `put_fin`: putting the
  element on its way into the hole closes it.
-/

namespace Pinc.CoreHeap

/-! ## The order of the pairs -/

def Le (a b : Nat × Nat) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)
def Lt (a b : Nat × Nat) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

theorem lexLe_iff (a b : Nat × Nat) : lexLe a b = true ↔ Le a b := by simp [lexLe, Le]
theorem lexLt_iff (a b : Nat × Nat) : lexLt a b = true ↔ Lt a b := by simp [lexLt, Lt]
theorem Le_trans {a b c : Nat × Nat} (h1 : Le a b) (h2 : Le b c) : Le a c := by unfold Le at *; omega
theorem Le_of_Lt {a b : Nat × Nat} (h : Lt a b) : Le a b := by unfold Le Lt at *; omega
theorem not_Le {a b : Nat × Nat} : ¬ Le a b ↔ Lt b a := by unfold Le Lt; omega
theorem not_Lt {a b : Nat × Nat} : ¬ Lt a b ↔ Le b a := by unfold Le Lt; omega
theorem Le_refl (a : Nat × Nat) : Le a a := by unfold Le; omega
theorem Lt_Le_trans {a b c : Nat × Nat} (h1 : Lt a b) (h2 : Le b c) : Lt a c := by unfold Le Lt at *; omega
theorem Le_of_eq {a b : Nat × Nat} (h : a = b) : Le a b := h ▸ Le_refl a

/-! ## Facts about `put` -/

theorem heap_put (s : S) (i id j : Nat) : (put s i id).heap j = if j = i then id else s.heap j := by
  simp [put, upd]
theorem pos_put (s : S) (i id a : Nat) : (put s i id).pos a = if a = id then some i else s.pos a := by
  simp [put, upd]
@[simp] theorem len_put (s : S) (i id : Nat) : (put s i id).len = s.len := rfl
@[simp] theorem n_put (s : S) (i id : Nat) : (put s i id).n = s.n := rfl
@[simp] theorem dl_put (s : S) (i id : Nat) : (put s i id).dl = s.dl := rfl

theorem key_put_eq (s : S) (i id : Nat) : key (put s i id) i = (s.dl id, id) := by
  simp [key, heap_put]
theorem key_put_ne (s : S) (i id j : Nat) (h : j ≠ i) : key (put s i id) j = key s j := by
  simp [key, heap_put, h]

/-! ## The invariant -/

/-- The heap order: each element is not earlier than its parent. -/
def Ord (s : S) : Prop := ∀ j, 0 < j → j < s.len → Le (key s ((j - 1) / 2)) (key s j)

/-- The position index and the heap are inverse on the ids present. -/
structure PosInv (s : S) : Prop where
  pa : ∀ j, j < s.len → s.pos (s.heap j) = some j
  pb : ∀ a p, s.pos a = some p → p < s.len ∧ s.heap p = a
  hlt : ∀ j, j < s.len → s.heap j < s.n

structure Inv (s : S) : Prop where
  pos : PosInv s
  ord : Ord s

theorem init_inv (n : Nat) : Inv (init n) :=
  ⟨⟨fun j hj => absurd hj (by simp [init]), fun a p h => by simp [init] at h,
    fun j hj => absurd hj (by simp [init])⟩, fun j _ hj => absurd hj (by simp [init])⟩

/-- The heap never holds more than `n` items, and holds each id once: a list of distinct numbers below `n`. -/
theorem len_le (s : S) (h : PosInv s) : s.len ≤ s.n := by
  have hnd : ((List.range s.len).map s.heap).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := s.len))
    intro x y hx hy hxy hh
    have hx := List.mem_range.mp hx
    have hy := List.mem_range.mp hy
    have h1 := h.pa x hx
    have h2 := h.pa y hy
    rw [hh] at h1
    rw [h1] at h2
    exact hxy (Option.some.inj h2)
  have hsub : ((List.range s.len).map s.heap) ⊆ List.range s.n := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    exact List.mem_range.mpr (h.hlt j (List.mem_range.mp hj))
  have := hnd.length_le_of_subset hsub
  simpa using this

/-! ## The heap with one hole

The sifts of the code move one element along a path with a hole (the cell the element left); the hole is where the
element `x` will be put at the end. `HS s i x`: the heap is well formed except at the hole `i`, `x` is the element on its
way, and the order holds on every edge that does not touch the hole, and from the hole's parent to the hole's
children. -/

structure HS (s : S) (i x : Nat) : Prop where
  i_lt : i < s.len
  x_lt : x < s.n
  hlt : ∀ j, j < s.len → j ≠ i → s.heap j < s.n
  pa : ∀ j, j < s.len → j ≠ i → s.pos (s.heap j) = some j
  pb : ∀ a p, s.pos a = some p → a ≠ x → p < s.len ∧ p ≠ i ∧ s.heap p = a
  pc : ∀ j, j < s.len → j ≠ i → s.heap j ≠ x
  px : ∃ q, s.pos x = some q
  ord : ∀ j, 0 < j → j < s.len → j ≠ i → (j - 1) / 2 ≠ i → Le (key s ((j - 1) / 2)) (key s j)
  gp : 0 < i → ∀ c, 0 < c → c < s.len → (c - 1) / 2 = i → Le (key s ((i - 1) / 2)) (key s c)

/-- What a loop leaves behind. -/
structure Fin' (r s : S) : Prop where
  pos : PosInv r
  ord : Ord r
  len : r.len = s.len
  n : r.n = s.n
  dl : r.dl = s.dl
  some : ∀ a, (r.pos a).isSome = (s.pos a).isSome

/-- Two states with the same size, capacity, deadlines and set of ids present. -/
structure Same (r s : S) : Prop where
  len : r.len = s.len
  n : r.n = s.n
  dl : r.dl = s.dl
  some : ∀ a, (r.pos a).isSome = (s.pos a).isSome

theorem Fin'.of_same {r s t : S} (h1 : Fin' r s) (h2 : Same s t) : Fin' r t :=
  ⟨h1.pos, h1.ord, h1.len.trans h2.len, h1.n.trans h2.n, h1.dl.trans h2.dl, fun a => (h1.some a).trans (h2.some a)⟩

theorem put_same (s : S) (i y : Nat) (h : (s.pos y).isSome = true) : Same (put s i y) s :=
  ⟨rfl, rfl, rfl, fun a => by
    rw [pos_put]
    by_cases ha : a = y
    · subst ha; simp [h]
    · simp [ha]⟩

theorem hs_of_inv (s : S) (h : Inv s) (i : Nat) (hi : i < s.len) : HS s i (s.heap i) := by
  have hp := h.pos
  refine ⟨hi, hp.hlt i hi, fun j hj _ => hp.hlt j hj, fun j hj _ => hp.pa j hj, ?_, ?_, ⟨i, hp.pa i hi⟩,
    fun j hj hj0 _ _ => h.ord j hj hj0, ?_⟩
  · intro a p hpa han
    obtain ⟨h1, h2⟩ := hp.pb a p hpa
    refine ⟨h1, ?_, h2⟩
    rintro rfl
    exact han h2.symm
  · intro j hj hji hjx
    have h1 := hp.pa j hj
    rw [hjx, hp.pa i hi] at h1
    exact hji (Option.some.inj h1).symm
  · intro hi0 c hc0 hc hci
    have h1 := h.ord i hi0 hi
    have h2 := h.ord c hc0 hc
    rw [hci] at h2
    exact Le_trans h1 h2

/-- Putting `x` into the hole closes it, given the order at the hole. -/
theorem put_fin (s : S) (i x : Nat) (k : Nat × Nat) (hs : HS s i x) (hk : k = (s.dl x, x))
    (hup : 0 < i → Le (key s ((i - 1) / 2)) k)
    (hdn : ∀ c, 0 < c → c < s.len → (c - 1) / 2 = i → Le k (key s c)) : Fin' (put s i x) s := by
  subst hk
  refine ⟨⟨?_, ?_, ?_⟩, ?_, rfl, rfl, rfl, ?_⟩
  · intro j hj
    rw [heap_put]
    by_cases hji : j = i
    · subst hji; simp [pos_put]
    · simp only [hji, if_false]
      have h1 := hs.pa j hj hji
      have h2 := hs.pc j hj hji
      rw [pos_put, if_neg h2]; exact h1
  · intro a p hpa
    rw [pos_put] at hpa
    by_cases hax : a = x
    · rw [if_pos hax] at hpa
      have := Option.some.inj hpa
      subst this
      refine ⟨hs.i_lt, ?_⟩
      simp [heap_put, hax]
    · rw [if_neg hax] at hpa
      obtain ⟨h1, h2, h3⟩ := hs.pb a p hpa hax
      refine ⟨h1, ?_⟩
      simp [heap_put, h2, h3]
  · intro j hj
    rw [heap_put]
    by_cases hji : j = i
    · simp [hji, hs.x_lt]
    · simp only [hji, if_false]; exact hs.hlt j hj hji
  · intro j hj0 hj
    simp only [len_put] at hj
    by_cases hji : j = i
    · subst hji
      rw [key_put_eq, key_put_ne _ _ _ _ (by omega)]
      exact hup hj0
    · rw [key_put_ne _ _ _ _ hji]
      by_cases hpi : (j - 1) / 2 = i
      · rw [hpi, key_put_eq]
        have := hdn j hj0 hj hpi
        exact this
      · rw [key_put_ne _ _ _ _ hpi]
        exact hs.ord j hj0 hj hji hpi
  · intro a
    rw [pos_put]
    by_cases hax : a = x
    · subst hax; obtain ⟨q, hq⟩ := hs.px; simp [hq]
    · simp [hax]

#audit_axioms Pinc.CoreHeap.init_inv
#audit_axioms Pinc.CoreHeap.len_le

end Pinc.CoreHeap
