import Pinc.DtnForward

/-!
# Slot-list lemmas for the forwarder model

The facts about `upd`, `slot`, `firstIdx`, `freeIdx` and `anyS` (and the weighted sum over a slot list) that the
theorems of `DtnForwardThm.lean`, `DtnForwardInv.lean` and `DtnForwardCons.lean` are built from. All are for every
list, so they hold at every table capacity.
-/

namespace Pinc.DtnForward

variable {α β : Type}

@[simp] theorem upd_length (l : List α) (i : Nat) (g : α → α) : (upd l i g).length = l.length := by
  induction l generalizing i with
  | nil => rfl
  | cons a r ih => cases i <;> simp [upd, ih]

@[simp] theorem slot_nil (i : Nat) : slot ([] : List (Option α)) i = none := by simp [slot]

theorem slot_cons_zero (o : Option α) (r : List (Option α)) : slot (o :: r) 0 = o := by simp [slot]

theorem slot_cons_succ (o : Option α) (r : List (Option α)) (i : Nat) : slot (o :: r) (i + 1) = slot r i := by
  simp [slot]

theorem slot_upd_same (l : List (Option α)) (i : Nat) (g : Option α → Option α) (h : i < l.length) :
    slot (upd l i g) i = g (slot l i) := by
  induction l generalizing i with
  | nil => simp at h
  | cons a r ih =>
    cases i with
    | zero => simp [upd, slot_cons_zero]
    | succ n => simp only [upd, slot_cons_succ]; exact ih n (by simpa using h)

theorem slot_upd_ne (l : List (Option α)) (i j : Nat) (g : Option α → Option α) (h : j ≠ i) :
    slot (upd l i g) j = slot l j := by
  induction l generalizing i j with
  | nil => simp [upd]
  | cons a r ih =>
    cases i <;> cases j <;> simp_all [upd, slot_cons_zero, slot_cons_succ]

theorem slot_upd_map (l : List (Option α)) (i j : Nat) (g : α → α) :
    slot (upd l i (Option.map g)) j = if j = i then (slot l j).map g else slot l j := by
  induction l generalizing i j with
  | nil => simp [upd]
  | cons a r ih =>
    cases i <;> cases j <;> simp_all [upd, slot_cons_zero, slot_cons_succ]

theorem slot_map (l : List (Option α)) (g : Option α → Option β) (hn : g none = none) (i : Nat) :
    slot (l.map g) i = g (slot l i) := by
  induction l generalizing i with
  | nil => simp [hn]
  | cons a r ih => cases i <;> simp [slot_cons_zero, slot_cons_succ, ih]

theorem slot_lt {l : List (Option α)} {i : Nat} {x : α} (h : slot l i = some x) : i < l.length := by
  refine Classical.byContradiction fun hc => ?_
  simp [slot, List.getElem?_eq_none (Nat.le_of_not_lt hc)] at h

/-- `firstIdx` is the index of a satisfying slot with none before it. -/
theorem firstIdx_some {p : α → Bool} {l : List (Option α)} {i : Nat} (h : firstIdx p l = some i) :
    ∃ x, slot l i = some x ∧ p x = true ∧ ∀ j < i, (slot l j).any p = false := by
  induction l generalizing i with
  | nil => simp [firstIdx] at h
  | cons o r ih =>
    simp only [firstIdx, List.findIdx?_cons] at h
    by_cases ho : (o.any p) = true
    · simp [ho] at h
      subst h
      cases o with
      | none => simp at ho
      | some x => exact ⟨x, by simp [slot_cons_zero], by simpa using ho, by simp⟩
    · simp [ho] at h
      obtain ⟨k, hk, rfl⟩ := h
      obtain ⟨x, hx, hp, hb⟩ := ih (by simpa [firstIdx] using hk)
      refine ⟨x, by simpa [slot_cons_succ] using hx, hp, ?_⟩
      intro j hj
      cases j with
      | zero => simpa [slot_cons_zero] using ho
      | succ j => simpa [slot_cons_succ] using hb j (by omega)

theorem firstIdx_none {p : α → Bool} {l : List (Option α)} (h : firstIdx p l = none) (j : Nat) :
    (slot l j).any p = false := by
  induction l generalizing j with
  | nil => simp
  | cons o r ih =>
    unfold firstIdx at h
    rw [List.findIdx?_cons] at h
    by_cases ho : (o.any p) = true
    · rw [if_pos ho] at h; simp at h
    · rw [if_neg ho] at h
      have h2 : firstIdx p r = none := Option.map_eq_none_iff.mp h
      cases j with
      | zero => simpa [slot_cons_zero] using ho
      | succ j => simpa [slot_cons_succ] using ih h2 j

theorem firstIdx_of_slot {p : α → Bool} {l : List (Option α)} {i : Nat} {x : α} (h : slot l i = some x)
    (hp : p x = true) : (firstIdx p l).isSome = true := by
  cases hf : firstIdx p l with
  | some _ => rfl
  | none => simpa [h, hp] using firstIdx_none hf i

theorem anyS_eq (p : α → Bool) (l : List (Option α)) : anyS p l = (firstIdx p l).isSome := by
  induction l with
  | nil => simp [anyS, firstIdx]
  | cons o r ih =>
    unfold anyS firstIdx at *
    rw [List.findIdx?_cons, List.any_cons]
    by_cases ho : (o.any p) = true
    · rw [if_pos ho]; simp [ho]
    · have ho' : o.any p = false := by simpa using ho
      rw [if_neg ho, ho', Bool.false_or, ih, Option.isSome_map]

theorem anyS_iff (p : α → Bool) (l : List (Option α)) : anyS p l = true ↔ ∃ i x, slot l i = some x ∧ p x = true := by
  rw [anyS_eq]
  constructor
  · intro h
    cases hf : firstIdx p l with
    | none => simp [hf] at h
    | some i => obtain ⟨x, hx, hp, _⟩ := firstIdx_some hf; exact ⟨i, x, hx, hp⟩
  · rintro ⟨i, x, hx, hp⟩; exact firstIdx_of_slot hx hp

theorem freeIdx_some {l : List (Option α)} {i : Nat} (h : freeIdx l = some i) : slot l i = none ∧ i < l.length := by
  induction l generalizing i with
  | nil => simp [freeIdx] at h
  | cons o r ih =>
    simp only [freeIdx, List.findIdx?_cons] at h
    by_cases ho : o.isNone = true
    · simp [ho] at h
      subst h
      cases o <;> simp_all [slot_cons_zero]
    · simp [ho] at h
      obtain ⟨k, hk, rfl⟩ := h
      obtain ⟨a, b⟩ := ih (by simpa [freeIdx] using hk)
      exact ⟨by simpa [slot_cons_succ] using a, by simpa using b⟩

theorem freeIdx_isSome {l : List (Option α)} {i : Nat} (hl : i < l.length) (h : slot l i = none) :
    (freeIdx l).isSome = true := by
  induction l generalizing i with
  | nil => simp at hl
  | cons o r ih =>
    simp only [freeIdx, List.findIdx?_cons]
    by_cases ho : o.isNone = true
    · simp [ho]
    · cases i with
      | zero => simp [slot_cons_zero] at h; simp [h] at ho
      | succ n => simpa [ho, freeIdx] using ih (i := n) (by simpa using hl) (by simpa [slot_cons_succ] using h)

/-- The sum of a weight over the occupied slots. -/
def wsum (w : α → Nat) (l : List (Option α)) : Nat := (l.map fun o => o.elim 0 w).sum

@[simp] theorem wsum_nil (w : α → Nat) : wsum w ([] : List (Option α)) = 0 := rfl

theorem wsum_cons (w : α → Nat) (o : Option α) (r : List (Option α)) :
    wsum w (o :: r) = o.elim 0 w + wsum w r := by simp [wsum]

/-- Replace an occupied slot by an occupied slot. -/
theorem wsum_upd_some (w : α → Nat) (l : List (Option α)) (i : Nat) (g : α → α) {x : α}
    (h : slot l i = some x) : wsum w (upd l i (Option.map g)) + w x = wsum w l + w (g x) := by
  induction l generalizing i with
  | nil => simp at h
  | cons o r ih =>
    cases i with
    | zero =>
      simp [slot_cons_zero] at h; subst h
      simp [upd, wsum_cons]; omega
    | succ n =>
      simp [slot_cons_succ] at h
      have := ih n (by simpa [slot_cons_succ] using h)
      simp only [upd, wsum_cons]; omega

/-- Fill a free slot. -/
theorem wsum_upd_fill (w : α → Nat) (l : List (Option α)) (i : Nat) (y : α) (h : slot l i = none)
    (hl : i < l.length) : wsum w (upd l i fun _ => some y) = wsum w l + w y := by
  induction l generalizing i with
  | nil => simp at hl
  | cons o r ih =>
    cases i with
    | zero =>
      simp [slot_cons_zero] at h; subst h
      simp [upd, wsum_cons]; omega
    | succ n =>
      have := ih n (by simpa [slot_cons_succ] using h) (by simpa using hl)
      simp only [upd, wsum_cons]; omega

end Pinc.DtnForward
