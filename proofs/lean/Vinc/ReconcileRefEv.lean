import Vinc.ReconcileRefMerge

/-!
# Reconcile refinement, part 2i: what the merge events say

For two strictly ascending lists the events of `mergeEv` are: `both k` exactly for the items of the peer's list that
we also hold (with `k` their position in the peer's list), `mine x` for our items the peer lacks and `theirs x` for the
peer's items we lack, each in order.
-/

namespace Vinc.Reconcile

def Cmp.bothIdx : Cmp → Option Nat
  | .both k => some k
  | _ => none

def Cmp.mineItem : Cmp → Option Item
  | .mine x => some x
  | _ => none

def Cmp.theirsItem : Cmp → Option Item
  | .theirs x => some x
  | _ => none

abbrev Asc (l : List Item) : Prop := l.Pairwise (fun x y => lexLt x y = true)

/-- The positions (from `k`) of the items of `xs` that `ms` also holds. -/
def idxOf (ms : List Item) : List Item → Nat → List Nat
  | [], _ => []
  | x :: xs, k => if ms.contains x then k :: idxOf ms xs (k + 1) else idxOf ms xs (k + 1)

theorem idxOf_congr (ms ms' : List Item) : ∀ (xs : List Item) (k : Nat),
    (∀ x ∈ xs, ms'.contains x = ms.contains x) → idxOf ms' xs k = idxOf ms xs k
  | [], _, _ => rfl
  | x :: xs, k, h => by
    simp only [idxOf, h x (List.mem_cons_self ..)]
    rw [idxOf_congr ms ms' xs (k + 1) (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem filter_congr' (p q : Item → Bool) : ∀ (l : List Item), (∀ x ∈ l, p x = q x) → l.filter p = l.filter q
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.filter_cons, h x (List.mem_cons_self ..)]
    rw [filter_congr' p q l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem contains_cons_ne (m x : Item) (ms : List Item) (h : x ≠ m) : (m :: ms).contains x = ms.contains x := by
  simp [h]

theorem contains_gt (m x : Item) (ms : List Item) (hx : lexLt x m = true) (hs : ∀ y ∈ ms, lexLt m y = true) :
    (m :: ms).contains x = false := by
  have h1 : x ≠ m := lexLt_ne _ _ hx
  rw [contains_cons_ne m x ms h1]
  rw [List.contains_eq_any_beq]
  simp only [List.any_eq_false]
  intro y hy
  have : lexLt x y = true := lexLt_trans _ _ _ hx (hs y hy)
  have : x ≠ y := lexLt_ne _ _ this
  simpa using this

theorem mergeEv_spec : ∀ (n : Nat) (ms xs : List Item) (k : Nat), ms.length + xs.length ≤ n → Asc ms → Asc xs →
    ((mergeEv ms xs k).filterMap Cmp.bothIdx = idxOf ms xs k) ∧
    ((mergeEv ms xs k).filterMap Cmp.mineItem = ms.filter (fun x => !xs.contains x)) ∧
    ((mergeEv ms xs k).filterMap Cmp.theirsItem = xs.filter (fun x => !ms.contains x))
  | 0, ms, xs, k, h, _, _ => by
    have h1 : ms = [] := List.length_eq_zero_iff.mp (by omega)
    have h2 : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst h1 h2; simp [mergeEv, idxOf]
  | n + 1, [], [], k, _, _, _ => by simp [mergeEv, idxOf]
  | n + 1, m :: ms, [], k, h, ha, hb => by
    have ih := mergeEv_spec n ms [] k (by simp at h ⊢; omega) ha.tail hb
    simp [mergeEv, idxOf, Cmp.bothIdx, Cmp.mineItem, Cmp.theirsItem, List.filterMap_cons] at ih ⊢
    exact ⟨ih.1, ih.2⟩
  | n + 1, [], t :: ts, k, h, ha, hb => by
    have ih := mergeEv_spec n [] ts (k + 1) (by simp at h ⊢; omega) ha hb.tail
    have e1 : idxOf [] (t :: ts) k = idxOf [] ts (k + 1) := by simp [idxOf]
    simp [mergeEv, e1, Cmp.bothIdx, Cmp.mineItem, Cmp.theirsItem, List.filterMap_cons] at ih ⊢
    exact ⟨ih.1, ih.2⟩
  | n + 1, m :: ms, t :: ts, k, h, ha, hb => by
    have hams := List.pairwise_cons.mp ha
    have hbts := List.pairwise_cons.mp hb
    by_cases h1 : lexLt m t = true
    · have ih := mergeEv_spec n ms (t :: ts) k (by simp at h ⊢; omega) hams.2 hb
      have hgt : ∀ x ∈ t :: ts, lexLt m x = true := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h1
        · exact lexLt_trans _ _ _ h1 (hbts.1 x hx)
      have hmx : ∀ x ∈ t :: ts, (m :: ms).contains x = ms.contains x := fun x hx =>
        contains_cons_ne m x ms (lexLt_ne _ _ (hgt x hx)).symm
      have hm1 : ¬ m = t := lexLt_ne _ _ h1
      have hm2 : m ∉ ts := fun hm => lexLt_ne _ _ (hgt m (List.mem_cons_of_mem _ hm)) rfl
      have hmt : (t :: ts).contains m = false := by simp [hm1, hm2]
      simp only [mergeEv, h1, ite_true, List.filterMap_cons, Cmp.bothIdx, Cmp.mineItem, Cmp.theirsItem]
      refine ⟨?_, ?_, ?_⟩
      · rw [ih.1]; exact (idxOf_congr ms (m :: ms) (t :: ts) k hmx).symm
      · simp [List.filter_cons, hmt, ih.2.1, hm1, hm2]
      · rw [ih.2.2]; exact filter_congr' _ _ _ (fun x hx => by simp [(lexLt_ne _ _ (hgt x hx)).symm])
    · by_cases h2 : m = t
      · subst h2
        have ih := mergeEv_spec n ms ts (k + 1) (by simp at h ⊢; omega) hams.2 hbts.2
        have hmx : ∀ x ∈ ts, (m :: ms).contains x = ms.contains x := fun x hx =>
          contains_cons_ne m x ms (lexLt_ne _ _ (hbts.1 x hx)).symm
        have hxm : ∀ x ∈ ms, (m :: ts).contains x = ts.contains x := fun x hx =>
          contains_cons_ne m x ts (lexLt_ne _ _ (hams.1 x hx)).symm
        simp only [mergeEv, h1, Bool.false_eq_true, ite_false, ite_true, List.filterMap_cons, Cmp.bothIdx,
          Cmp.mineItem, Cmp.theirsItem]
        refine ⟨?_, ?_, ?_⟩
        · simp only [idxOf, List.contains_cons, beq_self_eq_true, Bool.true_or, ite_true]
          rw [ih.1]; congr 1
          exact (idxOf_congr ms (m :: ms) ts (k + 1) hmx).symm
        · simp only [List.filter_cons, List.contains_cons, beq_self_eq_true, Bool.true_or, Bool.not_true,
            Bool.false_eq_true, ite_false]
          rw [ih.2.1]; exact filter_congr' _ _ _ (fun x hx => by simp [(lexLt_ne _ _ (hams.1 x hx)).symm])
        · simp only [List.filter_cons, List.contains_cons, beq_self_eq_true, Bool.true_or, Bool.not_true,
            Bool.false_eq_true, ite_false]
          rw [ih.2.2]; exact filter_congr' _ _ _ (fun x hx => by simp [(lexLt_ne _ _ (hbts.1 x hx)).symm])
      · have h3 : lexLt t m = true := by
          rcases lexLt_total m t with h | h | h
          · exact absurd h h1
          · exact absurd h h2
          · exact h
        have ih := mergeEv_spec n (m :: ms) ts (k + 1) (by simp at h ⊢; omega) ha hbts.2
        have hmt : (m :: ms).contains t = false := contains_gt m t ms h3 hams.1
        have hxt : ∀ x ∈ m :: ms, (t :: ts).contains x = ts.contains x := by
          intro x hx
          have hlt : lexLt t x = true := by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact h3
            · exact lexLt_trans _ _ _ h3 (hams.1 x hx)
          exact contains_cons_ne t x ts (lexLt_ne _ _ hlt).symm
        simp only [mergeEv, h1, Bool.false_eq_true, ite_false, h2, List.filterMap_cons, Cmp.bothIdx, Cmp.mineItem,
          Cmp.theirsItem]
        refine ⟨?_, ?_, ?_⟩
        · simp only [idxOf, hmt, Bool.false_eq_true, ite_false]; exact ih.1
        · rw [ih.2.1]; exact filter_congr' _ _ _ (fun x hx => congrArg Bool.not (hxt x hx)) |>.symm
        · simp only [List.filter_cons, hmt, Bool.not_false, ite_true]
          rw [ih.2.2]

end Vinc.Reconcile
