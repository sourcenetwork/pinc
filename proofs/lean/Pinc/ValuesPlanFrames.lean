import Pinc.ValuesPlanCount

/-!
# The frames of one range

For the groups `[a, b)` of a tree of `n` groups, the frames of the reference (`ValuesPlanRef.fs_ref`) are the
groups `a, a + 1, ...` and the pair count of the frame of group `a + k` is `pendLen k`. This file proves the
three facts `plan.rs` is built on:

* `parentsBefore_sum`: `parents_before(n, a, a + k)` is the sum of the pair counts of the frames `0 ..= k`, so
  the pair count of frame `k` is the difference of two `parents_before` (`pendLen_diff`).
* `parentsIn_sum`: the pairs of all the frames are the `parents_in(0, n, a, b)` parents of the range.
* `sumTo_groupSize`: the group bytes of the first `k` frames are `min(len, (a + k) G) - a G`.

Together they give the closed forms for the size of a range and the stream start of every frame
(`frameStart_eq`), and `chain_length_le` bounds the path by the height of the tree.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesPlan
open Pinc.Layout Pinc.Encode

/-- `f 0 + ... + f (k - 1)`. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sumTo f k + f k

theorem sumTo_congr (f g : Nat → Nat) (k : Nat) (h : ∀ j, j < k → f j = g j) : sumTo f k = sumTo g k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [sumTo]; rw [ih (fun j hj => h j (by omega)), h k (by omega)]

theorem sumTo_mono (f : Nat → Nat) (j k : Nat) (h : j ≤ k) : sumTo f j ≤ sumTo f k := by
  induction k with
  | zero => have : j = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ k ih =>
    by_cases hj : j = k + 1
    · subst hj; exact Nat.le_refl _
    · have := ih (by omega); simp only [sumTo]; omega

/-! ### Lists built by `tab` -/

theorem tab_map {α β : Type} (f : Nat → α) (h : α → β) (s n : Nat) : (tab f s n).map h = tab (fun x => h (f x)) s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [tab, ih]

theorem tab_sum {α : Type} (f : Nat → α) (h : α → Nat) (s n : Nat) :
    ((tab f s n).map h).sum = sumTo (fun j => h (f (s + j))) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tab_append f s n 1]
    simp [tab, List.sum_append, ih, sumTo]

theorem tab_take {α : Type} (f : Nat → α) (s m k : Nat) : (tab f s m).take k = tab f s (min k m) := by
  induction m generalizing s k with
  | zero => simp [tab]
  | succ m ih =>
    cases k with
    | zero => simp [tab]
    | succ k => simp only [tab, List.take_succ_cons]; rw [ih (s + 1) k]; rw [show min (k + 1) (m + 1) = min k m + 1 by omega]; rfl

theorem mem_tab {α : Type} (f : Nat → α) (s n : Nat) (y : α) : y ∈ tab f s n ↔ ∃ j, j < n ∧ y = f (s + j) := by
  induction n generalizing s with
  | zero => simp [tab]
  | succ n ih =>
    simp only [tab, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨0, by omega, by simpa using h⟩
      · exact ⟨j + 1, by omega, by rw [h]; congr 1; omega⟩
    · rintro ⟨j, hj, h⟩
      cases j with
      | zero => exact Or.inl (by simpa using h)
      | succ j => exact Or.inr ⟨j, by omega, by rw [h]; congr 1; omega⟩

theorem tab_nodup {α : Type} (f : Nat → α) (hf : ∀ x y, f x = f y → x = y) (s n : Nat) : (tab f s n).Nodup := by
  induction n generalizing s with
  | zero => simp [tab]
  | succ n ih =>
    simp only [tab, List.nodup_cons]
    refine ⟨fun h => ?_, ih (s + 1)⟩
    obtain ⟨j, hj, e⟩ := (mem_tab f (s + 1) n _).1 h
    have := hf _ _ e
    omega

/-! ### Frame cutting -/

theorem fs_offs (S : List Step) (acc : List Nat) : (fs S acc).1.map (fun f => f.2.1) = groupOffs S := by
  induction S generalizing acc with
  | nil => simp [fs, groupOffs]
  | cons s T ih =>
    cases s with
    | parent o => simp only [fs, groupOffs]; exact ih _
    | group off l => simp only [fs, groupOffs, List.map_cons]; rw [ih []]

theorem fs_conserve (S : List Step) (acc : List Nat) :
    np S + acc.length = (((fs S acc).1).map (fun f => f.1.length)).sum + (fs S acc).2.length := by
  induction S generalizing acc with
  | nil => simp [fs, np]
  | cons s T ih =>
    cases s with
    | parent o => simp only [fs, np]; have := ih (acc ++ [o]); simp at this; omega
    | group off l => simp only [fs, np, List.map_cons, List.sum_cons]; have := ih []; simp at this; omega

theorem fs_prefix (S : List Step) (acc : List Nat) (hn : (groupOffs S).Nodup) :
    ∀ k (hk : k < (fs S acc).1.length),
      ((((fs S acc).1).take (k + 1)).map (fun f => f.1.length)).sum =
        acc.length + bef S (((fs S acc).1)[k]'hk).2.1 := by
  induction S generalizing acc with
  | nil => intro k hk; simp [fs] at hk
  | cons s T ih =>
    cases s with
    | parent o =>
      intro k hk
      simp only [fs] at hk ⊢
      simp only [groupOffs] at hn
      have := ih (acc ++ [o]) hn k hk
      simp only [bef]
      rw [List.length_append, List.length_singleton] at this
      omega
    | group off l =>
      intro k hk
      simp only [groupOffs, List.nodup_cons] at hn
      cases k with
      | zero => simp [fs, bef]
      | succ k =>
        simp only [fs, List.length_cons] at hk
        have hk' : k < (fs T []).1.length := by omega
        have := ih [] hn.2 k hk'
        have hm : ((fs T []).1[k]'hk').2.1 ∈ groupOffs T := by
          rw [← fs_offs T []]
          exact List.mem_map.2 ⟨_, List.getElem_mem hk', rfl⟩
        have hne : off ≠ ((fs T []).1[k]'hk').2.1 := fun h => hn.1 (h ▸ hm)
        simp only [fs, List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons, bef, hne, ite_false]
        simp only [List.length_nil, Nat.zero_add] at this
        omega

/-! ### The frames of a range -/

/-- The pair count of the frame of group `a + k` in a tree of `n` groups: the whole path for the first frame, the
path nodes that start at the group for a later one. -/
def pendLen (n a k : Nat) : Nat :=
  if k = 0 then (chain a 0 n 0).length else (starts (a + k) (chain (a + k) 0 n 0)).length

theorem frames_of_range (len log a b : Nat) (hab : a < b) (hb : b ≤ groups len log) :
    (fs (ref len log a b 0 (groups len log) 0) []).1 =
      tab (frameOf len log 0 (groups len log) 0 a []) a (b - a) := by
  have h := fs_ref len log a b _ 0 (groups len log) 0 [] rfl (by omega) (by omega) (by omega) hab
  rw [h]
  simp only []
  rw [show max 0 a = a by omega, show min (groups len log) b = b by omega]

theorem frame_pend (len log n a k : Nat) :
    (frameOf len log 0 n 0 a [] (a + k)).1.length = pendLen n a k := by
  simp only [frameOf, pendLen]
  by_cases hk : k = 0
  · subst hk; simp [offs]
  · have : ¬ a + k = a := by omega
    simp [this, hk, offs]

theorem groupOffs_ref_nodup (len log a b : Nat) (hab : a < b) (hb : b ≤ groups len log) :
    (groupOffs (ref len log a b 0 (groups len log) 0)).Nodup := by
  rw [← fs_offs _ [], frames_of_range len log a b hab hb, tab_map]
  exact tab_nodup _ (fun x y h => by
    simp only [frameOf] at h
    exact groupLen_inj log x y h) _ _

/-- `parents_before(n, a, a + k)` is the sum of the pair counts of the frames `0 ..= k`. -/
theorem parentsBefore_sum (len log a b k : Nat) (hab : a < b) (hb : b ≤ groups len log) (hk : a + k < b) :
    parentsBefore (groups len log) a (a + k) = sumTo (pendLen (groups len log) a) (k + 1) := by
  have hn := groupOffs_ref_nodup len log a b hab hb
  have hF := frames_of_range len log a b hab hb
  have hlen : k < (fs (ref len log a b 0 (groups len log) 0) []).1.length := by
    rw [hF, tab_length]; omega
  have hp := fs_prefix _ [] hn k hlen
  have hbef := pbGo_eq len log a b (groups len log) 0 (groups len log) 0 (a + k) 0 (by omega) (by omega) (by omega) (by omega) (by omega)
  unfold parentsBefore
  rw [hbef]
  simp only [List.length_nil, Nat.zero_add] at hp
  have hget : ((fs (ref len log a b 0 (groups len log) 0) []).1[k]'hlen).2.1 = (a + k) * groupLen log := by
    have h2 := tab_getElem (frameOf len log 0 (groups len log) 0 a []) a (b - a) k (by omega)
    simp only [hF] at hlen ⊢
    rw [List.getElem?_eq_getElem (by rw [tab_length]; omega)] at h2
    have h3 := Option.some.inj h2
    simp only [hF, h3, frameOf]
  rw [← hget, ← hp]
  simp only [hF, tab_take]
  rw [show min (k + 1) (b - a) = k + 1 by omega, tab_sum, Nat.zero_add]
  exact sumTo_congr _ _ _ (fun j _ => frame_pend len log _ a j)

/-- The pairs of all the frames are the parents of the range. -/
theorem parentsIn_sum (len log a b : Nat) (hab : a < b) (hb : b ≤ groups len log) :
    parentsIn a b 0 (groups len log) = sumTo (pendLen (groups len log) a) (b - a) := by
  have hc := fs_conserve (ref len log a b 0 (groups len log) 0) []
  have hF := frames_of_range len log a b hab hb
  have hr := fs_ref len log a b _ 0 (groups len log) 0 [] rfl (by omega) (by omega) (by omega) hab
  have ht : (fs (ref len log a b 0 (groups len log) 0) []).2 = [] := by rw [hr]
  rw [parentsIn_eq len log a b _ 0 _ 0 rfl (by omega) (by omega) (by omega) hab]
  simp only [ht, List.length_nil, hF, tab_sum] at hc ⊢
  have : sumTo (fun j => (frameOf len log 0 (groups len log) 0 a [] (a + j)).1.length) (b - a) =
      sumTo (pendLen (groups len log) a) (b - a) := sumTo_congr _ _ _ (fun j _ => frame_pend len log _ a j)
  omega

/-- The pair count of frame `k`: `parents_before` of its group minus that of the previous one. -/
theorem pendLen_diff (len log a b k : Nat) (hab : a < b) (hb : b ≤ groups len log) (hk : a + k < b) :
    pendLen (groups len log) a k * 64 =
      (parentsBefore (groups len log) a (a + k) - (if k = 0 then 0 else parentsBefore (groups len log) a (a + k - 1))) * 64 := by
  rw [parentsBefore_sum len log a b k hab hb hk]
  by_cases h0 : k = 0
  · subst h0; simp [sumTo]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [show a + (m + 1) - 1 = a + m by omega, parentsBefore_sum len log a b m hab hb (by omega)]
    simp [sumTo]

/-- The group bytes of the first `k` frames. -/
theorem sumTo_groupSize (len log a : Nat) (hlen : len ≤ u64Max) :
    ∀ k, a * groupLen log ≤ len → sumTo (fun j => groupSize len log (a + j)) k = min len ((a + k) * groupLen log) - a * groupLen log := by
  intro k ha
  have hg := groupLen_pos log
  induction k with
  | zero => simp [sumTo]; omega
  | succ k ih =>
    simp only [sumTo]
    rw [ih, groupSize_eq len log _ hlen]
    have e1 : (a + k) * groupLen log = a * groupLen log + k * groupLen log := Nat.add_mul ..
    have e2 : (a + (k + 1)) * groupLen log = a * groupLen log + k * groupLen log + groupLen log := by
      rw [Nat.add_mul, Nat.succ_mul, Nat.add_assoc]
    rw [e1, e2]
    generalize a * groupLen log = p at *
    generalize k * groupLen log = q at *
    generalize groupLen log = g at *
    by_cases h : p + q ≥ len <;> simp only [h, ite_true, ite_false] <;> omega

/-! ### The path -/

/-- The path is not longer than the height of the tree. -/
theorem chain_length_le (x : Nat) : ∀ (n lo hi idx : Nat), hi - lo = n → (chain x lo hi idx).length ≤ hh n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi idx hn
    subst hn
    by_cases h : hi - lo ≥ 2
    · have h1 := leftGroups_pos (hi - lo) h
      have h3 := leftGroups_lt (hi - lo) h
      rw [chain_node _ _ _ _ h]
      have hl := hh_leftGroups (hi - lo) h
      have hr := hh_right (hi - lo) h
      by_cases hx : x < lo + leftGroups (hi - lo)
      · simp only [hx, ite_true, List.length_cons]
        have := ih (leftGroups (hi - lo)) (by omega) lo (lo + leftGroups (hi - lo)) (idx + 1) (by omega)
        omega
      · simp only [hx, ite_false, List.length_cons]
        have := ih (hi - (lo + leftGroups (hi - lo))) (by omega) (lo + leftGroups (hi - lo)) hi (idx + leftGroups (hi - lo)) rfl
        rw [show hi - (lo + leftGroups (hi - lo)) = hi - lo - leftGroups (hi - lo) by omega] at this
        omega
    · rw [chain_leaf _ _ _ _ h]; simp

end Pinc.ValuesPlan
