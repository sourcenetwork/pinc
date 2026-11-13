import Vinc.Axioms
import Vinc.CoreHeap

/-!
# The deadline heap: the invariants hold, the root is the earliest, and the pops come out sorted

What the model proves about `DeadlineHeap`, for any capacity `n`, any deadlines (the largest `u64` included) and any
run of calls:

- `Inv`: the position index and the heap are inverse on the ids present (`pa`, `pb`), every id in the heap is below
  `n`, the heap order holds (each element is not earlier than its parent, the lower id first on a tie: `Ord`), and so
  an id is held at most once and the heap never holds more than `n` items (`len_le`);
- `set_inv`: `set` keeps `Inv` for every id (one outside `0..n` is ignored: `set_out`) and every deadline, and so does
  every run of calls (`run_inv`); the sifts are proved through a heap with one hole (`HS`), as the code's loops are;
- `set_exact`: `set` changes exactly the entry it names: every other id keeps its presence and its deadline, the id
  asked about has the deadline given (or none), and the size changes by one only when an id comes or goes
  (`set_len_new`, `set_len_upd`, `set_len_rem`);
- `len_le`, `set_len_le`, `full_all_held`: the heap never holds more than `n` items, and at `n` every id is held, so a
  deadline given then moves its id in place; `view_run`: the entries are a map from ids to deadlines that each call
  updates, whatever the run;
- `peek_min`: the root is the earliest of the pairs `(deadline, id)` held, the lowest id among equal deadlines;
- `drain_spec`: removing the root over and over (what a run of `poll_timeout` and `set id None` does) gives the pairs
  held in strictly increasing order, each once, and no other (a heap sort), after any run of calls (`drain_run`).
-/

namespace Vinc.CoreHeap

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

/-! ## Sifting up -/

theorem up_step (s : S) (i x : Nat) (k : Nat × Nat) (hs : HS s i x) (hk : k = (s.dl x, x)) (hi : 0 < i)
    (hlt : Lt k (key s ((i - 1) / 2)))
    (hdn : ∀ c, 0 < c → c < s.len → (c - 1) / 2 = i → Le k (key s c)) :
    HS (put s i (s.heap ((i - 1) / 2))) ((i - 1) / 2) x ∧
    ∀ c, 0 < c → c < s.len → (c - 1) / 2 = (i - 1) / 2 →
      Le k (key (put s i (s.heap ((i - 1) / 2))) c) := by
  subst hk
  have hpl : (i - 1) / 2 < i := by omega
  have hpl' : (i - 1) / 2 < s.len := by have := hs.i_lt; omega
  have hpi : (i - 1) / 2 ≠ i := by omega
  generalize hP : (i - 1) / 2 = P at *
  generalize hy : s.heap P = y
  have hyx : y ≠ x := by rw [← hy]; exact hs.pc P hpl' hpi
  have hyn : y < s.n := by rw [← hy]; exact hs.hlt P hpl' hpi
  have hposy : s.pos y = some P := by rw [← hy]; exact hs.pa P hpl' hpi
  refine ⟨⟨hpl', hs.x_lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj hjP
    rw [heap_put]
    by_cases hji : j = i
    · simp [hji, hyn]
    · simp only [hji, if_false]; exact hs.hlt j hj hji
  · intro j hj hjP
    rw [heap_put]
    by_cases hji : j = i
    · simp [hji, pos_put]
    · simp only [hji, if_false]
      have h1 := hs.pa j hj hji
      have hne : s.heap j ≠ y := by
        intro he
        rw [he] at h1
        rw [h1] at hposy
        exact hjP (Option.some.inj hposy)
      rw [pos_put, if_neg hne]; exact h1
  · intro a p hpa hax
    rw [pos_put] at hpa
    by_cases hay : a = y
    · rw [if_pos hay] at hpa
      have := Option.some.inj hpa
      subst this
      refine ⟨hs.i_lt, hpi.symm, ?_⟩
      simp [heap_put, hay]
    · rw [if_neg hay] at hpa
      obtain ⟨h1, h2, h3⟩ := hs.pb a p hpa hax
      have hpP : p ≠ P := by
        rintro rfl
        rw [hy] at h3
        exact hay h3.symm
      refine ⟨h1, hpP, ?_⟩
      simp [heap_put, h2, h3]
  · intro j hj hjP
    rw [heap_put]
    by_cases hji : j = i
    · simp [hji, hyx]
    · simp only [hji, if_false]; exact hs.pc j hj hji
  · obtain ⟨q, hq⟩ := hs.px
    exact ⟨q, by rw [pos_put, if_neg (Ne.symm hyx)]; exact hq⟩
  · intro j hj0 hj hjP hpj
    have hji : j ≠ i := by rintro rfl; exact hpj hP
    rw [key_put_ne _ _ _ _ hji]
    by_cases hpji : (j - 1) / 2 = i
    · rw [hpji, key_put_eq]
      have := hs.gp hi j hj0 hj hpji
      rw [hP] at this
      simpa [key, hy] using this
    · rw [key_put_ne _ _ _ _ hpji]
      exact hs.ord j hj0 hj hji hpji
  · intro hP0 c hc0 hc hcP
    have hnP : (P - 1) / 2 ≠ i := by omega
    rw [key_put_ne _ _ _ _ hnP]
    by_cases hci : c = i
    · subst hci
      rw [key_put_eq]
      have := hs.ord P hP0 hpl' hpi hnP
      simpa [key, hy] using this
    · rw [key_put_ne _ _ _ _ hci]
      have h1 := hs.ord P hP0 hpl' hpi hnP
      have h2 := hs.ord c hc0 hc hci (by rw [hcP]; exact hpi)
      rw [hcP] at h2
      exact Le_trans h1 h2
  · intro c hc0 hc hcP
    by_cases hci : c = i
    · subst hci
      rw [key_put_eq]
      have : (s.dl y, y) = key s P := by simp [key, hy]
      rw [this]
      exact Le_of_Lt hlt
    · rw [key_put_ne _ _ _ _ hci]
      have h2 := hs.ord c hc0 hc hci (by rw [hcP]; exact hpi)
      rw [hcP] at h2
      exact Le_trans (Le_of_Lt hlt) h2

theorem upLoop_spec (x : Nat) (k : Nat × Nat) :
    ∀ i s, HS s i x → k = (s.dl x, x) →
    (∀ c, 0 < c → c < s.len → (c - 1) / 2 = i → Le k (key s c)) → Fin' (upLoop s i x k) s := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro s hs hk hdn
    rw [upLoop]
    by_cases hc : 0 < i ∧ lexLe (key s ((i - 1) / 2)) k = false
    · rw [if_pos hc]
      have hlt : Lt k (key s ((i - 1) / 2)) := by
        have := hc.2
        rw [Bool.eq_false_iff] at this
        have h2 : ¬ Le (key s ((i - 1) / 2)) k := fun h => this ((lexLe_iff _ _).mpr h)
        exact not_Le.mp h2
      obtain ⟨h1, h2⟩ := up_step s i x k hs hk hc.1 hlt hdn
      have := ih ((i - 1) / 2) (by omega) _ h1 hk h2
      refine Fin'.of_same this (put_same s i _ ?_)
      have hP : (i - 1) / 2 < s.len := by have := hs.i_lt; omega
      rw [hs.pa _ hP (by omega)]; rfl
    · rw [if_neg hc]
      refine put_fin s i x k hs hk ?_ hdn
      intro hi0
      refine Classical.byContradiction fun hn => ?_
      have h3 : ¬ lexLe (key s ((i - 1) / 2)) k = true := fun h => hn ((lexLe_iff _ _).mp h)
      exact hc ⟨hi0, by simpa using h3⟩


/-! ## Sifting down -/

theorem minChild_le (s : S) (i d : Nat) (hd0 : 0 < d) (hd : d < s.len) (hdi : (d - 1) / 2 = i) :
    Le (key s (minChild s i)) (key s d) := by
  have hd' : d = 2 * i + 1 ∨ d = 2 * i + 2 := by omega
  unfold minChild
  by_cases hc : 2 * i + 2 < s.len ∧ lexLt (key s (2 * i + 2)) (key s (2 * i + 1)) = true
  · rw [if_pos hc]
    rcases hd' with rfl | rfl
    · exact Le_of_Lt ((lexLt_iff _ _).mp hc.2)
    · exact Le_refl _
  · rw [if_neg hc]
    rcases hd' with rfl | rfl
    · exact Le_refl _
    · have : ¬ lexLt (key s (2 * i + 2)) (key s (2 * i + 1)) = true := fun h => hc ⟨hd, h⟩
      have h2 : ¬ Lt (key s (2 * i + 2)) (key s (2 * i + 1)) := fun h => this ((lexLt_iff _ _).mpr h)
      exact not_Lt.mp h2

theorem minChild_par (s : S) (i : Nat) : (minChild s i - 1) / 2 = i ∧ 0 < minChild s i := by
  unfold minChild; split <;> omega

theorem down_step (s : S) (i x c : Nat) (k : Nat × Nat) (hs : HS s i x) (hc0 : 0 < c) (hcl : c < s.len)
    (hcp : (c - 1) / 2 = i)
    (hmin : ∀ d, 0 < d → d < s.len → (d - 1) / 2 = i → Le (key s c) (key s d))
    (hlt : Lt (key s c) k) (hup : 0 < i → Le (key s ((i - 1) / 2)) k) :
    HS (put s i (s.heap c)) c x ∧ (0 < c → Le (key (put s i (s.heap c)) ((c - 1) / 2)) k) := by
  have hci : c ≠ i := by omega
  generalize hy : s.heap c = y
  have hyx : y ≠ x := by rw [← hy]; exact hs.pc c hcl hci
  have hyn : y < s.n := by rw [← hy]; exact hs.hlt c hcl hci
  have hposy : s.pos y = some c := by rw [← hy]; exact hs.pa c hcl hci
  refine ⟨⟨hcl, hs.x_lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj hjc
    rw [heap_put]
    by_cases hji : j = i
    · simp [hji, hyn]
    · simp only [hji, if_false]; exact hs.hlt j hj hji
  · intro j hj hjc
    rw [heap_put]
    by_cases hji : j = i
    · simp [hji, pos_put]
    · simp only [hji, if_false]
      have h1 := hs.pa j hj hji
      have hne : s.heap j ≠ y := by
        intro he
        rw [he] at h1
        rw [h1] at hposy
        exact hjc (Option.some.inj hposy)
      rw [pos_put, if_neg hne]; exact h1
  · intro a p hpa hax
    rw [pos_put] at hpa
    by_cases hay : a = y
    · rw [if_pos hay] at hpa
      have := Option.some.inj hpa
      subst this
      refine ⟨hs.i_lt, hci.symm, ?_⟩
      simp [heap_put, hay]
    · rw [if_neg hay] at hpa
      obtain ⟨h1, h2, h3⟩ := hs.pb a p hpa hax
      have hpc : p ≠ c := by
        rintro rfl
        rw [hy] at h3
        exact hay h3.symm
      refine ⟨h1, hpc, ?_⟩
      simp [heap_put, h2, h3]
  · intro j hj hjc
    rw [heap_put]
    by_cases hji : j = i
    · simp [hji, hyx]
    · simp only [hji, if_false]; exact hs.pc j hj hji
  · obtain ⟨q, hq⟩ := hs.px
    exact ⟨q, by rw [pos_put, if_neg (Ne.symm hyx)]; exact hq⟩
  · intro j hj0 hj hjc hpj
    by_cases hji : j = i
    · subst hji
      rw [key_put_ne _ _ _ _ (by omega), key_put_eq]
      have := hs.gp hj0 c hc0 hcl hcp
      simpa [key, hy] using this
    · rw [key_put_ne _ _ _ _ hji]
      by_cases hpji : (j - 1) / 2 = i
      · rw [hpji, key_put_eq]
        have := hmin j hj0 hj hpji
        simpa [key, hy] using this
      · rw [key_put_ne _ _ _ _ hpji]
        exact hs.ord j hj0 hj hji hpji
  · intro hc0' d hd0 hd hdc
    have hdi : d ≠ i := by omega
    rw [key_put_ne _ _ _ _ hdi, hcp, key_put_eq]
    have h2 := hs.ord d hd0 hd hdi (by rw [hdc]; exact hci)
    rw [hdc] at h2
    simpa [key, hy] using h2
  · intro _
    rw [hcp, key_put_eq]
    have : (s.dl y, y) = key s c := by simp [key, hy]
    rw [this]
    exact Le_of_Lt hlt

theorem downLoop_spec (x : Nat) (k : Nat × Nat) :
    ∀ m i s, s.len - i = m → HS s i x → k = (s.dl x, x) →
    (0 < i → Le (key s ((i - 1) / 2)) k) → Fin' (downLoop s i x k) s := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro i s hm hs hk hup
    rw [downLoop]
    by_cases hl : 2 * i + 1 < s.len
    · rw [dif_pos hl]
      obtain ⟨hcp, hc0⟩ := minChild_par s i
      have hcl := minChild_lt s i hl
      have hmin := fun d => minChild_le s i d
      by_cases hk' : lexLe k (key s (minChild s i)) = true
      · rw [if_pos hk']
        refine put_fin s i x k hs hk hup ?_
        intro c hc0 hc hci
        exact Le_trans ((lexLe_iff _ _).mp hk') (hmin c hc0 hc hci)
      · rw [if_neg hk']
        have hlt : Lt (key s (minChild s i)) k := by
          have h2 : ¬ Le k (key s (minChild s i)) := fun h => hk' ((lexLe_iff _ _).mpr h)
          exact not_Le.mp h2
        obtain ⟨h1, h2⟩ := down_step s i x (minChild s i) k hs hc0 hcl hcp (fun d => hmin d) hlt hup
        have hge := minChild_ge s i
        have := ih (s.len - minChild s i) (by omega) (minChild s i) (put s i (s.heap (minChild s i))) rfl h1 hk h2
        refine Fin'.of_same this (put_same s i _ ?_)
        rw [hs.pa _ hcl (by omega)]; rfl
    · rw [dif_neg hl]
      refine put_fin s i x k hs hk hup ?_
      intro c hc0 hc hci
      omega

theorem down_inv (s : S) (h : Inv s) (i : Nat) (hi : i < s.len) : Fin' (down s i) s := by
  have hs := hs_of_inv s h i hi
  exact downLoop_spec (s.heap i) (key s i) _ i s rfl hs rfl (fun h0 => h.ord i h0 hi)

theorem put_self (s : S) (i x : Nat) (h1 : s.heap i = x) (h2 : s.pos x = some i) : put s i x = s := by
  have e1 : upd s.heap i x = s.heap := funext fun j => by
    simp only [upd]; split
    · rename_i hj; subst hj; exact h1.symm
    · rfl
  have e2 : upd s.pos x (some i) = s.pos := funext fun a => by
    simp only [upd]; split
    · rename_i hj; subst hj; exact h2.symm
    · rfl
  show ({ s with heap := upd s.heap i x, pos := upd s.pos x (some i) } : S) = s
  rw [e1, e2]

/-- The tail of a removal: the last element sits in the hole `p` and goes up, or down, to where it belongs. -/
theorem rem_tail (s2 : S) (p last : Nat) (hs : HS s2 p last) (hh : s2.heap p = last) (hp : s2.pos last = some p) :
    Fin' (settle (up s2 p) last) s2 := by
  unfold settle
  have e1 : key s2 p = (s2.dl last, last) := by simp [key, hh]
  have hu : up s2 p = upLoop s2 p last (s2.dl last, last) := by unfold up; rw [hh, e1]
  have hd : down s2 p = downLoop s2 p last (s2.dl last, last) := by unfold down; rw [hh, e1]
  by_cases hc : 0 < p ∧ Lt (s2.dl last, last) (key s2 ((p - 1) / 2))
  · have hF := upLoop_spec last (s2.dl last, last) p s2 hs rfl (fun c hc0 hcl hcp =>
      Le_trans (Le_of_Lt hc.2) (hs.gp hc.1 c hc0 hcl hcp))
    rw [hu]
    have hsome := hF.some last
    rw [hp] at hsome
    have hsome' : ((upLoop s2 p last (s2.dl last, last)).pos last).isSome = true := by rw [hsome]; rfl
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome'
    rw [hq]
    have hql : q < (upLoop s2 p last (s2.dl last, last)).len := (hF.pos.pb last q hq).1
    exact Fin'.of_same (down_inv _ ⟨hF.pos, hF.ord⟩ q hql) ⟨hF.len, hF.n, hF.dl, hF.some⟩
  · have hid : upLoop s2 p last (s2.dl last, last) = s2 := by
      rw [upLoop, if_neg (fun h2 => hc ⟨h2.1, by
        have h3 := h2.2
        rw [Bool.eq_false_iff] at h3
        exact not_Le.mp (fun h => h3 ((lexLe_iff _ _).mpr h))⟩)]
      exact put_self s2 p last hh hp
    rw [hu, hid, hp]
    show Fin' (down s2 p) s2
    rw [hd]
    refine downLoop_spec last (s2.dl last, last) (s2.len - p) p s2 rfl hs rfl ?_
    intro h0
    refine Classical.byContradiction fun hn => hc ⟨h0, ?_⟩
    exact not_Le.mp hn

/-! ## `set` -/

/-- What a call of `set` did, apart from keeping the invariant: `d` is the deadlines after it, `L` the size and `b`
whether the id asked about is present. -/
structure Facts (s : S) (id : Nat) (d : Nat → Nat) (L : Nat) (b : Bool) (r : S) : Prop where
  inv : Inv r
  n : r.n = s.n
  others : ∀ a, a ≠ id → (r.pos a).isSome = (s.pos a).isSome
  dl : r.dl = d
  len : r.len = L
  here : (r.pos id).isSome = b

theorem inj_id (s : S) (h : PosInv s) (id p j : Nat) (hp : s.pos id = some p) (hj : j < s.len) (hjp : j ≠ p) :
    s.heap j ≠ id := by
  intro he
  have := h.pa j hj
  rw [he, hp] at this
  exact hjp (Option.some.inj this).symm

theorem set_new (s : S) (h : Inv s) (id v : Nat) (hid : id < s.n) (hpos : s.pos id = none) :
    Facts s id (upd s.dl id v) (s.len + 1) true (set s id (some v)) := by
  have hp := h.pos
  have hne : ∀ j, j < s.len → s.heap j ≠ id := by
    intro j hj he
    have := hp.pa j hj
    rw [he, hpos] at this
    cases this
  simp only [set, hid, hpos, ite_true]
  generalize hs1 : ({ s with dl := upd s.dl id v, len := s.len + 1 } : S) = s1
  have hs1len : s1.len = s.len + 1 := by rw [← hs1]
  have hs1n : s1.n = s.n := by rw [← hs1]
  have hs1dl : s1.dl = upd s.dl id v := by rw [← hs1]
  have hs1h : s1.heap = s.heap := by rw [← hs1]
  have hs1p : s1.pos = s.pos := by rw [← hs1]
  have key1 : ∀ j, j < s.len → key (put s1 s.len id) j = key s j := by
    intro j hj
    rw [key_put_ne _ _ _ _ (by omega)]
    simp [key, hs1dl, hs1h, upd, hne j hj]
  have hHS : HS (put s1 s.len id) s.len id := by
    refine ⟨by simp [hs1len], by simp [hs1n, hid], ?_, ?_, ?_, ?_, ⟨s.len, by simp [pos_put]⟩, ?_, ?_⟩
    · intro j hj hjl
      simp only [len_put, hs1len] at hj
      simp only [heap_put, hjl, ite_false, hs1h, n_put, hs1n]
      exact hp.hlt j (by omega)
    · intro j hj hjl
      simp only [len_put, hs1len] at hj
      have hj' : j < s.len := by omega
      simp only [heap_put, hjl, ite_false, hs1h, pos_put, hne j hj', hs1p]
      exact hp.pa j hj'
    · intro a q hq hax
      rw [pos_put, if_neg hax, hs1p] at hq
      obtain ⟨h1, h2⟩ := hp.pb a q hq
      refine ⟨by simp [hs1len]; omega, by omega, ?_⟩
      simp [heap_put, hs1h, show q ≠ s.len by omega, h2]
    · intro j hj hjl
      simp only [len_put, hs1len] at hj
      simp only [heap_put, hjl, ite_false, hs1h]
      exact hne j (by omega)
    · intro j hj0 hj hjl hpj
      simp only [len_put, hs1len] at hj
      rw [key1 j (by omega), key1 _ (by omega)]
      exact h.ord j hj0 (by omega)
    · intro _ c hc0 hc hcp
      simp only [len_put, hs1len] at hc
      omega
  have hk : key (put s1 s.len id) s.len = ((put s1 s.len id).dl id, id) := key_put_eq _ _ _
  have hF := upLoop_spec id ((put s1 s.len id).dl id, id) s.len (put s1 s.len id) hHS rfl
    (fun c hc0 hc hcp => by simp only [len_put, hs1len] at hc; omega)
  have hup : up (put s1 s.len id) s.len = upLoop (put s1 s.len id) s.len id ((put s1 s.len id).dl id, id) := by
    unfold up; rw [← hk]; congr 1; simp [heap_put]
  rw [hup]
  refine ⟨⟨hF.pos, hF.ord⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF.n]; simp [hs1n]
  · intro a ha
    rw [hF.some]; simp [pos_put, ha, hs1p]
  · rw [hF.dl]; simp [hs1dl]
  · rw [hF.len]; simp [hs1len]
  · rw [hF.some]; simp [pos_put]


theorem set_upd (s : S) (h : Inv s) (id v p : Nat) (hid : id < s.n) (hpos : s.pos id = some p) :
    Facts s id (upd s.dl id v) s.len true (set s id (some v)) := by
  have hp := h.pos
  obtain ⟨hpl, hph⟩ := hp.pb id p hpos
  have hne : ∀ j, j < s.len → j ≠ p → s.heap j ≠ id := fun j hj hjp => inj_id s hp id p j hpos hj hjp
  simp only [set, hid, hpos, ite_true]
  generalize hs1 : ({ s with dl := upd s.dl id v } : S) = s1
  have hs1len : s1.len = s.len := by rw [← hs1]
  have hs1n : s1.n = s.n := by rw [← hs1]
  have hs1dl : s1.dl = upd s.dl id v := by rw [← hs1]
  have hs1h : s1.heap = s.heap := by rw [← hs1]
  have hs1p : s1.pos = s.pos := by rw [← hs1]
  have key1 : ∀ j, j < s.len → j ≠ p → key s1 j = key s j := by
    intro j hj hjp
    simp [key, hs1dl, hs1h, upd, hne j hj hjp]
  have kp : key s p = (s.dl id, id) := by simp [key, hph]
  have kp1 : key s1 p = (v, id) := by simp [key, hs1dl, hs1h, hph, upd]
  have hHS : HS s1 p id := by
    refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ⟨p, by rw [hs1p]; exact hpos⟩, ?_, ?_⟩
    · intro j hj _; rw [hs1h, hs1n]; exact hp.hlt j (by omega)
    · intro j hj _; rw [hs1h, hs1p]; exact hp.pa j (by omega)
    · intro a q hq hax
      rw [hs1p] at hq
      obtain ⟨h1, h2⟩ := hp.pb a q hq
      refine ⟨by omega, ?_, by rw [hs1h]; exact h2⟩
      rintro rfl
      rw [hph] at h2
      exact hax h2.symm
    · intro j hj hjp; rw [hs1h]; exact hne j (by omega) hjp
    · intro j hj0 hj hjp hpj
      rw [key1 j (by omega) hjp, key1 _ (by omega) hpj]
      exact h.ord j hj0 (by omega)
    · intro hp0 c hc0 hc hcp
      have hcp' : c ≠ p := by omega
      rw [key1 _ (by omega) (by omega), key1 c (by omega) hcp']
      have h1 := h.ord p hp0 hpl
      have h2 := h.ord c hc0 (by omega)
      rw [hcp] at h2
      exact Le_trans h1 h2
  have hup : up s1 p = upLoop s1 p id (v, id) := by
    unfold up; rw [kp1, hs1h, hph]
  have hdn : down s1 p = downLoop s1 p id (v, id) := by
    unfold down; rw [kp1, hs1h, hph]
  have hF : ∀ r, Fin' r s1 → Facts s id (upd s.dl id v) s.len true r := by
    intro r hr
    refine ⟨⟨hr.pos, hr.ord⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hr.n, hs1n]
    · intro a ha; rw [hr.some, hs1p]
    · rw [hr.dl, hs1dl]
    · rw [hr.len, hs1len]
    · rw [hr.some, hs1p, hpos]; rfl
  by_cases hlt : v < s.dl id
  · rw [if_pos hlt, hup]
    refine hF _ (upLoop_spec id (v, id) p s1 hHS (by simp [hs1dl, upd]) ?_)
    intro c hc0 hc hcp
    have hcp' : c ≠ p := by omega
    rw [key1 c (by omega) hcp']
    have h2 := h.ord c hc0 (by omega)
    rw [hcp, kp] at h2
    refine Le_trans ?_ h2
    unfold Le; simp; omega
  · rw [if_neg hlt]
    by_cases hgt : s.dl id < v
    · rw [if_pos hgt, hdn]
      refine hF _ (downLoop_spec id (v, id) (s1.len - p) p s1 rfl hHS (by simp [hs1dl, upd]) ?_)
      intro hp0
      rw [key1 _ (by omega) (by omega)]
      have h2 := h.ord p hp0 hpl
      rw [kp] at h2
      refine Le_trans h2 ?_
      unfold Le; simp; omega
    · rw [if_neg hgt]
      have hv : v = s.dl id := by omega
      have e : upd s.dl id v = s.dl := funext fun j => by
        simp only [upd]; split
        · rename_i hj; subst hj; exact hv
        · rfl
      have hs1s : s1 = s := by rw [← hs1, e]
      rw [hs1s]
      refine ⟨h, rfl, fun _ _ => rfl, ?_, rfl, ?_⟩
      · simp [e]
      · rw [hpos]; rfl

theorem set_rem (s : S) (h : Inv s) (id p : Nat) (hid : id < s.n) (hpos : s.pos id = some p) :
    Facts s id s.dl (if s.pos id = none then s.len else s.len - 1) false (set s id none) := by
  have hp := h.pos
  obtain ⟨hpl, hph⟩ := hp.pb id p hpos
  simp only [set, hid, hpos, ite_true]
  generalize hs1 : ({ s with len := s.len - 1, pos := upd s.pos id none } : S) = s1
  have hs1len : s1.len = s.len - 1 := by rw [← hs1]
  have hs1n : s1.n = s.n := by rw [← hs1]
  have hs1dl : s1.dl = s.dl := by rw [← hs1]
  have hs1h : s1.heap = s.heap := by rw [← hs1]
  have hs1p : s1.pos = upd s.pos id none := by rw [← hs1]
  have hLl : s.len - 1 < s.len := by omega
  generalize hlast : s.heap (s.len - 1) = last
  have hplast : s.pos last = some (s.len - 1) := by rw [← hlast]; exact hp.pa _ hLl
  have hlastn : last < s.n := by rw [← hlast]; exact hp.hlt _ hLl
  by_cases hli : last ≠ id
  · rw [if_pos hli]
    have hpL : p ≠ s.len - 1 := by
      rintro rfl
      rw [hlast] at hph
      exact hli hph
    have hpL' : p < s.len - 1 := by omega
    have hjinj : ∀ j, j < s.len → j ≠ p → s.heap j ≠ id := fun j hj hjp => inj_id s hp id p j hpos hj hjp
    have hjl : ∀ j, j < s.len - 1 → s.heap j ≠ last := by
      intro j hj he
      have := hp.pa j (by omega)
      rw [he, hplast] at this
      have := Option.some.inj this
      omega
    generalize hs2 : put s1 p last = s2
    have hs2len : s2.len = s.len - 1 := by rw [← hs2]; exact hs1len
    have hs2n : s2.n = s.n := by rw [← hs2]; exact hs1n
    have hs2dl : s2.dl = s.dl := by rw [← hs2]; exact hs1dl
    have hs2h : ∀ j, s2.heap j = if j = p then last else s.heap j := by
      intro j; rw [← hs2, heap_put, hs1h]
    have hs2p : ∀ a, s2.pos a = if a = last then some p else if a = id then none else s.pos a := by
      intro a; rw [← hs2, pos_put, hs1p]; simp [upd]
    have key2 : ∀ j, j ≠ p → key s2 j = key s j := by
      intro j hjp; simp [key, hs2h, hs2dl, hjp]
    have hHS : HS s2 p last := by
      refine ⟨by omega, by rw [hs2n]; exact hlastn, ?_, ?_, ?_, ?_, ⟨p, by simp [hs2p]⟩, ?_, ?_⟩
      · intro j hj hjp; rw [hs2h, if_neg hjp, hs2n]; exact hp.hlt j (by omega)
      · intro j hj hjp
        rw [hs2h, if_neg hjp, hs2p, if_neg (hjl j (by omega)), if_neg (hjinj j (by omega) hjp)]
        exact hp.pa j (by omega)
      · intro a q hq hal
        rw [hs2p, if_neg hal] at hq
        by_cases hai : a = id
        · rw [if_pos hai] at hq; cases hq
        · rw [if_neg hai] at hq
          obtain ⟨h1, h2⟩ := hp.pb a q hq
          have hqL : q ≠ s.len - 1 := by
            rintro rfl; rw [hlast] at h2; exact hal h2.symm
          have hqp : q ≠ p := by
            rintro rfl; rw [hph] at h2; exact hai h2.symm
          refine ⟨by omega, hqp, ?_⟩
          rw [hs2h, if_neg hqp]; exact h2
      · intro j hj hjp; rw [hs2h, if_neg hjp]; exact hjl j (by omega)
      · intro j hj0 hj hjp hpj
        rw [key2 j hjp, key2 _ hpj]
        exact h.ord j hj0 (by omega)
      · intro hp0 c hc0 hc hcp
        have hcp' : c ≠ p := by omega
        rw [key2 _ (by omega), key2 c hcp']
        have h1 := h.ord p hp0 hpl
        have h2 := h.ord c hc0 (by omega)
        rw [hcp] at h2
        exact Le_trans h1 h2
    have hT := rem_tail s2 p last hHS (by rw [hs2h, if_pos rfl]) (by rw [hs2p, if_pos rfl])
    refine ⟨⟨hT.pos, hT.ord⟩, hT.n.trans hs2n, ?_, hT.dl.trans hs2dl, ?_, ?_⟩
    · intro a ha
      rw [hT.some, hs2p]
      by_cases hal : a = last
      · subst hal; rw [hplast]; simp
      · simp [hal, ha]
    · rw [hT.len, hs2len]; simp
    · rw [hT.some, hs2p, if_neg (Ne.symm hli), if_pos rfl]; rfl
  · have hli' : last = id := by simpa using hli
    rw [if_neg hli]
    have hpL : p = s.len - 1 := by
      have := hp.pa p hpl
      rw [hph] at this
      have h2 : s.pos id = some (s.len - 1) := by rw [← hli']; exact hplast
      rw [hpos] at h2
      exact Option.some.inj h2
    have hjinj : ∀ j, j < s.len - 1 → s.heap j ≠ id := fun j hj => inj_id s hp id p j hpos (by omega) (by omega)
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, by rw [hs1n], ?_, by rw [hs1dl], ?_, ?_⟩
    · intro j hj
      rw [hs1len] at hj
      rw [hs1h, hs1p]
      have := hp.pa j (by omega)
      simp only [upd, hjinj j hj, ite_false]
      exact this
    · intro a q hq
      rw [hs1p] at hq
      simp only [upd] at hq
      split at hq
      · cases hq
      · rename_i hai
        obtain ⟨h1, h2⟩ := hp.pb a q hq
        have hqL : q ≠ s.len - 1 := by
          rintro rfl; rw [hlast, hli'] at h2; exact hai h2.symm
        rw [hs1len, hs1h]
        exact ⟨by omega, h2⟩
    · intro j hj
      rw [hs1len] at hj
      rw [hs1h, hs1n]; exact hp.hlt j (by omega)
    · intro j hj0 hj
      rw [hs1len] at hj
      have := h.ord j hj0 (by omega)
      simp only [key, hs1h, hs1dl]
      exact this
    · intro a ha; rw [hs1p]; simp [upd, ha]
    · rw [hs1len]; simp
    · rw [hs1p]; simp [upd]


theorem set_out (s : S) (id : Nat) (t : Option Nat) (h : ¬ id < s.n) : set s id t = s := by
  simp [set, h]

theorem set_nop (s : S) (id : Nat) (hpos : s.pos id = none) : set s id none = s := by
  by_cases hid : id < s.n <;> simp [set, hid, hpos]

/-- `set` keeps the invariant, for every id and every deadline. -/
theorem set_inv (s : S) (h : Inv s) (id : Nat) (t : Option Nat) : Inv (set s id t) := by
  by_cases hid : id < s.n
  · cases hpos : s.pos id with
    | none =>
      cases t with
      | none => rw [set_nop s id hpos]; exact h
      | some v => exact (set_new s h id v hid hpos).inv
    | some p =>
      cases t with
      | none => exact (set_rem s h id p hid hpos).inv
      | some v => exact (set_upd s h id v p hid hpos).inv
  · rw [set_out s id t hid]; exact h

/-- `set` changes exactly the entry it names: every other id keeps whether it is present and its deadline; the id
asked about has the deadline given, or none; the capacity is the same. -/
theorem set_exact (s : S) (h : Inv s) (id : Nat) (t : Option Nat) (hid : id < s.n) :
    (set s id t).n = s.n ∧
    (∀ a, a ≠ id → ((set s id t).pos a).isSome = (s.pos a).isSome ∧ (set s id t).dl a = s.dl a) ∧
    (∀ v, t = some v → ((set s id t).pos id).isSome = true ∧ (set s id t).dl id = v) ∧
    (t = none → (set s id t).pos id = none) := by
  cases hpos : s.pos id with
  | none =>
    cases t with
    | none => rw [set_nop s id hpos]; simp [hpos]
    | some v =>
      have F := set_new s h id v hid hpos
      refine ⟨F.n, fun a ha => ⟨F.others a ha, ?_⟩, fun w hw => ?_, fun hw => (by cases hw)⟩
      · rw [F.dl]; simp [upd, ha]
      · cases hw; exact ⟨F.here, by rw [F.dl]; simp [upd]⟩
  | some p =>
    cases t with
    | none =>
      have F := set_rem s h id p hid hpos
      refine ⟨F.n, fun a ha => ⟨F.others a ha, by rw [F.dl]⟩, fun w hw => (by cases hw), fun _ => ?_⟩
      have := F.here
      simpa using this
    | some v =>
      have F := set_upd s h id v p hid hpos
      refine ⟨F.n, fun a ha => ⟨F.others a ha, ?_⟩, fun w hw => ?_, fun hw => (by cases hw)⟩
      · rw [F.dl]; simp [upd, ha]
      · cases hw; exact ⟨F.here, by rw [F.dl]; simp [upd]⟩

/-- The size changes by one when an id comes or goes, and not otherwise. -/
theorem set_len_new (s : S) (h : Inv s) (id v : Nat) (hid : id < s.n) (hpos : s.pos id = none) :
    (set s id (some v)).len = s.len + 1 := (set_new s h id v hid hpos).len
theorem set_len_upd (s : S) (h : Inv s) (id v p : Nat) (hid : id < s.n) (hpos : s.pos id = some p) :
    (set s id (some v)).len = s.len := (set_upd s h id v p hid hpos).len
theorem set_len_rem (s : S) (h : Inv s) (id p : Nat) (hid : id < s.n) (hpos : s.pos id = some p) :
    (set s id none).len = s.len - 1 := by
  have := (set_rem s h id p hid hpos).len
  simpa [hpos] using this

theorem set_n (s : S) (h : Inv s) (id : Nat) (t : Option Nat) : (set s id t).n = s.n := by
  by_cases hid : id < s.n
  · exact (set_exact s h id t hid).1
  · rw [set_out s id t hid]

/-- A run of calls keeps the invariant. -/
theorem run_inv (s : S) (h : Inv s) : ∀ ops, Inv (run s ops)
  | [] => h
  | (id, t) :: l => run_inv (set s id t) (set_inv s h id t) l

theorem run_n (s : S) (h : Inv s) : ∀ ops, (run s ops).n = s.n
  | [] => rfl
  | (id, t) :: l => by
    rw [show run s ((id, t) :: l) = run (set s id t) l from rfl, run_n (set s id t) (set_inv s h id t) l]
    exact set_n s h id t

/-! ## The earliest -/

/-- The root is not later than any element of the heap. -/
theorem root_le (s : S) (h : Inv s) : ∀ j, j < s.len → Le (key s 0) (key s j) := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro hj
    by_cases hj0 : j = 0
    · subst hj0; exact Le_refl _
    · have h1 := ih ((j - 1) / 2) (by omega) (by omega)
      exact Le_trans h1 (h.ord j (by omega) hj)

/-- `peek` gives the earliest of the pairs `(deadline, id)` held, the lowest id among equal deadlines: an id that is
held, with its deadline, not later (in that order) than any pair held. -/
theorem peek_min (s : S) (h : Inv s) (t id : Nat) (hp : peek s = some (t, id)) :
    (s.pos id).isSome = true ∧ t = s.dl id ∧
    ∀ a, (s.pos a).isSome = true → Le (t, id) (s.dl a, a) := by
  unfold peek at hp
  split at hp
  · cases hp
  · rename_i hl
    have hlen : 0 < s.len := by omega
    have e := Option.some.inj hp
    have e1 : s.dl (s.heap 0) = t := (Prod.mk.inj e).1
    have e2 : s.heap 0 = id := (Prod.mk.inj e).2
    subst e1; subst e2
    refine ⟨?_, rfl, ?_⟩
    · rw [h.pos.pa 0 hlen]; rfl
    · intro a ha
      obtain ⟨p, hpa⟩ := Option.isSome_iff_exists.mp ha
      obtain ⟨hpl, hph⟩ := h.pos.pb a p hpa
      have := root_le s h p hpl
      simp only [key, hph] at this
      exact this

/-! ## Draining the heap: a heap sort -/

theorem drain_spec : ∀ (f : Nat) (s : S), Inv s → s.len ≤ f →
    (drain f s).Pairwise Lt ∧ (drain f s).length = s.len ∧
    ∀ x, x ∈ drain f s ↔ ∃ a, (s.pos a).isSome = true ∧ x = (s.dl a, a) := by
  have empty : ∀ s : S, Inv s → s.len = 0 → ∀ x : Nat × Nat, ¬ ∃ a, (s.pos a).isSome = true ∧ x = (s.dl a, a) := by
    intro s h h0 x ⟨a, ha, _⟩
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ha
    have := (h.pos.pb a p hp).1
    omega
  intro f
  induction f with
  | zero =>
    intro s h hl
    have h0 : s.len = 0 := by omega
    simp only [drain]
    refine ⟨List.Pairwise.nil, by simp [h0], fun x => ?_⟩
    simp only [List.not_mem_nil, false_iff]
    exact empty s h h0 x
  | succ f ih =>
    intro s h hl
    unfold drain
    cases hpk : peek s with
    | none =>
      have h0 : s.len = 0 := by
        unfold peek at hpk; split at hpk
        · assumption
        · cases hpk
      simp only
      refine ⟨List.Pairwise.nil, by simp [h0], fun x => ?_⟩
      simp only [List.not_mem_nil, false_iff]
      exact empty s h h0 x
    | some tid =>
      obtain ⟨t, id⟩ := tid
      simp only
      obtain ⟨hpres, ht, hmin⟩ := peek_min s h t id hpk
      obtain ⟨p, hpos⟩ := Option.isSome_iff_exists.mp hpres
      have hid : id < s.n := (h.pos.pb id p hpos).2 ▸ h.pos.hlt p (h.pos.pb id p hpos).1
      have hlenpos : 0 < s.len := by have := (h.pos.pb id p hpos).1; omega
      have F := set_rem s h id p hid hpos
      have hlen' : (set s id none).len = s.len - 1 := by
        have := F.len; simpa [hpos] using this
      obtain ⟨ihp, ihl, ihm⟩ := ih (set s id none) F.inv (by omega)
      have hnone : (set s id none).pos id = none := by
        have := F.here; simpa using this
      have hrdl : ∀ a, (set s id none).dl a = s.dl a := fun a => by rw [F.dl]
      refine ⟨?_, ?_, ?_⟩
      · refine List.Pairwise.cons ?_ ihp
        intro y hy
        obtain ⟨a, ha, rfl⟩ := (ihm y).mp hy
        have hai : a ≠ id := by
          rintro rfl; rw [hnone] at ha; simp at ha
        have has : (s.pos a).isSome = true := by rw [← F.others a hai]; exact ha
        have := hmin a has
        rw [hrdl]
        unfold Le at this; unfold Lt; simp only at this ⊢
        omega
      · simp [ihl, hlen']; omega
      · intro y
        rw [List.mem_cons, ihm y]
        constructor
        · rintro (rfl | ⟨a, ha, rfl⟩)
          · exact ⟨id, hpres, by rw [ht]⟩
          · have hai : a ≠ id := by
              rintro rfl; rw [hnone] at ha; simp at ha
            exact ⟨a, by rw [← F.others a hai]; exact ha, by rw [hrdl]⟩
        · rintro ⟨a, ha, rfl⟩
          by_cases hai : a = id
          · subst hai; left; rw [ht]
          · right; exact ⟨a, by rw [F.others a hai]; exact ha, by rw [hrdl]⟩

/-- What the pops of any run of calls give out: the pairs held, in strictly increasing order, each once. -/
theorem drain_run (n : Nat) (ops : List (Nat × Option Nat)) :
    let s := run (init n) ops
    (drain n s).Pairwise Lt ∧ ∀ x, x ∈ drain n s ↔ ∃ a, (s.pos a).isSome = true ∧ x = (s.dl a, a) := by
  have hI := run_inv (init n) (init_inv n) ops
  have hn : (run (init n) ops).len ≤ n := by
    have := len_le _ hI.pos
    rw [run_n (init n) (init_inv n) ops] at this
    exact this
  have := drain_spec n (run (init n) ops) hI hn
  exact ⟨this.1, this.2.2⟩


/-! ## The capacity -/

/-- After any call the heap holds at most `n` items. -/
theorem set_len_le (s : S) (h : Inv s) (id : Nat) (t : Option Nat) : (set s id t).len ≤ s.n := by
  have := len_le _ (set_inv s h id t).pos
  rwa [set_n s h id t] at this

/-- At capacity every id below `n` is held, so a call that gives an id a deadline moves it in place and the heap
does not grow. -/
theorem full_all_held (s : S) (h : Inv s) (hfull : s.len = s.n) (id : Nat) (hid : id < s.n) :
    (s.pos id).isSome = true := by
  cases hpos : s.pos id with
  | some _ => rfl
  | none =>
    have h1 := set_len_new s h id 0 hid hpos
    have h2 := set_len_le s h id (some 0)
    omega

/-! ## The entries as a map -/

/-- The deadline of each id, if it has one. -/
def view (s : S) (a : Nat) : Option Nat := if (s.pos a).isSome then some (s.dl a) else none

theorem view_set (s : S) (h : Inv s) (id : Nat) (t : Option Nat) (a : Nat) :
    view (set s id t) a = if id < s.n ∧ a = id then t else view s a := by
  by_cases hid : id < s.n
  · by_cases ha : a = id
    · subst ha
      obtain ⟨_, _, h3, h4⟩ := set_exact s h a t hid
      cases t with
      | some v =>
        obtain ⟨h5, h6⟩ := h3 v rfl
        simp [view, h5, h6, hid]
      | none => simp [view, h4 rfl, hid]
    · obtain ⟨_, h2, _, _⟩ := set_exact s h id t hid
      obtain ⟨h5, h6⟩ := h2 a ha
      simp [view, h5, h6, ha]
  · simp [set_out s id t hid, hid]

/-- The naive heap: a map from ids to deadlines. -/
def naive (n : Nat) (m : Nat → Option Nat) : List (Nat × Option Nat) → Nat → Option Nat
  | [] => m
  | (id, t) :: l => naive n (if id < n then upd m id t else m) l

theorem view_run (s : S) (h : Inv s) : ∀ ops, view (run s ops) = naive s.n (view s) ops
  | [] => rfl
  | (id, t) :: l => by
    show view (run (set s id t) l) = naive s.n (if id < s.n then upd (view s) id t else view s) l
    rw [view_run (set s id t) (set_inv s h id t) l, set_n s h id t]
    congr 1
    funext a
    rw [view_set s h id t a]
    by_cases hid : id < s.n
    · by_cases ha : a = id <;> simp [upd, hid, ha]
    · simp [hid]

#audit_axioms Vinc.CoreHeap.init_inv
#audit_axioms Vinc.CoreHeap.len_le
#audit_axioms Vinc.CoreHeap.upLoop_spec
#audit_axioms Vinc.CoreHeap.downLoop_spec
#audit_axioms Vinc.CoreHeap.set_inv
#audit_axioms Vinc.CoreHeap.set_exact
#audit_axioms Vinc.CoreHeap.set_len_new
#audit_axioms Vinc.CoreHeap.set_len_upd
#audit_axioms Vinc.CoreHeap.set_len_rem
#audit_axioms Vinc.CoreHeap.run_inv
#audit_axioms Vinc.CoreHeap.peek_min
#audit_axioms Vinc.CoreHeap.drain_spec
#audit_axioms Vinc.CoreHeap.drain_run
#audit_axioms Vinc.CoreHeap.set_len_le
#audit_axioms Vinc.CoreHeap.full_all_held
#audit_axioms Vinc.CoreHeap.view_run

end Vinc.CoreHeap
