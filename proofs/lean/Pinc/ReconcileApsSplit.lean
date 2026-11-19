import Pinc.ReconcileHash

/-!
# Reconcile APS, part 1: intervals and the split

The abstract part system works on key-space intervals `Iv` (a lower bound and an optional upper bound; `hi = none` is
infinity). `splitIvs T I fan` is the interval logic of `splitParts` (core.rs `split`): the receiver's items of `I`
are cut into blocks of `step = max 1 (ceil (c / fan))` and a separator `q[..cpl p q + 1]` is placed between the last
item `p` of a block and the first item `q` of the next. This file proves (`splitIvs_*`):

* `splitIvs_spec`: the children are pairwise disjoint sub-intervals of `I` whose union is `I` (a partition of the key
  space, so of every set); at most `fan` children; each holds at most `step` of the receiver's items, and with two or
  more items every child holds fewer;
* `ivs_props`: the receiver's items in the children are the blocks (consecutive slices, `chunkBy`, each of at most `step`).

The refinement of the byte machine has to show that the intervals `splitParts` writes are `splitIvs` of the receiver's
items in the part's range (the blocks are the index slices `x..y`; `slice_eq_filter` turns a rank range into a filter).
-/

namespace Pinc.Reconcile

/-- A key-space interval. -/
structure Iv where
  lo : Item
  hi : Option Item
  deriving DecidableEq

def Iv.has (I : Iv) (x : Item) : Bool := inRange I.lo I.hi x

def Iv.items (T : List Item) (I : Iv) : List Item := T.filter I.has

def cnt (T : List Item) (I : Iv) : Nat := (I.items T).length

/-- The whole key space. -/
def Iv.top : Iv := ⟨[], none⟩

theorem Iv.top_has (x : Item) : Iv.top.has x = true := by
  simp [Iv.has, Iv.top, inRange, lexLt_nil_right]

/-- Blocks of `step` consecutive items. -/
def chunkBy (step : Nat) : Nat → List Item → List (List Item)
  | 0, _ => []
  | f + 1, L => if L = [] then [] else L.take step :: chunkBy step f (L.drop step)

/-- The child intervals for the blocks, from the lower bound `l`. -/
def ivsOf (hi : Option Item) : Item → List (List Item) → List Iv
  | _, [] => []
  | l, [_] => [⟨l, hi⟩]
  | l, b1 :: b2 :: rest =>
    match b1.getLast?, b2.head? with
    | some p, some q => ⟨l, some (q.take (cpl p q + 1))⟩ :: ivsOf hi (q.take (cpl p q + 1)) (b2 :: rest)
    | _, _ => [⟨l, hi⟩]

/-- The block size of a split of `c` items into at most `fan` blocks. -/
def stepOf (c fan : Nat) : Nat := max 1 ((c + fan - 1) / fan)

/-- The blocks of a split. -/
def blocksOf (T : List Item) (I : Iv) (fan : Nat) : List (List Item) :=
  let L := I.items T
  chunkBy (stepOf L.length fan) L.length L

/-- `splitChildren`: the intervals of the parts a split writes. -/
def splitIvs (T : List Item) (I : Iv) (fan : Nat) : List Iv := ivsOf I.hi I.lo (blocksOf T I fan)

/-! ## Order helpers -/

theorem le_of_not_lt {a b : Item} (h : lexLt b a = false) : a = b ∨ lexLt a b = true := by
  rcases (lexLt_false_iff b a).mp h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h

theorem lt_trans' {a b c : Item} (h1 : lexLt a b = true) (h2 : lexLt b c = true) : lexLt a c = true :=
  lexLt_trans _ _ _ h1 h2

/-- `a < b` and `b <= c` give `a < c`. -/
theorem lt_le_trans {a b c : Item} (h1 : lexLt a b = true) (h2 : lexLt c b = false) : lexLt a c = true := by
  rcases le_of_not_lt h2 with rfl | h
  · exact h1
  · exact lt_trans' h1 h

/-- `a <= b` and `b < c` give `a < c`. -/
theorem le_lt_trans {a b c : Item} (h1 : lexLt b a = false) (h2 : lexLt b c = true) : lexLt a c = true := by
  rcases le_of_not_lt h1 with rfl | h
  · exact h2
  · exact lt_trans' h h2

theorem le_le_trans {a b c : Item} (h1 : lexLt b a = false) (h2 : lexLt c b = false) : lexLt c a = false := by
  cases h : lexLt c a with
  | false => rfl
  | true => have := lt_le_trans h h1; simp [h2] at this

def hiOk (hi : Option Item) (z : Item) : Bool := match hi with | none => true | some h => lexLt z h

theorem inRange_iff (l : Item) (hi : Option Item) (z : Item) :
    inRange l hi z = true ↔ lexLt z l = false ∧ hiOk hi z = true := by
  unfold inRange hiOk; cases hi <;> simp

theorem hiOk_le {hi : Option Item} {q z : Item} (h : hiOk hi q = true) (hz : lexLt q z = false) :
    hiOk hi z = true := by
  cases hi with
  | none => rfl
  | some h => exact le_lt_trans hz h

theorem lt_not_le {a b : Item} (h1 : lexLt a b = true) (h2 : lexLt a b = false) : False := by simp [h1] at h2

/-! ## Chunks -/

theorem chunkBy_join (step : Nat) : ∀ (f : Nat) (L : List Item), L.length ≤ f → 1 ≤ step →
    (chunkBy step f L).flatten = L
  | 0, L, h, _ => by simp at h; subst h; simp [chunkBy]
  | f + 1, L, h, hs => by
    unfold chunkBy
    by_cases hL : L = []
    · simp [hL]
    · have hpos : 0 < L.length := List.length_pos_iff.mpr hL
      simp only [hL, ↓reduceIte, List.flatten_cons]
      rw [chunkBy_join step f (L.drop step) (by rw [List.length_drop]; omega) hs]
      simp

theorem chunkBy_ne (step : Nat) (hs : 1 ≤ step) : ∀ (f : Nat) (L : List Item), ∀ b ∈ chunkBy step f L, b ≠ []
  | 0, L, b, h => by simp [chunkBy] at h
  | f + 1, L, b, h => by
    unfold chunkBy at h
    by_cases hL : L = []
    · simp [hL] at h
    · simp only [hL, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h
      · have : 0 < L.length := List.length_pos_iff.mpr hL
        intro h0
        have h0' : (L.take step).length = 0 := by rw [h0]; rfl
        rw [List.length_take] at h0'; omega
      · exact chunkBy_ne step hs f _ b h

theorem chunkBy_len (step : Nat) : ∀ (f : Nat) (L : List Item), ∀ b ∈ chunkBy step f L, b.length ≤ step
  | 0, L, b, h => by simp [chunkBy] at h
  | f + 1, L, b, h => by
    unfold chunkBy at h
    by_cases hL : L = []
    · simp [hL] at h
    · simp only [hL, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.length_take_le _ _
      · exact chunkBy_len step f _ b h

theorem chunkBy_count (step : Nat) (hs : 1 ≤ step) : ∀ (f : Nat) (L : List Item) (k : Nat),
    L.length ≤ f → L.length ≤ k * step → (chunkBy step f L).length ≤ k
  | 0, L, k, _, _ => by simp [chunkBy]
  | f + 1, L, k, h, hk => by
    unfold chunkBy
    by_cases hL : L = []
    · simp [hL]
    · simp only [hL, ↓reduceIte, List.length_cons]
      have hpos : 0 < L.length := List.length_pos_iff.mpr hL
      cases k with
      | zero => rw [Nat.zero_mul] at hk; omega
      | succ k =>
        have hpos' := hpos
        have h1 : (L.drop step).length ≤ f := by rw [List.length_drop]; omega
        have h2 : (L.drop step).length ≤ k * step := by rw [List.length_drop]; rw [Nat.succ_mul] at hk; omega
        have := chunkBy_count step hs f (L.drop step) k h1 h2
        omega

/-! ## The intervals of a block list -/

/-- `l <= x`. -/
def GeL (l x : Item) : Prop := lexLt x l = false

theorem getLast_max {l : List Item} (hs : Sorted l) {p : Item} (h : l.getLast? = some p) :
    ∀ a ∈ l, a = p ∨ lexLt a p = true := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp h
  intro a ha
  rw [Sorted, List.pairwise_append] at hs
  simp only [List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · exact Or.inr (hs.2.2 a ha p (by simp))
  · exact Or.inl rfl

theorem head_min {l : List Item} (hs : Sorted l) {q : Item} (h : l.head? = some q) :
    ∀ a ∈ l, a = q ∨ lexLt q a = true := by
  cases l with
  | nil => simp at h
  | cons x t =>
    simp at h; subst h
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Or.inl rfl
    · exact Or.inr ((List.pairwise_cons.mp hs).1 a ha)

/-- Key facts about the child intervals of a block list `blocks` of a sorted, non-empty-block list inside `l..hi`. -/
theorem ivs_props (hi : Option Item) : ∀ (blocks : List (List Item)) (l : Item),
    blocks ≠ [] → (∀ b ∈ blocks, b ≠ []) → Sorted blocks.flatten →
    (∀ x ∈ blocks.flatten, inRange l hi x = true) →
    (∀ z, inRange l hi z = true → ∃ J ∈ ivsOf hi l blocks, J.has z = true) ∧
    (∀ J ∈ ivsOf hi l blocks, ∀ z, J.has z = true → inRange l hi z = true) ∧
    (ivsOf hi l blocks).Pairwise (fun J K => ∀ z, J.has z = true → K.has z = false) ∧
    (ivsOf hi l blocks).map (fun J => J.items blocks.flatten) = blocks ∧
    (ivsOf hi l blocks).length = blocks.length
  | [], _, h, _, _, _ => absurd rfl h
  | [b], l, _, hne, hs, hr => by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro z hz; exact ⟨⟨l, hi⟩, by simp [ivsOf], hz⟩
    · intro J hJ z hz; simp [ivsOf] at hJ; subst hJ; exact hz
    · simp [ivsOf]
    · simp only [ivsOf, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, List.cons.injEq,
        and_true]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hr
      exact List.filter_eq_self.mpr hr
    · simp [ivsOf]
  | b1 :: b2 :: rest, l, _, hne, hs, hr => by
    obtain ⟨hb1, hb2, hrest⟩ : b1 ≠ [] ∧ b2 ≠ [] ∧ ∀ b ∈ rest, b ≠ [] :=
      ⟨hne _ (by simp), hne _ (by simp), fun b hb => hne b (by simp [hb])⟩
    obtain ⟨p, hp⟩ : ∃ p, b1.getLast? = some p := ⟨b1.getLast hb1, List.getLast?_eq_some_getLast hb1⟩
    obtain ⟨q, t2, hq⟩ : ∃ q t2, b2 = q :: t2 := by
      cases b2 with | nil => exact absurd rfl hb2 | cons q t => exact ⟨q, t, rfl⟩
    subst hq
    have hfl : (b1 :: (q :: t2) :: rest).flatten = b1 ++ (q :: (t2 ++ rest.flatten)) := by simp
    rw [hfl] at hs hr
    have hs' := hs
    rw [Sorted, List.pairwise_append] at hs'
    obtain ⟨hs1, hs2, hs12⟩ := hs'
    have hpmem : p ∈ b1 := by
      obtain ⟨ys, h⟩ := List.getLast?_eq_some_iff.mp hp
      rw [h]; simp
    have hqL2 : q ∈ q :: (t2 ++ rest.flatten) := List.mem_cons_self
    have hpq := hs12 p hpmem q hqL2
    obtain ⟨hs_b, hs_a⟩ := sep_between p q hpq
    generalize hsep : q.take (cpl p q + 1) = sep at hs_b hs_a
    have hmax := getLast_max hs1 hp
    have hmin : ∀ a ∈ q :: (t2 ++ rest.flatten), a = q ∨ lexLt q a = true := head_min hs2 (by simp)
    -- the items of the first block are below the separator, the others at or above it
    have hb1lt : ∀ a ∈ b1, lexLt a sep = true := by
      intro a ha
      rcases hmax a ha with rfl | h
      · exact hs_b
      · exact lt_trans' h hs_b
    have hL2ge : ∀ a ∈ q :: (t2 ++ rest.flatten), lexLt a sep = false := by
      intro a ha
      rcases hmin a ha with rfl | h
      · exact hs_a
      · cases h2 : lexLt a sep with
        | false => rfl
        | true => simp [lexLt_asymm _ _ (lt_le_trans h2 hs_a)] at h
    have hr' := List.forall_mem_append.mp hr
    have hrp : ∀ x ∈ b1, inRange l hi x = true := hr'.1
    have hrq : ∀ x ∈ q :: (t2 ++ rest.flatten), inRange l hi x = true := hr'.2
    have hlp : lexLt p l = false := ((inRange_iff _ _ _).mp (hrp p hpmem)).1
    have hql : hiOk hi q = true := ((inRange_iff _ _ _).mp (hrq q hqL2)).2
    have hr2 : ∀ x ∈ q :: (t2 ++ rest.flatten), inRange sep hi x = true := fun x hx =>
      (inRange_iff _ _ _).mpr ⟨hL2ge x hx, ((inRange_iff _ _ _).mp (hrq x hx)).2⟩
    have hflat : ((q :: t2) :: rest).flatten = q :: (t2 ++ rest.flatten) := by simp
    have ih := ivs_props hi ((q :: t2) :: rest) sep (by simp)
      (fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hb
        · simp
        · exact hrest b hb)
      (by rw [hflat]; exact hs2) (by rw [hflat]; exact hr2)
    rw [hflat] at ih
    obtain ⟨ia, id', ib, ic, ie⟩ := ih
    have hiv : ivsOf hi l (b1 :: (q :: t2) :: rest) =
        ⟨l, some sep⟩ :: ivsOf hi sep ((q :: t2) :: rest) := by simp [ivsOf, hp, hsep]
    rw [hiv]
    have hJ1 : ∀ z, (Iv.mk l (some sep)).has z = true ↔ lexLt z l = false ∧ lexLt z sep = true := by
      intro z; simp [Iv.has, inRange]
    have hD : ∀ J ∈ ivsOf hi sep ((q :: t2) :: rest), ∀ z, J.has z = true → lexLt z sep = false := by
      intro J hJ z hz
      exact ((inRange_iff _ _ _).mp (id' J hJ z hz)).1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨hz1, hz2⟩ := (inRange_iff _ _ _).mp hz
      by_cases hzs : lexLt z sep = true
      · exact ⟨⟨l, some sep⟩, List.mem_cons_self, (hJ1 z).mpr ⟨hz1, hzs⟩⟩
      · have hzs' : lexLt z sep = false := by simpa using hzs
        obtain ⟨J, hJ, hJz⟩ := ia z ((inRange_iff _ _ _).mpr ⟨hzs', hz2⟩)
        exact ⟨J, List.mem_cons_of_mem _ hJ, hJz⟩
    · intro J hJ z hz
      rcases List.mem_cons.mp hJ with rfl | hJ
      · obtain ⟨h1, h2⟩ := (hJ1 z).mp hz
        refine (inRange_iff _ _ _).mpr ⟨h1, ?_⟩
        exact hiOk_le hql (lexLt_asymm _ _ (lt_le_trans h2 hs_a))
      · have hzs := hD J hJ z hz
        obtain ⟨_, h2⟩ := (inRange_iff _ _ _).mp (id' J hJ z hz)
        refine (inRange_iff _ _ _).mpr ⟨?_, h2⟩
        cases h : lexLt z l with
        | false => rfl
        | true =>
          have h3 := lt_le_trans h hlp
          have h4 := lt_le_trans hs_b hzs
          simp [lexLt_asymm _ _ h3] at h4
    · rw [List.pairwise_cons]
      refine ⟨fun K hK z hz => ?_, ib⟩
      have h1 := ((hJ1 z).mp hz).2
      cases h : K.has z with
      | false => rfl
      | true => have := hD K hK z h; simp [h1] at this
    · have hfl2 : (b1 :: (q :: t2) :: rest).flatten = b1 ++ (q :: (t2 ++ rest.flatten)) := by simp
      rw [hfl2, List.map_cons]
      have e1 : (Iv.mk l (some sep)).items (b1 ++ (q :: (t2 ++ rest.flatten))) = b1 := by
        unfold Iv.items
        rw [List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr, List.append_nil]
        · intro a ha; simp [hJ1, hL2ge a ha]
        · intro a ha
          have := (inRange_iff _ _ _).mp (hrp a ha)
          simp [hJ1, this.1, hb1lt a ha]
      have e2 : (ivsOf hi sep ((q :: t2) :: rest)).map (fun J => J.items (b1 ++ (q :: (t2 ++ rest.flatten)))) =
          (q :: t2) :: rest := by
        refine Eq.trans (List.map_congr_left ?_) ic
        intro J hJ
        unfold Iv.items
        rw [List.filter_append, List.filter_eq_nil_iff.mpr, List.nil_append]
        intro a ha
        have := hD J hJ a
        cases h : J.has a with
        | false => simp
        | true => have := this h; simp [hb1lt a ha] at this
      rw [e1, e2]
    · simp [ie]


/-! ## The split -/

theorem Sorted.filter' {S : List Item} (h : Sorted S) (p : Item → Bool) : Sorted (S.filter p) :=
  List.Pairwise.sublist List.filter_sublist h

theorem stepOf_pos (c fan : Nat) : 1 ≤ stepOf c fan := by unfold stepOf; omega

theorem stepOf_lt {c fan : Nat} (hc : 2 ≤ c) (hf : 2 ≤ fan) : stepOf c fan < c := by
  unfold stepOf
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  have h1 : fan * k ≥ 2 * k := Nat.mul_le_mul_right _ hf
  have h2 : (k + 1 + fan - 1) / fan < k + 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_succ]; omega)
  omega

theorem stepOf_cover (c fan : Nat) (hf : 1 ≤ fan) : c ≤ fan * stepOf c fan := by
  unfold stepOf
  have h1 := Nat.div_add_mod (c + fan - 1) fan
  have h2 : (c + fan - 1) % fan < fan := Nat.mod_lt _ (by omega)
  have h3 : fan * ((c + fan - 1) / fan) ≤ fan * max 1 ((c + fan - 1) / fan) :=
    Nat.mul_le_mul_left _ (Nat.le_max_right _ _)
  omega

theorem items_of_sub {T : List Item} {I J : Iv} (h : ∀ z, J.has z = true → I.has z = true) :
    J.items T = J.items (I.items T) := by
  unfold Iv.items
  rw [List.filter_filter]
  symm
  apply List.filter_congr
  intro z _
  cases hj : J.has z with
  | false => simp
  | true => simp [h z hj]

/-- The specification of a split of a sorted receiver set `T` over the interval `I` into `fan` parts. -/
theorem splitIvs_spec {T : List Item} (hT : Sorted T) (I : Iv) {fan : Nat} (hf : 2 ≤ fan)
    (hc : 2 ≤ cnt T I) :
    (∀ z, I.has z = true → ∃ J ∈ splitIvs T I fan, J.has z = true) ∧
    (∀ J ∈ splitIvs T I fan, ∀ z, J.has z = true → I.has z = true) ∧
    (splitIvs T I fan).Pairwise (fun J K => ∀ z, J.has z = true → K.has z = false) ∧
    (splitIvs T I fan).length ≤ fan ∧
    (∀ J ∈ splitIvs T I fan, cnt T J ≤ stepOf (cnt T I) fan) ∧
    (∀ J ∈ splitIvs T I fan, cnt T J < cnt T I) := by
  have hL : Sorted (I.items T) := hT.filter' _
  have hrange : ∀ x ∈ (blocksOf T I fan).flatten, inRange I.lo I.hi x = true := by
    intro x hx
    unfold blocksOf at hx
    rw [chunkBy_join _ _ _ (Nat.le_refl _) (stepOf_pos _ _)] at hx
    exact (List.mem_filter.mp hx).2
  have hflat : (blocksOf T I fan).flatten = I.items T := by
    unfold blocksOf; exact chunkBy_join _ _ _ (Nat.le_refl _) (stepOf_pos _ _)
  have hne : blocksOf T I fan ≠ [] := by
    intro h
    have : (I.items T).length = 0 := by rw [← hflat, h]; rfl
    unfold cnt at hc; omega
  have hb : ∀ b ∈ blocksOf T I fan, b ≠ [] := chunkBy_ne _ (stepOf_pos _ _) _ _
  obtain ⟨a, d, b, c, e⟩ := ivs_props I.hi (blocksOf T I fan) I.lo hne hb (by rw [hflat]; exact hL) hrange
  rw [hflat] at c
  have hsub : ∀ J ∈ splitIvs T I fan, ∀ z, J.has z = true → I.has z = true := d
  have hitems : ∀ J ∈ splitIvs T I fan, J.items T ∈ blocksOf T I fan := by
    intro J hJ
    rw [items_of_sub (hsub J hJ)]
    rw [← c]
    exact List.mem_map.mpr ⟨J, hJ, rfl⟩
  refine ⟨a, hsub, b, ?_, ?_, ?_⟩
  · unfold splitIvs; rw [e]
    unfold blocksOf
    exact chunkBy_count _ (stepOf_pos _ _) _ _ _ (Nat.le_refl _) (by unfold cnt at *; exact stepOf_cover _ _ (by omega))
  · intro J hJ
    exact chunkBy_len _ _ _ _ (hitems J hJ)
  · intro J hJ
    have := chunkBy_len _ _ _ _ (hitems J hJ)
    have h2 := stepOf_lt hc hf
    unfold cnt at *
    omega

theorem cnt_mono {T : List Item} {I J : Iv} (h : ∀ z, J.has z = true → I.has z = true) : cnt T J ≤ cnt T I := by
  unfold cnt
  rw [items_of_sub (T := T) h]
  exact List.length_filter_le _ _

end Pinc.Reconcile
