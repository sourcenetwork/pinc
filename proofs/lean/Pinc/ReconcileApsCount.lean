import Pinc.ReconcileApsSession

/-!
# Reconcile APS, part 6: logarithms, sums and the difference of an interval

* `lg f n`: the number of times `n` can be divided by `f` (rounding up) before it is at most 1, the smallest `k` with
  `n <= f^k`; `lg_dec`: a split by a fan of at least `f` lowers it by one (the depth argument), `lg_mono`.
* `lsum`: a sum over a list (kept elementary so the proofs stay in this package).
* `Cfg.delta c I`: the number of items of the symmetric difference in `I`; `delta_sum_le`: over pairwise disjoint
  sub-intervals the deltas add up to at most the delta of the interval (so, at one level of the part tree, the differing
  intervals are at most the difference in number), `delta_pos_of_not_fpEq`: intervals whose fingerprints differ hold a
  difference item.
-/

namespace Pinc.Reconcile

theorem ceil_lt {n f : Nat} (hn : 2 ≤ n) (hf : 2 ≤ f) : (n + f - 1) / f < n := by
  have := stepOf_lt hn hf
  unfold stepOf at this; omega

/-- `lg f n`: the smallest `k` with `n <= f^k`. -/
def lg (f n : Nat) : Nat :=
  if h : 2 ≤ n ∧ 2 ≤ f then lg f ((n + f - 1) / f) + 1 else 0
termination_by n
decreasing_by exact ceil_lt h.1 h.2

theorem lg_small {f n : Nat} (h : n < 2) : lg f n = 0 := by
  rw [lg]; simp; omega

theorem lg_step {f n : Nat} (hn : 2 ≤ n) (hf : 2 ≤ f) : lg f n = lg f ((n + f - 1) / f) + 1 := by
  rw [lg]; simp [hn, hf]

theorem lg_mono {f : Nat} (hf : 2 ≤ f) : ∀ n m, m ≤ n → lg f m ≤ lg f n
  | n, m, h => by
    by_cases hm : 2 ≤ m
    · have hn : 2 ≤ n := by omega
      rw [lg_step hm hf, lg_step hn hf]
      have := lg_mono hf ((n + f - 1) / f) ((m + f - 1) / f) (Nat.div_le_div_right (by omega))
      omega
    · rw [lg_small (by omega)]; omega
termination_by n => n
decreasing_by exact ceil_lt (by omega) hf

theorem ceil_anti {c f fan : Nat} (hf : 1 ≤ f) (hfan : f ≤ fan) : (c + fan - 1) / fan ≤ (c + f - 1) / f := by
  have h1 := Nat.div_add_mod (c + f - 1) f
  have h2 : (c + f - 1) % f < f := Nat.mod_lt _ (by omega)
  have h3 : (c + f - 1) / f * f ≤ (c + f - 1) / f * fan := Nat.mul_le_mul_left _ hfan
  have h4 : (c + fan - 1) / fan < (c + f - 1) / f + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega), Nat.add_mul]
    rw [Nat.mul_comm f] at h1
    omega
  omega

/-- A split by a fan of at least `f` lowers `lg f` of the splitter's count by one. -/
theorem lg_dec {f fan c c' : Nat} (hf : 2 ≤ f) (hfan : f ≤ fan) (hc : 2 ≤ c) (hc' : c' ≤ stepOf c fan) :
    lg f c' + 1 ≤ lg f c := by
  rw [lg_step hc hf]
  have h1 : 1 ≤ (c + fan - 1) / fan := by
    rw [Nat.le_div_iff_mul_le (by omega)]; omega
  have h2 : stepOf c fan ≤ (c + f - 1) / f := by
    unfold stepOf; have := ceil_anti (c := c) (by omega) hfan; omega
  have := lg_mono hf _ _ (Nat.le_trans hc' h2)
  omega

/-! ## Sums -/

def lsum {α : Type} (g : α → Nat) : List α → Nat
  | [] => 0
  | a :: l => g a + lsum g l

theorem lsum_le {α : Type} {g h : α → Nat} : ∀ l : List α, (∀ a ∈ l, g a ≤ h a) → lsum g l ≤ lsum h l
  | [], _ => Nat.le_refl _
  | a :: l, hl => by
    simp only [lsum]
    have := hl a (List.mem_cons_self)
    have := lsum_le l (fun b hb => hl b (List.mem_cons_of_mem _ hb))
    omega

theorem lsum_add {α : Type} {g h : α → Nat} : ∀ l : List α, lsum (fun a => g a + h a) l = lsum g l + lsum h l
  | [] => rfl
  | a :: l => by simp only [lsum]; rw [lsum_add l]; omega

theorem lsum_const {α : Type} (k : Nat) : ∀ l : List α, lsum (fun _ => k) l = l.length * k
  | [] => by simp [lsum]
  | a :: l => by simp only [lsum, List.length_cons]; rw [lsum_const k l, Nat.succ_mul]; omega

theorem lsum_mul {α : Type} (g : α → Nat) (k : Nat) : ∀ l : List α, lsum (fun a => k * g a) l = k * lsum g l
  | [] => by simp [lsum]
  | a :: l => by simp only [lsum]; rw [lsum_mul g k l, Nat.mul_add]

theorem lsum_map {α β : Type} (f : α → β) (g : β → Nat) : ∀ l : List α, lsum g (l.map f) = lsum (fun a => g (f a)) l
  | [] => rfl
  | a :: l => by simp only [List.map_cons, lsum]; rw [lsum_map f g l]

theorem lsum_append {α : Type} (g : α → Nat) : ∀ l m : List α, lsum g (l ++ m) = lsum g l + lsum g m
  | [], m => by simp [lsum]
  | a :: l, m => by simp only [List.cons_append, lsum]; rw [lsum_append g l m]; omega

theorem lsum_perm {α : Type} (g : α → Nat) {l m : List α} (h : l.Perm m) : lsum g l = lsum g m := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [lsum]; rw [ih]
  | swap a b l => simp only [lsum]; omega
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

/-! ## The difference inside an interval -/

/-- The items of the symmetric difference of `A` and `B`, and their number. -/
def Cfg.dl (c : Cfg) : List Item := c.A.filter (fun x => !c.B.contains x) ++ c.B.filter (fun x => !c.A.contains x)

def Cfg.diff (c : Cfg) : Nat := c.dl.length

def Cfg.delta (c : Cfg) (I : Iv) : Nat := (c.exactHere I).length + (c.exactThere I).length

theorem Cfg.delta_eq (c : Cfg) (I : Iv) : c.delta I = (c.dl.filter I.has).length := by
  unfold Cfg.delta Cfg.dl Cfg.exactHere Cfg.exactThere Iv.items
  rw [List.filter_append, List.length_append, Nat.add_comm]
  congr 1 <;> (rw [List.filter_filter, List.filter_filter]; congr 1; apply List.filter_congr; intro x _; simp [Bool.and_comm])

theorem Cfg.delta_top (c : Cfg) : c.delta Iv.top = c.diff := by
  rw [Cfg.delta_eq]
  unfold Cfg.diff
  rw [List.filter_eq_self.mpr (fun x _ => Iv.top_has x)]

theorem Cfg.delta_mono (c : Cfg) {I J : Iv} (h : ∀ z, J.has z = true → I.has z = true) : c.delta J ≤ c.delta I := by
  rw [Cfg.delta_eq, Cfg.delta_eq]
  have : c.dl.filter J.has = (c.dl.filter I.has).filter J.has := by
    rw [List.filter_filter]; apply List.filter_congr; intro z _
    cases hj : J.has z <;> simp [h z, hj]
  rw [this]; exact List.length_filter_le _ _

theorem Cfg.delta_pos_of_not_fpEq (c : Cfg) {I : Iv} (h : ¬ c.fpEq I) : 1 ≤ c.delta I := by
  refine Decidable.byContradiction (fun hz => ?_)
  apply h
  have h0 : c.delta I = 0 := by omega
  unfold Cfg.delta at h0
  have e1 : c.exactHere I = [] := List.length_eq_zero_iff.mp (by omega)
  have e2 : c.exactThere I = [] := List.length_eq_zero_iff.mp (by omega)
  unfold Cfg.fpEq
  suffices hp : (I.items c.A).Perm (I.items c.B) by rw [sumH_perm hp, hp.length_eq]
  rw [List.perm_ext_iff_of_nodup (items_nodup c.hA I) (items_nodup c.hB I)]
  intro x
  constructor
  · intro hx
    have hx' := mem_items.mp hx
    refine Decidable.byContradiction (fun hn => ?_)
    have : x ∈ c.exactThere I := (c.exactThere_mem I x).mpr ⟨hx'.1, hx'.2, fun hb => hn (mem_items.mpr ⟨hb, hx'.2⟩)⟩
    rw [e2] at this; simp at this
  · intro hx
    have hx' := mem_items.mp hx
    refine Decidable.byContradiction (fun hn => ?_)
    have : x ∈ c.exactHere I := (c.exactHere_mem I x).mpr ⟨hx'.1, hx'.2, fun ha => hn (mem_items.mpr ⟨ha, hx'.2⟩)⟩
    rw [e1] at this; simp at this

theorem sum_has_le_one (z : Item) : ∀ Js : List Iv, Js.Pairwise (fun J K => ∀ w, J.has w = true → K.has w = false) →
    lsum (fun J => if J.has z = true then 1 else 0) Js ≤ 1
  | [], _ => by simp [lsum]
  | J :: Js, h => by
    rw [List.pairwise_cons] at h
    simp only [lsum]
    by_cases hz : J.has z = true
    · have : lsum (fun J => if J.has z = true then 1 else 0) Js = 0 := by
        have : ∀ K ∈ Js, (if K.has z = true then 1 else 0) = 0 := by
          intro K hK; have := h.1 K hK z hz; simp [this]
        have h2 := lsum_le (g := fun J => if J.has z = true then 1 else 0) (h := fun _ => 0) Js
          (fun K hK => Nat.le_of_eq (this K hK))
        have h3 := lsum_const (α := Iv) 0 Js
        simp at h3; omega
      simp [hz, this]
    · have := sum_has_le_one z Js h.2
      simp [hz]; exact this

theorem sum_has_zero (z : Item) (I : Iv) (hz : I.has z = false) (Js : List Iv)
    (hsub : ∀ J ∈ Js, ∀ w, J.has w = true → I.has w = true) :
    lsum (fun J => if J.has z = true then 1 else 0) Js = 0 := by
  have : ∀ K ∈ Js, (if K.has z = true then 1 else 0) = 0 := by
    intro K hK
    cases hk : K.has z with
    | false => simp
    | true => have := hsub K hK z hk; rw [hz] at this; simp at this
  have h2 := lsum_le (g := fun J => if J.has z = true then 1 else 0) (h := fun _ => 0) Js
    (fun K hK => Nat.le_of_eq (this K hK))
  have h3 := lsum_const (α := Iv) 0 Js
  simp at h3; omega

/-- Over pairwise disjoint sub-intervals the counts of any list add up to at most the count in the interval. -/
theorem count_sum_le (I : Iv) (Js : List Iv)
    (hd : Js.Pairwise (fun J K => ∀ w, J.has w = true → K.has w = false))
    (hsub : ∀ J ∈ Js, ∀ w, J.has w = true → I.has w = true) :
    ∀ Dl : List Item, lsum (fun J => (Dl.filter J.has).length) Js ≤ (Dl.filter I.has).length
  | [] => by
    have := lsum_const (α := Iv) 0 Js
    simp [lsum] at this ⊢
    simp [List.filter_nil, this]
  | z :: Dl => by
    have ih := count_sum_le I Js hd hsub Dl
    have e : lsum (fun J => ((z :: Dl).filter J.has).length) Js =
        lsum (fun J => (if J.has z = true then 1 else 0) + (Dl.filter J.has).length) Js := by
      apply Nat.le_antisymm <;> apply lsum_le <;> intro J _ <;> by_cases hz : J.has z = true <;>
        simp [List.filter_cons, hz] <;> omega
    rw [e, lsum_add]
    have hr : ((z :: Dl).filter I.has).length = (if I.has z = true then 1 else 0) + (Dl.filter I.has).length := by
      by_cases hz : I.has z = true <;> simp [List.filter_cons, hz] <;> omega
    by_cases hz : I.has z = true
    · have := sum_has_le_one z Js hd
      simp only [hz, ite_true] at hr
      omega
    · have hz' : I.has z = false := by simpa using hz
      have := sum_has_zero z I hz' Js hsub
      simp only [hz, if_false] at hr
      omega

/-- The deltas of pairwise disjoint sub-intervals add up to at most the delta of the interval. -/
theorem Cfg.delta_sum_le (c : Cfg) (I : Iv) (Js : List Iv)
    (hd : Js.Pairwise (fun J K => ∀ w, J.has w = true → K.has w = false))
    (hsub : ∀ J ∈ Js, ∀ w, J.has w = true → I.has w = true) :
    lsum (fun J => c.delta J) Js ≤ c.delta I := by
  have := count_sum_le I Js hd hsub c.dl
  rw [c.delta_eq I]
  have e : lsum (fun J => c.delta J) Js = lsum (fun J => (c.dl.filter J.has).length) Js := by
    apply Nat.le_antisymm <;> apply lsum_le <;> intro J _ <;> rw [c.delta_eq]; all_goals exact Nat.le_refl _
  rw [e]; exact this

end Pinc.Reconcile
