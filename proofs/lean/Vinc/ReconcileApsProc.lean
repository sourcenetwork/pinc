import Vinc.ReconcileApsModel

/-!
# Reconcile APS, part 3: what one `Proc` step does

Facts about a single part-processing step, used by the invariants (ReconcileApsSafe) and the potentials
(ReconcileApsCost):

* `Proc.facts`: the new parts are pairwise disjoint sub-intervals of the processed one (its first two conjuncts); the
  arenas only grow by items of the processed interval, and only when no part is left over (the third and fourth);
* `Proc.safe_adds`: what is added is safe whatever the id function: `here` gets items of `B` that `A` lacks, `there`
  items of `A`, each once;
* `Proc.cover` (needs `Indep`): in a lossless step (not an ids part) every difference item of the interval is
  added or lies in a new part;
* `aps_ids_exact_of_inj`: if the id function is injective on the leaf's items, the ids reply is the exact merge.
-/

namespace Vinc.Reconcile

def Iv.Disj (I J : Iv) : Prop := ∀ z, I.has z = true → J.has z = false

theorem Iv.Disj.symm {I J : Iv} (h : I.Disj J) : J.Disj I := by
  intro z hz
  cases hi : I.has z with
  | false => rfl
  | true => have := h z hi; simp [hz] at this

def WF (p : Part) : Prop := (p.kind = .ids → p.toInit = false) ∧ (∀ v, p.kind = .reply v → p.toInit = true)

theorem mem_items {T : List Item} {I : Iv} {x : Item} : x ∈ I.items T ↔ x ∈ T ∧ I.has x = true := by
  simp [Iv.items]

theorem items_nodup {T : List Item} (hT : Sorted T) (I : Iv) : (I.items T).Nodup := (hT.filter' _).nodup

theorem two_le_of_no_leaf (c : Cfg) {toInit : Bool} {I : Iv} {it : Bool}
    (hno : ¬ (cnt (c.set toInit) I ≤ leafOf toInit ∧ c.fits toInit it I)) : 2 ≤ cnt (c.set toInit) I := by
  refine Decidable.byContradiction (fun h => ?_)
  apply hno
  have h1 : cnt (c.set toInit) I ≤ 1 := by omega
  refine ⟨?_, c.fits_small toInit it I (by cases toInit <;> simpa [Cfg.set] using h1)⟩
  cases toInit <;> simp [leafOf, aleaf, bleaf] <;> omega

theorem two_le_of_no_leaf' (c : Cfg) {I : Iv} (hno : ¬ (cnt c.B I ≤ aleaf ∧ c.fits false true I)) :
    2 ≤ cnt c.B I := by
  refine Decidable.byContradiction (fun h => ?_)
  apply hno
  exact ⟨by simp [aleaf]; omega, c.fits_small false true I (by simpa using (by omega : cnt c.B I ≤ 1))⟩

theorem two_le_of_no_leaf_top (c : Cfg) (exact : Bool)
    (hno : ¬ (cnt c.A Iv.top ≤ aleaf ∧ c.fits true exact Iv.top)) : 2 ≤ cnt c.A Iv.top := by
  refine Decidable.byContradiction (fun h => ?_)
  apply hno
  exact ⟨by simp [aleaf]; omega, c.fits_small true exact _ (by simpa using (by omega : cnt c.A Iv.top ≤ 1))⟩

/-! ## The sets an exact merge or an ids reply adds -/

theorem Cfg.exactHere_mem (c : Cfg) (I : Iv) (x : Item) :
    x ∈ c.exactHere I ↔ x ∈ c.B ∧ I.has x = true ∧ x ∉ c.A := by
  simp [Cfg.exactHere, mem_items, and_assoc]

theorem Cfg.exactThere_mem (c : Cfg) (I : Iv) (x : Item) :
    x ∈ c.exactThere I ↔ x ∈ c.A ∧ I.has x = true ∧ x ∉ c.B := by
  simp [Cfg.exactThere, mem_items, and_assoc]

theorem Cfg.exactHere_nodup (c : Cfg) (I : Iv) : (c.exactHere I).Nodup :=
  List.Nodup.sublist List.filter_sublist (items_nodup c.hB I)

theorem Cfg.exactThere_nodup (c : Cfg) (I : Iv) : (c.exactThere I).Nodup :=
  List.Nodup.sublist List.filter_sublist (items_nodup c.hA I)

theorem Cfg.idsHere_sub (c : Cfg) (I : Iv) {x : Item} (h : x ∈ c.idsHere I) :
    x ∈ c.B ∧ I.has x = true ∧ x ∉ c.A := by
  unfold Cfg.idsHere at h
  obtain ⟨h1, h2⟩ := List.mem_filter.mp h
  obtain ⟨hB, hI⟩ := mem_items.mp h1
  refine ⟨hB, hI, fun hA => ?_⟩
  have : x ∈ I.items c.A := mem_items.mpr ⟨hA, hI⟩
  have hm : c.o.idf x ∈ c.ids I := List.mem_map.mpr ⟨x, this, rfl⟩
  simp [hm] at h2

theorem Cfg.idsHere_nodup (c : Cfg) (I : Iv) : (c.idsHere I).Nodup :=
  List.Nodup.sublist List.filter_sublist (items_nodup c.hB I)

theorem Cfg.idsThere_sub (c : Cfg) (I : Iv) {x : Item} (h : x ∈ c.idsThere I) : x ∈ c.A ∧ I.has x = true := by
  unfold Cfg.idsThere at h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  have := (List.mem_filter.mp hp).1
  exact mem_items.mp (List.fst_mem_of_mem_zipIdx this)

theorem Cfg.idsThere_nodup (c : Cfg) (I : Iv) : (c.idsThere I).Nodup := by
  unfold Cfg.idsThere
  have hsub : (((I.items c.A).zipIdx.filter (fun p =>
      !((I.items c.B).any (fun x => rposN (c.ids I) (c.o.idf x) == some p.2)))).map (·.1)).Sublist
      ((I.items c.A).zipIdx.map (·.1)) := (List.filter_sublist).map _
  rw [List.zipIdx_map_fst] at hsub
  exact List.Nodup.sublist hsub (items_nodup c.hA I)


theorem split_kids (c : Cfg) (T : List Item) (hT : Sorted T) (I : Iv) {fan : Nat} (hf : 2 ≤ fan) (hf2 : fan ≤ 16)
    (hc : 2 ≤ cnt T I) (side : Bool) (d : Nat) :
    (∀ k ∈ (splitIvs T I fan).map (fun J => (⟨.fp, side, J, d + 1⟩ : Part)), ∀ z, k.iv.has z = true → I.has z = true) ∧
    ((splitIvs T I fan).map (fun J => (⟨.fp, side, J, d + 1⟩ : Part))).Pairwise (fun k l => k.iv.Disj l.iv) ∧
    ((splitIvs T I fan).map (fun J => (⟨.fp, side, J, d + 1⟩ : Part))).length ≤ 16 := by
  obtain ⟨_, hsub, hdisj, hlen, _, _⟩ := splitIvs_spec hT I hf hc
  refine ⟨?_, ?_, ?_⟩
  · intro k hk z hz
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hk
    exact hsub J hJ z hz
  · rw [List.pairwise_map]; exact hdisj
  · simp; omega

/-- What one step does to the parts and the arenas. -/
theorem Proc.facts {c : Cfg} {ex : Bool} {p : Part} {kids : List Part} {ha ta : List Item} {lf : Bool}
    (hp : Proc c ex p kids ha ta lf) :
    (∀ k ∈ kids, ∀ z, k.iv.has z = true → p.iv.has z = true) ∧
    kids.Pairwise (fun k l => k.iv.Disj l.iv) ∧
    (∀ x ∈ ha ++ ta, p.iv.has x = true) ∧
    (kids ≠ [] → ha = [] ∧ ta = []) ∧
    (∀ k ∈ kids, WF k) ∧ kids.length ≤ 16 ∧ (∀ k ∈ kids, k.d = p.d + 1) := by
  have hmin := c.hmin
  cases hp with
  | fpEq h => simp
  | fpLeafResp hne hcnt hf =>
    refine ⟨?_, by simp, by simp, by simp, ?_, by simp, by simp⟩
    · simp
    · simp [WF]
  | fpLeafInit hne hcnt hf =>
    refine ⟨?_, by simp, by simp, by simp, ?_, by simp, by simp⟩
    · simp
    · cases ex <;> simp [WF]
  | fpSplit hne hno hf1 hf2 =>
    obtain ⟨h1, h2, h3⟩ := split_kids c _ (by cases ‹Bool› <;> simp [Cfg.set, c.hA, c.hB]) _ (by omega) hf2
      (two_le_of_no_leaf c hno) _ _
    refine ⟨h1, h2, by simp, by simp, ?_, h3, ?_⟩
    · intro k hk; obtain ⟨J, _, rfl⟩ := List.mem_map.mp hk; simp [WF]
    · intro k hk; obtain ⟨J, _, rfl⟩ := List.mem_map.mp hk; rfl
  | respLeaf hk hcnt hf =>
    refine ⟨by simp, by simp, by simp, by simp, ?_, by simp, by simp⟩
    · simp [WF]
  | respNarrow hk hno hf1 hf2 =>
    obtain ⟨h1, h2, h3⟩ := split_kids c _ c.hB _ (by omega) hf2 (two_le_of_no_leaf' c hno) true _
    refine ⟨h1, h2, by simp, by simp, ?_, h3, ?_⟩
    · intro k hk; obtain ⟨J, _, rfl⟩ := List.mem_map.mp hk; simp [WF]
    · intro k hk; obtain ⟨J, _, rfl⟩ := List.mem_map.mp hk; rfl
  | fullInit =>
    refine ⟨by simp, by simp, ?_, by simp, by simp, by simp, by simp⟩
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact ((c.exactHere_mem _ _).mp h).2.1
    · exact ((c.exactThere_mem _ _).mp h).2.1
  | replyExact =>
    refine ⟨by simp, by simp, ?_, by simp, by simp, by simp, by simp⟩
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact ((c.exactHere_mem _ _).mp h).2.1
    · exact ((c.exactThere_mem _ _).mp h).2.1
  | replyIds =>
    refine ⟨by simp, by simp, ?_, by simp, by simp, by simp, by simp⟩
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact (c.idsHere_sub _ h).2.1
    · exact (c.idsThere_sub _ h).2

/-- What is added is safe whatever the id function. -/
theorem Proc.safe_adds {c : Cfg} {ex : Bool} {p : Part} {kids : List Part} {ha ta : List Item} {lf : Bool}
    (hp : Proc c ex p kids ha ta lf) :
    (∀ x ∈ ha, x ∈ c.B ∧ x ∉ c.A) ∧ (∀ x ∈ ta, x ∈ c.A) ∧ ha.Nodup ∧ ta.Nodup := by
  cases hp with
  | fullInit =>
    exact ⟨fun x hx => ⟨((c.exactHere_mem _ _).mp hx).1, ((c.exactHere_mem _ _).mp hx).2.2⟩,
      fun x hx => ((c.exactThere_mem _ _).mp hx).1, c.exactHere_nodup _, c.exactThere_nodup _⟩
  | replyExact =>
    exact ⟨fun x hx => ⟨((c.exactHere_mem _ _).mp hx).1, ((c.exactHere_mem _ _).mp hx).2.2⟩,
      fun x hx => ((c.exactThere_mem _ _).mp hx).1, c.exactHere_nodup _, c.exactThere_nodup _⟩
  | replyIds =>
    exact ⟨fun x hx => ⟨(c.idsHere_sub _ hx).1, (c.idsHere_sub _ hx).2.2⟩,
      fun x hx => (c.idsThere_sub _ hx).1, c.idsHere_nodup _, c.idsThere_nodup _⟩
  | _ => simp


theorem split_cover (c : Cfg) (T : List Item) (hT : Sorted T) (I : Iv) {fan : Nat} (hf : 2 ≤ fan)
    (hc : 2 ≤ cnt T I) (side : Bool) (d : Nat) (x : Item) (hx : I.has x = true) :
    ∃ k ∈ (splitIvs T I fan).map (fun J => (⟨.fp, side, J, d + 1⟩ : Part)), k.iv.has x = true := by
  obtain ⟨J, hJ, hJx⟩ := (splitIvs_spec hT I hf hc).1 x hx
  exact ⟨⟨.fp, side, J, d + 1⟩, List.mem_map.mpr ⟨J, hJ, rfl⟩, hJx⟩

/-- A lossless step loses no difference item: with independent hashes, a difference item of the processed interval is
added or lies in a new part, unless the part is an ids reply. -/
theorem Proc.cover {c : Cfg} {ex : Bool} {p : Part} {kids : List Part} {ha ta : List Item} {lf : Bool}
    (hI : Indep c.o) (hp : Proc c ex p kids ha ta lf) (hk : p.kind ≠ .reply true)
    (x : Item) (hx : p.iv.has x = true) :
    (x ∈ c.B → x ∉ c.A → x ∈ ha ∨ ∃ k ∈ kids, k.iv.has x = true) ∧
    (x ∈ c.A → x ∉ c.B → x ∈ ta ∨ ∃ k ∈ kids, k.iv.has x = true) := by
  have hmin := c.hmin
  cases hp with
  | fpEq h =>
    have := fp_inj hI (items_nodup c.hA _) (items_nodup c.hB _) h x
    refine ⟨fun hB hA => ?_, fun hA hB => ?_⟩
    · exact absurd (mem_items.mp (this.mpr (mem_items.mpr ⟨hB, hx⟩))).1 hA
    · exact absurd (mem_items.mp (this.mp (mem_items.mpr ⟨hA, hx⟩))).1 hB
  | fpLeafResp hne hcnt hf => exact ⟨fun _ _ => Or.inr ⟨_, List.mem_singleton_self _, hx⟩, fun _ _ => Or.inr ⟨_, List.mem_singleton_self _, hx⟩⟩
  | fpLeafInit hne hcnt hf => exact ⟨fun _ _ => Or.inr ⟨_, List.mem_singleton_self _, hx⟩, fun _ _ => Or.inr ⟨_, List.mem_singleton_self _, hx⟩⟩
  | @fpSplit d toInit I fan hne hno hf1 hf2 =>
    have hc := two_le_of_no_leaf c hno
    obtain ⟨k, hk', hkx⟩ := split_cover c _ (by cases toInit <;> simp [Cfg.set, c.hA, c.hB]) I (fan := fan) (by omega) hc (!toInit) d x hx
    exact ⟨fun _ _ => Or.inr ⟨k, hk', hkx⟩, fun _ _ => Or.inr ⟨k, hk', hkx⟩⟩
  | respLeaf hk hcnt hf => exact ⟨fun _ _ => Or.inr ⟨_, List.mem_singleton_self _, hx⟩, fun _ _ => Or.inr ⟨_, List.mem_singleton_self _, hx⟩⟩
  | @respNarrow d I k0 fan hk hno hf1 hf2 =>
    obtain ⟨k, hk', hkx⟩ := split_cover c _ c.hB I (fan := fan) (by omega) (two_le_of_no_leaf' c hno) true d x hx
    exact ⟨fun _ _ => Or.inr ⟨k, hk', hkx⟩, fun _ _ => Or.inr ⟨k, hk', hkx⟩⟩
  | fullInit =>
    exact ⟨fun hB hA => Or.inl ((c.exactHere_mem _ _).mpr ⟨hB, hx, hA⟩),
      fun hA hB => Or.inl ((c.exactThere_mem _ _).mpr ⟨hA, hx, hB⟩)⟩
  | replyExact =>
    exact ⟨fun hB hA => Or.inl ((c.exactHere_mem _ _).mpr ⟨hB, hx, hA⟩),
      fun hA hB => Or.inl ((c.exactThere_mem _ _).mpr ⟨hA, hx, hB⟩)⟩
  | replyIds => exact absurd rfl hk

end Vinc.Reconcile
