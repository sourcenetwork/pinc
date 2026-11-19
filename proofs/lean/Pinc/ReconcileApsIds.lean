import Pinc.ReconcileApsBounds

/-!
# Reconcile APS, part 9: the ids leaf

`aps_ids_exact_of_inj`: when the id function is injective on the items of a leaf interval, the reply to an ids part
(`idsHere`, `idsThere`: the `rposition` of the ids, the bitmap, the extras) is the exact merge of the interval. With
arbitrary ids the reply is only safe (`Proc.safe_adds`), and the final check does the rest (`aps_session_exact`).
-/

namespace Pinc.Reconcile

theorem nodup_idx {l : List Nat} (h : l.Nodup) {i j v : Nat} (h1 : l[i]? = some v) (h2 : l[j]? = some v) :
    i = j := by
  obtain ⟨hi, e1⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨hj, e2⟩ := List.getElem?_eq_some_iff.mp h2
  exact (List.Nodup.getElem_inj h).mp (e1.trans e2.symm)

theorem nodup_map_on {α : Type} {l : List α} {f : α → Nat} (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y)
    (h : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih (fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) h.2⟩
    rintro ⟨b, hb, e⟩
    exact h.1 (hf b (List.mem_cons_of_mem _ hb) a List.mem_cons_self e ▸ hb)

theorem rposN_some {ids : List Nat} {v j : Nat} (h : rposN ids v = some j) : ids[j]? = some v := by
  unfold rposN at h
  obtain ⟨q, hq, hj⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hq
  have hmem : q ∈ ids.zipIdx.filter (fun p => p.1 == v) := by rw [hys]; simp
  obtain ⟨h1, h2⟩ := List.mem_filter.mp hmem
  have := List.mem_zipIdx_iff_getElem?.mp h1
  have hv : q.1 = v := by simpa using h2
  rw [← hj, ← hv]; exact this

theorem rposN_of {ids : List Nat} (hn : ids.Nodup) {v j : Nat} (h : ids[j]? = some v) : rposN ids v = some j := by
  unfold rposN
  have hmem : (v, j) ∈ ids.zipIdx.filter (fun p => p.1 == v) :=
    List.mem_filter.mpr ⟨List.mem_zipIdx_iff_getElem?.mpr h, by simp⟩
  have hne : ids.zipIdx.filter (fun p => p.1 == v) ≠ [] := List.ne_nil_of_mem hmem
  rw [List.getLast?_eq_some_getLast hne]
  have hl := List.getLast_mem hne
  obtain ⟨h1, h2⟩ := List.mem_filter.mp hl
  have h3 := List.mem_zipIdx_iff_getElem?.mp h1
  have hv : ((ids.zipIdx.filter (fun p => p.1 == v)).getLast hne).1 = v := by simpa using h2
  rw [hv] at h3
  have e : ((ids.zipIdx.filter (fun p => p.1 == v)).getLast hne).2 = j := nodup_idx hn h3 h
  rw [Option.map_some, e]

theorem aps_ids_exact_of_inj (c : Cfg) (I : Iv)
    (hinj : ∀ x ∈ I.items c.A ++ I.items c.B, ∀ y ∈ I.items c.A ++ I.items c.B, c.o.idf x = c.o.idf y → x = y) :
    (∀ x, x ∈ c.idsHere I ↔ x ∈ c.exactHere I) ∧ (∀ x, x ∈ c.idsThere I ↔ x ∈ c.exactThere I) := by
  have hA : ∀ x ∈ I.items c.A, ∀ y ∈ I.items c.A, c.o.idf x = c.o.idf y → x = y := fun x hx y hy =>
    hinj x (List.mem_append_left _ hx) y (List.mem_append_left _ hy)
  have hnd : (c.ids I).Nodup := nodup_map_on hA (items_nodup c.hA I)
  constructor
  · intro x
    rw [Cfg.exactHere_mem]
    unfold Cfg.idsHere
    rw [List.mem_filter, mem_items]
    constructor
    · rintro ⟨⟨hB, hh⟩, hc⟩
      refine ⟨hB, hh, fun hxA => ?_⟩
      have : (c.ids I).contains (c.o.idf x) = true :=
        List.contains_iff_mem.mpr (List.mem_map.mpr ⟨x, mem_items.mpr ⟨hxA, hh⟩, rfl⟩)
      rw [this] at hc; exact absurd hc (by simp)
    · rintro ⟨hB, hh, hnA⟩
      refine ⟨⟨hB, hh⟩, ?_⟩
      cases hcon : (c.ids I).contains (c.o.idf x) with
      | false => rfl
      | true =>
        obtain ⟨a, ha, hax⟩ := List.mem_map.mp (List.contains_iff_mem.mp hcon)
        have := hinj a (List.mem_append_left _ ha) x (List.mem_append_right _ (mem_items.mpr ⟨hB, hh⟩)) hax
        subst this
        exact absurd (mem_items.mp ha).1 hnA
  · intro x
    rw [Cfg.exactThere_mem]
    unfold Cfg.idsThere
    rw [List.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
      have hqa := mem_items.mp (List.fst_mem_of_mem_zipIdx hq1)
      refine ⟨hqa.1, hqa.2, fun hB => ?_⟩
      have hj := List.mem_zipIdx_iff_getElem?.mp hq1
      have hids : (c.ids I)[q.2]? = some (c.o.idf q.1) := by
        unfold Cfg.ids; rw [List.getElem?_map, hj]; rfl
      have hr := rposN_of hnd hids
      have : (I.items c.B).any (fun y => rposN (c.ids I) (c.o.idf y) == some q.2) = true := by
        rw [List.any_eq_true]
        exact ⟨q.1, mem_items.mpr ⟨hB, hqa.2⟩, by simp [hr]⟩
      simp [this] at hq2
    · rintro ⟨hA', hh, hnB⟩
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (mem_items.mpr ⟨hA', hh⟩ : x ∈ I.items c.A)
      refine ⟨(x, j), List.mem_filter.mpr ⟨List.mem_zipIdx_iff_getElem?.mpr hj, ?_⟩, rfl⟩
      simp only [Bool.not_eq_true']
      refine Decidable.byContradiction (fun hany => ?_)
      have hany' : (I.items c.B).any (fun y => rposN (c.ids I) (c.o.idf y) == some j) = true := by
        simpa using hany
      obtain ⟨y, hy, hyj⟩ := List.any_eq_true.mp hany'
      have hr := rposN_some (by simpa using hyj)
      have hids : (c.ids I)[j]? = some (c.o.idf x) := by
        unfold Cfg.ids; rw [List.getElem?_map, hj]; rfl
      rw [hids] at hr
      have hxy := hinj x (List.mem_append_left _ (mem_items.mpr ⟨hA', hh⟩)) y (List.mem_append_right _ hy)
        (Option.some.inj hr)
      subst hxy
      exact hnB (mem_items.mp hy).1

end Pinc.Reconcile
