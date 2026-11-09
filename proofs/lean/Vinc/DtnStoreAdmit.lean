import Vinc.DtnStore

/-!
# The charged store: the oldest-transit search and the invariants of the simple operations

Lemmas about `Vinc.DtnStore` for every ledger: `minT_none` and `minT_some` say that `oldest_transit` finds a transit item
exactly when one exists and finds the one with the least admission number; `Inv` (the bytes charged are the sum of the
sizes and within the budget, keys and admission numbers distinct) is preserved by `expire`, `release` and `reclass`.
The fit test, the eviction loop and `admitItem` are in `Vinc.DtnStoreLoop`, `Vinc.DtnStoreThm` and `Vinc.DtnStoreProps`
(whose header lists the statements of the task).
-/

namespace Vinc.DtnStore

theorem minT_none (l : List (Option Entry)) (i : Nat) :
    minT l i = none ↔ ∀ e ∈ l.filterMap id, e.cls ≠ .transit := by
  induction l generalizing i with
  | nil => simp [minT]
  | cons s l ih =>
    cases s with
    | none => simp [minT, ih]
    | some e =>
      by_cases h : e.cls = .transit
      · simp only [minT, h, ite_true]
        cases minT l (i + 1) with
        | none => simp [h]
        | some p => obtain ⟨q, j⟩ := p; simp [h]; split <;> simp
      · simp [minT, h, ih (i + 1)]

theorem minT_some (l : List (Option Entry)) (i q j : Nat) (h : minT l i = some (q, j)) :
    i ≤ j ∧ ∃ e, l[j - i]? = some (some e) ∧ e.cls = .transit ∧ e.seq = q ∧
      ∀ e' ∈ l.filterMap id, e'.cls = .transit → q ≤ e'.seq := by
  induction l generalizing i q j with
  | nil => simp [minT] at h
  | cons s l ih =>
    cases s with
    | none =>
      simp only [minT] at h
      obtain ⟨hj, e, he, hc, hq, hall⟩ := ih (i + 1) q j h
      refine ⟨by omega, e, ?_, hc, hq, by simpa using hall⟩
      have : j - i = (j - (i + 1)) + 1 := by omega
      rw [this]; simpa using he
    | some e =>
      by_cases hc : e.cls = .transit
      · simp only [minT, hc, ite_true] at h
        cases hr : minT l (i + 1) with
        | none =>
          rw [hr] at h
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨Nat.le_refl _, e, by simp, hc, rfl, ?_⟩
          intro e' he' ht
          simp at he'
          rcases he' with rfl | he'
          · exact Nat.le_refl _
          · exact absurd ht ((minT_none l (i+1)).1 hr e' (by simpa using he'))
        | some p =>
          obtain ⟨q', j'⟩ := p
          rw [hr] at h
          obtain ⟨hj', e2, he2, hc2, hq2, hall2⟩ := ih (i + 1) q' j' hr
          by_cases hlt : e.seq < q' ∨ (e.seq = q' ∧ i ≤ j')
          · simp only [hlt, ite_true, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨Nat.le_refl _, e, by simp, hc, rfl, ?_⟩
            intro e' he' ht
            simp at he'
            rcases he' with rfl | he'
            · exact Nat.le_refl _
            · have := hall2 e' (by simpa using he') ht; omega
          · simp only [hlt, ite_false, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨by omega, e2, ?_, hc2, hq2, ?_⟩
            · have : j' - i = (j' - (i + 1)) + 1 := by omega
              rw [this]; simpa using he2
            · intro e' he' ht
              simp at he'
              rcases he' with rfl | he'
              · omega
              · exact hall2 e' (by simpa using he') ht
      · simp only [minT, hc, ite_false] at h
        obtain ⟨hj, e2, he2, hc2, hq2, hall⟩ := ih (i + 1) q j h
        refine ⟨by omega, e2, ?_, hc2, hq2, ?_⟩
        · have : j - i = (j - (i + 1)) + 1 := by omega
          rw [this]; simpa using he2
        · intro e' he' ht
          simp at he'
          rcases he' with rfl | he'
          · exact absurd ht hc
          · exact hall e' (by simpa using he') ht

/-! ## Invariants of the simple operations -/

theorem inv_removed {L L' : Ledger} {ev : List Entry} (hI : Inv L) (hp : L.entries.Perm (ev ++ L'.entries))
    (hb : L'.budget = L.budget) (hs : L'.nextSeq = L.nextSeq) (hu : L'.used = L.used - sumB ev) : Inv L' := by
  have hsum := sumB_perm hp
  rw [sumB_append] at hsum
  refine ⟨by have := hI.used_eq; omega, by have := hI.used_le; omega, by have := hI.budget_le; omega, ?_, ?_, ?_⟩
  · have := (hp.map (·.key)).nodup_iff.1 hI.keys
    rw [List.map_append] at this
    exact (List.nodup_append.1 this).2.1
  · have := (hp.map (·.seq)).nodup_iff.1 hI.seqs
    rw [List.map_append] at this
    exact (List.nodup_append.1 this).2.1
  · intro e he
    rw [hs]
    exact hI.seq_lt e (hp.symm.mem_iff.1 (List.mem_append_right _ he))

theorem expire_perm (L : Ledger) (now : Nat) :
    L.entries.Perm ((expire L now).2 ++ (expire L now).1.entries) := by
  rw [entries_expire]
  exact (List.filter_append_perm (expiredAt now) L.entries).symm

theorem expire_inv {L : Ledger} (h : Inv L) (now : Nat) : Inv (expire L now).1 :=
  inv_removed h (expire_perm L now) rfl rfl rfl

theorem takeAt_inv {L L' : Ledger} {i : Nat} {e : Entry} (hI : Inv L) (h : takeAt L i = some (L', e)) : Inv L' := by
  have hp := takeAt_perm h
  have hb : L'.budget = L.budget ∧ L'.nextSeq = L.nextSeq ∧ L'.used = L.used - e.bytes := by
    unfold takeAt at h; split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
    · simp at h
  exact inv_removed (ev := [e]) hI (by simpa using hp) hb.1 hb.2.1 (by simpa [sumB] using hb.2.2)

theorem release_inv {L : Ledger} (hI : Inv L) (k : Key) : Inv (release L k).1 := by
  unfold release
  split
  · exact hI
  · split
    · rename_i L' e h; exact takeAt_inv hI h
    · exact hI

theorem reclass_entries (L : Ledger) (k : Key) (c : Class) (h : L.contains k = true) :
    (reclass L k c).1.entries = L.entries.map fun e => if e.key = k then { e with cls := c } else e := by
  simp only [reclass, h, ite_true, Ledger.entries]
  generalize L.slots = l
  induction l with
  | nil => simp
  | cons s l ih => cases s <;> simp [ih]

theorem reclass_ok_iff (L : Ledger) (k : Key) (c : Class) : (reclass L k c).2 = L.contains k := by
  unfold reclass; split <;> simp_all

theorem reclass_inv {L : Ledger} (hI : Inv L) (k : Key) (c : Class) : Inv (reclass L k c).1 := by
  by_cases h : L.contains k = true
  · have he := reclass_entries L k c h
    have hbud : (reclass L k c).1.budget = L.budget ∧ (reclass L k c).1.used = L.used ∧
        (reclass L k c).1.nextSeq = L.nextSeq := by simp [reclass, h]
    have hsum : sumB ((reclass L k c).1.entries) = sumB L.entries := by
      rw [he]; unfold sumB
      congr 1
      rw [List.map_map]
      congr 1
      funext e; simp only [Function.comp]; split <;> simp
    refine ⟨by rw [hbud.2.1, hsum]; exact hI.used_eq, by rw [hbud.2.1, hbud.1]; exact hI.used_le,
      by rw [hbud.1]; exact hI.budget_le, ?_, ?_, ?_⟩
    · rw [he, List.map_map]
      have hf : ((fun x : Entry => x.key) ∘ fun e : Entry => if e.key = k then { e with cls := c } else e) =
          fun x => x.key := by funext e; simp only [Function.comp]; split <;> simp
      rw [hf]; exact hI.keys
    · rw [he, List.map_map]
      have hf : ((fun x : Entry => x.seq) ∘ fun e : Entry => if e.key = k then { e with cls := c } else e) =
          fun x => x.seq := by funext e; simp only [Function.comp]; split <;> simp
      rw [hf]; exact hI.seqs
    · intro e he'
      rw [he] at he'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he'
      rw [hbud.2.2]
      have := hI.seq_lt x hx
      split <;> simpa
  · have : (reclass L k c).1 = L := by simp [reclass, h]
    rw [this]; exact hI

theorem contains_iff {L : Ledger} {k : Key} : L.contains k = true ↔ ∃ e ∈ L.entries, e.key = k := by
  unfold Ledger.contains; simp

theorem nodup_map_inj {α β : Type} (f : α → β) : ∀ (l : List α), (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => by simp at hx
  | a :: t, h, x, hx, y, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd ⟨y, hy, hxy.symm⟩ h.1
    · exact absurd ⟨x, hx, hxy⟩ h.1
    · exact nodup_map_inj f t (by simpa using h.2) x hx y hy hxy

end Vinc.DtnStore
