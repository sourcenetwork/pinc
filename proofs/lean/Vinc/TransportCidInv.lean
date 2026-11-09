import Vinc.Axioms
import Vinc.TransportCidThm

/-!
# Connection ids: every call keeps the table

`refill1_spec` is the step that puts one lookahead id into the table (a free slot, or the slot of the entry
least recently used among those allowed to make room); `refill_spec` runs it for the two lookahead indices;
`install_inv`, `auth_inv` and `claim_next` carry the invariant through the calls; `Reach` adds the indices
forgotten and shows that none is ever held again.
-/

namespace Vinc.TransportCid

theorem put_has (c : C) (hb : ∀ s, slots ≤ s → c.ent s = none) (s : Nat) (hs : s < slots) (e : E) (j : Nat) :
    has (put c s e) j = true ↔ e.idx = j ∨ ∃ t f, t ≠ s ∧ c.ent t = some f ∧ f.idx = j := by
  rw [has_iff _ (put_bound c s e hs hb)]
  constructor
  · rintro ⟨t, f, ht, hf⟩
    rw [put_ent] at ht
    by_cases hts : t = s
    · simp [hts] at ht; subst ht; exact Or.inl hf
    · simp [hts] at ht; exact Or.inr ⟨t, f, hts, ht, hf⟩
  · rintro (h | ⟨t, f, hts, ht, hf⟩)
    · exact ⟨s, e, by simp [put_ent], h⟩
    · exact ⟨t, f, by simp [put_ent, hts, ht], hf⟩

theorem core_put (c : C) (hc : Core c) (s : Nat) (hs : s < slots) (k : Nat) (hk1 : c.hi < k) (hk2 : k ≤ c.hi + look)
    (hnew : ∀ t f, c.ent t = some f → f.idx ≠ k) : Core (put c s ⟨k, c.tick, false⟩) := by
  refine ⟨put_bound c s _ hs hc.bound, ?_, ?_, ?_, ?_⟩
  · intro s' t' e f he hf hef
    rw [put_ent] at he hf
    by_cases h1 : s' = s <;> by_cases h2 : t' = s
    · rw [h1, h2]
    · simp [h1] at he; simp [h2] at hf
      subst he; exact absurd hef.symm (hnew t' f hf)
    · simp [h2] at hf; simp [h1] at he
      subst hf; exact absurd hef (hnew s' e he)
    · simp [h1] at he; simp [h2] at hf
      exact hc.nodup s' t' e f he hf hef
  · intro s' e he
    rw [put_ent] at he
    by_cases h1 : s' = s
    · simp [h1] at he; subst he; simp; omega
    · simp [h1] at he; exact hc.pos s' e he
  · intro s' e he
    rw [put_ent] at he
    by_cases h1 : s' = s
    · simp [h1] at he; subst he; exact hk2
    · simp [h1] at he; exact hc.window s' e he
  · intro s' e he hseen
    rw [put_ent] at he
    by_cases h1 : s' = s
    · simp [h1] at he; subst he; simp at hseen
    · simp [h1] at he; exact hc.seenLe s' e he hseen

theorem refill1_spec (c : C) (k : Nat) (hc : Core c) (hk1 : c.hi < k) (hk2 : k ≤ c.hi + look) :
    ∀ c' ev, refill1 c k = (c', ev) →
      Core c' ∧ c'.hi = c.hi ∧ c'.sec = c.sec ∧ c'.tick = c.tick ∧ c'.ns = c.ns ∧ c'.fr = c.fr ∧
      has c' k = true ∧
      (∀ j, has c j = true → has c' j = true ∨ ev = some j) ∧
      (∀ v, ev = some v → v ≤ c.hi) ∧
      (∀ j, has c' j = true → has c j = true ∨ j = k) ∧
      (∀ v, ev = some v → has c' v = false) := by
  intro c' ev h
  unfold refill1 at h
  by_cases hh : has c k = true
  · rw [if_pos hh] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hc, rfl, rfl, rfl, rfl, rfl, hh, fun j hj => Or.inl hj, fun v hv => by simp at hv,
      fun j hj => Or.inl hj, fun v hv => by simp at hv⟩
  · have hnew : ∀ t f, c.ent t = some f → f.idx ≠ k := by
      intro t f ht hfk
      exact hh ((has_iff c hc.bound k).2 ⟨t, f, ht, hfk⟩)
    rw [if_neg hh] at h
    cases hf : freeSlot c with
    | some s =>
      obtain ⟨hs, hn⟩ := freeSlot_spec c s hf
      simp only [hf, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨core_put c hc s hs k hk1 hk2 hnew, rfl, rfl, rfl, rfl, rfl, ?_, ?_, fun v hv => by simp at hv, ?_,
        fun v hv => by simp at hv⟩
      · rw [put_has c hc.bound s hs]; exact Or.inl rfl
      · intro j hj
        left
        rw [put_has c hc.bound s hs]
        obtain ⟨t, f, ht, hfj⟩ := (has_iff c hc.bound j).1 hj
        refine Or.inr ⟨t, f, ?_, ht, hfj⟩
        rintro rfl; rw [hn] at ht; simp at ht
      · intro j hj
        rw [put_has c hc.bound s hs] at hj
        rcases hj with h | ⟨t, f, _, ht, hfj⟩
        · exact Or.inr h.symm
        · exact Or.inl ((has_iff c hc.bound j).2 ⟨t, f, ht, hfj⟩)
    | none =>
      have hfull := freeSlot_none c hf
      obtain ⟨s0, hs0, e0, he0, hle0⟩ := full_has_low c hc hfull
      have hev0 : evictable c e0 = true := by simp [evictable, hle0]
      have hsome := victim_isSome c s0 hs0 e0 he0 hev0
      cases hv : victim c with
      | none => rw [hv] at hsome; simp at hsome
      | some s =>
        obtain ⟨hs, e, he, hev⟩ := victim_spec c s hv
        have hevle : e.idx ≤ c.hi := by
          simp only [evictable, Bool.or_eq_true, decide_eq_true_eq] at hev
          rcases hev with h | h
          · exact hc.seenLe s e he h
          · exact h
        simp only [hf, hv, he, Option.map_some, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨core_put c hc s hs k hk1 hk2 hnew, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · rw [put_has c hc.bound s hs]; exact Or.inl rfl
        · intro j hj
          obtain ⟨t, f, ht, hfj⟩ := (has_iff c hc.bound j).1 hj
          by_cases hts : t = s
          · subst hts; rw [he] at ht; simp at ht; subst ht; exact Or.inr (by simp [hfj])
          · left; rw [put_has c hc.bound s hs]; exact Or.inr ⟨t, f, hts, ht, hfj⟩
        · intro v hv'; simp at hv'; subst hv'; exact hevle
        · intro j hj
          rw [put_has c hc.bound s hs] at hj
          rcases hj with h | ⟨t, f, _, ht, hfj⟩
          · exact Or.inr h.symm
          · exact Or.inl ((has_iff c hc.bound j).2 ⟨t, f, ht, hfj⟩)
        · intro v hv'
          simp at hv'
          subst hv'
          apply Classical.byContradiction; intro hx
          have hx' : has (put c s ⟨k, c.tick, false⟩) e.idx = true := by simpa using hx
          rw [put_has c hc.bound s hs] at hx'
          rcases hx' with h | ⟨t, f, hts, ht, hfj⟩
          · simp at h; omega
          · exact hts (hc.nodup t s f e ht he hfj)

theorem refill_spec (c : C) (hc : Core c) : ∀ c' ev, refill c = (c', ev) →
    Core c' ∧ c'.hi = c.hi ∧ c'.sec = c.sec ∧ c'.tick = c.tick ∧ c'.ns = c.ns ∧ c'.fr = c.fr ∧
      (c.sec = true → has c' (c.hi + 1) = true ∧ has c' (c.hi + 2) = true) ∧
      (∀ j, has c j = true → has c' j = true ∨ j ∈ ev) ∧
      (∀ v ∈ ev, v ≤ c.hi) ∧
      (∀ v ∈ ev, has c' v = false) ∧
      (∀ j, has c' j = true → has c j = true ∨ (c.hi < j ∧ j ≤ c.hi + look)) := by
  intro c' ev h
  unfold refill at h
  by_cases hs : c.sec = true
  · rw [if_pos hs] at h
    rcases hr1 : refill1 c (c.hi + 1) with ⟨c1, e1⟩
    simp only [hr1] at h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a11, a10⟩ :=
      refill1_spec c (c.hi + 1) hc (by omega) (by simp [look]) c1 e1 hr1
    rcases hr2 : refill1 c1 (c.hi + 2) with ⟨c2, e2⟩
    simp only [hr2] at h
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b11, b10⟩ :=
      refill1_spec c1 (c.hi + 2) a1 (by omega) (by simp [look]; omega) c2 e2 hr2
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨b1, by omega, by rw [b3, a3], by rw [b4, a4], by rw [b5, a5], by rw [b6, a6], fun _ => ⟨?_, b7⟩,
      ?_, ?_, ?_, ?_⟩
    · rcases b8 (c.hi + 1) a7 with h | h
      · exact h
      · have := b9 _ h; omega
    · intro j hj
      rcases a8 j hj with h | h
      · rcases b8 j h with h2 | h2
        · exact Or.inl h2
        · right; simp [h2]
      · right; simp [h]
    · intro v hv
      simp at hv
      rcases hv with h | h
      · have := a9 v h; omega
      · have := b9 v h; omega
    · intro v hv
      simp at hv
      rcases hv with h | h
      · have hv0 := a10 v h
        have := a9 v h
        apply Classical.byContradiction; intro hx
        have hx' : has c2 v = true := by simpa using hx
        rcases b11 v hx' with h2 | h2
        · rw [hv0] at h2; simp at h2
        · omega
      · exact b10 v h
    · intro j hj
      rcases b11 j hj with h | h
      · rcases a11 j h with h2 | h2
        · exact Or.inl h2
        · right; simp only [look]; omega
      · right; simp only [look]; omega
  · have hs' : c.sec = false := by simpa using hs
    rw [if_neg hs] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hc, rfl, rfl, rfl, rfl, rfl, fun h => absurd h hs, fun j hj => Or.inl hj, by simp, by simp,
      fun j hj => Or.inl hj⟩

theorem refill_spec' (c : C) (hc : Core c) :
    Core (refill c).1 ∧ (refill c).1.hi = c.hi ∧ (refill c).1.sec = c.sec ∧ (refill c).1.tick = c.tick ∧
      (refill c).1.ns = c.ns ∧ (refill c).1.fr = c.fr ∧
      (c.sec = true → has (refill c).1 (c.hi + 1) = true ∧ has (refill c).1 (c.hi + 2) = true) ∧
      (∀ j, has c j = true → has (refill c).1 j = true ∨ j ∈ (refill c).2) ∧
      (∀ v ∈ (refill c).2, v ≤ c.hi) ∧
      (∀ v ∈ (refill c).2, has (refill c).1 v = false) ∧
      (∀ j, has (refill c).1 j = true → has c j = true ∨ (c.hi < j ∧ j ≤ c.hi + look)) :=
  refill_spec c hc (refill c).1 (refill c).2 rfl

end Vinc.TransportCid
