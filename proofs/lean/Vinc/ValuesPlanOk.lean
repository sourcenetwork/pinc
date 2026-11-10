import Vinc.ValuesPlanModel

/-!
# What a plan that was accepted looks like

`RO len rs s t` says the ranges `rs` are valid ranges of a value of `len` bytes laid back to back from stream
offset `s` to `t`: each is a non-empty group interval inside the value and starts where the framed encodings
before it end (`refSize`). `planNew_ok` proves that a plan `Plan::new` accepts satisfies it from offset 0, that
its ranges are the spans rounded out to whole groups (empty spans dropped), that every span lies inside the value,
that at most 255 spans were given and that the response is at most `2^62 - 1` bytes.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Vinc.ValuesPlan
open Vinc.Layout Vinc.Encode

/-- The framed size of a range. -/
def szr (len : Nat) (r : PR) : Nat := refSize len r.first r.last

/-- The ranges are valid and laid back to back from `s` to `t`. -/
def RO (len : Nat) : List PR → Nat → Nat → Prop
  | [], s, t => s = t
  | r :: rest, s, t => r.first < r.last ∧ r.last ≤ groups len lg ∧ r.start = s ∧ RO len rest (s + szr len r) t

theorem RO_append (len : Nat) : ∀ (rs : List PR) (s t : Nat) (r : PR),
    RO len rs s t → r.first < r.last → r.last ≤ groups len lg → r.start = t →
    RO len (rs ++ [r]) s (t + szr len r) := by
  intro rs
  induction rs with
  | nil => intro s t r h h1 h2 h3; simp only [RO] at h ⊢; subst h; exact ⟨h1, h2, h3, rfl⟩
  | cons x rest ih =>
    intro s t r h h1 h2 h3
    obtain ⟨a, b, c, d⟩ := h
    exact ⟨a, b, c, ih _ _ r d h1 h2 h3⟩

/-- The fold over the spans keeps the ranges valid and consecutive, and records what the spans must satisfy. -/
theorem fold_inv (len : Nat) : ∀ (l : List (Nat × Nat)) (s : Nat) (rs : List PR) (s0 t : Nat) (rs' : List PR),
    RO len rs s0 s → s ≤ MAXS →
    l.foldlM (specStep len) (s, rs) = Except.ok (t, rs') →
    RO len rs' s0 t ∧ t ≤ MAXS ∧ (∀ sp ∈ l, sp.2 ≠ 0 → sp.1 + sp.2 ≤ len) ∧
      rs'.map (fun r => (r.first, r.last)) = rs.map (fun r => (r.first, r.last)) ++
        ((l.filter (fun sp => sp.2 ≠ 0)).map (fun sp => (sp.1 / G, divCeil (sp.1 + sp.2) G))) := by
  intro l
  induction l with
  | nil =>
    intro s rs s0 t rs' h hs hf
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simp [h, hs]
  | cons sp l ih =>
    intro s rs s0 t rs' h hs hf
    simp only [List.foldlM, bind, Except.bind] at hf
    by_cases h0 : sp.2 = 0
    · simp only [specStep, h0, ite_true] at hf
      obtain ⟨a, b, c, d⟩ := ih s rs s0 t rs' h hs hf
      refine ⟨a, b, ?_, ?_⟩
      · intro x hx hx0
        rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd h0 hx0
        · exact c x hx hx0
      · simpa [h0] using d
    · by_cases hoob : sp.1 + sp.2 > len
      · simp [specStep, h0, hoob] at hf
      · by_cases htl : s + refSize len (sp.1 / G) (divCeil (sp.1 + sp.2) G) > MAXS
        · simp [specStep, h0, hoob, htl] at hf
        · have hb := divCeil_bounds (sp.1 + sp.2) len (by omega) (by omega)
          have hg := G_pos
          have hab : sp.1 / G < divCeil (sp.1 + sp.2) G := by
            rw [Nat.div_lt_iff_lt_mul hg]
            have := hb.2.1
            have := Nat.mul_comm (divCeil (sp.1 + sp.2) G) G
            omega
          simp only [specStep, h0, hoob, htl, ite_false, ite_true] at hf
          have hro := RO_append len rs s0 s ⟨sp.1 / G, divCeil (sp.1 + sp.2) G, s⟩ h hab hb.1 rfl
          obtain ⟨a, b, c, d⟩ := ih (s + refSize len (sp.1 / G) (divCeil (sp.1 + sp.2) G)) _ s0 t rs' hro (by omega) hf
          refine ⟨a, b, ?_, ?_⟩
          · intro x hx hx0
            rcases List.mem_cons.1 hx with rfl | hx
            · omega
            · exact c x hx hx0
          · rw [d]; simp [h0]

/-- A plan that `Plan::new` accepts. -/
theorem planNew_ok (len : Nat) (hlen : len ≤ u64Max) (spans : List (Nat × Nat)) (pl : PlanM)
    (h : planNew len spans = Except.ok pl) :
    pl.len = len ∧ RO len pl.rs 0 pl.total ∧ pl.total ≤ MAXS ∧ spans.length ≤ MAXR ∧
      (∀ sp ∈ spans, sp.2 ≠ 0 → sp.1 + sp.2 ≤ len) ∧
      pl.rs.map (fun r => (r.first, r.last)) =
        (spans.filter (fun sp => sp.2 ≠ 0)).map (fun sp => (sp.1 / G, divCeil (sp.1 + sp.2) G)) := by
  rw [planNew_eq_spec len hlen] at h
  unfold specNew at h
  by_cases hn : spans.length > MAXR
  · simp [hn] at h
  · simp only [hn, ite_false] at h
    cases hf : spans.foldlM (specStep len) (0, []) with
    | error e => rw [hf] at h; cases h
    | ok st =>
      simp only [hf, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      obtain ⟨a, b, c, d⟩ := fold_inv len spans 0 [] 0 st.1 st.2 (by simp [RO]) (by simp [MAXS]) hf
      exact ⟨rfl, a, b, by omega, c, by simpa using d⟩

/-- The ranges of a valid chain: each starts after the sizes of the ranges before it, and the end is the sum. -/
theorem RO_index (len : Nat) : ∀ (rs : List PR) (s t : Nat), RO len rs s t →
    (∀ r ∈ rs, r.first < r.last ∧ r.last ≤ groups len lg) ∧ t = s + (rs.map (szr len)).sum ∧
      ∀ i (hi : i < rs.length), (rs[i]).start = s + ((rs.take i).map (szr len)).sum := by
  intro rs
  induction rs with
  | nil => intro s t h; simp only [RO] at h; subst h; simp
  | cons r rest ih =>
    intro s t h
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨a, b, c⟩ := ih _ _ h4
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨h1, h2⟩
      · exact a x hx
    · rw [b]; simp only [List.map_cons, List.sum_cons]; omega
    · intro i hi
      cases i with
      | zero => simpa using h3
      | succ i =>
        simp only [List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
        have := c i (by simpa using hi)
        omega

end Vinc.ValuesPlan
