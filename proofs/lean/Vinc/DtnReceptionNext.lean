import Vinc.DtnReception

/-!
# `Reception::next_missing`

The loop of the code (`vinc-dtn/src/bundle.rs`): starting at the byte offset `from * g`, walk the held intervals in
order; an interval that ends at or before the offset is skipped, one that starts after it ends the search (the missing
run is the offsets up to its start, cut at the end of the bundle), one that contains it moves the offset to its end;
after the last interval the missing run is the rest of the bundle. The result is the run as symbol indices.

`nmGo_some` and `nmGo_none` state what the loop returns for any sound set of intervals, in offsets. With a held set
that is a union of whole symbols (`Closed`: what `feed` produces, `feedGo_closed`), `next_missing_some` and
`next_missing_none` say it in symbols: the run `[a, b)` is the first run of unheld symbols at or after `from`, every
symbol from `from` to `a` is held, none of `a..b` is, and the symbol `b` is held unless it is the end of the bundle; no
run is returned only when every symbol from `from` on is held. The multiplication `from.saturating_mul(g)` of the code
saturates only for a `from` beyond the largest `u64`, past the end of any bundle, where both the code and this model
find nothing missing.
-/

namespace Vinc.DtnReception
open Vinc.Ranges

/-- `Reception::next_missing`, the loop of the code, from the byte offset `at_`. -/
def nmGo (g total : Nat) : List Interval → Nat → Option (Nat × Nat)
  | [], at_ => if at_ < total * g then some (at_ / g, total) else none
  | iv :: rest, at_ =>
    if iv.2 ≤ at_ then nmGo g total rest at_
    else if iv.1 > at_ then some (at_ / g, min iv.1 (total * g) / g)
    else nmGo g total rest iv.2

theorem covers_cons (iv : Interval) (rest : List Interval) (x : Nat) :
    Covers (iv :: rest) x ↔ (iv.1 ≤ x ∧ x < iv.2) ∨ Covers rest x := by
  constructor
  · rintro ⟨c, hc, h1, h2⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨c, hc, h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨c, hc, h1, h2⟩)
    · exact ⟨iv, List.mem_cons_self .., h1, h2⟩
    · exact ⟨c, List.mem_cons_of_mem _ hc, h1, h2⟩

theorem sound_cons {iv : Interval} {rest : List Interval} (h : Sound (iv :: rest)) :
    iv.1 < iv.2 ∧ (∀ c ∈ rest, iv.2 < c.1) ∧ Sound rest := by
  obtain ⟨h1, h2⟩ := h
  rw [List.pairwise_cons] at h2
  exact ⟨h1 iv (List.mem_cons_self ..), h2.1, fun c hc => h1 c (List.mem_cons_of_mem _ hc), h2.2⟩

/-- No run is returned: every offset from `at_` to the end of the bundle is held. -/
theorem nmGo_none (g total : Nat) : ∀ (l : List Interval) (at_ : Nat), nmGo g total l at_ = none →
    ∀ x, at_ ≤ x → x < total * g → Covers l x := by
  intro l
  induction l with
  | nil =>
    intro at_ h x hx hlt
    simp only [nmGo] at h
    split at h
    · cases h
    · omega
  | cons iv rest ih =>
    intro at_ h x hx hlt
    simp only [nmGo] at h
    rw [covers_cons]
    by_cases h1 : iv.2 ≤ at_
    · rw [if_pos h1] at h
      exact Or.inr (ih at_ h x hx hlt)
    · rw [if_neg h1] at h
      by_cases h2 : iv.1 > at_
      · rw [if_pos h2] at h; cases h
      · rw [if_neg h2] at h
        by_cases hx2 : x < iv.2
        · exact Or.inl ⟨by omega, hx2⟩
        · exact Or.inr (ih iv.2 h x (by omega) hlt)

/-- A run is returned: it starts at the first offset `u` at or after `at_` that is not held (all before it are held),
it ends at `v`, the next held offset or the end of the bundle, and nothing in `[u, v)` is held. -/
theorem nmGo_some (g total : Nat) (hg : 0 < g) : ∀ (l : List Interval), Sound l → (∀ iv ∈ l, iv.2 ≤ total * g) →
    ∀ (at_ a b : Nat),
    nmGo g total l at_ = some (a, b) →
    ∃ u v, at_ ≤ u ∧ u < v ∧ u < total * g ∧ (∀ x, at_ ≤ x → x < u → Covers l x) ∧
      (∀ x, u ≤ x → x < v → ¬ Covers l x) ∧ (v = total * g ∨ Covers l v) ∧ a = u / g ∧
      b = min v (total * g) / g := by
  intro l
  induction l with
  | nil =>
    intro _ _ at_ a b h
    simp only [nmGo] at h
    split at h
    · rename_i hlt
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨at_, total * g, Nat.le_refl _, hlt, hlt, fun x h1 h2 => by omega, fun x _ _ ⟨c, hc, _⟩ => by simp at hc,
        Or.inl rfl, rfl, ?_⟩
      rw [Nat.min_self, Nat.mul_div_cancel _ hg]
    · cases h
  | cons iv rest ih =>
    intro hs hb at_ a b h
    obtain ⟨hiv, hafter, hrest⟩ := sound_cons hs
    have hbr : ∀ c ∈ rest, c.2 ≤ total * g := fun c hc => hb c (List.mem_cons_of_mem _ hc)
    have hbiv := hb iv (List.mem_cons_self ..)
    simp only [nmGo] at h
    by_cases h1 : iv.2 ≤ at_
    · rw [if_pos h1] at h
      obtain ⟨u, v, hu, huv, hut, hc, hn, hv, ha, hb⟩ := ih hrest hbr at_ a b h
      refine ⟨u, v, hu, huv, hut, fun x hx1 hx2 => ?_, fun x hx1 hx2 hcov => ?_, ?_, ha, hb⟩
      · exact (covers_cons ..).2 (Or.inr (hc x hx1 hx2))
      · rcases (covers_cons ..).1 hcov with ⟨_, h3⟩ | h3
        · omega
        · exact hn x hx1 hx2 h3
      · rcases hv with hv | hv
        · exact Or.inl hv
        · exact Or.inr ((covers_cons ..).2 (Or.inr hv))
    · rw [if_neg h1] at h
      by_cases h2 : iv.1 > at_
      · rw [if_pos h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨at_, iv.1, Nat.le_refl _, h2, ?_, fun x h1 h2' => by omega, fun x hx1 hx2 hcov => ?_,
          Or.inr ((covers_cons ..).2 (Or.inl ⟨Nat.le_refl _, hiv⟩)), rfl, rfl⟩
        · omega
        · rcases (covers_cons ..).1 hcov with ⟨h3, _⟩ | ⟨c, hc, h3, _⟩
          · omega
          · have := hafter c hc; omega
      · rw [if_neg h2] at h
        obtain ⟨u, v, hu, huv, hut, hc, hn, hv, ha, hb⟩ := ih hrest hbr iv.2 a b h
        refine ⟨u, v, by omega, huv, hut, fun x hx1 hx2 => ?_, fun x hx1 hx2 hcov => ?_, ?_, ha, hb⟩
        · by_cases hx : x < iv.2
          · exact (covers_cons ..).2 (Or.inl ⟨by omega, hx⟩)
          · exact (covers_cons ..).2 (Or.inr (hc x (by omega) hx2))
        · rcases (covers_cons ..).1 hcov with ⟨_, h3⟩ | h3
          · omega
          · exact hn x hx1 hx2 h3
        · rcases hv with hv | hv
          · exact Or.inl hv
          · exact Or.inr ((covers_cons ..).2 (Or.inr hv))

/-- The held set is a union of whole symbols: two offsets of one symbol are held together. -/
def Closed (g : Nat) (l : List Interval) : Prop := ∀ x y, x / g = y / g → Covers l x → Covers l y

/-- Everything held is inside the bundle (`total * g` bytes). -/
def Within (n : Nat) (l : List Interval) : Prop := ∀ x, Covers l x → x < n

theorem blk_iff {g : Nat} (hg : 0 < g) (x s : Nat) : x / g = s ↔ s * g ≤ x ∧ x < (s + 1) * g := by
  constructor
  · rintro rfl
    refine ⟨Nat.div_mul_le_self x g, ?_⟩
    have := Nat.lt_div_mul_add (a := x) hg
    rw [Nat.add_mul, Nat.one_mul]; omega
  · rintro ⟨h1, h2⟩
    apply Nat.le_antisymm
    · have : x / g < s + 1 := (Nat.div_lt_iff_lt_mul hg).2 h2
      omega
    · exact (Nat.le_div_iff_mul_le hg).2 h1

theorem closed_nil (g : Nat) : Closed g [] := fun _ _ _ ⟨c, hc, _⟩ => by simp at hc

theorem within_nil (n : Nat) : Within n [] := fun _ ⟨c, hc, _⟩ => by simp at hc

/-- A sound set inside the bundle has every interval inside it. -/
theorem within_bound {n : Nat} {l : List Interval} (hs : Sound l) (hw : Within n l) : ∀ iv ∈ l, iv.2 ≤ n := by
  intro iv hiv
  have h1 := hs.1 iv hiv
  have := hw (iv.2 - 1) ⟨iv, hiv, by omega, by omega⟩
  omega

/-- Where the held offsets change, a symbol starts: the offset before is in another symbol. -/
theorem edge_aligned {g : Nat} (hg : 0 < g) {l : List Interval} (hcl : Closed g l) (y : Nat) (hy : 0 < y)
    (hne : ¬ (Covers l y ↔ Covers l (y - 1))) : y % g = 0 := by
  by_cases hr : y % g = 0
  · exact hr
  exfalso
  apply hne
  have h1 := Nat.div_mul_le_self y g
  have h2 : y / g * g ≠ y := fun h => hr (by rw [← h]; exact Nat.mul_mod_left _ _)
  have h3 := (blk_iff hg y (y / g)).1 rfl
  have hsame : (y - 1) / g = y / g := by
    rw [blk_iff hg]; exact ⟨by omega, by omega⟩
  exact ⟨hcl y (y - 1) hsame.symm, hcl (y - 1) y hsame⟩

/-- A symbol of the bundle (`s < total`) is held when each of its offsets is. -/
theorem holds_of_covers (g total : Nat) (l : List Interval) (hs : Sound l) (s : Nat) (hst : s < total)
    (h : ∀ x, s * g ≤ x → x < (s + 1) * g → Covers l x) : holds g total l s = true :=
  (holds_iff g total l hs s).2 ⟨hst, h⟩

/-- **`next_missing` returns the first run of unheld symbols.** For a held set of whole symbols inside the bundle, if
the loop returns `[a, b)` from symbol `from`: `from <= a < b <= total`, every symbol from `from` to `a` is held,
none of `a..b` is, and symbol `b` is held unless it is the end of the bundle. -/
theorem next_missing_some (g total : Nat) (hg : 0 < g) (l : List Interval) (hs : Sound l) (hcl : Closed g l)
    (hw : Within (total * g) l) (f a b : Nat) (h : nmGo g total l (f * g) = some (a, b)) :
    f ≤ a ∧ a < b ∧ b ≤ total ∧ (∀ s, f ≤ s → s < a → holds g total l s = true) ∧
      (∀ s, a ≤ s → s < b → holds g total l s = false) ∧ (b < total → holds g total l b = true) := by
  obtain ⟨u, v, hu, huv, hut, hc, hn, hv, rfl, rfl⟩ :=
    nmGo_some g total hg l hs (within_bound hs hw) (f * g) a b h
  have hmulT : (total * g) % g = 0 := Nat.mul_mod_left _ _
  -- the start of the run is a whole symbol
  have hua : u % g = 0 := by
    by_cases hf : u = f * g
    · rw [hf]; exact Nat.mul_mod_left _ _
    · exact edge_aligned hg hcl u (by omega) (fun hiff =>
        hn u (Nat.le_refl _) huv (hiff.2 (hc (u - 1) (by omega) (by omega))))
  -- and so is its end
  have hva : v % g = 0 := by
    rcases hv with hv | hv
    · rw [hv]; exact hmulT
    · exact edge_aligned hg hcl v (by omega) (fun hiff => hn (v - 1) (by omega) (by omega) (hiff.1 hv))
  have hvm : (min v (total * g)) % g = 0 := by
    rcases Nat.le_total v (total * g) with h | h
    · rw [Nat.min_eq_left h]; exact hva
    · rw [Nat.min_eq_right h]; exact hmulT
  have hu' : u / g * g = u := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hua)
  have hb' : min v (total * g) / g * g = min v (total * g) := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hvm)
  generalize u / g = a at *
  generalize min v (total * g) / g = b at *
  have hbT : b * g ≤ total * g := by rw [hb']; exact Nat.min_le_right _ _
  have hbv : b * g ≤ v := by rw [hb']; exact Nat.min_le_left _ _
  have hab : a * g < b * g := by
    rw [hu', hb']; exact Nat.lt_min.2 ⟨huv, hut⟩
  have haT : a < total := Nat.lt_of_mul_lt_mul_right (by rw [hu']; exact hut)
  refine ⟨Nat.le_of_mul_le_mul_right (by rw [hu']; exact hu) hg, Nat.lt_of_mul_lt_mul_right hab,
    Nat.le_of_mul_le_mul_right hbT hg, ?_, ?_, ?_⟩
  · intro s hfs hsa
    refine holds_of_covers g total l hs s (by omega) fun x hx1 hx2 => hc x ?_ ?_
    · have := Nat.mul_le_mul_right g hfs; omega
    · have := Nat.mul_le_mul_right g (show s + 1 ≤ a by omega); rw [hu'] at this; omega
  · intro s has hsb
    cases hh' : holds g total l s
    · rfl
    exfalso
    obtain ⟨hst, hcov⟩ := (holds_iff g total l hs s).1 hh'
    have h1 := Nat.mul_le_mul_right g has
    have h2 := Nat.mul_lt_mul_of_pos_right hsb hg
    exact hn (s * g) (by omega) (by omega) (hcov (s * g) (Nat.le_refl _) (by rw [Nat.add_mul]; omega))
  · intro hbt
    have hbT' : b * g < total * g := Nat.mul_lt_mul_of_pos_right hbt hg
    have hveq : v = b * g := by
      rw [hb'] at hbT'
      rcases Nat.le_total v (total * g) with h | h
      · rw [Nat.min_eq_left h] at hb'; omega
      · rw [Nat.min_eq_right h] at hbT'; omega
    have hvc : Covers l v := by
      rcases hv with hv | hv
      · omega
      · exact hv
    refine holds_of_covers g total l hs b hbt fun x hx1 hx2 => hcl v x ?_ hvc
    rw [hveq, Nat.mul_div_cancel _ hg]; exact ((blk_iff hg x b).2 ⟨hx1, hx2⟩).symm

/-- **No run:** every symbol from `from` on is held. -/
theorem next_missing_none (g total : Nat) (hg : 0 < g) (l : List Interval) (hs : Sound l) (f : Nat)
    (h : nmGo g total l (f * g) = none) : ∀ s, f ≤ s → s < total → holds g total l s = true := by
  intro s hfs hst
  refine holds_of_covers g total l hs s hst fun x hx1 hx2 => nmGo_none g total l (f * g) h x ?_ ?_
  · have := Nat.mul_le_mul_right g hfs; omega
  · have := Nat.mul_le_mul_right g (show s + 1 ≤ total by omega); omega

/-- A feed keeps the held set a union of whole symbols (what `next_missing_some` needs). -/
theorem feedGo_closed [DecidableEq V] (ct : Nat → V) (W G : Nat) (hG : 0 < G) (vs : List V) :
    ∀ (buf : Nat → V) (h : List Interval) (full : Bool) (a : Nat), Reach W h → Closed G h →
      Closed G (feedGo ct W G buf h full a vs).2.1 := by
  induction vs with
  | nil => intro buf h full a _ hc; exact hc
  | cons v vs ih =>
    intro buf h full a hr hc
    rw [feedGo_cons]
    by_cases hv : v = ct a
    · rw [if_pos hv]
      refine ih _ _ _ _ (Reach.step _ hr) ?_
      have hsound : Sound h := (canon_iff h).1 (reach_inv hr).1
      cases hf : insertFixed W h (a * G, (a + 1) * G) with
      | none => rw [insertState_of_none W h _ hf]; exact hc
      | some l' =>
        have hst : insertState W h (a * G, (a + 1) * G) = l' := by simp [insertState, hf]
        rw [hst]
        intro x y hxy hx
        rw [insertFixed_covers W h hsound _ l' hf] at hx ⊢
        rcases hx with hx | ⟨hx1, hx2⟩
        · exact Or.inl (hc x y hxy hx)
        · right
          have hxa : x / G = a := (blk_iff hG x a).2 ⟨hx1, hx2⟩
          exact (blk_iff hG y a).1 (hxy.symm.trans hxa)
    · rw [if_neg hv]; exact hc

/-- A feed of symbols that are inside the bundle keeps everything held inside it. -/
theorem feedGo_within [DecidableEq V] (ct : Nat → V) (W G total : Nat) (vs : List V) :
    ∀ (buf : Nat → V) (h : List Interval) (full : Bool) (a : Nat), Reach W h → Within (total * G) h →
      a + vs.length ≤ total → Within (total * G) (feedGo ct W G buf h full a vs).2.1 := by
  induction vs with
  | nil => intro buf h full a _ hw _; exact hw
  | cons v vs ih =>
    intro buf h full a hr hw hlen
    rw [feedGo_cons]
    by_cases hv : v = ct a
    · rw [if_pos hv]
      refine ih _ _ _ _ (Reach.step _ hr) ?_ (by simp at hlen; omega)
      have hsound : Sound h := (canon_iff h).1 (reach_inv hr).1
      cases hf : insertFixed W h (a * G, (a + 1) * G) with
      | none => rw [insertState_of_none W h _ hf]; exact hw
      | some l' =>
        have hst : insertState W h (a * G, (a + 1) * G) = l' := by simp [insertState, hf]
        rw [hst]
        intro x hx
        rw [insertFixed_covers W h hsound _ l' hf] at hx
        rcases hx with hx | ⟨hx1, hx2⟩
        · exact hw x hx
        · have : (a + 1) * G ≤ total * G := Nat.mul_le_mul_right _ (by simp at hlen; omega)
          omega
    · rw [if_neg hv]; exact hw

#print axioms nmGo_none
#print axioms nmGo_some
#print axioms next_missing_some
#print axioms next_missing_none
#print axioms feedGo_closed
#print axioms feedGo_within

end Vinc.DtnReception
