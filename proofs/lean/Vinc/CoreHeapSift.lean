import Vinc.CoreHeapInv

/-!
# The deadline heap, part 2: the sifts

`upLoop_spec` and `downLoop_spec`: the loops of `up` and `down` move one element along a path with a hole (`HS`,
`CoreHeapInv`) and leave a heap that has the invariant and the same size, capacity, deadlines and ids present (`Fin'`);
`down_inv` sifts down from a heap that has the invariant; `rem_tail`, the tail of a removal: the last element sits in
the hole and goes up, or down, to where it belongs.
-/

namespace Vinc.CoreHeap

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

#audit_axioms Vinc.CoreHeap.upLoop_spec
#audit_axioms Vinc.CoreHeap.downLoop_spec

end Vinc.CoreHeap
