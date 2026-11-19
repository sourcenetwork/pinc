import Pinc.Axioms
import Pinc.ValuesSchedExact

/-!
# The run-wide exact partition

`ReachR` is `Reach` for a striped fetch with each move guarded by the room it needs: the lists the move builds end
below capacity, which is when none of its pushes widened (`ValuesSchedRoom`). In every state of `ReachR` the work is
partitioned exactly (`ExactS`): the queue and the active providers' lists hold every byte at most once, no byte
outside the wanted set, and every wanted byte the store has not verified exactly once. This is the TLA+ invariant
`Exact` (with `Room`) for every run, any capacity, any fuel of `take_chunk`, any `keep` of a steal.

The proof is a conservation law per move (`Cons`): no move makes a byte, and every unverified byte is held after the
move as many times as before. A verified byte may be dropped by a prune or by `take_chunk`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesSched

/-- How many times the byte is held by the queue and the active providers' lists. -/
def Hold (s : Sys) (x : Nat) : Nat := mult s.q x + (s.act.map (fun p => mult (s.a p) x)).sum

/-- The exact partition: held at most once, nothing outside the wanted set, every unverified wanted byte held. -/
structure ExactS (W : Nat → Prop) (st : Store) (s : Sys) : Prop where
  once : ∀ x, Hold s x ≤ 1
  outside : ∀ x, ¬ W x → Hold s x = 0
  wanted : ∀ x, W x → ¬ st.V x → Hold s x = 1

/-- A move conserves the unverified bytes and makes none. -/
def Cons (st : Store) (s s' : Sys) : Prop := ∀ x, Hold s' x ≤ Hold s x ∧ (¬ st.V x → Hold s' x = Hold s x)

theorem exactS_cons {W : Nat → Prop} {st : Store} {s s' : Sys} (h : ExactS W st s) (c : Cons st s s') :
    ExactS W st s' :=
  ⟨fun x => Nat.le_trans (c x).1 (h.once x), fun x hx => by have := (c x).1; have := h.outside x hx; omega,
   fun x hx hv => by rw [(c x).2 hv]; exact h.wanted x hx hv⟩

theorem sum_split {l : List Nat} {p : Nat} (hp : p ∈ l) (g : Nat → Nat) :
    (l.map g).sum = g p + ((l.erase p).map g).sum := by
  have := ((List.perm_cons_erase hp).map g).sum_nat
  simpa using this

theorem sum_upd {l : List Nat} (hnd : l.Nodup) {p : Nat} (hp : p ∈ l) (f : Nat → List Span) (v : List Span) (x : Nat) :
    (l.map (fun j => mult (upd f p v j) x)).sum + mult (f p) x = (l.map (fun j => mult (f j) x)).sum + mult v x := by
  rw [sum_split hp (fun j => mult (upd f p v j) x), sum_split hp (fun j => mult (f j) x), upd_same]
  have : (l.erase p).map (fun j => mult (upd f p v j) x) = (l.erase p).map (fun j => mult (f j) x) := by
    apply List.map_congr_left
    intro j hj
    have := ((List.Nodup.mem_erase_iff hnd).1 hj).1
    rw [upd_other _ _ _ _ this]
  rw [this]; omega

theorem hold_decomp (s : Sys) (hnd : s.act.Nodup) {p : Nat} (hp : p ∈ s.act) (x : Nat) :
    Hold s x = mult s.q x + (mult (s.a p) x + ((s.act.erase p).map (fun j => mult (s.a j) x)).sum) := by
  unfold Hold; rw [sum_split hp]

theorem mult_a_le {s : Sys} (hnd : s.act.Nodup) {p : Nat} (hp : p ∈ s.act) (x : Nat) :
    mult s.q x + mult (s.a p) x ≤ Hold s x := by
  rw [hold_decomp s hnd hp x]; omega

/-! ### The moves conserve -/

theorem cons_verify {st st' : Store} (s : Sys) (hmono : ∀ x, st.V x → st'.V x) : Cons st' s s :=
  fun x => ⟨Nat.le_refl _, fun _ => rfl⟩

theorem cons_prune {n : Nat} (st : Store) (p : Nat) (s : Sys) (hs : Sized n s) (hp : p ∈ s.act)
    (ho : ∀ x, Hold s x ≤ 1) (hr : (retainMissing st n (s.a p)).length < n) : Cons st s (pruneMv st n p s) := by
  intro x
  have h1 := sum_upd hs.2.2 hp s.a (retainMissing st n (s.a p)) x
  have h2 := retainMissing_mult_room st (s.a p) hr (fun y => by have := mult_a_le hs.2.2 hp y; have := ho y; omega) x
  have h3 := mult_a_le hs.2.2 hp x
  have h4 := ho x
  simp only [Hold, pruneMv] at *
  by_cases hv : st.V x = true
  · simp only [hv, if_true] at h2; refine ⟨by omega, fun h => absurd hv h⟩
  · simp [hv] at h2; simp [hv]; omega


theorem cons_topUp {n : Nat} (hn : 0 < n) (st : Store) (fuel want p : Nat) (s : Sys) (hs : Sized n s) (hp : p ∈ s.act)
    (ho : ∀ x, Hold s x ≤ 1) (hr : (tc st n want fuel 0 s.q []).2.length < n)
    (hl : ((topUpMv st n fuel want p s).a p).length < n) : Cons st s (topUpMv st n fuel want p s) := by
  intro x
  have hlen : (retainMissing st n (s.a p)).length < n := by
    simp only [topUpMv, upd_same] at hl
    exact Nat.lt_of_le_of_lt (foldl_push_length_ge n _ _) hl
  have hqa : ∀ y, mult s.q y + mult (s.a p) y ≤ 1 := fun y => Nat.le_trans (mult_a_le hs.2.2 hp y) (ho y)
  have hR := retainMissing_mult_room st (s.a p) hlen (fun y => by have := hqa y; omega)
  have hT := tc_mult st hn want fuel 0 s.q [] hs.1 hr (fun y => by simp [mult]; have := hqa y; omega)
  have hT1 : ∀ y, mult (tc st n want fuel 0 s.q []).1 y + mult (tc st n want fuel 0 s.q []).2 y ≤ mult s.q y := by
    intro y; have := (hT y).1; simpa [mult] using this
  have hT2 : ∀ y, ¬ st.V y → mult (tc st n want fuel 0 s.q []).1 y + mult (tc st n want fuel 0 s.q []).2 y = mult s.q y := by
    intro y hy; have := (hT y).2.1 hy; simpa [mult] using this
  have hT3 : ∀ y, st.V y → mult (tc st n want fuel 0 s.q []).2 y = 0 := by
    intro y hy; have := (hT y).2.2 hy; simpa [mult] using this
  have hX : ∀ y, mult (extend n (retainMissing st n (s.a p)) (tc st n want fuel 0 s.q []).2) y =
      mult (retainMissing st n (s.a p)) y + mult (tc st n want fuel 0 s.q []).2 y := by
    intro y
    apply foldl_push_mult_room _ (by simpa [topUpMv, upd_same, extend] using hl)
    intro z
    rw [hR z]
    by_cases hv : st.V z = true
    · have := hT3 z hv; simp only [hv, if_true]; omega
    · have := hT2 z hv; have := hqa z; simp only [hv]; simp; omega
  have h1 := sum_upd hs.2.2 hp s.a (extend n (retainMissing st n (s.a p)) (tc st n want fuel 0 s.q []).2) x
  have h3 := hX x
  have h5 := mult_a_le hs.2.2 hp x
  have h2 := hR x
  have h4 := hT1 x
  simp only [Hold] at h5 ⊢
  simp only [topUpMv]
  refine ⟨?_, fun hv => ?_⟩
  · by_cases hv : st.V x = true
    · simp only [hv, if_true] at h2; omega
    · simp only [hv] at h2; simp at h2; omega
  · have h6 := hT2 x hv
    simp only [hv] at h2; simp at h2
    omega

theorem cons_evict {n : Nat} (hn : 0 < n) (st : Store) (p : Nat) (s : Sys) (hs : Sized n s) (hp : p ∈ s.act)
    (ho : ∀ x, Hold s x ≤ 1) (hr : (retainMissing st n (s.a p)).length < n)
    (hq : (evictMv st n p s).q.length < n) : Cons st s (evictMv st n p s) := by
  intro x
  have hqa : ∀ y, mult s.q y + mult (s.a p) y ≤ 1 := fun y => Nat.le_trans (mult_a_le hs.2.2 hp y) (ho y)
  have hR := retainMissing_mult_room st (s.a p) hr (fun y => by have := hqa y; omega) x
  have hE := evictQueue_mult_room s.q (retainMissing st n (s.a p)) hq x
  have h5 := hold_decomp s hs.2.2 hp x
  have h6 : (((s.act.erase p).map (fun j => mult (upd s.a p [] j) x)).sum) =
      ((s.act.erase p).map (fun j => mult (s.a j) x)).sum := by
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [upd_other _ _ _ _ ((List.Nodup.mem_erase_iff hs.2.2).1 hj).1]
  simp only [Hold] at h5
  simp only [Hold, evictMv]
  refine ⟨?_, fun hv => ?_⟩
  · by_cases hv : st.V x = true
    · simp only [hv, if_true] at hR; omega
    · simp only [hv] at hR; simp at hR; omega
  · simp only [hv] at hR; simp at hR; omega

theorem sum_ite_zero (l : List Nat) (c : Prop) [Decidable c] (g : Nat → Nat) :
    (l.map (fun j => if c then 0 else g j)).sum = if c then 0 else (l.map g).sum := by
  by_cases h : c
  · simp only [h, if_true]
    induction l with
    | nil => rfl
    | cons a t ih => simp [ih]
  · simp [h]

theorem mult_ab_le {s : Sys} (hnd : s.act.Nodup) {p b : Nat} (hp : p ∈ s.act) (hb : b ∈ s.act) (hbp : b ≠ p)
    (x : Nat) : mult (s.a p) x + mult (s.a b) x ≤ Hold s x := by
  rw [hold_decomp s hnd hp x]
  have hbe : b ∈ s.act.erase p := (List.Nodup.mem_erase_iff hnd).2 ⟨hbp, hb⟩
  rw [sum_split hbe (fun j => mult (s.a j) x)]
  omega

theorem cons_steal {n : Nat} (hn : 0 < n) (st : Store) (keep p b : Nat) (s : Sys) (hs : Sized n s) (hp : p ∈ s.act)
    (hb : b ∈ s.act) (hbp : b ≠ p) (ho : ∀ x, Hold s x ≤ 1)
    (hret : ∀ j ∈ s.act, (retainMissing st n (s.a j)).length < n)
    (h1 : (stealSplit n keep 0 (retainMissing st n (s.a b)) [] []).1.length < n)
    (h2 : (stealSplit n keep 0 (retainMissing st n (s.a b)) [] []).2.length < n)
    (hlp : ((stealMv st n keep p b s).a p).length < n) (hlb : ((stealMv st n keep p b s).a b).length < n) :
    Cons st s (stealMv st n keep p b s) := by
  intro x
  obtain ⟨a1, ha1⟩ : ∃ a1 : Nat → List Span, a1 = fun j => if j ∈ s.act then retainMissing st n (s.a j) else s.a j :=
    ⟨_, rfl⟩
  have hqa : ∀ j ∈ s.act, ∀ y, mult (s.a j) y ≤ 1 := fun j hj y =>
    Nat.le_trans (Nat.le_trans (Nat.le_add_left _ (mult s.q y)) (mult_a_le hs.2.2 hj y)) (ho y)
  have hA : ∀ j ∈ s.act, ∀ y, mult (a1 j) y = if st.V y then 0 else mult (s.a j) y := by
    intro j hj y
    rw [ha1]; simp only [if_pos hj]
    exact retainMissing_mult_room st (s.a j) (hret j hj) (hqa j hj) y
  have hl0 : a1 b = retainMissing st n (s.a b) := by rw [ha1]; simp [hb]
  obtain ⟨r, hr0⟩ : ∃ r, r = stealSplit n keep 0 (a1 b) [] [] := ⟨_, rfl⟩
  have hr : r = stealSplit n keep 0 (retainMissing st n (s.a b)) [] [] := by rw [hr0, hl0]
  have hr1 : r.1.length < n := by rw [hr]; exact h1
  have hr2 : r.2.length < n := by rw [hr]; exact h2
  have hS : ∀ y, mult r.1 y + mult r.2 y = mult (a1 b) y := by
    intro y
    rw [hr, hl0]
    exact stealSplit_mult_room hn keep _ (fun z => by
      rw [retainMissing_mult_room st _ (hret b hb) (hqa b hb)]; split <;> simp [hqa b hb z]) h1 h2 y
  have e : stealMv st n keep p b s = { s with a := upd (upd a1 b (extend n [] r.1)) p (extend n ((upd a1 b (extend n [] r.1)) p) r.2) } := by
    subst ha1; subst hr0; rfl
  have hb2 : (upd a1 b (extend n [] r.1)) p = a1 p := upd_other _ _ _ _ hbp.symm
  have hPl : ((stealMv st n keep p b s).a p).length < n := hlp
  rw [e] at hPl hlb
  simp only [upd_same, hb2] at hPl
  have hBl : (extend n [] r.1).length < n := by
    simp only [upd_other _ _ _ _ hbp, upd_same] at hlb; exact hlb
  have hmp : ∀ y, mult (extend n (a1 p) r.2) y = mult (a1 p) y + mult r.2 y := by
    intro y
    apply foldl_push_mult_room _ (by simpa [extend] using hPl)
    intro z
    have := hS z
    have := hA p hp z
    have := hA b hb z
    have := mult_ab_le hs.2.2 hp hb hbp z
    have := ho z
    by_cases hv : st.V z = true <;> simp only [hv, Bool.false_eq_true, if_true, if_false] at * <;> omega
  have hmb : ∀ y, mult (extend n [] r.1) y = mult r.1 y := by
    intro y
    have := foldl_push_mult_room (n := n) r.1 (l := []) (by simpa [extend] using hBl) (fun z => by
      have := hS z; have := hA b hb z; have := hqa b hb z
      by_cases hv : st.V z = true <;> simp only [hv, Bool.false_eq_true, if_true, if_false] at * <;> simp [mult] <;> omega) y
    simpa [extend, mult] using this
  have h1' := sum_upd hs.2.2 hp (upd a1 b (extend n [] r.1)) (extend n (a1 p) r.2) x
  have h2' := sum_upd hs.2.2 hb a1 (extend n [] r.1) x
  rw [hb2] at h1'
  have hsum : (s.act.map (fun j => mult (a1 j) x)).sum = if st.V x then 0 else (s.act.map (fun j => mult (s.a j) x)).sum := by
    rw [← sum_ite_zero]
    congr 1
    apply List.map_congr_left
    intro j hj
    exact hA j hj x
  have hH : Hold (stealMv st n keep p b s) x = mult s.q x +
      (s.act.map (fun j => mult (upd (upd a1 b (extend n [] r.1)) p (extend n (a1 p) r.2) j) x)).sum := by
    rw [e]; simp only [Hold, hb2]
  have h3 := hmp x
  have h4 := hmb x
  have h5 := hS x
  refine ⟨?_, fun hv => ?_⟩
  · rw [hH]
    by_cases hv : st.V x = true
    · simp only [hv, if_true] at hsum; simp only [Hold]; omega
    · simp only [hv, Bool.false_eq_true, if_false] at hsum; simp only [Hold]; omega
  · rw [hH]
    simp only [hv, Bool.false_eq_true, if_false] at hsum; simp only [Hold]; omega

theorem sum_map_zero (l : List Nat) : (l.map (fun _ => 0)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem exact_start {nw n : Nat} (st : Store) (want : List Span) (ps : List Nat) (hwant : ∀ x, mult want x ≤ 1)
    (hr : (retainMissing st nw want).length < nw) (hq : (startSys st nw n want ps).q.length < n) :
    ExactS (cov want) st (startSys st nw n want ps) := by
  have hR : ∀ y, mult (retainMissing st nw want) y = if st.V y then 0 else mult want y :=
    retainMissing_mult_room st want hr hwant
  have hQ : ∀ y, mult (startSys st nw n want ps).q y = if st.V y then 0 else mult want y := by
    intro y
    have hq' : (extend n [] (retainMissing st nw want)).length < n := hq
    have := foldl_push_mult_room (n := n) (retainMissing st nw want) (l := []) hq'
      (fun z => by simp only [mult]; rw [hR z]; have := hwant z; split <;> omega) y
    simp only [startSys, extend]
    rw [this, hR y]; simp [mult]
  have hH : ∀ y, Hold (startSys st nw n want ps) y = if st.V y then 0 else mult want y := by
    intro y
    simp only [Hold, startSys, mult, Nat.add_zero] at hQ ⊢
    simp only [sum_map_zero, Nat.add_zero]
    simpa [startSys, extend] using hQ y
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx hv => ?_⟩
  · rw [hH]; have := hwant x; split <;> omega
  · rw [hH]
    have : mult want x = 0 := by
      by_cases h : 0 < mult want x
      · exact absurd ((cov_iff_mult want x).2 h) hx
      · omega
    split <;> omega
  · rw [hH]
    have h1 := (cov_iff_mult want x).1 hx
    have h2 := hwant x
    simp only [hv, Bool.false_eq_true, if_false]
    omega

/-- The reachable states of a striped fetch, each move guarded by the room it needs: the lists it builds end below
capacity, so none of its pushes widened. -/
inductive ReachR (nw n : Nat) (want : List Span) : Store → Sys → Prop
  | start (st : Store) (ps : List Nat) : ps.Nodup → (retainMissing st nw want).length < nw →
      (startSys st nw n want ps).q.length < n → ReachR nw n want st (startSys st nw n want ps)
  | verify (st st' : Store) (s : Sys) : ReachR nw n want st s → (∀ x, st.V x → st'.V x) → ReachR nw n want st' s
  | topUp (st : Store) (s : Sys) (fuel want' p : Nat) :
      ReachR nw n want st s → p ∈ s.act → (tc st n want' fuel 0 s.q []).2.length < n →
      ((topUpMv st n fuel want' p s).a p).length < n → ReachR nw n want st (topUpMv st n fuel want' p s)
  | prune (st : Store) (s : Sys) (p : Nat) :
      ReachR nw n want st s → p ∈ s.act → ((pruneMv st n p s).a p).length < n →
      ReachR nw n want st (pruneMv st n p s)
  | steal (st : Store) (s : Sys) (keep p b : Nat) :
      ReachR nw n want st s → p ∈ s.act → b ∈ s.act → b ≠ p →
      (∀ j ∈ s.act, (retainMissing st n (s.a j)).length < n) →
      (stealSplit n keep 0 (retainMissing st n (s.a b)) [] []).1.length < n →
      (stealSplit n keep 0 (retainMissing st n (s.a b)) [] []).2.length < n →
      ((stealMv st n keep p b s).a p).length < n → ((stealMv st n keep p b s).a b).length < n →
      ReachR nw n want st (stealMv st n keep p b s)
  | evict (st : Store) (s : Sys) (p : Nat) :
      ReachR nw n want st s → p ∈ s.act → s.act.erase p ≠ [] → (retainMissing st n (s.a p)).length < n →
      (evictMv st n p s).q.length < n → ReachR nw n want st (evictMv st n p s)

theorem reachR_reach {nw n : Nat} {want : List Span} {st : Store} {s : Sys} (h : ReachR nw n want st s) :
    Reach nw n want st s := by
  induction h with
  | start st ps hps _ _ => exact Reach.start st ps hps
  | verify st st' s _ hm ih => exact Reach.verify st st' s ih hm
  | topUp st s fuel want' p _ hp _ _ ih => exact Reach.topUp st s fuel want' p ih hp
  | prune st s p _ hp _ ih => exact Reach.prune st s p ih hp
  | steal st s keep p b _ hp hb hbp _ _ _ _ _ ih => exact Reach.steal st s keep p b ih hp hb hbp
  | evict st s p _ hp hne _ _ ih => exact Reach.evict st s p ih hp hne

/-- The run-wide exact partition: in every state of a striped fetch with room, the queue and the active providers'
lists hold every byte at most once, nothing outside the wanted bytes, and every wanted byte the store has not
verified exactly once. -/
theorem reachR_exact {nw n : Nat} (hnw : 0 < nw) (hn : 0 < n) (want : List Span) (hwant : ∀ x, mult want x ≤ 1)
    (st : Store) (s : Sys) (h : ReachR nw n want st s) : ExactS (cov want) st s := by
  induction h with
  | start st ps hps hr hq => exact exact_start st want ps hwant hr hq
  | verify st st' s hr hm ih =>
    exact ⟨ih.once, ih.outside, fun x hx hv => ih.wanted x hx (fun h => hv (hm x h))⟩
  | topUp st s fuel want' p hr hp h1 h2 ih =>
    have hs := (reach_inv hnw hn want st s (reachR_reach hr)).1
    exact exactS_cons ih (cons_topUp hn st fuel want' p s hs hp ih.once h1 h2)
  | prune st s p hr hp h1 ih =>
    have hs := (reach_inv hnw hn want st s (reachR_reach hr)).1
    exact exactS_cons ih (cons_prune st p s hs hp ih.once (by
      simpa [pruneMv, upd_same] using h1))
  | steal st s keep p b hr hp hb hbp h0 h1 h2 h3 h4 ih =>
    have hs := (reach_inv hnw hn want st s (reachR_reach hr)).1
    exact exactS_cons ih (cons_steal hn st keep p b s hs hp hb hbp ih.once h0 h1 h2 h3 h4)
  | evict st s p hr hp hne h1 h2 ih =>
    have hs := (reach_inv hnw hn want st s (reachR_reach hr)).1
    exact exactS_cons ih (cons_evict hn st p s hs hp ih.once h1 h2)

/-- A fetch that has emptied the queue and every active list, in a run with room, has every wanted byte verified:
no wanted byte is held once it is verified, and an unverified one is held exactly once. -/
theorem reachR_done {nw n : Nat} (hnw : 0 < nw) (hn : 0 < n) (want : List Span) (hwant : ∀ x, mult want x ≤ 1)
    (st : Store) (s : Sys) (h : ReachR nw n want st s) (hq : s.q = []) (ha : ∀ p ∈ s.act, s.a p = []) :
    ∀ x, cov want x → st.V x := by
  intro x hx
  by_cases hv : st.V x
  · exact hv
  · have h1 := (reachR_exact hnw hn want hwant st s h).wanted x hx hv
    have h2 : Hold s x = 0 := by
      simp only [Hold, hq, mult]
      have : (s.act.map (fun p => mult (s.a p) x)).sum = 0 := by
        have : ∀ l : List Nat, (∀ p ∈ l, p ∈ s.act) → (l.map (fun p => mult (s.a p) x)).sum = 0 := by
          intro l
          induction l with
          | nil => intro _; rfl
          | cons a t ih =>
            intro hl
            simp only [List.map_cons, List.sum_cons, ha a (hl a (by simp)), mult, Nat.zero_add]
            exact ih (fun p hp => hl p (by simp [hp]))
        exact this s.act (fun p hp => hp)
      omega
    omega

end Pinc.ValuesSched

#audit_axioms Pinc.ValuesSched.cons_topUp
#audit_axioms Pinc.ValuesSched.cons_steal
#audit_axioms Pinc.ValuesSched.cons_evict
#audit_axioms Pinc.ValuesSched.cons_prune
#audit_axioms Pinc.ValuesSched.exact_start
#audit_axioms Pinc.ValuesSched.reachR_exact
#audit_axioms Pinc.ValuesSched.reachR_done
