import Pinc.Axioms
import Pinc.ValuesSchedExactRun

/-!
# `RangeList::split`: order and exactly once

For a sorted list (spans in increasing order, no overlap) and shares that end below capacity (no push widened), the
shares hold every byte of the list in exactly one share (`split_once`), none beyond the first `clamp(k)` shares, and
the shares keep the list's order: every byte of share `i` is below every byte of share `j` for `i < j`
(`split_order`). With `split_cov` and `split_aligned` this is the whole contract of `split`.

The invariant of the loop (`SInv`): the shares above the current one are empty, every byte placed is below the
cursor, and the shares are in order.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesSched

/-- The multiplicity of a byte over the first `K` shares. -/
def shareSum (K : Nat) (out : Nat → List Span) (x : Nat) : Nat := ((List.range K).map (fun i => mult (out i) x)).sum

theorem shareSum_upd {K idx : Nat} (h : idx < K) (f : Nat → List Span) (v : List Span) (x : Nat) :
    shareSum K (upd f idx v) x + mult (f idx) x = shareSum K f x + mult v x :=
  sum_upd (List.nodup_range) (List.mem_range.2 h) f v x

structure SInv (K f idx : Nat) (out : Nat → List Span) : Prop where
  lt : idx < K
  above : ∀ i, idx < i → out i = []
  below : ∀ i y, 0 < mult (out i) y → y < f
  order : ∀ i j x y, i < j → 0 < mult (out i) x → 0 < mult (out j) y → x < y

theorem SInv.mono {K f idx : Nat} {out : Nat → List Span} (h : SInv K f idx out) {f' : Nat} (hf : f ≤ f') :
    SInv K f' idx out :=
  ⟨h.lt, h.above, fun i y hy => Nat.lt_of_lt_of_le (h.below i y hy) hf, h.order⟩

theorem SInv.succ {K f idx : Nat} {out : Nat → List Span} (h : SInv K f idx out) (hk : idx + 1 < K) :
    SInv K f (idx + 1) out :=
  ⟨hk, fun i hi => h.above i (by omega), h.below, h.order⟩

theorem sinv_push {n K cur idx : Nat} {out : Nat → List Span} (h : SInv K cur idx out) (t : Nat)
    (hroom : (out idx).length < n) :
    SInv K (cur + t) idx (upd out idx (push n (out idx) ⟨cur, t⟩)) ∧
    ∀ y, mult (push n (out idx) ⟨cur, t⟩) y = mult (out idx) y + (if cur ≤ y ∧ y < cur + t then 1 else 0) := by
  have hd : ∀ y, (Span.mk cur t).Mem y → mult (out idx) y = 0 := by
    intro y hy
    by_cases h0 : 0 < mult (out idx) y
    · have := h.below idx y h0; simp only [Span.Mem] at hy; omega
    · omega
  have hm : ∀ y, mult (push n (out idx) ⟨cur, t⟩) y = mult (out idx) y + (if cur ≤ y ∧ y < cur + t then 1 else 0) := by
    intro y
    rw [push_mult hroom _ hd y]
    by_cases hc : cur ≤ y ∧ y < cur + t <;> simp [Span.Mem, hc]
  refine ⟨⟨h.lt, ?_, ?_, ?_⟩, hm⟩
  · intro i hi
    rw [upd_other _ _ _ _ (by omega)]; exact h.above i hi
  · intro i y hy
    by_cases hii : i = idx
    · subst hii; rw [upd_same, hm] at hy
      by_cases hc : cur ≤ y ∧ y < cur + t
      · omega
      · simp only [hc, if_false] at hy
        have := h.below i y (by omega); omega
    · rw [upd_other _ _ _ _ hii] at hy
      have := h.below i y hy; omega
  · intro i j x y hij hx hy
    by_cases hi : i = idx
    · subst hi
      rw [upd_other _ _ _ _ (by omega)] at hy
      have := h.above j hij; rw [this] at hy; simp [mult] at hy
    · rw [upd_other _ _ _ _ hi] at hx
      by_cases hj : j = idx
      · subst hj; rw [upd_same, hm] at hy
        by_cases hc : cur ≤ y ∧ y < cur + t
        · have := h.below i x hx; omega
        · simp only [hc, if_false] at hy
          exact h.order i j x y hij hx (by omega)
      · rw [upd_other _ _ _ _ hj] at hy
        exact h.order i j x y hij hx hy

theorem splitSpan_length_ge (n k share e : Nat) :
    ∀ m cur idx acc (out : Nat → List Span), e - cur = m → ∀ i,
      (out i).length ≤ ((splitSpan n k share e cur idx acc out).2.2 i).length := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro cur idx acc out hm i
    unfold splitSpan
    by_cases hc : cur < e
    · rw [dif_pos hc]
      have hst := stake_pos (decide (k ≤ idx + 1)) share acc (e - cur) (by omega)
      have hup : (out i).length ≤ (upd out idx (push n (out idx) ⟨cur, stake (decide (k ≤ idx + 1)) share acc (e - cur)⟩) i).length := by
        unfold upd; split
        · rename_i hh; subst hh; exact push_length_ge n _ _
        · exact Nat.le_refl _
      by_cases hcut : share ≤ acc + stake (decide (k ≤ idx + 1)) share acc (e - cur) ∧ decide (k ≤ idx + 1) = false
      · rw [if_pos hcut]
        exact Nat.le_trans hup (ih (e - (cur + stake (decide (k ≤ idx + 1)) share acc (e - cur))) (by omega) _ _ _ _ rfl i)
      · rw [if_neg hcut]
        exact Nat.le_trans hup (ih (e - (cur + stake (decide (k ≤ idx + 1)) share acc (e - cur))) (by omega) _ _ _ _ rfl i)
    · rw [dif_neg hc]; exact Nat.le_refl _

theorem splitFold_length_ge (n k share : Nat) (l : List Span) :
    ∀ (st : SplitState) i, (st.2.2 i).length ≤ ((splitFold n k share l st).2.2 i).length := by
  induction l with
  | nil => intro st i; exact Nat.le_refl _
  | cons s t ih =>
    intro st i
    exact Nat.le_trans (splitSpan_length_ge n k share (s.off + s.len) _ s.off st.1 st.2.1 st.2.2 rfl i)
      (ih (splitSpan n k share (s.off + s.len) s.off st.1 st.2.1 st.2.2) i)

theorem ite_add3 (cur t e x : Nat) (h : cur + t ≤ e) :
    (if cur ≤ x ∧ x < cur + t then 1 else 0) + (if cur + t ≤ x ∧ x < e then 1 else 0) =
      (if cur ≤ x ∧ x < e then 1 else 0) := by
  by_cases a : cur ≤ x ∧ x < cur + t <;> by_cases b : cur + t ≤ x ∧ x < e <;> by_cases c : cur ≤ x ∧ x < e <;>
    simp [a, b, c] <;> omega

theorem splitSpan_once (n K share : Nat) (hn : 0 < n) (e : Nat) :
    ∀ m cur idx acc (out : Nat → List Span), e - cur = m → cur ≤ e → SInv K cur idx out →
      (∀ i, ((splitSpan n K share e cur idx acc out).2.2 i).length < n) →
      SInv K e (splitSpan n K share e cur idx acc out).1 (splitSpan n K share e cur idx acc out).2.2 ∧
      ∀ x, shareSum K (splitSpan n K share e cur idx acc out).2.2 x =
        shareSum K out x + (if cur ≤ x ∧ x < e then 1 else 0) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro cur idx acc out hm hce hinv hroom
    by_cases hc : cur < e
    · have e1 : splitSpan n K share e cur idx acc out =
          (if share ≤ acc + stake (decide (K ≤ idx + 1)) share acc (e - cur) ∧ decide (K ≤ idx + 1) = false then
            splitSpan n K share e (cur + stake (decide (K ≤ idx + 1)) share acc (e - cur)) (idx + 1) 0
              (upd out idx (push n (out idx) ⟨cur, stake (decide (K ≤ idx + 1)) share acc (e - cur)⟩))
          else splitSpan n K share e (cur + stake (decide (K ≤ idx + 1)) share acc (e - cur)) idx
              (acc + stake (decide (K ≤ idx + 1)) share acc (e - cur))
              (upd out idx (push n (out idx) ⟨cur, stake (decide (K ≤ idx + 1)) share acc (e - cur)⟩))) := by
        rw [splitSpan, dif_pos hc]
      have hst := stake_pos (decide (K ≤ idx + 1)) share acc (e - cur) (by omega)
      rw [e1] at hroom ⊢
      generalize ht : stake (decide (K ≤ idx + 1)) share acc (e - cur) = t at *
      by_cases hcut : share ≤ acc + t ∧ decide (K ≤ idx + 1) = false
      · rw [if_pos hcut] at hroom ⊢
        have hk : idx + 1 < K := by have := hcut.2; simp at this; omega
        have h1 := splitSpan_length_ge n K share e (e - (cur + t)) (cur + t) (idx + 1) 0
          (upd out idx (push n (out idx) ⟨cur, t⟩)) rfl idx
        rw [upd_same] at h1
        have hl : (out idx).length < n :=
          Nat.lt_of_le_of_lt (Nat.le_trans (push_length_ge n (out idx) ⟨cur, t⟩) h1) (hroom idx)
        obtain ⟨hinv', hm'⟩ := sinv_push hinv t hl
        obtain ⟨r1, r2⟩ := ih (e - (cur + t)) (by omega) (cur + t) (idx + 1) 0 _ rfl (by omega) (hinv'.succ hk) hroom
        refine ⟨r1, fun x => ?_⟩
        rw [r2 x]
        have := shareSum_upd hinv.lt out (push n (out idx) ⟨cur, t⟩) x
        have := hm' x
        have := ite_add3 cur t e x (by omega)
        omega
      · rw [if_neg hcut] at hroom ⊢
        have h1 := splitSpan_length_ge n K share e (e - (cur + t)) (cur + t) idx (acc + t)
          (upd out idx (push n (out idx) ⟨cur, t⟩)) rfl idx
        rw [upd_same] at h1
        have hl : (out idx).length < n :=
          Nat.lt_of_le_of_lt (Nat.le_trans (push_length_ge n (out idx) ⟨cur, t⟩) h1) (hroom idx)
        obtain ⟨hinv', hm'⟩ := sinv_push hinv t hl
        obtain ⟨r1, r2⟩ := ih (e - (cur + t)) (by omega) (cur + t) idx (acc + t) _ rfl (by omega) hinv' hroom
        refine ⟨r1, fun x => ?_⟩
        rw [r2 x]
        have := shareSum_upd hinv.lt out (push n (out idx) ⟨cur, t⟩) x
        have := hm' x
        have := ite_add3 cur t e x (by omega)
        omega
    · rw [splitSpan, dif_neg hc] at hroom ⊢
      have : cur = e := by omega
      subst this
      refine ⟨hinv, fun x => ?_⟩
      simp

theorem splitFold_once (n K share : Nat) (hn : 0 < n) (l : List Span) (hl : Sorted l) :
    ∀ (st : SplitState) f, (∀ s ∈ l, f ≤ s.off) → SInv K f st.1 st.2.2 →
      (∀ i, ((splitFold n K share l st).2.2 i).length < n) →
      (∃ F, SInv K F (splitFold n K share l st).1 (splitFold n K share l st).2.2) ∧
      ∀ x, shareSum K (splitFold n K share l st).2.2 x = shareSum K st.2.2 x + mult l x := by
  induction l with
  | nil => intro st f _ hinv _; exact ⟨⟨f, hinv⟩, fun x => by simp [splitFold, mult]⟩
  | cons s t ih =>
    intro st f hf hinv hroom
    have hs : Sorted t := sorted_tail hl
    have hpc := List.pairwise_cons.1 hl
    have hfold : splitFold n K share (s :: t) st = splitFold n K share t
        (splitSpan n K share (s.off + s.len) s.off st.1 st.2.1 st.2.2) := rfl
    rw [hfold] at hroom ⊢
    have hlen := splitFold_length_ge n K share t (splitSpan n K share (s.off + s.len) s.off st.1 st.2.1 st.2.2)
    obtain ⟨a1, a2⟩ := splitSpan_once n K share hn (s.off + s.len) _ s.off st.1 st.2.1 st.2.2 rfl (by omega)
      (hinv.mono (hf s (by simp))) (fun i => Nat.lt_of_le_of_lt (hlen i) (hroom i))
    obtain ⟨b1, b2⟩ := ih hs (splitSpan n K share (s.off + s.len) s.off st.1 st.2.1 st.2.2) (s.off + s.len)
      (fun u hu => hpc.1 u hu) a1 hroom
    refine ⟨b1, fun x => ?_⟩
    rw [b2 x, a2 x]
    have : mult (s :: t) x = (if s.Mem x then 1 else 0) + mult t x := rfl
    have h3 : (if s.off ≤ x ∧ x < s.off + s.len then 1 else 0) = (if s.Mem x then 1 else 0) := by
      by_cases hh : s.off ≤ x ∧ x < s.off + s.len <;> simp [Span.Mem, hh]
    omega

/-- Every byte of a sorted list lands in exactly one share, none in a share past `clamp(k)`, when no share widened. -/
theorem split_once {n : Nat} (hn : 0 < n) (S k : Nat) (l : List Span) (hl : Sorted l)
    (hroom : ∀ i, (split n S k l i).length < n) (x : Nat) :
    shareSum (clampK S k) (split n S k l) x = mult l x ∧ ∀ i, clampK S k ≤ i → split n S k l i = [] := by
  have hK := clampK_pos S k
  have := splitFold_once n (clampK S k) (max (total l / clampK S k / G * G) G) hn l hl (0, 0, fun _ => []) 0
    (fun s _ => Nat.zero_le _) ⟨by simpa using hK, fun i _ => rfl, fun i y hy => by simp [mult] at hy,
      fun i j x y _ hx => by simp [mult] at hx⟩ hroom
  obtain ⟨⟨F, hF⟩, hsum⟩ := this
  refine ⟨by rw [show split n S k l = (splitFold n (clampK S k) (max (total l / clampK S k / G * G) G) l (0, 0, fun _ => [])).2.2 from rfl, hsum x]; simp [shareSum, mult, sum_map_zero], fun i hi => ?_⟩
  exact hF.above i (by have := hF.lt; omega)

/-- The shares keep the list's order. -/
theorem split_order {n : Nat} (hn : 0 < n) (S k : Nat) (l : List Span) (hl : Sorted l)
    (hroom : ∀ i, (split n S k l i).length < n) {i j x y : Nat} (hij : i < j)
    (hx : cov (split n S k l i) x) (hy : cov (split n S k l j) y) : x < y := by
  have := splitFold_once n (clampK S k) (max (total l / clampK S k / G * G) G) hn l hl (0, 0, fun _ => []) 0
    (fun s _ => Nat.zero_le _) ⟨by simpa using clampK_pos S k, fun i _ => rfl, fun i y hy => by simp [mult] at hy,
      fun i j x y _ hx => by simp [mult] at hx⟩ hroom
  obtain ⟨⟨F, hF⟩, _⟩ := this
  exact hF.order i j x y hij ((cov_iff_mult _ _).1 hx) ((cov_iff_mult _ _).1 hy)

end Pinc.ValuesSched

#audit_axioms Pinc.ValuesSched.splitSpan_once
#audit_axioms Pinc.ValuesSched.splitFold_once
#audit_axioms Pinc.ValuesSched.split_once
#audit_axioms Pinc.ValuesSched.split_order
