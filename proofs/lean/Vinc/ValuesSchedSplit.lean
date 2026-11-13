import Vinc.Axioms
import Vinc.ValuesSchedHoles

/-!
# `RangeList::split`

The loop of `split` over the spans of a list, as the code writes it (`k` clamped to `1..=S`, a share of at least one
group, a cut when the share is full, the last share taking the rest). `split_cov`: every byte of the input lands in a
share; `split_aligned`: for a list of whole groups, every span of every share starts and ends on a group boundary,
so a cut is never inside a group; the share index never leaves `0..k` (the first conjunct of `splitSpan_cov` and `splitFold_cov`).

The fetch calls `split` only with `k = 1` (a fetch of one provider is the only one not striped), where it is the
identity on coverage; the proofs are for every `k`, so a future caller with more providers is covered too.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Vinc.ValuesSched

/-- Replace entry `i` of a family of lists. -/
def upd (f : Nat → List Span) (i : Nat) (v : List Span) : Nat → List Span := fun j => if j = i then v else f j

theorem upd_same (f : Nat → List Span) (i : Nat) (v : List Span) : upd f i v i = v := by simp [upd]
theorem upd_other (f : Nat → List Span) (i j : Nat) (v : List Span) (h : j ≠ i) : upd f i v j = f j := by simp [upd, h]

/-- The bytes taken by one step of the inner loop: the rest of the span, or the room left in the share (at least 1). -/
def stake (last : Bool) (share acc rem : Nat) : Nat := min (if last then rem else max (share - acc) 1) rem

theorem stake_pos (last : Bool) (share acc rem : Nat) (h : 0 < rem) : 0 < stake last share acc rem ∧ stake last share acc rem ≤ rem := by
  unfold stake; cases last <;> simp <;> omega

/-- The inner `while cur < end` loop of `split` for one span. State: the cursor, the share index, the bytes in the share. -/
def splitSpan (n k share e : Nat) (cur idx acc : Nat) (out : Nat → List Span) : Nat × Nat × (Nat → List Span) :=
  if h : cur < e then
    let last := decide (k ≤ idx + 1)
    let take := stake last share acc (e - cur)
    let out' := upd out idx (push n (out idx) ⟨cur, take⟩)
    if share ≤ acc + take ∧ last = false then splitSpan n k share e (cur + take) (idx + 1) 0 out'
    else splitSpan n k share e (cur + take) idx (acc + take) out'
  else (idx, acc, out)
termination_by e - cur
decreasing_by
  all_goals (have := (stake_pos (decide (k ≤ idx + 1)) share acc (e - cur) (by omega)).1; omega)

/-- `RangeList::split` with capacity `n` per share, `S` shares and `k` wanted: the family of shares. -/
def split (n S k : Nat) (l : List Span) : Nat → List Span :=
  let k' := max 1 (min k (max S 1))
  let share := max (total l / k' / G * G) G
  (l.foldl (fun st s => splitSpan n k' share (s.off + s.len) s.off st.1 st.2.1 st.2.2) (0, 0, fun _ => [])).2.2

/-- Every span starts and ends on a group boundary. -/
def Aligned (l : List Span) : Prop := ∀ s ∈ l, s.off % G = 0 ∧ s.len % G = 0

theorem push_aligned {n : Nat} {l : List Span} (hl : Aligned l) {s : Span} (hs : s.off % G = 0 ∧ s.len % G = 0) :
    Aligned (push n l s) := by
  intro t ht
  unfold push at ht
  by_cases h0 : s.len = 0
  · rw [if_pos h0] at ht; exact hl t ht
  · rw [if_neg h0] at ht
    cases hg : l.getLast? with
    | none =>
      rw [hg] at ht
      simp only at ht
      by_cases hn : 0 < n
      · rw [if_pos hn] at ht; simp at ht; subst ht; exact hs
      · rw [if_neg hn] at ht; exact hl t ht
    | some last =>
      rw [hg] at ht
      simp only at ht
      have hlast : last ∈ l := List.mem_of_getLast? hg
      have hla := hl last hlast
      by_cases h1 : (last.off ≤ s.off ∧ s.off ≤ last.off + last.len) ∨ l.length = n
      · rw [if_pos h1] at ht
        rcases List.mem_append.1 ht with h | h
        · exact hl t (List.dropLast_subset l h)
        · simp at h; subst h; simp only [Span.hull, G] at *; omega
      · rw [if_neg h1] at ht
        by_cases h2 : l.length < n
        · rw [if_pos h2] at ht
          rcases List.mem_append.1 ht with h | h
          · exact hl t h
          · simp at h; subst h; exact hs
        · rw [if_neg h2] at ht; exact hl t ht

theorem upd_aligned {out : Nat → List Span} (h : ∀ i, Aligned (out i)) (j : Nat) (v : List Span) (hv : Aligned v) :
    ∀ i, Aligned (upd out j v i) := by
  intro i; unfold upd; split
  · exact hv
  · exact h i

/-- The inner loop keeps the share index below `k`, every share within capacity, and every byte of the span (and
everything already in a share) in some share. -/
theorem splitSpan_cov (n k share : Nat) (hn : 0 < n) (e : Nat) :
    ∀ m cur idx acc (out : Nat → List Span), e - cur = m → idx < k → (∀ i, (out i).length ≤ n) →
      (splitSpan n k share e cur idx acc out).1 < k ∧
      (∀ i, ((splitSpan n k share e cur idx acc out).2.2 i).length ≤ n) ∧
      ∀ x, ((∃ i, i < k ∧ cov (out i) x) ∨ (cur ≤ x ∧ x < e)) → ∃ i, i < k ∧ cov ((splitSpan n k share e cur idx acc out).2.2 i) x := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro cur idx acc out hm hidx hlen
    unfold splitSpan
    by_cases hc : cur < e
    · rw [dif_pos hc]
      have hst := stake_pos (decide (k ≤ idx + 1)) share acc (e - cur) (by omega)
      have hlen' : ∀ i, (upd out idx (push n (out idx) ⟨cur, stake (decide (k ≤ idx + 1)) share acc (e - cur)⟩) i).length ≤ n := by
        intro i; unfold upd; split
        · exact push_length_le hn (hlen idx) _
        · exact hlen i
      have hcov : ∀ x, ((∃ i, i < k ∧ cov (out i) x) ∨ (cur ≤ x ∧ x < e)) →
          ((∃ i, i < k ∧ cov (upd out idx (push n (out idx) ⟨cur, stake (decide (k ≤ idx + 1)) share acc (e - cur)⟩) i) x) ∨
            (cur + stake (decide (k ≤ idx + 1)) share acc (e - cur) ≤ x ∧ x < e)) := by
        intro x hx
        rcases hx with ⟨i, hik, hi⟩ | hx
        · by_cases hii : i = idx
          · subst hii
            exact Or.inl ⟨i, hik, by rw [upd_same]; exact push_cov hn (hlen i) _ x (Or.inl hi)⟩
          · exact Or.inl ⟨i, hik, by rw [upd_other _ _ _ _ hii]; exact hi⟩
        · by_cases hx2 : x < cur + stake (decide (k ≤ idx + 1)) share acc (e - cur)
          · exact Or.inl ⟨idx, hidx, by
              rw [upd_same]
              exact push_cov hn (hlen idx) _ x (Or.inr ⟨hx.1, hx2⟩)⟩
          · exact Or.inr ⟨by omega, hx.2⟩
      by_cases hcut : share ≤ acc + stake (decide (k ≤ idx + 1)) share acc (e - cur) ∧ decide (k ≤ idx + 1) = false
      · rw [if_pos hcut]
        have hk : idx + 1 < k := by
          have := hcut.2; simp at this; omega
        obtain ⟨h1, h2, h3⟩ := ih (e - (cur + stake (decide (k ≤ idx + 1)) share acc (e - cur))) (by omega) (cur + stake (decide (k ≤ idx + 1)) share acc (e - cur)) (idx + 1) 0 _ rfl hk hlen'
        exact ⟨h1, h2, fun x hx => h3 x (hcov x hx)⟩
      · rw [if_neg hcut]
        obtain ⟨h1, h2, h3⟩ := ih (e - (cur + stake (decide (k ≤ idx + 1)) share acc (e - cur))) (by omega) (cur + stake (decide (k ≤ idx + 1)) share acc (e - cur)) idx (acc + stake (decide (k ≤ idx + 1)) share acc (e - cur)) _ rfl hidx hlen'
        exact ⟨h1, h2, fun x hx => h3 x (hcov x hx)⟩
    · rw [dif_neg hc]
      refine ⟨hidx, hlen, fun x hx => ?_⟩
      rcases hx with hx | hx
      · exact hx
      · omega

/-- On whole groups every cut of the inner loop is on a group boundary: all spans written to a share are aligned. -/
theorem splitSpan_aligned (n k share : Nat) (hn : 0 < n) (hsh : share % G = 0) (e : Nat) (he : e % G = 0) :
    ∀ m cur idx acc (out : Nat → List Span), e - cur = m → idx < k → (k ≤ idx + 1 ∨ acc < share) →
      cur % G = 0 → acc % G = 0 → (∀ i, Aligned (out i)) →
      (∀ i, Aligned ((splitSpan n k share e cur idx acc out).2.2 i)) ∧
      (splitSpan n k share e cur idx acc out).1 < k ∧
      (k ≤ (splitSpan n k share e cur idx acc out).1 + 1 ∨ (splitSpan n k share e cur idx acc out).2.1 < share) ∧
      (splitSpan n k share e cur idx acc out).2.1 % G = 0 := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro cur idx acc out hm hidx hacc hcur hacm hal
    unfold splitSpan
    by_cases hc : cur < e
    · rw [dif_pos hc]
      have hst := stake_pos (decide (k ≤ idx + 1)) share acc (e - cur) (by omega)
      have htake : stake (decide (k ≤ idx + 1)) share acc (e - cur) % G = 0 := by
        unfold stake
        by_cases hl : k ≤ idx + 1
        · simp [hl]; simp only [G] at *; omega
        · have : acc < share := by simp [hl] at hacc ⊢; omega
          simp [hl]; simp only [G] at *; omega
      have hal' : ∀ i, Aligned (upd out idx (push n (out idx) ⟨cur, stake (decide (k ≤ idx + 1)) share acc (e - cur)⟩) i) :=
        upd_aligned hal idx _ (push_aligned (hal idx) ⟨hcur, htake⟩)
      by_cases hcut : share ≤ acc + stake (decide (k ≤ idx + 1)) share acc (e - cur) ∧ decide (k ≤ idx + 1) = false
      · rw [if_pos hcut]
        have hk : idx + 1 < k := by
          have := hcut.2; simp at this; omega
        exact ih (e - (cur + stake (decide (k ≤ idx + 1)) share acc (e - cur))) (by omega) (cur + stake (decide (k ≤ idx + 1)) share acc (e - cur)) (idx + 1) 0 _ rfl hk (Or.inr (by simp only [G] at hsh; omega)) (by simp only [G] at *; omega) (by simp) hal'
      · rw [if_neg hcut]
        have hk2 : k ≤ idx + 1 ∨ acc + stake (decide (k ≤ idx + 1)) share acc (e - cur) < share := by
          by_cases hl : k ≤ idx + 1
          · exact Or.inl hl
          · right
            by_cases hh : acc + stake (decide (k ≤ idx + 1)) share acc (e - cur) < share
            · exact hh
            · exact absurd ⟨by omega, by simp [hl]⟩ hcut
        exact ih (e - (cur + stake (decide (k ≤ idx + 1)) share acc (e - cur))) (by omega) (cur + stake (decide (k ≤ idx + 1)) share acc (e - cur)) idx (acc + stake (decide (k ≤ idx + 1)) share acc (e - cur)) _ rfl hidx hk2 (by simp only [G] at *; omega) (by simp only [G] at *; omega) hal'
    · rw [dif_neg hc]; exact ⟨hal, hidx, hacc, hacm⟩

/-- The state of the outer loop: the share index, the bytes in the share and the shares. -/
abbrev SplitState := Nat × Nat × (Nat → List Span)

/-- The outer loop. -/
def splitFold (n k share : Nat) (l : List Span) (st : SplitState) : SplitState :=
  l.foldl (fun st s => splitSpan n k share (s.off + s.len) s.off st.1 st.2.1 st.2.2) st

theorem splitFold_cov (n k share : Nat) (hn : 0 < n) (l : List Span) :
    ∀ (st : SplitState), st.1 < k → (∀ i, (st.2.2 i).length ≤ n) →
      (splitFold n k share l st).1 < k ∧ (∀ i, ((splitFold n k share l st).2.2 i).length ≤ n) ∧
      ∀ x, ((∃ i, i < k ∧ cov (st.2.2 i) x) ∨ cov l x) → ∃ i, i < k ∧ cov ((splitFold n k share l st).2.2 i) x := by
  induction l with
  | nil => intro st h1 h2; exact ⟨h1, h2, fun x hx => hx.elim id (fun h => absurd h (cov_nil x))⟩
  | cons s t ih =>
    intro st h1 h2
    obtain ⟨a1, a2, a3⟩ := splitSpan_cov n k share hn (s.off + s.len) _ s.off st.1 st.2.1 st.2.2 rfl h1 h2
    obtain ⟨b1, b2, b3⟩ := ih (splitSpan n k share (s.off + s.len) s.off st.1 st.2.1 st.2.2) a1 a2
    refine ⟨b1, b2, fun x hx => b3 x ?_⟩
    rcases hx with hx | hx
    · exact Or.inl (a3 x (Or.inl hx))
    · rw [cov_cons] at hx
      rcases hx with hx | hx
      · exact Or.inl (a3 x (Or.inr hx))
      · exact Or.inr hx

theorem splitFold_aligned (n k share : Nat) (hn : 0 < n) (hsh : share % G = 0) (l : List Span) (hl : Aligned l) :
    ∀ (st : SplitState), st.1 < k → (k ≤ st.1 + 1 ∨ st.2.1 < share) → st.2.1 % G = 0 → (∀ i, Aligned (st.2.2 i)) →
      (∀ i, Aligned ((splitFold n k share l st).2.2 i)) := by
  induction l with
  | nil => intro st _ _ _ h; exact h
  | cons s t ih =>
    intro st h1 h2 h3 h4
    have hs := hl s (by simp)
    obtain ⟨a1, a2, a3, a4⟩ := splitSpan_aligned n k share hn hsh (s.off + s.len) (by simp only [G] at *; omega) _ s.off st.1 st.2.1 st.2.2 rfl h1 h2 hs.1 h3 h4
    exact ih (fun u hu => hl u (by simp [hu])) (splitSpan n k share (s.off + s.len) s.off st.1 st.2.1 st.2.2) a2 a3 a4 a1

/-- The clamped number of shares. -/
def clampK (S k : Nat) : Nat := max 1 (min k (max S 1))

theorem clampK_pos (S k : Nat) : 0 < clampK S k := by unfold clampK; omega
theorem clampK_le (S k : Nat) : clampK S k ≤ max S 1 := by unfold clampK; omega

/-- Every byte of the list lands in a share below `clamp(k)`, which is at most `S`. -/
theorem split_cov {n : Nat} (hn : 0 < n) (S k : Nat) (l : List Span) (x : Nat) (h : cov l x) :
    ∃ i, i < clampK S k ∧ cov (split n S k l i) x := by
  have := splitFold_cov n (clampK S k) (max (total l / clampK S k / G * G) G) hn l (0, 0, fun _ => [])
    (by have := clampK_pos S k; simpa using this) (by simp)
  obtain ⟨_, _, h3⟩ := this
  obtain ⟨i, hik, hi⟩ := h3 x (Or.inr h)
  exact ⟨i, hik, hi⟩

/-- For a list of whole groups every span of every share starts and ends on a group boundary. -/
theorem split_aligned {n : Nat} (hn : 0 < n) (S k : Nat) (l : List Span) (hl : Aligned l) (i : Nat) :
    Aligned (split n S k l i) := by
  have hsh : (max (total l / clampK S k / G * G) G) % G = 0 := by simp only [G]; omega
  exact splitFold_aligned n (clampK S k) (max (total l / clampK S k / G * G) G) hn hsh l hl
    (0, 0, fun _ => []) (clampK_pos S k) (Or.inr (by simp only [G]; omega)) (by simp) (by intro i s hs; simp at hs) i

end Vinc.ValuesSched

#audit_axioms Vinc.ValuesSched.split_cov
#audit_axioms Vinc.ValuesSched.split_aligned
#audit_axioms Vinc.ValuesSched.splitSpan_cov
#audit_axioms Vinc.ValuesSched.splitSpan_aligned
#audit_axioms Vinc.ValuesSched.push_aligned
