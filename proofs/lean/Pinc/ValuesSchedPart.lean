import Pinc.Axioms
import Pinc.ValuesSchedMove

/-!
# Exact accounting of the moves (no byte twice, no byte lost, bytes moved = total)

`ValuesSchedCover` proves that no wanted byte is ever dropped, also when a push onto a full list widens a span and so
asks for a byte twice. This file proves the other half for the moves where no push widens (`NW` premises: the
list was not full, or the span touched the last one): the multiplicity of every byte is conserved exactly.

- `evictQueue_mult`: the share returned to the queue front adds its bytes to the queue, once each.
- `steal_head_tail_total` (and `stealSplit_exact`, from any start): the head and the tail of a steal partition the victim's list
  byte for byte, and the tail's total is `total l - min keep (total l)`: the bytes moved are exactly what the
  `Steal` trace record reports and what the thief's list gains.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Pinc.ValuesSched

theorem mult_reverse (r : List Span) (x : Nat) : mult r.reverse x = mult r x := by
  induction r with
  | nil => simp [mult]
  | cons s t ih => simp [mult, mult_append, ih]; omega

theorem pushFront_length_succ {n : Nat} {q : List Span} (hq : q.length < n) (p : Span) :
    (pushFront n q p).length ≤ q.length + 1 := by
  by_cases h0 : p.len = 0
  · unfold pushFront; rw [if_pos h0]; omega
  · rw [pushFront_eq_of_room hq p h0]; simp

theorem foldl_pushFront_mult {n : Nat} (r : List Span) :
    ∀ q : List Span, q.length + r.length ≤ n → ∀ x, mult (r.foldl (pushFront n) q) x = mult q x + mult r x := by
  induction r with
  | nil => intro q _ x; simp [mult]
  | cons p t ih =>
    intro q hq x
    simp only [List.foldl_cons, List.length_cons] at *
    have hroom : q.length < n := by omega
    rw [ih (pushFront n q p) (by have := pushFront_length_succ hroom p; omega) x, pushFront_mult_of_room hroom p x]
    simp only [mult]; omega

/-- The share of an evicted provider goes back to the queue front: with room for it, the multiplicity of every byte of
the queue grows by exactly the share's. -/
theorem evictQueue_mult {n : Nat} (q miss : List Span) (hroom : q.length + miss.length ≤ n) (x : Nat) :
    mult (evictQueue n q miss) x = mult q x + mult miss x := by
  unfold evictQueue
  rw [foldl_pushFront_mult miss.reverse q (by simpa using hroom) x, mult_reverse]

/-- The conditions under which no push of the head/tail cut widens a list. -/
def ssNW (n keep : Nat) : Nat → List Span → List Span → List Span → Prop
  | _, [], _, _ => True
  | acc, s :: rest, head, tail =>
    if keep ≤ acc then ¬ Wid n tail s ∧ ssNW n keep (acc + s.len) rest head (push n tail s)
    else if acc + s.len ≤ keep then ¬ Wid n head s ∧ ssNW n keep (acc + s.len) rest (push n head s) tail
    else ¬ Wid n head ⟨s.off, keep - acc⟩ ∧ ¬ Wid n tail ⟨s.off + (keep - acc), s.len - (keep - acc)⟩ ∧
      ssNW n keep (acc + s.len) rest (push n head ⟨s.off, keep - acc⟩) (push n tail ⟨s.off + (keep - acc), s.len - (keep - acc)⟩)

theorem stealSplit_exact {n : Nat} (hn : 0 < n) (keep : Nat) :
    ∀ (l : List Span) acc (head tail : List Span), head.length ≤ n → tail.length ≤ n →
      (∀ x, mult head x + mult tail x + mult l x ≤ 1) → ssNW n keep acc l head tail →
      (∀ x, mult (stealSplit n keep acc l head tail).1 x + mult (stealSplit n keep acc l head tail).2 x
          = mult head x + mult tail x + mult l x) ∧
      total (stealSplit n keep acc l head tail).1 + total (stealSplit n keep acc l head tail).2
          = total head + total tail + total l ∧
      total (stealSplit n keep acc l head tail).1 = total head + (min keep (acc + total l) - min keep acc) ∧
      total (stealSplit n keep acc l head tail).2 + (max keep acc) = total tail + max keep (acc + total l) := by
  intro l
  induction l with
  | nil =>
    intro acc head tail _ _ _ _
    unfold stealSplit
    refine ⟨fun x => by simp [mult], by simp [total], by simp [total], by simp [total]⟩
  | cons s t ih =>
    intro acc head tail hh ht hd hnw
    unfold stealSplit
    unfold ssNW at hnw
    have hdisj : ∀ x, s.Mem x → mult head x + mult tail x = 0 := by
      intro x hx
      have := hd x
      simp only [mult, hx, if_true] at this
      omega
    by_cases h1 : keep ≤ acc
    · rw [if_pos h1] at hnw ⊢
      obtain ⟨hw, hrest⟩ := hnw
      have hpm := push_mult_nw hn ht s hw (fun x hx => by have := hdisj x hx; omega)
      have hpt := push_total_nw hn ht s hw (fun x hx => by have := hdisj x hx; omega)
      have hpl := push_length_le hn ht s
      obtain ⟨a1, a2, a3, a4⟩ := ih (acc + s.len) head (push n tail s) hh hpl
        (fun x => by rw [hpm x]; have := hd x; simp only [mult] at this ⊢; omega) hrest
      refine ⟨fun x => by rw [a1 x, hpm x]; simp only [mult]; omega, ?_, ?_, ?_⟩
      · rw [a2, hpt]; simp only [total]; omega
      · rw [a3]; simp only [total]; omega
      · have := a4; rw [hpt] at this; simp only [total] at *; omega
    · rw [if_neg h1] at hnw ⊢
      by_cases h2 : acc + s.len ≤ keep
      · rw [if_pos h2] at hnw ⊢
        obtain ⟨hw, hrest⟩ := hnw
        have hpm := push_mult_nw hn hh s hw (fun x hx => by have := hdisj x hx; omega)
        have hpt := push_total_nw hn hh s hw (fun x hx => by have := hdisj x hx; omega)
        have hpl := push_length_le hn hh s
        obtain ⟨a1, a2, a3, a4⟩ := ih (acc + s.len) (push n head s) tail hpl ht
          (fun x => by rw [hpm x]; have := hd x; simp only [mult] at this ⊢; omega) hrest
        refine ⟨fun x => by rw [a1 x, hpm x]; simp only [mult]; omega, ?_, ?_, ?_⟩
        · rw [a2, hpt]; simp only [total]; omega
        · rw [a3, hpt]; simp only [total]; omega
        · have := a4; simp only [total] at *; omega
      · rw [if_neg h2] at hnw ⊢
        obtain ⟨hw1, hw2, hrest⟩ := hnw
        obtain ⟨s1, hs1⟩ : ∃ s1 : Span, s1 = ⟨s.off, keep - acc⟩ := ⟨_, rfl⟩
        obtain ⟨s2, hs2⟩ : ∃ s2 : Span, s2 = ⟨s.off + (keep - acc), s.len - (keep - acc)⟩ := ⟨_, rfl⟩
        rw [← hs1] at hw1
        rw [← hs2] at hw2
        rw [← hs1, ← hs2] at hrest
        rw [← hs1, ← hs2]
        have hsplit : ∀ x, (if s.Mem x then 1 else 0) = (if s1.Mem x then 1 else 0) + (if s2.Mem x then 1 else 0) := by
          intro x
          simp only [Span.Mem, hs1, hs2]
          by_cases a : s.off ≤ x ∧ x < s.off + s.len <;> by_cases b : s.off ≤ x ∧ x < s.off + (keep - acc) <;>
            by_cases c : s.off + (keep - acc) ≤ x ∧ x < s.off + (keep - acc) + (s.len - (keep - acc)) <;>
            simp [a, b, c] <;> omega
        have hdisj1 : ∀ x, s1.Mem x → mult head x = 0 := by
          intro x hx
          have hxs : s.Mem x := by simp only [Span.Mem, hs1] at hx ⊢; omega
          have := hdisj x hxs; omega
        have hdisj2 : ∀ x, s2.Mem x → mult tail x = 0 := by
          intro x hx
          have hxs : s.Mem x := by simp only [Span.Mem, hs2] at hx ⊢; omega
          have := hdisj x hxs; omega
        have hpm1 := push_mult_nw hn hh s1 hw1 hdisj1
        have hpt1 := push_total_nw hn hh s1 hw1 hdisj1
        have hpm2 := push_mult_nw hn ht s2 hw2 hdisj2
        have hpt2 := push_total_nw hn ht s2 hw2 hdisj2
        have hpl1 := push_length_le hn hh s1
        have hpl2 := push_length_le hn ht s2
        obtain ⟨a1, a2, a3, a4⟩ := ih (acc + s.len) (push n head s1) (push n tail s2) hpl1 hpl2
          (fun x => by rw [hpm1 x, hpm2 x]; have := hd x; have := hsplit x; simp only [mult] at *; omega) hrest
        refine ⟨fun x => by rw [a1 x, hpm1 x, hpm2 x]; have := hsplit x; simp only [mult]; omega, ?_, ?_, ?_⟩
        · rw [a2, hpt1, hpt2]; simp only [total, hs1, hs2]; omega
        · rw [a3, hpt1]; simp only [total, hs1]; omega
        · have := a4; rw [hpt2] at this; simp only [total, hs2] at *; omega

/-- The cut of a steal from an empty start: the head and the tail partition the victim's list byte for byte, and the
bytes moved (the tail's total) are what the list holds beyond `keep`. -/
theorem steal_head_tail_total {n : Nat} (hn : 0 < n) (keep : Nat) (l : List Span) (hd : ∀ x, mult l x ≤ 1)
    (hnw : ssNW n keep 0 l [] []) :
    (∀ x, mult (stealSplit n keep 0 l [] []).1 x + mult (stealSplit n keep 0 l [] []).2 x = mult l x) ∧
    total (stealSplit n keep 0 l [] []).2 = total l - min keep (total l) ∧
    total (stealSplit n keep 0 l [] []).1 = min keep (total l) := by
  obtain ⟨a1, a2, a3, a4⟩ := stealSplit_exact hn keep l 0 [] [] (by simp) (by simp)
    (fun x => by simp [mult]; exact hd x) hnw
  refine ⟨fun x => by rw [a1 x]; simp [mult], ?_, ?_⟩
  · simp only [total] at a4; omega
  · simp only [total] at a3; omega

#audit_axioms Pinc.ValuesSched.evictQueue_mult
#audit_axioms Pinc.ValuesSched.stealSplit_exact
#audit_axioms Pinc.ValuesSched.steal_head_tail_total

end Pinc.ValuesSched
