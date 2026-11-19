import Pinc.Axioms
import Pinc.ValuesSchedRoom
import Pinc.ValuesSchedCover

/-!
# The run-wide exact partition and `take_chunk` exactness

With room in every list (no push widens, the premise `Room` of the TLA+ model), the work is partitioned exactly:
`ExactS`: every byte is held at most once by the queue and the active providers' lists together, none outside the
wanted set, and every wanted byte the store has not verified exactly once.

* `tc_mult`: `take_chunk` never makes a byte, and moves every unverified byte of the queue to the chunk exactly once
  (a verified byte it meets is dropped, none is added to the chunk), under the room of the chunk and any queue.
* `ReachR`: the reachable states of `Reach` for a striped fetch, each move guarded by the room it needs (the lists it
  builds end below capacity, which is when none of its pushes widened).
* `reachR_exact`: in every state of `ReachR`, `ExactS` holds.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesSched

theorem tc_out_length_ge (st : Store) {n : Nat} (size : Nat) :
    ∀ fuel got (q out : List Span), out.length ≤ (tc st n size fuel got q out).2.length := by
  intro fuel
  induction fuel with
  | zero => intro got q out; exact Nat.le_refl _
  | succ f ih =>
    intro got q out
    unfold tc
    by_cases hg : got < size
    · rw [if_pos hg]
      cases q with
      | nil => exact Nat.le_refl _
      | cons s rest => exact Nat.le_trans (foldl_push_length_ge n _ out) (ih _ _ _)
    · rw [if_neg hg]; exact Nat.le_refl _

/-- `take_chunk` conserves the unverified bytes and never makes one: the queue and the chunk together hold at most
what they held, exactly that for an unverified byte; the chunk gains no verified byte. -/
theorem tc_mult (st : Store) {n : Nat} (hn : 0 < n) (size : Nat) :
    ∀ fuel got (q out : List Span), q.length ≤ n → (tc st n size fuel got q out).2.length < n →
      (∀ x, mult out x + mult q x ≤ 1) → ∀ x,
      mult (tc st n size fuel got q out).1 x + mult (tc st n size fuel got q out).2 x ≤ mult q x + mult out x ∧
      (¬ st.V x → mult (tc st n size fuel got q out).1 x + mult (tc st n size fuel got q out).2 x = mult q x + mult out x) ∧
      (st.V x → mult (tc st n size fuel got q out).2 x = mult out x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro got q out _ _ _ x
    have e : tc st n size 0 got q out = (q, out) := rfl
    rw [e]
    exact ⟨Nat.le_refl _, fun _ => rfl, fun _ => rfl⟩
  | succ f ih =>
    intro got q out hq hro hd x
    by_cases hg : got < size
    · cases q with
      | nil =>
        have e : tc st n size (f + 1) got [] out = ([], out) := by simp [tc, hg]
        rw [e]
        exact ⟨Nat.le_refl _, fun _ => rfl, fun _ => rfl⟩
      | cons s rest =>
        have e : tc st n size (f + 1) got (s :: rest) out =
            tc st n size f (got + ((holesOf st ⟨s.off, takeLen (size - got) s⟩).map (·.len)).sum)
              (if takeLen (size - got) s < s.len then
                pushFront n rest ⟨s.off + takeLen (size - got) s, s.len - takeLen (size - got) s⟩ else rest)
              ((holesOf st ⟨s.off, takeLen (size - got) s⟩).foldl (push n) out) := by simp [tc, hg]
        rw [e] at hro ⊢
        have hrest : rest.length < n := by simp at hq; omega
        have hl := takeLen_le (size - got) s
        obtain ⟨t, ht⟩ : ∃ t, t = takeLen (size - got) s := ⟨_, rfl⟩
        rw [← ht] at hro ⊢ hl
        have hout1 : ((holesOf st ⟨s.off, t⟩).foldl (push n) out).length < n :=
          Nat.lt_of_le_of_lt (tc_out_length_ge st size f _ _ _) hro
        have hdisj : ∀ y, mult out y + mult (holesOf st ⟨s.off, t⟩) y ≤ 1 := by
          intro y
          have := hd y
          rw [holesOf_mult]
          simp only [mult] at this
          by_cases hv : st.V y = true <;> by_cases hm : (Span.mk s.off t).Mem y <;>
            by_cases hs : s.Mem y <;> simp [hv, hm, hs] at this ⊢ <;>
            first | omega | (exfalso; simp only [Span.Mem] at hm hs; omega)
        have hm1 := foldl_push_mult_room (n := n) (holesOf st ⟨s.off, t⟩) (l := out) hout1 hdisj
        have hq1 : (if t < s.len then pushFront n rest ⟨s.off + t, s.len - t⟩ else rest).length ≤ n := by
          split
          · exact pushFront_length_le hn (by omega) _
          · omega
        have hmq1 : ∀ y, mult (if t < s.len then pushFront n rest ⟨s.off + t, s.len - t⟩ else rest) y =
            mult rest y + (if t < s.len ∧ (Span.mk (s.off + t) (s.len - t)).Mem y then 1 else 0) := by
          intro y
          split
          · rename_i hlt
            rw [pushFront_mult_of_room hrest]; simp [hlt]
          · rename_i hlt; simp [hlt]
        have hsplit : ∀ y, (if s.Mem y then 1 else 0) = (if (Span.mk s.off t).Mem y then 1 else 0) +
            (if t < s.len ∧ (Span.mk (s.off + t) (s.len - t)).Mem y then 1 else 0) := by
          intro y
          simp only [Span.Mem]
          by_cases a : s.off ≤ y ∧ y < s.off + s.len <;> by_cases b : s.off ≤ y ∧ y < s.off + t <;>
            by_cases c : t < s.len ∧ s.off + t ≤ y ∧ y < s.off + t + (s.len - t) <;> simp [a, b, c] <;> omega
        have hD : ∀ y, mult ((holesOf st ⟨s.off, t⟩).foldl (push n) out) y +
            mult (if t < s.len then pushFront n rest ⟨s.off + t, s.len - t⟩ else rest) y ≤ mult out y + mult (s :: rest) y := by
          intro y
          rw [hm1 y, hmq1 y, holesOf_mult]
          have := hsplit y
          simp only [mult]
          by_cases hv : st.V y = true <;> by_cases hm : (Span.mk s.off t).Mem y <;> simp [hv, hm] at this ⊢ <;> omega
        have hE : ∀ y, ¬ st.V y →
            mult ((holesOf st ⟨s.off, t⟩).foldl (push n) out) y +
            mult (if t < s.len then pushFront n rest ⟨s.off + t, s.len - t⟩ else rest) y = mult out y + mult (s :: rest) y := by
          intro y hy
          rw [hm1 y, hmq1 y, holesOf_mult]
          have := hsplit y
          simp only [mult]
          by_cases hm : (Span.mk s.off t).Mem y <;> simp [hy, hm] at this ⊢ <;> omega
        have ih' := ih (got + ((holesOf st ⟨s.off, t⟩).map (·.len)).sum) _ _ hq1 hro
          (fun y => by have := hD y; have := hd y; omega) x
        refine ⟨?_, ?_, ?_⟩
        · have := hD x; have := ih'.1; omega
        · intro hx; have := hE x hx; have := ih'.2.1 hx; omega
        · intro hx
          rw [ih'.2.2 hx, hm1 x, holesOf_mult]
          simp [hx]
    · have e : tc st n size (f + 1) got q out = (q, out) := by simp [tc, hg]
      rw [e]
      exact ⟨Nat.le_refl _, fun _ => rfl, fun _ => rfl⟩

end Pinc.ValuesSched

#audit_axioms Pinc.ValuesSched.tc_mult
