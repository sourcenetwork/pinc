import Vinc.Axioms
import Vinc.ValuesSchedEvict

/-!
# A decreasing measure of the schedule

`phi st s = (U, A, Q)`: `U` the unverified wanted bytes among the first `L` bytes of the value, `A` the active
providers, `Q` the queue's summed length plus its span count. Under the lexicographic order on `ℕ³` (well founded,
`lex3_wf`) every scheduling move of `sched.rs` leaves `phi` equal or smaller (`step_phi_le`):

- a verification never raises `U` and lowers it when a new wanted byte is verified (`verify_lt`);
- an eviction lowers `A` by one (`evict_lt`), whatever it puts back in the queue;
- a top-up lowers `Q` when it takes anything from a non-empty queue (`topUp_lt`), and never raises `Q`;
- a prune and a steal leave `phi` equal: they only rearrange bytes among the active providers (a steal's thief held
  nothing, and the idle clocks of `ValuesSchedSteal` gate how often one can happen).

So a run without a verification, an eviction or a productive top-up can only prune and steal; the number of evictions
is at most `MAX_PROVIDERS`, and the verifications are at most the groups of the value. That every provider that is
asked eventually answers (liveness) is the system-level argument built on these lemmas.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Vinc.ValuesSched

/-- Unverified wanted bytes among the first `L`: byte `x` counts when a span of `want` covers it and the store has not
verified it. -/
def unvN (want : List Span) (V : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => unvN want V k + (if 0 < mult want k ∧ V k = false then 1 else 0)

theorem term_le (m : Nat) (a b : Bool) (hab : a = true → b = true) :
    (if 0 < m ∧ b = false then 1 else 0) ≤ (if 0 < m ∧ a = false then 1 else 0) := by
  cases a <;> cases b <;> simp_all

theorem unvN_mono (want : List Span) (V V' : Nat → Bool) (h : ∀ x, V x = true → V' x = true) :
    ∀ L, unvN want V' L ≤ unvN want V L := by
  intro L
  induction L with
  | zero => simp [unvN]
  | succ k ih =>
    simp only [unvN]
    have := term_le (mult want k) (V k) (V' k) (h k)
    omega

theorem unvN_lt (want : List Span) (V V' : Nat → Bool) (h : ∀ x, V x = true → V' x = true) :
    ∀ L, ∀ x, x < L → 0 < mult want x → V x = false → V' x = true → unvN want V' L < unvN want V L := by
  intro L
  induction L with
  | zero => intro x hx; omega
  | succ k ih =>
    intro x hx hm hv hv'
    simp only [unvN]
    by_cases hxk : x = k
    · subst hxk
      have := unvN_mono want V V' h x
      simp [hm, hv, hv']
      omega
    · have := ih x (by omega) hm hv hv'
      have h2 := term_le (mult want k) (V k) (V' k) (h k)
      omega

/-- The queue measure: bytes plus spans. -/
def qm (q : List Span) : Nat := total q + q.length

/-- The measure of the schedule. -/
def phi (want : List Span) (L : Nat) (st : Store) (s : Sys) : Nat × Nat × Nat :=
  (unvN want st.V L, s.act.length, qm s.q)

/-- The lexicographic order on triples. -/
abbrev Lex3 : Nat × Nat × Nat → Nat × Nat × Nat → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem lex3_wf : WellFounded Lex3 :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

theorem qm_pushFront (rest : List Span) (r : Span) (n : Nat) (hr : r.len ≠ 0) (hroom : rest.length < n) :
    qm (pushFront n rest r) = qm rest + r.len + 1 := by
  rw [pushFront_eq_of_room hroom r hr]; simp [qm, total]; omega

/-- One step of `take_chunk` lowers the queue measure; the loop never raises it. -/
theorem tc_qm (st : Store) {n : Nat} (size : Nat) :
    ∀ fuel got (q out : List Span), q.length ≤ n →
      qm (tc st n size fuel got q out).1 ≤ qm q ∧
      (0 < fuel → got < size → q ≠ [] → qm (tc st n size fuel got q out).1 < qm q) := by
  intro fuel
  induction fuel with
  | zero => intro got q out hq; exact ⟨Nat.le_refl _, fun h => by omega⟩
  | succ f ih =>
    intro got q out hq
    unfold tc
    by_cases hg : got < size
    · rw [if_pos hg]
      cases q with
      | nil => simp only; exact ⟨by simp [qm, total], fun _ _ h => absurd rfl h⟩
      | cons s rest =>
        simp only
        have hrest : rest.length < n := by simp at hq; omega
        have hqs : qm (s :: rest) = s.len + qm rest + 1 := by simp [qm, total]; omega
        have hstep : qm (if takeLen (size - got) s < s.len then
              pushFront n rest ⟨s.off + takeLen (size - got) s, s.len - takeLen (size - got) s⟩ else rest) < qm (s :: rest) := by
          have hle := takeLen_le (size - got) s
          by_cases hlt : takeLen (size - got) s < s.len
          · rw [if_pos hlt, qm_pushFront rest _ n (by simp; omega) hrest, hqs]
            have := takeLen_pos (size - got) s (by omega)
            simp only; omega
          · rw [if_neg hlt, hqs]; omega
        have hq1 : (if takeLen (size - got) s < s.len then
              pushFront n rest ⟨s.off + takeLen (size - got) s, s.len - takeLen (size - got) s⟩ else rest).length ≤ n := by
          split
          · exact pushFront_length_le (by omega) (by omega) _
          · omega
        exact ⟨Nat.le_trans (ih _ _ _ hq1).1 (by omega),
          fun _ _ _ => Nat.lt_of_le_of_lt (ih _ _ _ hq1).1 hstep⟩
    · rw [if_neg hg]; exact ⟨Nat.le_refl _, fun _ h => absurd h hg⟩

theorem step_phi_le {n : Nat} (hn : 0 < n) (want : List Span) (L : Nat) {st st' : Store} {s s' : Sys}
    (hst : Step n st s st' s') (hs : Sized n s) : phi want L st' s' = phi want L st s ∨ Lex3 (phi want L st' s') (phi want L st s) := by
  cases hst with
  | verify _ _ h =>
    have := unvN_mono want st.V st'.V h L
    simp only [phi]
    by_cases hlt : unvN want st'.V L < unvN want st.V L
    · exact Or.inr (Prod.Lex.left _ _ hlt)
    · left; rw [show unvN want st'.V L = unvN want st.V L by omega]
  | topUp _ fuel want' p hp =>
    have h1 := (tc_qm st want' fuel 0 s.q [] hs.1).1
    simp only [phi, topUpMv]
    by_cases hlt : qm (tc st n want' fuel 0 s.q []).1 < qm s.q
    · exact Or.inr (Prod.Lex.right _ (Prod.Lex.right _ hlt))
    · left; rw [show qm (tc st n want' fuel 0 s.q []).1 = qm s.q by omega]
  | prune _ p hp => left; rfl
  | steal _ keep p b hp hb hbp => left; rfl
  | evict _ p hp =>
    have hlt : (s.act.erase p).length < s.act.length := by
      rw [List.length_erase_of_mem hp]
      have : 0 < s.act.length := List.length_pos_of_mem hp
      omega
    simp only [phi, evictMv]
    exact Or.inr (Prod.Lex.right _ (Prod.Lex.left _ _ hlt))

/-- A verification of a new wanted byte lowers the measure. -/
theorem verify_lt (want : List Span) (L : Nat) {st st' : Store} (s : Sys) (h : ∀ x, st.V x = true → st'.V x = true)
    (x : Nat) (hx : x < L) (hm : 0 < mult want x) (hv : st.V x = false) (hv' : st'.V x = true) :
    Lex3 (phi want L st' s) (phi want L st s) :=
  Prod.Lex.left _ _ (unvN_lt want st.V st'.V h L x hx hm hv hv')

/-- An eviction lowers the measure, whatever it puts back in the queue. -/
theorem evict_lt (want : List Span) (L : Nat) (st : Store) (s : Sys) (n p : Nat) (hp : p ∈ s.act) :
    Lex3 (phi want L st (evictMv st n p s)) (phi want L st s) := by
  have hlt : (s.act.erase p).length < s.act.length := by
    rw [List.length_erase_of_mem hp]
    have : 0 < s.act.length := List.length_pos_of_mem hp
    omega
  exact Prod.Lex.right _ (Prod.Lex.left _ _ hlt)

/-- A top-up that takes from a non-empty queue lowers the measure. -/
theorem topUp_lt {n : Nat} (hn : 0 < n) (want : List Span) (L : Nat) (st : Store) (s : Sys) (fuel want' p : Nat)
    (hs : Sized n s) (hf : 0 < fuel) (hw : 0 < want') (hq : s.q ≠ []) :
    Lex3 (phi want L st (topUpMv st n fuel want' p s)) (phi want L st s) :=
  Prod.Lex.right _ (Prod.Lex.right _ ((tc_qm st want' fuel 0 s.q [] hs.1).2 hf hw hq))

end Vinc.ValuesSched

#audit_axioms Vinc.ValuesSched.unvN_mono
#audit_axioms Vinc.ValuesSched.unvN_lt
#audit_axioms Vinc.ValuesSched.lex3_wf
#audit_axioms Vinc.ValuesSched.tc_qm
#audit_axioms Vinc.ValuesSched.step_phi_le
#audit_axioms Vinc.ValuesSched.verify_lt
#audit_axioms Vinc.ValuesSched.evict_lt
#audit_axioms Vinc.ValuesSched.topUp_lt
