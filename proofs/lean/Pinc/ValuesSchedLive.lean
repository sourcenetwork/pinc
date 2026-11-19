import Pinc.Axioms
import Pinc.ValuesSchedTerm

/-!
# Completion at the queue level

`ValuesSchedTerm` shows every scheduling move leaves the measure `phi = (unverified wanted bytes, active providers,
queue size)` equal or smaller, and that a verification of a new wanted byte, an eviction and a productive top-up make
it strictly smaller. Here they are connected to a completion theorem about executions of the scheduler.

An execution (`Exec`) is a sequence of labelled moves from a reachable state. The progress that makes a fetch end is
not a property of the scheduler alone: it is the explicit fairness hypothesis `QFair`, the three promises of the
environment and of the host:

* an honest provider that holds a wanted byte the store has not verified eventually has it verified (`honest`);
* a non-empty queue is eventually topped up with a positive size (`queue`);
* a provider that lies is eventually evicted (`liar`).

`completes`: in every execution that satisfies `QFair`, some state has every wanted byte verified. The proof is the
well-foundedness of the lexicographic order: from any state with an unverified wanted byte, `reach_cover` says the
byte is in the queue or in an active provider's list, and each case of `QFair` gives a later state of strictly smaller
measure. `honest_survives` says the honest provider the hypotheses speak of is still active at every state, so the
eviction of the liars never empties the fetch.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesSched

/-- The label of a scheduling move. -/
inductive Mv where
  | verify
  | topUp (fuel want p : Nat)
  | prune (p : Nat)
  | steal (keep p b : Nat)
  | evict (p : Nat)

/-- What a labelled move does: the state before and after. An eviction needs another active provider left. -/
def MvOk (n : Nat) (mv : Mv) (st : Store) (s : Sys) (st' : Store) (s' : Sys) : Prop :=
  match mv with
  | .verify => (∀ x, st.V x → st'.V x) ∧ s' = s
  | .topUp fuel want p => p ∈ s.act ∧ st' = st ∧ s' = topUpMv st n fuel want p s
  | .prune p => p ∈ s.act ∧ st' = st ∧ s' = pruneMv st n p s
  | .steal keep p b => p ∈ s.act ∧ b ∈ s.act ∧ b ≠ p ∧ st' = st ∧ s' = stealMv st n keep p b s
  | .evict p => p ∈ s.act ∧ s.act.erase p ≠ [] ∧ st' = st ∧ s' = evictMv st n p s

theorem MvOk.step {n : Nat} {mv : Mv} {st st' : Store} {s s' : Sys} (h : MvOk n mv st s st' s') : Step n st s st' s' := by
  cases mv with
  | verify => obtain ⟨h1, h2⟩ := h; rw [h2]; exact Step.verify st st' s h1
  | topUp fuel want p => obtain ⟨h1, h2, h3⟩ := h; rw [h2, h3]; exact Step.topUp st s fuel want p h1
  | prune p => obtain ⟨h1, h2, h3⟩ := h; rw [h2, h3]; exact Step.prune st s p h1
  | steal keep p b =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h; rw [h4, h5]; exact Step.steal st s keep p b h1 h2 h3
  | evict p => obtain ⟨h1, h2, h3, h4⟩ := h; rw [h3, h4]; exact Step.evict st s p h1

theorem MvOk.reach {nw n : Nat} {want : List Span} {mv : Mv} {st st' : Store} {s s' : Sys}
    (hr : Reach nw n want st s) (h : MvOk n mv st s st' s') : Reach nw n want st' s' := by
  cases mv with
  | verify => obtain ⟨h1, h2⟩ := h; rw [h2]; exact Reach.verify st st' s hr h1
  | topUp fuel want' p => obtain ⟨h1, h2, h3⟩ := h; rw [h2, h3]; exact Reach.topUp st s fuel want' p hr h1
  | prune p => obtain ⟨h1, h2, h3⟩ := h; rw [h2, h3]; exact Reach.prune st s p hr h1
  | steal keep p b =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h; rw [h4, h5]; exact Reach.steal st s keep p b hr h1 h2 h3
  | evict p => obtain ⟨h1, h2, h3, h4⟩ := h; rw [h3, h4]; exact Reach.evict st s p hr h1 h2

/-- An execution: a reachable start and a labelled move from every state to the next. -/
structure Exec (nw n : Nat) (want : List Span) (stA : Nat → Store) (sA : Nat → Sys) (mv : Nat → Mv) : Prop where
  start : Reach nw n want (stA 0) (sA 0)
  step : ∀ i, MvOk n (mv i) (stA i) (sA i) (stA (i + 1)) (sA (i + 1))

theorem Exec.reach {nw n : Nat} {want : List Span} {stA : Nat → Store} {sA : Nat → Sys} {mv : Nat → Mv}
    (h : Exec nw n want stA sA mv) : ∀ i, Reach nw n want (stA i) (sA i) := by
  intro i
  induction i with
  | zero => exact h.start
  | succ i ih => exact (h.step i).reach ih

theorem Exec.v_mono {nw n : Nat} {want : List Span} {stA : Nat → Store} {sA : Nat → Sys} {mv : Nat → Mv}
    (h : Exec nw n want stA sA mv) {i j : Nat} (hij : i ≤ j) : ∀ x, (stA i).V x = true → (stA j).V x = true := by
  induction hij with
  | refl => intro x hx; exact hx
  | @step j hij ih =>
    intro x hx
    have := ih x hx
    have hs := h.step j
    cases hm : mv j with
    | verify => rw [hm] at hs; exact hs.1 x this
    | topUp fuel want' p => rw [hm] at hs; rw [hs.2.1]; exact this
    | prune p => rw [hm] at hs; rw [hs.2.1]; exact this
    | steal keep p b => rw [hm] at hs; rw [hs.2.2.2.1]; exact this
    | evict p => rw [hm] at hs; rw [hs.2.2.1]; exact this

theorem lex3_trans {a b c : Nat × Nat × Nat} (h1 : Lex3 a b) (h2 : Lex3 b c) : Lex3 a c := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨c1, c2, c3⟩ := c
  simp only [Lex3, Prod.lex_def] at *
  omega

/-- The measure never rises along an execution. -/
theorem Exec.phi_le {nw n : Nat} (hnw : 0 < nw) (hn : 0 < n) {want : List Span} (L : Nat) {stA : Nat → Store}
    {sA : Nat → Sys} {mv : Nat → Mv} (h : Exec nw n want stA sA mv) {i j : Nat} (hij : i ≤ j) :
    phi want L (stA j) (sA j) = phi want L (stA i) (sA i) ∨ Lex3 (phi want L (stA j) (sA j)) (phi want L (stA i) (sA i)) := by
  induction hij with
  | refl => exact Or.inl rfl
  | @step j hij ih =>
    have hs := (reach_inv hnw hn want (stA j) (sA j) (h.reach j)).1
    have hstep := step_phi_le hn want L (h.step j).step hs
    rcases ih with ih | ih <;> rcases hstep with hstep | hstep
    · exact Or.inl (hstep.trans ih)
    · exact Or.inr (ih ▸ hstep)
    · exact Or.inr (hstep ▸ ih)
    · exact Or.inr (lex3_trans hstep ih)

theorem unvN_pos (want : List Span) (V : Nat → Bool) : ∀ L, 0 < unvN want V L →
    ∃ x, x < L ∧ 0 < mult want x ∧ V x = false := by
  intro L
  induction L with
  | zero => intro h; simp [unvN] at h
  | succ k ih =>
    intro h
    simp only [unvN] at h
    by_cases hk : 0 < mult want k ∧ V k = false
    · exact ⟨k, by omega, hk.1, hk.2⟩
    · simp only [hk, if_false] at h
      obtain ⟨x, hx, h1, h2⟩ := ih (by omega)
      exact ⟨x, by omega, h1, h2⟩

/-- The fairness hypothesis of the queue-level completion theorem: the promises of the providers and of the host. -/
structure QFair (n L : Nat) (want : List Span) (H : Nat → Prop) (stA : Nat → Store) (sA : Nat → Sys)
    (mv : Nat → Mv) : Prop where
  /-- An honest provider that holds a wanted byte not yet verified eventually has it verified. -/
  honest : ∀ i p x, p ∈ (sA i).act → H p → cov ((sA i).a p) x → 0 < mult want x → (stA i).V x = false →
    ∃ j, i ≤ j ∧ (stA j).V x = true
  /-- A non-empty queue is eventually topped up with a positive fuel and size. -/
  queue : ∀ i, (sA i).q ≠ [] → ∃ j, i ≤ j ∧ (sA j).q ≠ [] ∧ ∃ fuel w p, mv j = Mv.topUp fuel w p ∧ 0 < fuel ∧ 0 < w
  /-- A provider that lies is eventually evicted. -/
  liar : ∀ i p, p ∈ (sA i).act → ¬ H p → ∃ j, i ≤ j ∧ mv j = Mv.evict p

/-- Completion at the queue level: under `QFair`, an execution reaches a state with every wanted byte verified. -/
theorem completes {nw n L : Nat} (hnw : 0 < nw) (hn : 0 < n) {want : List Span} (hwf : ∀ x, 0 < mult want x → x < L)
    {H : Nat → Prop} {stA : Nat → Store} {sA : Nat → Sys} {mv : Nat → Mv}
    (hx : Exec nw n want stA sA mv) (hf : QFair n L want H stA sA mv) :
    ∃ k, ∀ x, cov want x → (stA k).V x = true := by
  have key : ∀ P, ∀ i, phi want L (stA i) (sA i) = P → ∃ k, unvN want (stA k).V L = 0 := by
    intro P
    induction P using lex3_wf.induction with
      | _ P ih =>
        intro i hi
        by_cases h0 : unvN want (stA i).V L = 0
        · exact ⟨i, h0⟩
        · obtain ⟨x, hxL, hxm, hxv⟩ := unvN_pos want (stA i).V L (by omega)
          have hrs := hx.reach i
          have hcover := reach_cover hnw hn want (stA i) (sA i) hrs x ((cov_iff_mult want x).2 hxm) (by simp [hxv])
          -- a later state of strictly smaller measure
          have hdrop : ∃ j, Lex3 (phi want L (stA j) (sA j)) (phi want L (stA i) (sA i)) := by
            rcases hcover with hq | ⟨p, hp, hpx⟩
            · have hne : (sA i).q ≠ [] := by
                intro h; rw [h] at hq; exact cov_nil x hq
              obtain ⟨j, hij, hqj, fuel, w, p, hmv, hfuel, hw⟩ := hf.queue i hne
              have hs := (reach_inv hnw hn want (stA j) (sA j) (hx.reach j)).1
              have hstep := hx.step j
              rw [hmv] at hstep
              obtain ⟨_, hst, hsys⟩ := hstep
              have hlt := topUp_lt hn want L (stA j) (sA j) fuel w p hs hfuel hw hqj
              refine ⟨j + 1, ?_⟩
              rw [hst, hsys]
              rcases hx.phi_le hnw hn L hij with h | h
              · rw [h] at hlt; exact hlt
              · exact lex3_trans hlt h
            · by_cases hH : H p
              · obtain ⟨j, hij, hvj⟩ := hf.honest i p x hp hH hpx hxm hxv
                refine ⟨j, ?_⟩
                exact Prod.Lex.left _ _ (unvN_lt want (stA i).V (stA j).V (hx.v_mono hij) L x hxL hxm hxv hvj)
              · obtain ⟨j, hij, hmv⟩ := hf.liar i p hp hH
                have hstep := hx.step j
                rw [hmv] at hstep
                obtain ⟨hpj, _, hst, hsys⟩ := hstep
                have hlt := evict_lt want L (stA j) (sA j) n p hpj
                refine ⟨j + 1, ?_⟩
                rw [hst, hsys]
                rcases hx.phi_le hnw hn L hij with h | h
                · rw [h] at hlt; exact hlt
                · exact lex3_trans hlt h
          obtain ⟨j, hj⟩ := hdrop
          exact ih _ (hi ▸ hj) j rfl
  obtain ⟨k, hk⟩ := key _ 0 rfl
  refine ⟨k, fun x hxw => ?_⟩
  refine Classical.byContradiction fun hv => ?_
  have hvf : (stA k).V x = false := by cases h : (stA k).V x <;> simp_all
  have hxl := hwf x ((cov_iff_mult want x).1 hxw)
  have gen : ∀ L', x < L' → 0 < unvN want (stA k).V L' := by
    intro L'
    induction L' with
    | zero => intro h; omega
    | succ m ih =>
      intro h
      simp only [unvN]
      by_cases hm : x = m
      · subst hm; simp [(cov_iff_mult want x).1 hxw, hvf]
      · have := ih (by omega); omega
  have := gen L hxl
  omega

/-- The honest provider the hypotheses speak of stays active: evictions only remove providers that lie, so the
fetch is never emptied. -/
theorem honest_survives {nw n : Nat} {want : List Span} {H : Nat → Prop} {stA : Nat → Store} {sA : Nat → Sys}
    {mv : Nat → Mv} (hx : Exec nw n want stA sA mv) (h0 : ∃ h, H h ∧ h ∈ (sA 0).act)
    (hev : ∀ j p, mv j = Mv.evict p → ¬ H p) (hnd : ∀ i, (sA i).act.Nodup) :
    ∀ i, ∃ h, H h ∧ h ∈ (sA i).act := by
  intro i
  induction i with
  | zero => exact h0
  | succ i ih =>
    obtain ⟨h, hh, hm⟩ := ih
    have hs := hx.step i
    cases hmv : mv i with
    | verify => rw [hmv] at hs; rw [hs.2]; exact ⟨h, hh, hm⟩
    | topUp fuel w p => rw [hmv] at hs; rw [hs.2.2]; exact ⟨h, hh, hm⟩
    | prune p => rw [hmv] at hs; rw [hs.2.2]; exact ⟨h, hh, hm⟩
    | steal keep p b => rw [hmv] at hs; rw [hs.2.2.2.2]; exact ⟨h, hh, hm⟩
    | evict p =>
      rw [hmv] at hs
      rw [hs.2.2.2]
      have : h ≠ p := fun e => hev i p hmv (e ▸ hh)
      exact ⟨h, hh, (List.mem_erase_of_ne this).2 hm⟩

end Pinc.ValuesSched

#audit_axioms Pinc.ValuesSched.completes
#audit_axioms Pinc.ValuesSched.honest_survives
#audit_axioms Pinc.ValuesSched.Exec.phi_le
