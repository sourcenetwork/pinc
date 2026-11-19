import Pinc.ValuesSysSafe

/-!
# Completion of the value fetch, and the scenarios

PROPERTY 2, the completion theorem, and PROPERTY 10, the scenarios, as Lean theorems.

## What is proved here, and what is not

`terminates` and `completes` are about every fair execution of `Pinc.ValuesSys.Step`: an infinite sequence of states
in which each step is a step of the model or a stutter. The fairness assumption is the explicit hypothesis
`Fairness`, two statements about the execution:

* `Progress`: a running fetch with a wanted group still missing either ends, or verifies another wanted group,
  within finitely many steps. This is the pipeline of the machine at work under an honest provider that stays
  reachable and is redialled: the dial, the request, the answer, the parse, the write and the commit, with the
  retry, the steal and the stall redial that repair every loss. It is NOT proved here: the scheduling is the
  operations of `sched` in the model, and the pipeline lives in the TLA+ model `ValuesSys.tla`, where TLC checks it
  as a liveness property under weak and strong fairness (`ValuesSys_n1`, `_n2`, `_n3`, `_drop`, `_slow`, `_liar`,
  `_alllie`, `_restart`, `_resume`) and where it found two stuck states of the code (a refused open whose retry was
  swallowed by the stream of another provider, and an idle provider that reconnected and was never topped up
  again); the witnesses `ValuesSys_n2_old` and `_n2_oldconn` keep the old behaviour as counterexamples.
* `CheckFair`: when nothing wanted is missing, `check_done` runs (weak fairness of an enabled step).

What IS proved, with no assumption on the scheduling beyond what its operations keep (`Op.plumbOk`): the counting argument that turns the
progress of the pipeline into the end of the fetch (`terminates`), and that the end is `Complete` when nothing else
can end a fetch (`completes`: no deadline, a store that does not refuse, no provider that lies, a valid start), and the
safety of every state (`ValuesSysSafe`), which holds whatever the pipeline does.
-/

namespace Pinc.ValuesSys
open Classical

/-- The wanted groups lie inside the value. -/
def Wf (c : Cfg) : Prop := ∀ x, c.want x = true → x < c.g

/-- The wanted groups not verified yet. -/
def missing (c : Cfg) (s : St) : Nat :=
  ((List.range c.g).filter (fun x => c.want x && !s.ver x)).length

theorem missing_zero {c : Cfg} {s : St} (hw : Wf c) (h : missing c s = 0) :
    ∀ x, c.want x = true → s.ver x = true := by
  intro x hx
  refine Classical.byContradiction fun hv => ?_
  have hv' : s.ver x = false := by simpa using hv
  have hmem : x ∈ (List.range c.g).filter (fun x => c.want x && !s.ver x) := by
    simp [List.mem_filter, hx, hv', hw x hx]
  have : 0 < missing c s := List.length_pos_of_mem hmem
  omega

/-- An execution: every step is a step of the model or a stutter. -/
def Exec (c : Cfg) (σ : Nat → St) : Prop := ∀ n, Step c (σ n) (σ (n + 1)) ∨ σ (n + 1) = σ n

/-- The fairness assumption: see the module comment. -/
structure Fairness (c : Cfg) (σ : Nat → St) : Prop where
  /-- A running fetch with a wanted group missing ends or verifies one more. -/
  progress : ∀ n, (σ n).run = .running → 0 < missing c (σ n) →
    ∃ m, n ≤ m ∧ ((σ m).run = .done ∨ missing c (σ m) < missing c (σ n))
  /-- Weak fairness of `check_done`: with nothing missing it runs. -/
  checkFair : ∀ n, (σ n).run = .running → missing c (σ n) = 0 → ∃ m, n ≤ m ∧ (σ m).run = .done

/-- A step never goes back to idle without a restart, and the restart budget never grows. -/
theorem step_keeps {c : Cfg} {s s' : St} (st : Step c s s') (hi : s.run ≠ .idle) (h0 : s.rs = 0) :
    s'.run ≠ .idle ∧ s'.rs = 0 := by
  cases st with
  | startBadRoot h1 => simp_all
  | startComplete h1 => simp_all
  | startNoProvider h1 => simp_all
  | begin h1 => simp_all
  | sched op h1 h2 hok => simp_all
  | acceptHdr p g k h1 => simp_all
  | acceptEnd p g k h1 => simp_all
  | acceptDup p g k h1 => simp_all
  | accept p g k h1 => simp_all
  | skip p g h1 => simp_all
  | acceptAhead p g k h1 => simp_all
  | evict p h1 =>
    unfold evictSt; split
    · simp [finish, evict2, evict1]; split <;> simp_all
    · simp [evictBooks, evict2, evict1]; split <;> simp_all
  | write d h1 => simp_all
  | writeRefused d h1 => simp_all [finish]
  | commit d h1 =>
    unfold commitSt; split <;> simp_all [readable]
  | commitRefused d h1 => simp_all [finish]
  | release h1 => unfold releaseHd; cases s.hd <;> simp_all [readable]
  | check h1 => unfold releaseHd; cases s.hd <;> simp_all [finish, readable]
  | tick h1 => simp_all
  | deadlineFire d h1 => simp_all [finish]
  | restart h1 h2 => omega

/-- Along an execution that starts with no restart budget the fetch never goes back to idle once started. -/
theorem exec_keeps {c : Cfg} {σ : Nat → St} (hx : Exec c σ) {n : Nat}
    (hn : (σ n).run ≠ .idle) (hrs : (σ n).rs = 0) : ∀ k, (σ (n + k)).run ≠ .idle ∧ (σ (n + k)).rs = 0 := by
  intro k
  induction k with
  | zero => exact ⟨hn, hrs⟩
  | succ k ih =>
    rcases hx (n + k) with st | e
    · exact step_keeps st ih.1 ih.2
    · rw [← Nat.add_assoc, e]; exact ih

theorem exec_rs {c : Cfg} {σ : Nat → St} (hx : Exec c σ) (h0 : (σ 0).rs = 0) (h1 : (σ 0).run ≠ .idle) :
    ∀ n, (σ n).rs = 0 ∧ (σ n).run ≠ .idle := by
  intro n
  have := exec_keeps hx (n := 0) h1 h0 n
  rw [Nat.zero_add] at this
  exact ⟨this.2, this.1⟩

/-- Every state of an execution of a fetch that started is reachable. -/
theorem exec_reach {c : Cfg} {σ : Nat → St} {rs : Nat} (hx : Exec c σ) (h0 : Reach c rs (σ 0)) :
    ∀ n, Reach c rs (σ n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rcases hx n with st | e
    · exact Reach.step _ _ ih st
    · rw [e]; exact ih

/-- COMPLETION, the counting argument: under the fairness assumption a started fetch with no restart budget always
ends. -/
theorem terminates {c : Cfg} {σ : Nat → St} (hx : Exec c σ) (hf : Fairness c σ)
    (h0 : (σ 0).rs = 0) (hs : (σ 0).run ≠ .idle) :
    ∀ n, (σ n).run = .running → ∃ m, (σ m).run = .done := by
  have keep := exec_rs hx h0 hs
  suffices H : ∀ j n, (σ n).run = .running → missing c (σ n) = j → ∃ m, (σ m).run = .done from
    fun n hn => H _ n hn rfl
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro n hn hj
    by_cases hz : missing c (σ n) = 0
    · obtain ⟨m, _, hm⟩ := hf.checkFair n hn hz
      exact ⟨m, hm⟩
    · obtain ⟨m, _, hm⟩ := hf.progress n hn (Nat.pos_of_ne_zero hz)
      rcases hm with hd | hlt
      · exact ⟨m, hd⟩
      · by_cases hd : (σ m).run = .done
        · exact ⟨m, hd⟩
        · have hr : (σ m).run = .running := by
            have := (keep m).2
            revert hd this
            cases (σ m).run <;> simp
          exact ih _ (by omega) m hr rfl

/-- COMPLETION: a started fetch with no restart budget ends in `Complete` when nothing else can end it: no deadline, a
store that never refuses, providers that never lie, a start that finds a provider and a valid root. -/
theorem completes {c : Cfg} {σ : Nat → St} {rs : Nat} (hx : Exec c σ) (hf : Fairness c σ)
    (hr : Reach c rs (σ 0)) (h0 : (σ 0).rs = 0) (hs : (σ 0).run ≠ .idle)
    (hdl : c.deadline = none) (hst : c.storeFail = false) (hlq : ∀ p, c.liars p = false)
    (hn : ∃ p, c.listed p = true) (hroot : ¬ (c.empty = true ∧ c.rootOk = false))
    (n : Nat) (hn' : (σ n).run = .running) : ∃ m, (σ m).run = .done ∧ (σ m).fin = some .complete := by
  obtain ⟨m, hm⟩ := terminates hx hf h0 hs n hn'
  have hre : Reach c rs (σ m) := exec_reach hx hr m
  refine ⟨m, hm, ?_⟩
  have i := reach_inv hre
  have hnf : (σ m).nfin = 1 := i.doneFin.1.1 hm
  have hfin : (σ m).fin ≠ none := fun e => by have := i.doneFin.2.1.1 e; omega
  rcases hfv : (σ m).fin with _ | f
  · exact absurd hfv hfin
  · cases f with
    | complete => rfl
    | deadline => obtain ⟨d, hd, _⟩ := i.reasonDeadline hfv; simp [hdl] at hd
    | noProvider => obtain ⟨p, hp⟩ := hn; have := i.reasonNoProv hfv p; simp_all
    | store => have := i.reasonStore hfv; simp_all
    | badRoot => exact absurd (i.reasonRoot hfv) hroot
    | everyProviderLied =>
      obtain ⟨_, hall⟩ := every_provider_lied hre hfv
      obtain ⟨p, hp⟩ := hn
      have := liar_only hre p (hall p hp).2
      simp_all

end Pinc.ValuesSys
