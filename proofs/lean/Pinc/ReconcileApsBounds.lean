import Pinc.ReconcileApsCost

/-!
# Reconcile APS, part 8: progress, termination and the cost bound

For an honest pair of sorted sets, any hash, any id function and any choice of the code's
nondeterminism (`fits`, the fan of a split, the order parts are processed), from the first message of a pass (`Init`):

* `aps_progress`: a state with a pending part always has a step (the code never gets stuck);
* `aps_depth_bound`: every part ever created has depth at most `depthBound f nA nB = 2 (lg f nA + lg f nB) + 3`
  (`f = 2` always holds; with `minFan = 16`, i.e. no split was ever narrowed, the same statement is the 16-way bound);
* `aps_steps_bound`: the parts processed so far plus the potential left never exceed
  `stepsBound f D nA nB = 17 + 17 D (2 (lg f nA + lg f nB) + 2)` with `D` the size of the symmetric difference, so a pass
  processes at most that many parts: the work follows the difference times the depth, not the sets;
* `aps_finishes`: from every reachable state some execution ends with no pending part within the bound
  (termination: the potential falls by at least one per step).

`lg f n` is the smallest `k` with `n <= f^k`. With the default fan 16, `lg 16 n <= 16` for every `n < 2^64`, so the
depth is at most 67 and the steps at most `17 + 17 D 34`.
-/

namespace Pinc.Reconcile

/-- Reachable from the first message of a pass (not the cold stream). -/
inductive IReach (c : Cfg) : St → Prop
  | init {ex s} (h : Init c ex s) : IReach c s
  | step {s s'} (h : IReach c s) (hs : PStep c s s') : IReach c s'

theorem IReach.toP {c : Cfg} {s : St} (h : IReach c s) : PReach c s := by
  induction h with
  | init h => exact PReach.init h
  | step _ hs ih => exact PReach.step ih hs

def depthBound (f nA nB : Nat) : Nat := 2 * (lg f nA + lg f nB) + 3
def stepsBound (f D nA nB : Nat) : Nat := 17 + 17 * (D * (2 * (lg f nA + lg f nB) + 2))
def Cfg.psum (c : Cfg) (f : Nat) (s : St) : Nat := lsum (c.pot f) s.pend

theorem cnt_top (T : List Item) : cnt T Iv.top = T.length := by
  unfold cnt Iv.items
  rw [List.filter_eq_self.mpr (fun x _ => Iv.top_has x)]

/-! ## Progress -/

theorem Proc_exists (c : Cfg) (ex : Bool) (p : Part) (hwf : WF p) :
    ∃ kids ha ta lf, Proc c ex p kids ha ta lf := by
  obtain ⟨kind, toInit, I, d⟩ := p
  have h16 := c.hmax
  cases kind with
  | fp =>
    by_cases h : c.fpEq I
    · exact ⟨_, _, _, _, Proc.fpEq h⟩
    · cases toInit
      · by_cases hl : cnt c.B I ≤ bleaf ∧ c.fits false true I
        · exact ⟨_, _, _, _, Proc.fpLeafResp h hl.1 hl.2⟩
        · exact ⟨_, _, _, _, Proc.fpSplit (fan := 16) h (by simpa [Cfg.set, leafOf] using hl) h16 (Nat.le_refl _)⟩
      · by_cases hl : cnt c.A I ≤ aleaf ∧ c.fits true ex I
        · exact ⟨_, _, _, _, Proc.fpLeafInit h hl.1 hl.2⟩
        · exact ⟨_, _, _, _, Proc.fpSplit (fan := 16) h (by simpa [Cfg.set, leafOf] using hl) h16 (Nat.le_refl _)⟩
  | ids =>
    have : toInit = false := hwf.1 rfl
    subst this
    by_cases hl : cnt c.B I ≤ aleaf ∧ c.fits false true I
    · exact ⟨_, _, _, _, Proc.respLeaf (k := .ids) (Or.inl rfl) hl.1 hl.2⟩
    · exact ⟨_, _, _, _, Proc.respNarrow (k := .ids) (fan := 16) (Or.inl rfl) hl h16 (Nat.le_refl _)⟩
  | full =>
    cases toInit
    · by_cases hl : cnt c.B I ≤ aleaf ∧ c.fits false true I
      · exact ⟨_, _, _, _, Proc.respLeaf (k := .full) (Or.inr rfl) hl.1 hl.2⟩
      · exact ⟨_, _, _, _, Proc.respNarrow (k := .full) (fan := 16) (Or.inr rfl) hl h16 (Nat.le_refl _)⟩
    · exact ⟨_, _, _, _, Proc.fullInit⟩
  | reply v =>
    have : toInit = true := hwf.2 v rfl
    subst this
    cases v
    · exact ⟨_, _, _, _, Proc.replyExact⟩
    · exact ⟨_, _, _, _, Proc.replyIds⟩

/-- A state with a pending part has a step. -/
theorem aps_progress {c : Cfg} {s : St} (h : PReach c s) (hp : s.pend ≠ []) : ∃ s', PStep c s s' := by
  obtain ⟨_, _, _, hwf⟩ := reach_inv h
  obtain ⟨q, rest0, hq0⟩ : ∃ q rest0, s.pend = q :: rest0 := by
    cases hh : s.pend with
    | nil => exact absurd hh hp
    | cons q r => exact ⟨q, r, rfl⟩
  obtain ⟨kids, ha, ta, lf, hpr⟩ := Proc_exists c s.exact q (hwf q (by rw [hq0]; exact List.mem_cons_self))
  exact ⟨_, PStep.step (by rw [hq0]) hpr⟩

/-! ## The potential falls -/

theorem step_psum {c : Cfg} {f : Nat} (hfl : 2 ≤ f) (hfm : f ≤ c.minFan) {s s' : St} (hs : PStep c s s') :
    c.psum f s' + 1 ≤ c.psum f s := by
  cases hs with
  | @step p rest kids ha ta lf hperm hp =>
    obtain ⟨_, hc⟩ := hp.cost hfl hfm
    unfold Cfg.psum
    simp only
    rw [lsum_perm _ hperm, lsum_append]
    simp only [lsum]
    omega

theorem step_ok {c : Cfg} {f : Nat} (hfl : 2 ≤ f) (hfm : f ≤ c.minFan) {s s' : St} (hs : PStep c s s')
    (Ψ : Nat) (hd : ∀ q ∈ s.log ++ s.pend, q.d + c.psi f q ≤ Ψ) : ∀ q ∈ s'.log ++ s'.pend, q.d + c.psi f q ≤ Ψ := by
  cases hs with
  | @step p rest kids ha ta lf hperm hp =>
    obtain ⟨hpsi, _⟩ := hp.cost hfl hfm
    obtain ⟨_, _, _, _, _, _, hdk⟩ := hp.facts
    have hpm : p ∈ s.pend := hperm.symm.mem_iff.mp List.mem_cons_self
    intro q hq
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with (hq | rfl) | hq | hq
    · exact hd q (List.mem_append_left _ hq)
    · exact hd _ (List.mem_append_right _ hpm)
    · have := hpsi q hq; have := hdk q hq; have := hd p (List.mem_append_right _ hpm); omega
    · exact hd q (List.mem_append_right _ (hperm.symm.mem_iff.mp (List.mem_cons_of_mem _ hq)))

/-! ## The first message -/

theorem init_bounds {c : Cfg} {f : Nat} (hfl : 2 ≤ f) (hfm : f ≤ c.minFan) {ex : Bool} {s : St} (h : Init c ex s) :
    (∀ q ∈ s.log ++ s.pend, q.d + c.psi f q ≤ depthBound f c.A.length c.B.length) ∧
    s.log.length + c.psum f s ≤ stepsBound f c.diff c.A.length c.B.length := by
  have hnA := cnt_top c.A
  have hnB := cnt_top c.B
  have hdt := c.delta_top
  cases h with
  | leaf hcnt hf =>
    unfold depthBound stepsBound Cfg.psum
    cases ex
    · simp only [Bool.false_eq_true, ↓reduceIte, lsum, List.length_nil, List.nil_append, List.mem_singleton]
      rw [pot_ids, psi_ids, hnA, hnB, hdt]
      refine ⟨fun q hq => ?_, ?_⟩
      · subst hq; simp only [psi_ids, hnA, hnB]; omega
      · omega
    · simp only [↓reduceIte, lsum, List.length_nil, List.nil_append, List.mem_singleton]
      rw [pot_fullF, psi_fullF, hnA, hnB, hdt]
      refine ⟨fun q hq => ?_, ?_⟩
      · subst hq; simp only [psi_fullF, hnA, hnB]; omega
      · omega
  | @split fan hno hf1 hf2 =>
    have hc := two_le_of_no_leaf_top c ex hno
    obtain ⟨hsub, hdisj, hlen⟩ := split_kids c c.A c.hA Iv.top (fan := fan) (by omega) hf2 hc false 0
    have hlg : ∀ J ∈ splitIvs c.A Iv.top fan,
        lg f (cnt c.A J) + lg f (cnt c.B J) + 1 ≤ lg f (cnt c.A Iv.top) + lg f (cnt c.B Iv.top) := by
      intro J hJ
      have := split_lg f fan hfl (by omega) Iv.top c.A c.B c.hA hc J hJ; omega
    have hpsi : ∀ k ∈ (splitIvs c.A Iv.top fan).map (fun J => (⟨.fp, false, J, 0 + 1⟩ : Part)),
        c.psi f k + 2 ≤ depthBound f c.A.length c.B.length := by
      intro k hk
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hk
      have := hlg J hJ
      rw [hnA, hnB] at this
      rw [psi_fp]; unfold depthBound; omega
    refine ⟨?_, ?_⟩
    · intro q hq
      simp only [List.nil_append] at hq
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hq
      have := hpsi _ hq
      show 0 + 1 + c.psi f _ ≤ _
      omega
    · have hsp := split_pot c f ((splitIvs c.A Iv.top fan).map (fun J => (⟨.fp, false, J, 0 + 1⟩ : Part))) Iv.top
        (depthBound f c.A.length c.B.length - 2)
        (fun k hk => ⟨by obtain ⟨J, _, rfl⟩ := List.mem_map.mp hk; rfl, by have := hpsi k hk; omega⟩)
        hlen hdisj hsub
      unfold Cfg.psum stepsBound
      simp only [List.length_nil]
      rw [hdt] at hsp
      have e : depthBound f c.A.length c.B.length - 2 = 2 * (lg f c.A.length + lg f c.B.length) + 1 := by
        unfold depthBound; omega
      have h5 : c.diff * (2 * (lg f c.A.length + lg f c.B.length) + 1) ≤
          c.diff * (2 * (lg f c.A.length + lg f c.B.length) + 2) := Nat.mul_le_mul_left _ (by omega)
      rw [e] at hsp
      simp only [Nat.zero_add] at hsp
      omega


theorem lg_le_of_pow {f : Nat} (hf : 2 ≤ f) : ∀ k n : Nat, n ≤ f ^ k → lg f n ≤ k
  | 0, n, h => by simp at h; rw [lg_small (by omega)]; omega
  | k + 1, n, h => by
    by_cases hn : 2 ≤ n
    · rw [lg_step hn hf]
      have : (n + f - 1) / f ≤ f ^ k := by
        have h2 : (n + f - 1) / f < f ^ k + 1 := by
          rw [Nat.div_lt_iff_lt_mul (by omega), Nat.add_mul, Nat.one_mul]
          rw [Nat.pow_succ] at h
          omega
        omega
      have := lg_le_of_pow hf k _ this
      omega
    · rw [lg_small (by omega)]; omega

theorem aps_invariants {c : Cfg} {f : Nat} (hfl : 2 ≤ f) (hfm : f ≤ c.minFan) {s : St} (h : IReach c s) :
    (∀ q ∈ s.log ++ s.pend, q.d + c.psi f q ≤ depthBound f c.A.length c.B.length) ∧
    s.log.length + c.psum f s ≤ stepsBound f c.diff c.A.length c.B.length := by
  induction h with
  | init h => exact init_bounds hfl hfm h
  | step _ hs ih =>
    refine ⟨step_ok hfl hfm hs _ ih.1, ?_⟩
    have := step_psum hfl hfm hs
    cases hs
    simp only [List.length_append, List.length_singleton]
    omega

/-- Every part ever created has depth at most `depthBound`. -/
theorem aps_depth_bound {c : Cfg} {f : Nat} (hfl : 2 ≤ f) (hfm : f ≤ c.minFan) {s : St} (h : IReach c s) :
    ∀ q ∈ s.log ++ s.pend, q.d ≤ depthBound f c.A.length c.B.length := by
  intro q hq
  have := (aps_invariants hfl hfm h).1 q hq
  omega

/-- A finished pass processed at most `stepsBound` parts. -/
theorem aps_steps_bound {c : Cfg} {f : Nat} (hfl : 2 ≤ f) (hfm : f ≤ c.minFan) {s : St} (h : IReach c s)
    (hp : s.pend = []) : s.log.length ≤ stepsBound f c.diff c.A.length c.B.length := by
  have := (aps_invariants hfl hfm h).2
  have e : c.psum f s = 0 := by unfold Cfg.psum; rw [hp]; rfl
  omega

/-- Termination: from every reachable state some execution ends with nothing pending, within the bound. -/
theorem aps_finishes {c : Cfg} {s : St} (h : IReach c s) :
    ∃ s', IReach c s' ∧ s'.pend = [] ∧ s'.log.length ≤ stepsBound 2 c.diff c.A.length c.B.length := by
  have hfm : 2 ≤ c.minFan := c.hmin
  suffices ∀ n s, c.psum 2 s = n → IReach c s →
      ∃ s', IReach c s' ∧ s'.pend = [] ∧ s'.log.length ≤ stepsBound 2 c.diff c.A.length c.B.length from
    this _ s rfl h
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro s hn hs
    by_cases hp : s.pend = []
    · exact ⟨s, hs, hp, aps_steps_bound (Nat.le_refl 2) hfm hs hp⟩
    · obtain ⟨s', hstep⟩ := aps_progress hs.toP hp
      have := step_psum (c := c) (f := 2) (Nat.le_refl 2) hfm hstep
      exact ih (c.psum 2 s') (by omega) s' rfl (IReach.step hs hstep)

/-- With the 16-way split never narrowed, a set of fewer than 2^64 items per side gives at most 67 levels. -/
theorem aps_depth_bound_16 {c : Cfg} (h16 : c.minFan = 16) {s : St} (h : IReach c s)
    (hA : c.A.length ≤ 2 ^ 64) (hB : c.B.length ≤ 2 ^ 64) : ∀ q ∈ s.log ++ s.pend, q.d ≤ 67 := by
  intro q hq
  have := aps_depth_bound (f := 16) (by omega) (by omega) h q hq
  have h1 : lg 16 c.A.length ≤ 16 := lg_le_of_pow (by omega) 16 _ (by simpa using hA)
  have h2 : lg 16 c.B.length ≤ 16 := lg_le_of_pow (by omega) 16 _ (by simpa using hB)
  unfold depthBound at this
  omega

end Pinc.Reconcile
