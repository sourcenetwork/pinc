import Vinc.ValuesSysSafe

/-!
# When every provider lies

PROPERTY 3, the converse of `every_provider_lied`: a started fetch with a provider named and every named provider
evicted has failed with `EveryProviderLied`. The invariant `Inv2` says a running fetch keeps a candidate (the
eviction of the last one ends the fetch), and that a fetch that ended with every named provider evicted ended by that
eviction.
-/

namespace Vinc.ValuesSys
open Classical

structure Inv2 (c : Cfg) (s : St) : Prop where
  cand : s.run = .running → ∃ p, s.inP p = true
  allLied : s.run = .done → (∃ p, c.listed p = true) → (∀ p, c.listed p = true → s.inP p = false) →
    s.fin = some .everyProviderLied

theorem inv2_init (c : Cfg) (rs : Nat) : Inv2 c (init c rs) := by
  refine ⟨?_, ?_⟩ <;> intro h <;> simp [init] at h

/-- A fetch that ends from a running state with its candidates untouched. -/
theorem Inv2.ofFinish {c : Cfg} {s X : St} (h2 : Inv2 c s) (h : Inv c s) (hr : s.run = .running)
    (hX : X.inP = s.inP) (f : Final) : Inv2 c (finish X f) := by
  refine ⟨fun e => by simp [finish] at e, fun _ ⟨p, hp⟩ hall => ?_⟩
  obtain ⟨q, hq⟩ := h2.cand hr
  have hql : c.listed q = true := by
    rcases h.inPL q hq with h3 | h3
    · exact h3
    · simp [hr] at h3
  have := hall q hql
  simp [finish, hX, hq] at this

theorem Inv2.step {c : Cfg} {s s' : St} (h2 : Inv2 c s) (h : Inv c s) (st : Step c s s') : Inv2 c s' := by
  cases st with
  | startBadRoot h1 h3 h4 =>
    refine ⟨fun e => by simp [finish] at e, fun _ ⟨p, hp⟩ hall => ?_⟩
    simp [finish] at hall; simp_all
  | startComplete h1 h3 h4 =>
    refine ⟨fun e => by simp [finish] at e, fun _ ⟨p, hp⟩ hall => ?_⟩
    simp [finish] at hall; simp_all
  | startNoProvider h1 h3 h4 h5 =>
    refine ⟨fun e => by simp [finish] at e, fun _ ⟨p, hp⟩ hall => ?_⟩
    simp [finish] at hall; simp_all
  | begin h1 h3 h4 h5 =>
    obtain ⟨p, hp⟩ := h5
    refine ⟨fun _ => ⟨p, by simpa using hp⟩, fun e => by simp at e⟩
  | plumb q a r h1 h3 po => exact ⟨fun e => h2.cand h1, fun e => by simp_all⟩
  | accept p g k h1 h3 h4 h5 h6 h7 h8 => exact ⟨fun e => h2.cand h1, fun e => by simp_all⟩
  | skip p g h1 h3 h4 h5 h6 => exact h2
  | acceptAhead p g k h1 h3 h4 h5 h6 h7 h8 => exact ⟨fun e => h2.cand h1, fun e => by simp_all⟩
  | evict p h1 h3 h4 h5 =>
    unfold evictSt; split
    · next hall =>
      refine ⟨fun e => by simp [finish] at e, fun _ _ _ => by simp [finish]⟩
    · next hnall =>
      have hrun : (evictBooks s p).run = .running := by
        have : (evict2 s p).run = s.run := by unfold evict2; split <;> rfl
        simpa [evictBooks, this] using h1
      refine ⟨fun _ => ?_, fun e => by simp [hrun] at e⟩
      have : ∃ q, (evict2 s p).inA q = true := by
        refine Classical.byContradiction fun hc => hnall fun q => ?_
        have := fun q => not_exists.mp hc q
        simpa using this q
      obtain ⟨q, hq⟩ := this
      have key : (evict2 s p).inP q = true := by
        by_cases h6 : ∀ q, (evict1 s p).inA q = false
        · have e2 : evict2 s p = { evict1 s p with inA := (evict1 s p).inP } := by simp [evict2, h6]
          rw [e2] at hq ⊢; simpa using hq
        · have e2 : evict2 s p = evict1 s p := by simp [evict2, h6]
          rw [e2] at hq ⊢
          simp [evict1] at hq ⊢
          exact ⟨hq.1, h.inAP q (by simpa using hq.2)⟩
      exact ⟨q, by simpa [evictBooks] using key⟩
  | write d h1 h3 h4 => exact ⟨fun e => h2.cand h1, fun e => by simp_all⟩
  | writeRefused d h1 h3 h4 h5 => exact h2.ofFinish h h1 rfl _
  | commit d h1 h3 h4 =>
    have : (commitSt c s d.g).run = s.run ∧ (commitSt c s d.g).inP = s.inP := by
      unfold commitSt; split <;> simp [readable]
    exact ⟨fun e => by rw [this.2]; exact h2.cand (by rw [← this.1]; exact e), fun e => by simp_all⟩
  | commitRefused d h1 h3 h4 h5 => exact h2.ofFinish h h1 rfl _
  | release h1 h3 h4 =>
    have : (releaseHd s).run = s.run ∧ (releaseHd s).inP = s.inP := by
      unfold releaseHd; cases s.hd <;> simp [readable]
    exact ⟨fun e => by rw [this.2]; exact h2.cand (by rw [← this.1]; exact e), fun e => by simp_all⟩
  | check h1 h3 h4 =>
    have : (releaseHd s).inP = s.inP := by unfold releaseHd; cases s.hd <;> simp [readable]
    exact h2.ofFinish h h1 this _
  | tick h1 h3 => exact ⟨fun e => h2.cand h1, fun e => by simp_all⟩
  | deadlineFire d h1 h3 h4 h5 => exact h2.ofFinish h h1 rfl _
  | restart h1 h3 => exact ⟨fun e => by simp [init] at e, fun e => by simp [init] at e⟩

theorem reach_inv2 {c : Cfg} {rs : Nat} {s : St} (h : Reach c rs s) : Inv2 c s := by
  induction h with
  | init => exact inv2_init c rs
  | step s s' hr st ih => exact ih.step (reach_inv hr) st

/-- PROPERTY 3: when every provider lies, the fetch fails with `EveryProviderLied` (and it ends: a running fetch always
has a candidate left). -/
theorem all_lie_fails {c : Cfg} {rs : Nat} {s : St} (h : Reach c rs s) (hn : ∃ p, c.listed p = true)
    (hall : ∀ p, c.listed p = true → s.inP p = false) (hst : s.run ≠ .idle) :
    s.run = .done ∧ s.fin = some .everyProviderLied := by
  have i2 := reach_inv2 h
  have i := reach_inv h
  have hd : s.run = .done := by
    cases hrun : s.run with
    | idle => exact absurd hrun hst
    | done => rfl
    | running =>
      obtain ⟨q, hq⟩ := i2.cand hrun
      obtain ⟨p, hp⟩ := hn
      have hql : c.listed q = true := by
        rcases i.inPL q hq with h3 | h3
        · exact h3
        · simp [hrun] at h3
      have := hall q hql
      simp_all
  exact ⟨hd, i2.allLied hd hn hall⟩

end Vinc.ValuesSys
