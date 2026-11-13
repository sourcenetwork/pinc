import Vinc.Axioms
import Vinc.ValuesSchedMove

/-!
# Coverage of the work: no wanted byte is ever dropped

The scheduler state is the stripe queue `q`, the assigned list `a p` of every provider and the set `act` of providers
that hold a share (`in_assign`). `Reach` is every state the code can reach from a start (or a resume) by the moves of
`sched.rs`: a verification (the store only grows), a top-up from the queue, a steal, an eviction, and the early return
of a top-up that still prunes verified bytes from the provider's list. The moves are the functions of the code on the
list model (`tc`, `stealSplit`, `evictQueue`, `retainMissing`, `extend`) with the capacity `n` of the 64-span lists.

`reach_cover`: in every reachable state, every wanted byte that the store has not verified is in the queue or in the
assigned list of an active provider. Nothing is dropped by a top-up, a steal (cut at any `keep`), an eviction (the
share goes back to the queue), a prune, or a widening push; this is the invariant "coverage never shrinks" lifted
from the list to the schedule. `reach_complete`: when the queue and every active list are empty, every wanted byte is
verified, so a fetch that empties its work has fetched what it was asked for. The start covers resume:
`start_inv` and `start1_inv`, the queue after `start` holds every wanted byte that was not verified.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Vinc.ValuesSched

theorem rm_aux_length {n : Nat} (hn : 0 < n) (st : Store) (l : List Span) :
    ∀ {acc : List Span}, acc.length ≤ n →
      (l.foldl (fun out s => (holesOf st s).foldl (push n) out) acc).length ≤ n := by
  induction l with
  | nil => intro acc h; exact h
  | cons s t ih => intro acc h; exact ih (foldl_push_length hn _ h)

theorem retainMissing_length_le {n : Nat} (hn : 0 < n) (st : Store) (l : List Span) :
    (retainMissing st n l).length ≤ n := rm_aux_length hn st l (by simp)

/-- The state of the scheduler. -/
structure Sys where
  q : List Span
  a : Nat → List Span
  act : List Nat

/-- Every unverified wanted byte is in the queue or in an active provider's list. -/
def Cover (W : Nat → Prop) (st : Store) (s : Sys) : Prop :=
  ∀ x, W x → ¬ st.V x → cov s.q x ∨ ∃ p ∈ s.act, cov (s.a p) x

/-- All the lists are within their capacity and the active set has no repeat. -/
def Sized (n : Nat) (s : Sys) : Prop := s.q.length ≤ n ∧ (∀ p, (s.a p).length ≤ n) ∧ s.act.Nodup

/-- A top-up from the queue: prune the provider's list, take a chunk of `want` bytes, add it. -/
def topUpMv (st : Store) (n fuel want p : Nat) (s : Sys) : Sys :=
  let r := tc st n want fuel 0 s.q []
  { s with q := r.1, a := upd s.a p (extend n (retainMissing st n (s.a p)) r.2) }

/-- The prune that every top-up starts with (and the whole of one that returns early). -/
def pruneMv (st : Store) (n p : Nat) (s : Sys) : Sys :=
  { s with a := upd s.a p (retainMissing st n (s.a p)) }

/-- A steal of provider `b` by provider `p` at `keep` bytes: every active list is pruned first. -/
def stealMv (st : Store) (n keep p b : Nat) (s : Sys) : Sys :=
  let a1 : Nat → List Span := fun j => if j ∈ s.act then retainMissing st n (s.a j) else s.a j
  let r := stealSplit n keep 0 (a1 b) [] []
  let a2 := upd a1 b (extend n [] r.1)
  { s with a := upd a2 p (extend n (a2 p) r.2) }

/-- An eviction: the share goes back to the front of the queue, the provider leaves the active set. -/
def evictMv (st : Store) (n p : Nat) (s : Sys) : Sys :=
  { q := evictQueue n s.q (retainMissing st n (s.a p)), a := upd s.a p [], act := s.act.erase p }

/-- The state after `start`: the missing part of the wanted ranges, in the queue. -/
def startSys (st : Store) (nw n : Nat) (want : List Span) (ps : List Nat) : Sys :=
  { q := extend n [] (retainMissing st nw want), a := fun _ => [], act := ps }

/-- The state after `start` of a fetch of one provider (not striped): the missing part, split in one share. -/
def start1Sys (st : Store) (nw n : Nat) (want : List Span) : Sys :=
  { q := [], a := upd (fun _ => []) 0 (extend n [] (split n 4 1 (retainMissing st nw want) 0)), act := [0] }

/-- The reachable states, with the store that has verified the bytes so far. -/
inductive Reach (nw n : Nat) (want : List Span) : Store → Sys → Prop
  | start (st : Store) (ps : List Nat) : ps.Nodup → Reach nw n want st (startSys st nw n want ps)
  | start1 (st : Store) : Reach nw n want st (start1Sys st nw n want)
  | verify (st st' : Store) (s : Sys) : Reach nw n want st s → (∀ x, st.V x → st'.V x) → Reach nw n want st' s
  | topUp (st : Store) (s : Sys) (fuel want' p : Nat) :
      Reach nw n want st s → p ∈ s.act → Reach nw n want st (topUpMv st n fuel want' p s)
  | prune (st : Store) (s : Sys) (p : Nat) :
      Reach nw n want st s → p ∈ s.act → Reach nw n want st (pruneMv st n p s)
  | steal (st : Store) (s : Sys) (keep p b : Nat) :
      Reach nw n want st s → p ∈ s.act → b ∈ s.act → b ≠ p → Reach nw n want st (stealMv st n keep p b s)
  | evict (st : Store) (s : Sys) (p : Nat) :
      Reach nw n want st s → p ∈ s.act → s.act.erase p ≠ [] → Reach nw n want st (evictMv st n p s)

theorem upd_length {n : Nat} {f : Nat → List Span} (h : ∀ p, (f p).length ≤ n) (i : Nat) {v : List Span}
    (hv : v.length ≤ n) : ∀ p, (upd f i v p).length ≤ n := by
  intro p; unfold upd; split
  · exact hv
  · exact h p

theorem upd_mem_act {f : Nat → List Span} {i j : Nat} {v : List Span} (h : j ≠ i) : upd f i v j = f j :=
  upd_other f i j v h

theorem topUp_inv {nw n : Nat} (hn : 0 < n) (st : Store) (W : Nat → Prop) (fuel want p : Nat) (s : Sys)
    (hp : p ∈ s.act) (hs : Sized n s) (hc : Cover W st s) :
    Sized n (topUpMv st n fuel want p s) ∧ Cover W st (topUpMv st n fuel want p s) := by
  obtain ⟨hq, ha, hnd⟩ := hs
  have hl := tc_length st hn want fuel 0 s.q [] hq (by simp)
  have hap := retainMissing_length_le hn st (s.a p)
  refine ⟨⟨hl.1, upd_length ha p (extend_length_le hn hap _), hnd⟩, fun x hx hv => ?_⟩
  simp only [topUpMv]
  rcases hc x hx hv with h | ⟨j, hj, h⟩
  · have := (tc_cov st hn want x hv fuel 0 s.q [] hq (by simp) (Or.inl h)).2.2
    rcases this with h | h
    · exact Or.inl h
    · refine Or.inr ⟨p, hp, ?_⟩
      rw [upd_same]
      exact extend_cov hn hap _ x (Or.inr h)
  · by_cases hjp : j = p
    · subst hjp
      refine Or.inr ⟨j, hj, ?_⟩
      rw [upd_same]
      exact extend_cov hn hap _ x (Or.inl (retainMissing_cov st hn _ x hv h))
    · exact Or.inr ⟨j, hj, by rw [upd_other _ _ _ _ hjp]; exact h⟩

theorem prune_inv {n : Nat} (hn : 0 < n) (st : Store) (W : Nat → Prop) (p : Nat) (s : Sys)
    (hp : p ∈ s.act) (hs : Sized n s) (hc : Cover W st s) :
    Sized n (pruneMv st n p s) ∧ Cover W st (pruneMv st n p s) := by
  obtain ⟨hq, ha, hnd⟩ := hs
  refine ⟨⟨hq, upd_length ha p (retainMissing_length_le hn st _), hnd⟩, fun x hx hv => ?_⟩
  simp only [pruneMv]
  rcases hc x hx hv with h | ⟨j, hj, h⟩
  · exact Or.inl h
  · by_cases hjp : j = p
    · subst hjp
      exact Or.inr ⟨j, hj, by rw [upd_same]; exact retainMissing_cov st hn _ x hv h⟩
    · exact Or.inr ⟨j, hj, by rw [upd_other _ _ _ _ hjp]; exact h⟩

theorem steal_inv {n : Nat} (hn : 0 < n) (st : Store) (W : Nat → Prop) (keep p b : Nat) (s : Sys)
    (hp : p ∈ s.act) (hb : b ∈ s.act) (hbp : b ≠ p) (hs : Sized n s) (hc : Cover W st s) :
    Sized n (stealMv st n keep p b s) ∧ Cover W st (stealMv st n keep p b s) := by
  obtain ⟨hq, ha, hnd⟩ := hs
  have ha1 : ∀ j, ((fun j => if j ∈ s.act then retainMissing st n (s.a j) else s.a j) j).length ≤ n := by
    intro j; simp only; split
    · exact retainMissing_length_le hn st _
    · exact ha j
  have hsl := stealSplit_length hn keep (((fun j => if j ∈ s.act then retainMissing st n (s.a j) else s.a j) b))
    0 [] [] (by simp) (by simp)
  have hex1 : (extend n [] (stealSplit n keep 0 ((fun j => if j ∈ s.act then retainMissing st n (s.a j) else s.a j) b) [] []).1).length ≤ n :=
    extend_length_le hn (by simp) _
  have ha2 := upd_length ha1 b hex1
  refine ⟨⟨hq, ?_, hnd⟩, fun x hx hv => ?_⟩
  · simp only [stealMv]
    exact upd_length ha2 p (extend_length_le hn (ha2 p) _)
  · simp only [stealMv]
    rcases hc x hx hv with h | ⟨j, hj, h⟩
    · exact Or.inl h
    · right
      have hj1 : cov ((fun j => if j ∈ s.act then retainMissing st n (s.a j) else s.a j) j) x := by
        simp only [if_pos hj]; exact retainMissing_cov st hn _ x hv h
      by_cases hjb : j = b
      · subst hjb
        have hh := (stealSplit_cov hn keep x (((fun j => if j ∈ s.act then retainMissing st n (s.a j) else s.a j) j))
          0 [] [] (by simp) (by simp) (Or.inr (Or.inr hj1)))
        rcases hh.2.2 with hh | hh
        · exact ⟨j, hj, by
            rw [upd_other _ _ _ _ hbp, upd_same]
            exact extend_cov hn (by simp) _ x (Or.inr hh)⟩
        · refine ⟨p, hp, ?_⟩
          rw [upd_same]
          exact extend_cov hn (ha2 p) _ x (Or.inr hh)
      · by_cases hjp : j = p
        · subst hjp
          refine ⟨j, hj, ?_⟩
          rw [upd_same]
          refine extend_cov hn (ha2 j) _ x (Or.inl ?_)
          rw [upd_other _ _ _ _ hjb]; exact hj1
        · exact ⟨j, hj, by rw [upd_other _ _ _ _ hjp, upd_other _ _ _ _ hjb]; exact hj1⟩

theorem evict_inv {n : Nat} (hn : 0 < n) (st : Store) (W : Nat → Prop) (p : Nat) (s : Sys)
    (hp : p ∈ s.act) (hs : Sized n s) (hc : Cover W st s) :
    Sized n (evictMv st n p s) ∧ Cover W st (evictMv st n p s) := by
  obtain ⟨hq, ha, hnd⟩ := hs
  have hmiss := retainMissing_length_le hn st (s.a p)
  refine ⟨⟨evictQueue_length hn _ _ hq, upd_length ha p (by simp), hnd.erase p⟩, fun x hx hv => ?_⟩
  simp only [evictMv]
  rcases hc x hx hv with h | ⟨j, hj, h⟩
  · exact Or.inl (evictQueue_cov hn x _ _ hq (Or.inl h)).2
  · by_cases hjp : j = p
    · subst hjp
      exact Or.inl (evictQueue_cov hn x _ _ hq (Or.inr (retainMissing_cov st hn _ x hv h))).2
    · refine Or.inr ⟨j, ?_, by rw [upd_other _ _ _ _ hjp]; exact h⟩
      exact (List.mem_erase_of_ne hjp).2 hj

/-- A start, striped or not, covers every wanted byte the store has not verified: only `missing` bytes are queued. -/
theorem start_inv {nw n : Nat} (hnw : 0 < nw) (hn : 0 < n) (st : Store) (want : List Span) (ps : List Nat)
    (hps : ps.Nodup) :
    Sized n (startSys st nw n want ps) ∧ Cover (cov want) st (startSys st nw n want ps) := by
  refine ⟨⟨extend_length_le hn (by simp) _, by simp [startSys], hps⟩, fun x hx hv => ?_⟩
  left
  exact extend_cov hn (by simp) _ x (Or.inr (retainMissing_cov st hnw _ x hv hx))

theorem start1_inv {nw n : Nat} (hnw : 0 < nw) (hn : 0 < n) (st : Store) (want : List Span) :
    Sized n (start1Sys st nw n want) ∧ Cover (cov want) st (start1Sys st nw n want) := by
  refine ⟨⟨by simp [start1Sys], ?_, by simp [start1Sys]⟩, fun x hx hv => ?_⟩
  · intro p; simp only [start1Sys]; unfold upd; split
    · exact extend_length_le hn (by simp) _
    · simp
  · right
    refine ⟨0, by simp [start1Sys], ?_⟩
    simp only [start1Sys, upd_same]
    have hneed : cov (retainMissing st nw want) x := retainMissing_cov st hnw _ x hv hx
    obtain ⟨i, hik, hi⟩ := split_cov hn 4 1 _ x hneed
    have : i = 0 := by unfold clampK at hik; omega
    subst this
    exact extend_cov hn (by simp) _ x (Or.inr hi)

/-- In every reachable state the lists are within capacity and every unverified wanted byte is queued or assigned. -/
theorem reach_inv {nw n : Nat} (hnw : 0 < nw) (hn : 0 < n) (want : List Span) (st : Store) (s : Sys)
    (h : Reach nw n want st s) : Sized n s ∧ Cover (cov want) st s := by
  induction h with
  | start st ps hps => exact start_inv hnw hn st want ps hps
  | start1 st => exact start1_inv hnw hn st want
  | verify st st' s _ hmono ih =>
    exact ⟨ih.1, fun x hx hv => ih.2 x hx (fun hh => hv (hmono x hh))⟩
  | topUp st s fuel want' p _ hp ih => exact topUp_inv (nw := nw) hn st _ fuel want' p s hp ih.1 ih.2
  | prune st s p _ hp ih => exact prune_inv hn st _ p s hp ih.1 ih.2
  | steal st s keep p b _ hp hb hbp ih => exact steal_inv hn st _ keep p b s hp hb hbp ih.1 ih.2
  | evict st s p _ hp _ ih => exact evict_inv hn st _ p s hp ih.1 ih.2

/-- No wanted byte is ever dropped. -/
theorem reach_cover {nw n : Nat} (hnw : 0 < nw) (hn : 0 < n) (want : List Span) (st : Store) (s : Sys)
    (h : Reach nw n want st s) : Cover (cov want) st s := (reach_inv hnw hn want st s h).2

/-- A fetch that has emptied its queue and every active list has fetched every wanted byte. -/
theorem reach_complete {nw n : Nat} (hnw : 0 < nw) (hn : 0 < n) (want : List Span) (st : Store) (s : Sys)
    (h : Reach nw n want st s) (hq : s.q = []) (ha : ∀ p ∈ s.act, s.a p = []) :
    ∀ x, cov want x → st.V x := by
  intro x hx
  by_cases hv : st.V x
  · exact hv
  · rcases reach_cover hnw hn want st s h x hx hv with h1 | ⟨p, hp, h2⟩
    · rw [hq] at h1; exact absurd h1 (cov_nil x)
    · rw [ha p hp] at h2; exact absurd h2 (cov_nil x)

end Vinc.ValuesSched

#audit_axioms Vinc.ValuesSched.reach_inv
#audit_axioms Vinc.ValuesSched.retainMissing_length_le
#audit_axioms Vinc.ValuesSched.reach_cover
#audit_axioms Vinc.ValuesSched.reach_complete
#audit_axioms Vinc.ValuesSched.topUp_inv
#audit_axioms Vinc.ValuesSched.prune_inv
#audit_axioms Vinc.ValuesSched.steal_inv
#audit_axioms Vinc.ValuesSched.evict_inv
#audit_axioms Vinc.ValuesSched.start_inv
#audit_axioms Vinc.ValuesSched.start1_inv
