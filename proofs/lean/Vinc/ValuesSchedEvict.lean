import Vinc.Axioms
import Vinc.ValuesSchedCover

/-!
# LIAR_EVICT

`Fetch::evict` of `fetch/sched.rs` on the flags and streams it touches. A provider whose bytes failed verification is
cut off: its request streams are reset with `code::LIAR` and forgotten, it leaves the candidates (`in_provs`) and the
holders of a share (`in_assign`), its clocks, rate counters and retry are cleared and its share is taken. When no
provider holds a share any more, the holders are restored from the candidates; if there are still none, the fetch is
`Done`, every remaining stream is reset with `code::CANCELLED`, and it fails with `EveryProviderLied`.

- `evictF_clears`: the evicted provider has `in_provs = in_assign = false`, no share, no clocks.
- `evictF_streams`: none of its streams stays, and each was reset with the liar code.
- `evictF_all_lied`: if no other provider is a candidate the fetch ends `Done` with `EveryProviderLied` and no stream
  open; `evictF_survivor`: if another provider holds a share it stays `Running`.
- `evictF_inv`, `evicted_forever`: a holder is always a candidate, and an evicted provider is never a candidate or a
  holder again: every assignment (a top-up, a steal in either role, the return of a share) requires `in_assign`.
- `moves_keep_inactive`: on the work lists, no move changes the list of a provider outside the active set, and the
  active set only shrinks: the evicted provider is never given work.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Vinc.ValuesSched

/-- `code::LIAR` and `code::CANCELLED`. -/
def codeLiar : Nat := 3
def codeCancelled : Nat := 0

inductive St where
  | idle
  | running
  | done
  deriving DecidableEq

inductive Fail where
  | everyProviderLied
  | other
  deriving DecidableEq

/-- The fields of one provider that eviction touches. -/
structure PS where
  inProvs : Bool
  inAssign : Bool
  assign : List Span
  retry : Option Nat
  lp : Option Nat
  pt : Option Nat
  pb : Nat

/-- The part of the fetch an eviction touches: the four provider slots, the request streams (provider slot, stream),
the state, the resets sent (stream, code) and the failure reported. -/
structure FS where
  provs : Nat → PS
  rx : List (Nat × Nat)
  state : St
  resets : List (Nat × Nat)
  failed : Option Fail

/-- `MAX_PROVIDERS`. -/
def slots : Nat := 4

def anyAssign (pr : Nat → PS) : Bool := (List.range slots).any fun i => (pr i).inAssign

def clearP (x : PS) : PS :=
  { x with inProvs := false, inAssign := false, retry := none, lp := none, pt := none, pb := 0, assign := [] }

def updP (f : Nat → PS) (i : Nat) (v : PS) : Nat → PS := fun j => if j = i then v else f j

/-- The slots after the evicted provider is cleared. -/
def ev1 (fs : FS) (p : Nat) : Nat → PS := updP fs.provs p (clearP (fs.provs p))

/-- ... and after the holders are restored from the candidates if nobody holds a share. -/
def ev2 (fs : FS) (p : Nat) : Nat → PS :=
  if anyAssign (ev1 fs p) = true then ev1 fs p
  else fun i => { ev1 fs p i with inAssign := (ev1 fs p i).inProvs }

/-- The flag part of `evict` (the return of the share to the queue is `evictMv`). -/
def evictF (fs : FS) (p : Nat) : FS :=
  let base : FS := { fs with provs := ev2 fs p, rx := fs.rx.filter (fun r => r.1 ≠ p),
                              resets := (fs.rx.filter fun r => r.1 = p).map (fun r => (r.2, codeLiar)) ++ fs.resets }
  if anyAssign (ev2 fs p) = true then base
  else { base with state := St.done, rx := [], failed := some Fail.everyProviderLied,
                    resets := base.rx.map (fun r => (r.2, codeCancelled)) ++ base.resets }

theorem anyAssign_false {pr : Nat → PS} (h : anyAssign pr = false) : ∀ i, i < slots → (pr i).inAssign = false := by
  intro i hi
  unfold anyAssign at h
  simp only [List.any_eq_false, List.mem_range] at h
  have := h i hi
  simpa using this

theorem anyAssign_true {pr : Nat → PS} {i : Nat} (hi : i < slots) (h : (pr i).inAssign = true) : anyAssign pr = true := by
  unfold anyAssign
  simp only [List.any_eq_true, List.mem_range]
  exact ⟨i, hi, h⟩

theorem evictF_provs (fs : FS) (p : Nat) : (evictF fs p).provs = ev2 fs p := by
  unfold evictF; split <;> rfl

theorem ev1_p (fs : FS) (p : Nat) : ev1 fs p p = clearP (fs.provs p) := by simp [ev1, updP]
theorem ev1_other (fs : FS) (p i : Nat) (h : i ≠ p) : ev1 fs p i = fs.provs i := by simp [ev1, updP, h]

theorem ev2_p (fs : FS) (p : Nat) : ev2 fs p p = clearP (fs.provs p) := by
  unfold ev2; split
  · exact ev1_p fs p
  · simp [ev1_p, clearP]

/-- The evicted provider is a candidate and a holder no more, and holds no share or clock. -/
theorem evictF_clears (fs : FS) (p : Nat) :
    ((evictF fs p).provs p).inProvs = false ∧ ((evictF fs p).provs p).inAssign = false ∧
      ((evictF fs p).provs p).assign = [] ∧ ((evictF fs p).provs p).retry = none ∧
      ((evictF fs p).provs p).lp = none ∧ ((evictF fs p).provs p).pt = none ∧ ((evictF fs p).provs p).pb = 0 := by
  rw [evictF_provs, ev2_p]; simp [clearP]

/-- None of its streams stays, and each of them was reset with the liar code. -/
theorem evictF_streams (fs : FS) (p : Nat) :
    (∀ r ∈ (evictF fs p).rx, r.1 ≠ p) ∧
    (∀ r ∈ fs.rx, r.1 = p → (r.2, codeLiar) ∈ (evictF fs p).resets) := by
  constructor
  · intro r hr
    unfold evictF at hr
    split at hr
    · simp at hr; exact hr.2
    · simp at hr
  · intro r hr hp
    have hm : (r.2, codeLiar) ∈ ((fs.rx.filter fun r => r.1 = p).map (fun r => (r.2, codeLiar)) ++ fs.resets) :=
      List.mem_append_left _ (List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, by simp [hp]⟩, rfl⟩)
    unfold evictF
    split
    · exact hm
    · exact List.mem_append_right _ hm

/-- If no other provider is a candidate (every provider lied), the fetch is done, failed with `EveryProviderLied`, and
has no stream open. -/
theorem evictF_all_lied (fs : FS) (p : Nat) (hp : p < slots)
    (hinv : ∀ i, i < slots → (fs.provs i).inAssign = true → (fs.provs i).inProvs = true)
    (hothers : ∀ i, i < slots → i ≠ p → (fs.provs i).inProvs = false) :
    (evictF fs p).state = St.done ∧ (evictF fs p).failed = some Fail.everyProviderLied ∧ (evictF fs p).rx = [] := by
  have hn : anyAssign (ev2 fs p) = false := by
    cases h : anyAssign (ev2 fs p)
    · rfl
    · exfalso
      unfold anyAssign at h
      simp only [List.any_eq_true, List.mem_range] at h
      obtain ⟨i, hi, hia⟩ := h
      by_cases hip : i = p
      · subst hip
        rw [ev2_p] at hia; simp [clearP] at hia
      · unfold ev2 at hia
        split at hia
        · rw [ev1_other fs p i hip] at hia
          have := hinv i hi hia
          rw [hothers i hi hip] at this
          exact absurd this (by decide)
        · simp [ev1_other fs p i hip, hothers i hi hip] at hia
  unfold evictF
  rw [hn]
  simp

/-- If another provider still holds a share after the eviction, the fetch is not ended by it. -/
theorem evictF_survivor (fs : FS) (p i : Nat) (hi : i < slots) (hip : i ≠ p) (h : (fs.provs i).inAssign = true) :
    (evictF fs p).state = fs.state ∧ (evictF fs p).failed = fs.failed := by
  have hy : anyAssign (ev2 fs p) = true := by
    apply anyAssign_true hi
    unfold ev2
    split
    · rw [ev1_other fs p i hip]; exact h
    · rename_i hno
      exfalso
      have := anyAssign_false (by simpa using hno) i hi
      rw [ev1_other fs p i hip] at this
      rw [h] at this; exact absurd this (by decide)
  unfold evictF; rw [if_pos hy]; exact ⟨rfl, rfl⟩

/-- A holder is a candidate: an evicted provider stays out of both. -/
def FlagInv (fs : FS) : Prop :=
  ∀ i, i < slots → (fs.provs i).inAssign = true → (fs.provs i).inProvs = true

theorem evictF_inv (fs : FS) (p : Nat) (h : FlagInv fs) : FlagInv (evictF fs p) := by
  intro i hi hia
  rw [evictF_provs] at hia ⊢
  unfold ev2 at hia ⊢
  split at hia
  · rename_i hy
    simp only [hy, if_true] at ⊢
    by_cases hip : i = p
    · subst hip; rw [ev1_p] at hia; simp [clearP] at hia
    · rw [ev1_other fs p i hip] at hia ⊢; exact h i hi hia
  · rename_i hy
    simp only [hy] at ⊢
    simpa using hia

/-- Once evicted, never a candidate or a holder again, across any further evictions. -/
theorem evicted_forever (fs : FS) (p q : Nat) (hps : p < slots) (hp : (fs.provs p).inProvs = false) (h : FlagInv fs) :
    ((evictF fs q).provs p).inProvs = false ∧ ((evictF fs q).provs p).inAssign = false := by
  rw [evictF_provs]
  unfold ev2
  by_cases hpq : p = q
  · subst hpq; split
    · rw [ev1_p]; simp [clearP]
    · simp [ev1_p, clearP]
  · have hia : (fs.provs p).inAssign = false := by
      cases hh : (fs.provs p).inAssign
      · rfl
      · have := h p hps hh; rw [hp] at this; exact absurd this (by decide)
    split
    · rw [ev1_other fs q p hpq]; exact ⟨hp, hia⟩
    · simp [ev1_other fs q p hpq, hp]

/-! ## The work lists: an evicted provider is never given work -/

theorem topUpMv_other (st : Store) (n fuel want p j : Nat) (s : Sys) (h : j ≠ p) :
    (topUpMv st n fuel want p s).a j = s.a j := by
  simp [topUpMv, upd_other _ _ _ _ h]

theorem stealMv_other (st : Store) (n keep p b j : Nat) (s : Sys) (hj : j ∉ s.act) (hjp : j ≠ p) (hjb : j ≠ b) :
    (stealMv st n keep p b s).a j = s.a j := by
  simp [stealMv, upd_other _ _ _ _ hjp, upd_other _ _ _ _ hjb, hj]

theorem evictMv_act (st : Store) (n p : Nat) (s : Sys) (hnd : s.act.Nodup) :
    p ∉ (evictMv st n p s).act ∧ ∀ j, j ∈ (evictMv st n p s).act → j ∈ s.act := by
  refine ⟨?_, fun j hj => ?_⟩
  · simp only [evictMv]; exact fun h => (List.Nodup.mem_erase_iff hnd).1 h |>.1 rfl
  · simp only [evictMv] at hj; exact List.mem_of_mem_erase hj

/-- One scheduling move, as `Reach` applies them, without its history. -/
inductive Step (n : Nat) : Store → Sys → Store → Sys → Prop
  | verify (st st' : Store) (s : Sys) : (∀ x, st.V x → st'.V x) → Step n st s st' s
  | topUp (st : Store) (s : Sys) (fuel want p : Nat) : p ∈ s.act → Step n st s st (topUpMv st n fuel want p s)
  | prune (st : Store) (s : Sys) (p : Nat) : p ∈ s.act → Step n st s st (pruneMv st n p s)
  | steal (st : Store) (s : Sys) (keep p b : Nat) :
      p ∈ s.act → b ∈ s.act → b ≠ p → Step n st s st (stealMv st n keep p b s)
  | evict (st : Store) (s : Sys) (p : Nat) : p ∈ s.act → Step n st s st (evictMv st n p s)

/-- A provider outside the active set (evicted) stays outside it and keeps the list it has: no move gives it work. -/
theorem step_inactive {n : Nat} {st st' : Store} {s s' : Sys} (hst : Step n st s st' s') (j : Nat) (hj : j ∉ s.act) :
    j ∉ s'.act ∧ s'.a j = s.a j := by
  cases hst with
  | verify _ _ _ => exact ⟨hj, rfl⟩
  | topUp _ fuel want p hp =>
    have hjp : j ≠ p := fun h => hj (h ▸ hp)
    exact ⟨hj, topUpMv_other st n fuel want p j s hjp⟩
  | prune _ p hp =>
    have hjp : j ≠ p := fun h => hj (h ▸ hp)
    exact ⟨hj, by simp [pruneMv, upd_other _ _ _ _ hjp]⟩
  | steal _ keep p b hp hb hbp =>
    have hjp : j ≠ p := fun h => hj (h ▸ hp)
    have hjb : j ≠ b := fun h => hj (h ▸ hb)
    exact ⟨hj, stealMv_other st n keep p b j s hj hjp hjb⟩
  | evict _ p hp =>
    have hjp : j ≠ p := fun h => hj (h ▸ hp)
    refine ⟨fun h => hj (List.mem_of_mem_erase h), ?_⟩
    simp [evictMv, upd_other _ _ _ _ hjp]

/-- The evicted provider itself: out of the active set, with an empty list. -/
theorem evict_removes {n : Nat} (st : Store) (s : Sys) (p : Nat) (hnd : s.act.Nodup) :
    p ∉ (evictMv st n p s).act ∧ (evictMv st n p s).a p = [] := by
  refine ⟨(evictMv_act st n p s hnd).1, ?_⟩
  simp [evictMv, upd_same]

end Vinc.ValuesSched

#audit_axioms Vinc.ValuesSched.evictF_clears
#audit_axioms Vinc.ValuesSched.evictF_streams
#audit_axioms Vinc.ValuesSched.evictF_all_lied
#audit_axioms Vinc.ValuesSched.evictF_survivor
#audit_axioms Vinc.ValuesSched.evictF_inv
#audit_axioms Vinc.ValuesSched.evicted_forever
#audit_axioms Vinc.ValuesSched.step_inactive
#audit_axioms Vinc.ValuesSched.evict_removes
#audit_axioms Vinc.ValuesSched.evictMv_act
