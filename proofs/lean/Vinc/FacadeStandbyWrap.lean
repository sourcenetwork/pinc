import Vinc.Axioms
import Vinc.FacadeStandbyOrder

/-!
# The facade's standby slab: no stale entry names a live ticket again

Since the fix of #419 the release that brings a slot's generation round (from `2^32 - 1` to 0) drops every stale
entry of the queue (`wrapQueue`). So every entry of the queue names a slot whose generation is the entry's or past
it, and the entry's only while the slot is live (`GInv`, `init_ginv`, `run_ginv`, `exec_ginv`): a stale entry's
generation is below its slot's, and the slot's generation comes back to it only by going round, which drops the entry
first. So `alloc` never hands out a ticket that an entry of the queue names (`alloc_unnamed`) and no run revives a
stale entry (`exec_norevive`), whatever the calls (a slot released unarmed, or the bare slab driven past `2^32`
releases of a slot). From the empty slab, over any run: the slot of every live entry is queued, no ticket has two live
entries and the queue holds at most twice as many entries as the slab has slots (`exec_exact`); the live entries of
the queue are the documented order (`exec_inorder`); and the baton wakes the oldest armed ticket of that order
(`exec_oldest`).
-/

namespace Vinc.FacadeStandby

/-- Every entry of the queue names a slot whose generation is the entry's or past it, and the entry's only while the
slot is live. -/
def GInv (s : S) : Prop :=
  ∀ u ∈ s.queue, ∃ sl, s.slots[u.idx]? = some sl ∧ u.gen ≤ sl.gen ∧ (u.gen = sl.gen → sl.live = true)

theorem init_ginv : GInv ({} : S) := by
  intro u hu
  simp at hu

/-- A slot changed keeping its liveness and generation. -/
theorem lg_set (a : List Slot) (i : Nat) (sl v : Slot) (hsl : a[i]? = some sl) (hl : v.live = sl.live)
    (hg : v.gen = sl.gen) : LG a (a.set i v) := by
  have hlt := lt_of_get hsl
  refine ⟨by simp, ?_⟩
  intro j sk hj
  rw [get_set]
  by_cases hij : i = j
  · subst hij; rw [hsl] at hj; cases hj; exact ⟨v, by simp [hlt], hl, hg⟩
  · simp only [hij, false_and, ↓reduceIte]; exact ⟨sk, hj, rfl, rfl⟩

/-- Slots that keep each slot's liveness and generation, with a queue whose entries were all in the queue, keep it. -/
theorem ginv_lg {s s' : S} (hg : GInv s) (hk : LG s.slots s'.slots) (hq : ∀ u ∈ s'.queue, u ∈ s.queue) :
    GInv s' := by
  intro u hu
  obtain ⟨sl, h1, h2, h3⟩ := hg u (hq u hu)
  obtain ⟨sl', h4, l4, g4⟩ := hk.2 _ sl h1
  refine ⟨sl', h4, ?_, ?_⟩
  · rw [g4]; exact h2
  · intro e
    rw [l4]
    exact h3 (by rw [← g4]; exact e)

theorem alloc_ginv (s : S) (h : Inv s) (hg : GInv s) : GInv (alloc s).2 := by
  rcases alloc_cases s h with ⟨i, rest, sl0, _, hsl0, _, _, h2⟩ | ⟨_, _, h2⟩
  · rw [h2]
    intro u hu
    obtain ⟨sl, h3, h4, h5⟩ := hg u hu
    by_cases hui : u.idx = i
    · have e : sl = sl0 := by
        rw [hui, hsl0] at h3
        exact (Option.some.inj h3).symm
      rw [e] at h4
      refine ⟨{ sl0 with live := true }, ?_, h4, fun _ => rfl⟩
      show (s.slots.set i { sl0 with live := true })[u.idx]? = _
      rw [hui, get_set]
      simp [lt_of_get hsl0]
    · refine ⟨sl, ?_, h4, h5⟩
      show (s.slots.set i { sl0 with live := true })[u.idx]? = _
      rw [get_set]
      simp [Ne.symm hui, h3]
  · rw [h2]
    intro u hu
    obtain ⟨sl, h3, h4, h5⟩ := hg u hu
    refine ⟨sl, ?_, h4, h5⟩
    show (s.slots ++ [newSlot])[u.idx]? = _
    rw [get_push]
    simp [Nat.ne_of_lt (lt_of_get h3), h3]

theorem arm_ginv (t : Ticket) (w : Nat) (s : S) (hg : GInv s) : GInv (arm t w s) := by
  unfold arm
  cases hs : slotOf s t with
  | none => exact hg
  | some sl =>
    obtain ⟨hsl, hlive, hgen⟩ := slotOf_some.mp hs
    by_cases hq : sl.queued = true
    · simp only [hq, ↓reduceIte]
      exact ginv_lg hg (lg_set s.slots t.idx sl _ hsl rfl rfl) (fun _ hu => hu)
    · simp only [hq, Bool.false_eq_true, ↓reduceIte]
      have hk := lg_set s.slots t.idx sl { sl with waker := some w, queued := true } hsl rfl rfl
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · obtain ⟨sl1, h1, h2, h3⟩ := hg u (compact_sub hu)
        obtain ⟨sl', h4, l4, g4⟩ := hk.2 _ sl1 h1
        refine ⟨sl', h4, ?_, ?_⟩
        · rw [g4]; exact h2
        · intro e
          rw [l4]
          exact h3 (by rw [← g4]; exact e)
      · rw [List.mem_singleton] at hu
        rw [hu]
        refine ⟨{ sl with waker := some w, queued := true }, ?_, Nat.le_of_eq hgen.symm, fun _ => hlive⟩
        show (s.slots.set t.idx { sl with waker := some w, queued := true })[t.idx]? = _
        rw [get_set]
        simp [lt_of_get hsl]

theorem baton_ginv (s : S) (hg : GInv s) : GInv (baton s).2 := by
  refine ginv_lg hg (shape_lg (baton_shape s).1) ?_
  intro u hu
  rcases baton_first s with ⟨_, h2, _⟩ | ⟨pre, t, rest, _, _, h1, _, _, _, _, h6⟩
  · rw [h2] at hu; cases hu
  · rw [h6] at hu
    rw [h1]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hu)

theorem release_ginv (t : Ticket) (s : S) (h : Inv s) (hg : GInv s) : GInv (release t s) := by
  unfold release
  cases hs : slotOf s t with
  | none => exact hg
  | some sl =>
    obtain ⟨hsl, _, _⟩ := slotOf_some.mp hs
    have hlt := lt_of_get hsl
    have hglt := h.gen_lt _ sl hsl
    intro u hu
    change u ∈ wrapQueue sl.gen _ s.queue at hu
    unfold wrapQueue at hu
    split at hu
    · -- the release brings the generation round: every entry left is live
      obtain ⟨_, hv⟩ := List.mem_filter.mp hu
      obtain ⟨sl', hs'⟩ := valid_iff.mp hv
      obtain ⟨h1, h2, h3⟩ := slotAt_some.mp hs'
      exact ⟨sl', h1, Nat.le_of_eq h3.symm, fun _ => h2⟩
    · rename_i hw
      obtain ⟨sl1, h1, h2, h3⟩ := hg u hu
      have hmod : (sl.gen + 1) % GENS = sl.gen + 1 := Nat.mod_eq_of_lt (by omega)
      by_cases hut : u.idx = t.idx
      · have e : sl1 = sl := by
          rw [hut, hsl] at h1
          exact (Option.some.inj h1).symm
        rw [e] at h2
        refine ⟨{ sl with live := false, gen := (sl.gen + 1) % GENS, waker := none, queued := false }, ?_, ?_, ?_⟩
        · show (s.slots.set t.idx _)[u.idx]? = _
          rw [hut, get_set]
          simp [hlt]
        · show u.gen ≤ (sl.gen + 1) % GENS
          rw [hmod]
          omega
        · intro e2
          exfalso
          have e3 : u.gen = sl.gen + 1 := by rw [← hmod]; exact e2
          omega
      · refine ⟨sl1, ?_, h2, h3⟩
        show (s.slots.set t.idx _)[u.idx]? = _
        rw [get_set]
        simp [Ne.symm hut, h1]

theorem run_ginv (o : Op) (s : S) (h : Inv s) (hg : GInv s) : GInv (o.run s) := by
  cases o with
  | alloc => exact alloc_ginv s h hg
  | arm t w => exact arm_ginv t w s hg
  | notify t =>
    show GInv (notify t s).2
    refine ginv_lg hg (shape_lg (notify_shape t s).1) ?_
    intro u hu
    rw [(notify_shape t s).2.2] at hu
    exact hu
  | baton => exact baton_ginv s hg
  | notifyAll =>
    show GInv (notifyAll s).2
    refine ginv_lg hg (shape_lg (notifyAll_shape s).1) ?_
    intro u hu
    rw [(notifyAll_shape s).2.2] at hu
    exact hu
  | release t => exact release_ginv t s h hg

theorem exec_ginv : ∀ (os : List Op) (s : S), Inv s → GInv s → GInv (exec os s)
  | [], _, _, hg => hg
  | o :: os, s, h, hg => exec_ginv os (o.run s) (run_inv o s h) (run_ginv o s h hg)

/-- `alloc` hands out a ticket that no entry of the queue names. -/
theorem alloc_unnamed (s : S) (h : Inv s) (hg : GInv s) : (alloc s).1 ∉ s.queue := by
  intro hm
  rcases alloc_cases s h with ⟨i, rest, sl0, _, hsl0, hdead, h1, _⟩ | ⟨_, h1, _⟩
  · rw [h1] at hm
    obtain ⟨sl, h3, _, h5⟩ := hg _ hm
    have h3' : s.slots[i]? = some sl := h3
    rw [hsl0] at h3'
    have e : sl0 = sl := Option.some.inj h3'
    rw [← e] at h5
    have hl : sl0.live = true := h5 rfl
    rw [hdead] at hl
    cases hl
  · rw [h1] at hm
    exact Nat.lt_irrefl _ (h.q_idx _ hm)

theorem not_revives (o : Op) (s : S) (h : Inv s) (hg : GInv s) : ¬o.revives s := by
  cases o with
  | alloc => exact alloc_unnamed s h hg
  | arm t w => exact fun h => h
  | notify t => exact fun h => h
  | baton => exact fun h => h
  | notifyAll => exact fun h => h
  | release t => exact fun h => h

/-- No run revives a stale entry: no `alloc` hands out a ticket a stale entry of the queue still names. -/
theorem exec_norevive : ∀ (os : List Op) (s : S), Inv s → GInv s → NoRevive os s
  | [], _, _, _ => trivial
  | o :: os, s, h, hg => ⟨not_revives o s h hg, exec_norevive os (o.run s) (run_inv o s h) (run_ginv o s h hg)⟩

/-- From the empty slab, over any run, the queue is exact: the slot of every live entry is queued, no ticket has two
live entries, and the queue holds at most twice as many entries as the slab has slots. -/
theorem exec_exact (os : List Op) : QInv (exec os {}) :=
  exec_qinv os {} init_inv init_qinv (exec_norevive os {} init_inv init_ginv)

/-- From the empty slab, over any run, the live entries of the queue are the documented order. -/
theorem exec_inorder (os : List Op) :
    (execO os {} []).1.queue.filter (valid (execO os {} []).1.slots) = (execO os {} []).2 :=
  exec_order os {} [] init_inv init_qinv rfl (exec_norevive os {} init_inv init_ginv)

/-- From the empty slab, over any run, the baton wakes the oldest armed ticket of the documented order. -/
theorem exec_oldest (os : List Op) :
    (baton (execO os {} []).1).1 = orderWoken (execO os {} []).1.slots (execO os {} []).2 :=
  baton_oldest _ _ (exec_inorder os)

#audit_axioms Vinc.FacadeStandby.exec_ginv
#audit_axioms Vinc.FacadeStandby.alloc_unnamed
#audit_axioms Vinc.FacadeStandby.exec_norevive
#audit_axioms Vinc.FacadeStandby.exec_exact
#audit_axioms Vinc.FacadeStandby.exec_inorder
#audit_axioms Vinc.FacadeStandby.exec_oldest

end Vinc.FacadeStandby
