import Vinc.Axioms
import Vinc.CoreQueue
import Vinc.CoreQueueThm

/-!
# The event queue over a run of calls: order, counters, and the headroom

Over any run of pushes, pops and purges of a ring of any size (`Inv`, kept by `step`):

- the events that leave are the events that entered, in the order they entered: what was popped, followed by what
  is queued, is a subsequence of what was pushed (`Inv.fifo`);
- every drop is counted, and every loss is counted: the pushes are the pops, plus the events a purge took, plus
  `dropped`, plus what is queued (`Inv.balance`); and the unrecoverable pushes are the unrecoverable pops, plus the
  unrecoverable events a purge took, plus the unrecoverable events queued, plus `lost` (`Inv.balance_unrec`), so an
  event the application cannot recover leaves the queue unread only by a purge of its session or by the loss
  `lost` counts, and `lost` grows only when the full queue holds no recoverable event (`push_lost`);
- the headroom: a ring that is not `stalled` for headroom `h`, given a step that pushes at most `h` unrecoverable
  events (and any number of recoverable ones, and no pop), loses nothing: `lost` does not change
  (`pushAll_lost`, `step_no_loss`). The code's `event_queue` is at least twice its `event_headroom`
  (`queue_covers_headroom`), which its `const` assertion states.
-/

namespace Vinc.CoreQueue

/-- How many events the application cannot recover. -/
def nU (l : List E) : Nat := l.countP (fun e => !e.lossy)

theorem len_split (l : List E) : l.length = l.countP (·.lossy) + nU l := by
  induction l with
  | nil => simp [nU]
  | cons e t ih =>
    unfold nU at *
    simp only [List.length_cons, List.countP_cons]
    by_cases h : e.lossy = true <;> simp [h] <;> omega

theorem nU_append (a b : List E) : nU (a ++ b) = nU a + nU b := by
  simp [nU, List.countP_append]

theorem nU_cons (e : E) (t : List E) : nU (e :: t) = nU t + (if e.lossy = false then 1 else 0) := by
  unfold nU
  rw [List.countP_cons]
  by_cases h : e.lossy = true <;> simp [h]

theorem nU_nil : nU [] = 0 := by simp [nU]

theorem nU_single (e : E) : nU [e] = if e.lossy = false then 1 else 0 := by
  rw [nU_cons, nU_nil]; simp

theorem nU_rep {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) : nU q = r.len - r.ll := by
  have := len_split q
  have := h.ll_eq
  have := h.len_eq
  omega

theorem filter_split (p : E → Bool) (k : E → Bool) :
    ∀ l : List E, l.countP p = (l.filter k).countP p + (l.filter (fun e => !k e)).countP p
  | [] => by simp
  | e :: t => by
    have ih := filter_split p k t
    by_cases h : k e = true
    · simp [List.filter_cons, h, List.countP_cons, ih]; omega
    · have h' : k e = false := by simpa using h
      simp [List.filter_cons, h', List.countP_cons, ih]; omega

theorem pushSpec_length {cap : Nat} {q : List E} (ev : E) (hc : 0 < cap) (hq : q.length ≤ cap) :
    (pushSpec cap ev q).length + (if q.length = cap then 1 else 0) = q.length + 1 := by
  unfold pushSpec
  by_cases hf : q.length = cap
  · rw [if_pos hf, if_pos hf]
    by_cases hl : ev.lossy = true
    · simp [hl]
    · simp only [hl, if_false, List.length_append, List.length_singleton]
      cases hq' : evictFirstLossy q with
      | some t => have := evictFirstLossy_length q t hq'; simp; omega
      | none => simp [List.length_eraseIdx]; omega
  · rw [if_neg hf, if_neg hf]; simp

theorem pushSpec_nU {cap : Nat} {q : List E} (ev : E) (hc : 0 < cap) (hq : q.length ≤ cap) :
    nU (pushSpec cap ev q) +
      (if q.length = cap ∧ ev.lossy = false ∧ (∀ x ∈ q, x.lossy = false) then 1 else 0) =
    nU q + (if ev.lossy = false then 1 else 0) := by
  by_cases hf : q.length = cap
  · by_cases hl : ev.lossy = true
    · have hcond : ¬ (q.length = cap ∧ ev.lossy = false ∧ ∀ x ∈ q, x.lossy = false) := fun hh => by
        have := hh.2.1; simp [hl] at this
      rw [if_neg hcond]
      simp [pushSpec, hf, hl]
    · have hl' : ev.lossy = false := by simpa using hl
      cases hq' : evictFirstLossy q with
      | some t =>
        have c1 := evictFirstLossy_length q t hq'
        have c2 := evictFirstLossy_count q t hq'
        have s1 := len_split q
        have s2 := len_split t
        have hn : ¬ (∀ x ∈ q, x.lossy = false) := fun hall =>
          absurd ((evictFirstLossy_none q).2 hall) (by simp [hq'])
        rw [if_neg (show ¬ (q.length = cap ∧ ev.lossy = false ∧ ∀ x ∈ q, x.lossy = false) from
          fun hh => hn hh.2.2)]
        have hps : pushSpec cap ev q = t ++ [ev] := by simp [pushSpec, hf, hl, hq']
        rw [hps, nU_append, nU_single]
        have e1 : (if ev.lossy = false then 1 else 0) = 1 := if_pos hl'
        rw [e1]
        omega
      | none =>
        have hall := (evictFirstLossy_none q).1 hq'
        rw [if_pos (show q.length = cap ∧ ev.lossy = false ∧ ∀ x ∈ q, x.lossy = false from ⟨hf, hl', hall⟩)]
        have s1 := len_split q
        have c0 : q.countP (·.lossy) = 0 := by
          rw [List.countP_eq_zero]; intro a ha; simp [hall a ha]
        have s2 := len_split (q.eraseIdx 0)
        have c1 : (q.eraseIdx 0).countP (·.lossy) = 0 := by
          rw [List.countP_eq_zero]; intro a ha
          simp [hall a ((List.eraseIdx_sublist q 0).subset ha)]
        have hlen : (q.eraseIdx 0).length = q.length - 1 := by simp [List.length_eraseIdx]
        have hps : pushSpec cap ev q = q.eraseIdx 0 ++ [ev] := by simp [pushSpec, hf, hl, hq']
        rw [hps, nU_append, nU_single]
        have e1 : (if ev.lossy = false then 1 else 0) = 1 := if_pos hl'
        rw [e1]
        have := hc
        omega
  · have hcond : ¬ (q.length = cap ∧ ev.lossy = false ∧ ∀ x ∈ q, x.lossy = false) := fun hh => hf hh.1
    rw [if_neg hcond]
    have hps : pushSpec cap ev q = q ++ [ev] := by simp [pushSpec, hf]
    rw [hps, nU_append, nU_single]
    omega

theorem pushSpec_sublist {cap : Nat} (q : List E) (ev : E) : (pushSpec cap ev q).Sublist (q ++ [ev]) := by
  unfold pushSpec
  by_cases hf : q.length = cap
  · rw [if_pos hf]
    by_cases hl : ev.lossy = true
    · rw [if_pos hl]; exact List.sublist_append_left _ _
    · rw [if_neg hl]
      cases hq' : evictFirstLossy q with
      | some t => exact (evictFirstLossy_sublist q t hq').append (List.Sublist.refl _)
      | none => exact (List.eraseIdx_sublist q 0).append (List.Sublist.refl _)
  · rw [if_neg hf]; exact List.Sublist.refl _

/-! ## A run -/

inductive Op where
  | push (ev : E)
  | pop
  | purge (s : Nat)

/-- The ring and, as ghosts, the queue it stands for and what went in, out and away. -/
structure S where
  r : R := {}
  q : List E := []
  pushed : List E := []
  popped : List E := []
  gone : List E := []

def step (cap : Nat) (st : S) : Op → S
  | .push ev => { st with r := push cap ev st.r, q := pushSpec cap ev st.q, pushed := st.pushed ++ [ev] }
  | .pop => { st with r := (pop cap st.r).2, q := st.q.tail, popped := st.popped ++ st.q.take 1 }
  | .purge s => { st with r := purge cap s st.r, q := st.q.filter (keep s),
                          gone := st.gone ++ st.q.filter (fun e => !keep s e) }

structure Inv (cap : Nat) (st : S) : Prop where
  rep : Rep cap st.r st.q
  fifo : (st.popped ++ st.q).Sublist st.pushed
  balance : st.pushed.length = st.popped.length + st.gone.length + st.r.dropped + st.q.length
  balance_unrec : nU st.pushed = nU st.popped + nU st.gone + nU st.q + st.r.lost

theorem inv_init (cap : Nat) (hc : 0 < cap) : Inv cap ({} : S) :=
  ⟨rep_init cap hc, by simp, by simp [R.dropped], by simp [nU]⟩

theorem step_inv {cap : Nat} {st : S} (h : Inv cap st) (op : Op) : Inv cap (step cap st op) := by
  have hr := h.rep
  cases op with
  | push ev =>
    simp only [step]
    refine ⟨push_rep hr ev, ?_, ?_, ?_⟩ <;> dsimp only
    · have s := pushSpec_sublist (cap := cap) st.q ev
      have := h.fifo
      have h2 : (st.popped ++ pushSpec cap ev st.q).Sublist (st.popped ++ (st.q ++ [ev])) :=
        (List.Sublist.refl _).append s
      rw [← List.append_assoc] at h2
      exact h2.trans (this.append (List.Sublist.refl [ev]))
    · have a := push_dropped hr ev
      have b := pushSpec_length (cap := cap) (q := st.q) ev hr.cap_pos hr.len_le
      have := h.balance
      simp only [List.length_append, List.length_singleton]
      omega
    · have a := push_lost hr ev
      have b := pushSpec_nU (cap := cap) (q := st.q) ev hr.cap_pos hr.len_le
      have := h.balance_unrec
      rw [nU_append, a, nU_single]
      omega
  | pop =>
    cases hq : st.q with
    | nil =>
      have hp := pop_empty (hq ▸ hr : Rep cap st.r [])
      have hst : step cap st .pop = st := by
        obtain ⟨r, q, a, b, c⟩ := st
        simp only at hq hp
        subst hq
        simp [step, hp]
      rw [hst]; exact h
    | cons e t =>
      have hp := pop_rep (hq ▸ hr : Rep cap st.r (e :: t))
      obtain ⟨_, hrep, hd, hl⟩ := hp
      simp only [step, hq, List.take_succ_cons, List.take_zero, List.tail_cons]
      refine ⟨hrep, ?_, ?_, ?_⟩
      · have := h.fifo
        rw [hq] at this
        simpa [List.append_assoc] using this
      · have := h.balance
        rw [hq] at this
        simp only [List.length_cons] at this
        simp only [List.length_append, List.length_cons, List.length_nil, hd]
        omega
      · have := h.balance_unrec
        rw [hq, nU_cons] at this
        simp only [nU_append, nU_single, hl]
        omega
  | purge s =>
    simp only [step]
    have hp := purge_rep hr s
    have hc := purge_counts (r := st.r) cap s
    refine ⟨hp, ?_, ?_, ?_⟩
    · have := h.fifo
      have h2 : (st.popped ++ st.q.filter (keep s)).Sublist (st.popped ++ st.q) :=
        (List.Sublist.refl _).append List.filter_sublist
      exact h2.trans this
    · have := h.balance
      have e := filter_split (fun _ => true) (keep s) st.q
      simp only [List.countP_true] at e
      simp only [List.length_append, hc.1]
      omega
    · have := h.balance_unrec
      have e := filter_split (fun e => !e.lossy) (keep s) st.q
      simp only [nU_append, hc.2]
      unfold nU at *
      omega

/-- Over any run, the invariant holds. -/
theorem run_inv {cap : Nat} (hc : 0 < cap) (ops : List Op) : Inv cap (ops.foldl (step cap) ({} : S)) := by
  suffices ∀ (st : S), Inv cap st → Inv cap (ops.foldl (step cap) st) from this _ (inv_init cap hc)
  induction ops with
  | nil => intro st h; exact h
  | cons op t ih => intro st h; exact ih _ (step_inv h op)

/-- Events leave in the order they entered: what was popped, then what is queued, is a subsequence of the pushes. -/
theorem run_fifo {cap : Nat} (hc : 0 < cap) (ops : List Op) :
    let st := ops.foldl (step cap) ({} : S)
    (st.popped ++ st.q).Sublist st.pushed := (run_inv hc ops).fifo

/-- Every drop and every loss is counted. -/
theorem run_counted {cap : Nat} (hc : 0 < cap) (ops : List Op) :
    let st := ops.foldl (step cap) ({} : S)
    st.pushed.length = st.popped.length + st.gone.length + st.r.dropped + st.q.length ∧
    nU st.pushed = nU st.popped + nU st.gone + nU st.q + st.r.lost :=
  ⟨(run_inv hc ops).balance, (run_inv hc ops).balance_unrec⟩

/-! ## The headroom -/

def pushAll (cap : Nat) : List E → R → R
  | [], r => r
  | ev :: t, r => pushAll cap t (push cap ev r)

/-- A step that pushes at most as many unrecoverable events as the places the queue has beyond its own
unrecoverable events loses nothing, whatever recoverable events it pushes. -/
theorem pushAll_lost {cap : Nat} :
    ∀ (evs : List E) {r : R} {q : List E}, Rep cap r q → nU q + nU evs ≤ cap → (pushAll cap evs r).lost = r.lost
  | [], r, q, _, _ => rfl
  | ev :: t, r, q, h, hu => by
    have hl := push_lost h ev
    have hs := pushSpec_nU (cap := cap) (q := q) ev h.cap_pos h.len_le
    have hcond : ¬ (q.length = cap ∧ ev.lossy = false ∧ (∀ x ∈ q, x.lossy = false)) := by
      rintro ⟨hf, hev, hall⟩
      have s := len_split q
      have c0 : q.countP (·.lossy) = 0 := by
        rw [List.countP_eq_zero]; intro a ha; simp [hall a ha]
      rw [nU_cons] at hu
      simp [hev] at hu
      omega
    rw [if_neg hcond] at hl hs
    have hrec := pushAll_lost t (push_rep h ev) (by
      rw [nU_cons] at hu
      omega)
    simp only [pushAll]
    rw [hrec, hl]
    simp

/-- The stall: the queue's unrecoverable events leave less than the headroom. -/
theorem not_stalled_iff {cap h : Nat} {r : R} {q : List E} (hr : Rep cap r q) :
    stalled cap h r = false ↔ nU q + h ≤ cap := by
  rw [nU_rep hr]
  simp [stalled]

/-- The target: if the queue is not stalled and a step pushes at most `h` unrecoverable events, `lost` does not
grow. -/
theorem step_no_loss {cap h : Nat} {r : R} {q : List E} (hr : Rep cap r q) (hs : stalled cap h r = false)
    (evs : List E) (hu : nU evs ≤ h) : (pushAll cap evs r).lost = r.lost := by
  have := (not_stalled_iff hr).1 hs
  exact pushAll_lost evs hr (by omega)

/-- The queue has room for twice the headroom, for any table size. -/
theorem queue_covers_headroom (k : Nat) : 2 * eventHeadroom k ≤ eventQueue k := by
  unfold eventHeadroom eventQueue; omega

/-- Without the headroom the queue can lose: three unrecoverable pushes onto an empty ring of two places. -/
def ue (i : Nat) : E := { id := i, lossy := false, sess := 0, closed := false }

theorem headroom_tight : (pushAll 2 [ue 1, ue 2, ue 3] ({} : R)).lost = 1 := by decide

#audit_axioms Vinc.CoreQueue.headroom_tight
#audit_axioms Vinc.CoreQueue.step_inv
#audit_axioms Vinc.CoreQueue.run_inv
#audit_axioms Vinc.CoreQueue.run_fifo
#audit_axioms Vinc.CoreQueue.run_counted
#audit_axioms Vinc.CoreQueue.pushAll_lost
#audit_axioms Vinc.CoreQueue.step_no_loss
#audit_axioms Vinc.CoreQueue.queue_covers_headroom

end Vinc.CoreQueue
