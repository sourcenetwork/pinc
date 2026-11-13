import Vinc.Axioms
import Vinc.CoreQueue
import Vinc.CoreQueueThm
import Vinc.CoreQueueRun
import Vinc.CoreHeld

/-!
# The held ring: order, the bound, merging, and an unrecoverable event is never evicted

What the model proves about `Held`, for any number of places and any run of pushes and pops (`Inv`, kept by `hstep`;
the cells, head and eviction loop are `Vinc.CoreQueue`'s, so a list `q` stands for what is held, `Rep`):

- a push appends the event; a recoverable event that repeats one held (`E.sess`, the kind and stream) is not held
  again; onto a full ring it gives up the oldest recoverable event, or, when the ring holds none, is refused; both
  count one drop (`hpush_rep`, `hpush_dropped`, with `hSpec`);
- only a recoverable event is ever given up: every unrecoverable event held stays (`hSpec_keeps`); the new event
  is refused only if the ring is full of unrecoverable events, which is what `stalled` reports (`hstalled_iff`,
  `hSpec_refuses`); so a push the endpoint makes only while the ring is not stalled holds an unrecoverable event
  (`hSpec_holds`) and never refuses one (`refused_needs_stall`);
- events leave in the order they entered: what was popped, then what is held, is a subsequence of the pushes
  (`Inv.fifo`); the pushes are the pops, the merges, the drops and what is held (`Inv.balance`); the unrecoverable
  pushes are the unrecoverable pops, the unrecoverable events held and the events refused (`Inv.balance_unrec`),
  and a refusal is a counted drop (`Inv.refused_le`);
- the recoverable events held have distinct kind and stream (`Inv.distinct`).
-/

namespace Vinc.CoreHeld
open Vinc.CoreQueue

/-- What a push does to the held list. -/
def hSpec (cap : Nat) (ev : E) (q : List E) : List E :=
  if ev.lossy && q.any (fun x => x.sess == ev.sess) then q
  else if q.length = cap then
    match evictFirstLossy q with
    | some t => t ++ [ev]
    | none => q
  else q ++ [ev]

theorem merges_iff {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) (ev : E) :
    merges cap ev r = (ev.lossy && q.any (fun x => x.sess == ev.sess)) := by
  unfold merges
  cases hl : ev.lossy
  · simp
  · simp only [Bool.true_and]
    apply Bool.eq_iff_iff.2
    rw [List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨i, hi, hm⟩
      have hi' : i < q.length := by rw [← h.len_eq]; exact List.mem_range.1 hi
      rw [get_eq h i hi'] at hm
      exact ⟨q[i], List.getElem_mem hi', hm⟩
    · rintro ⟨x, hx, hm⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      refine ⟨i, List.mem_range.2 (by rw [h.len_eq]; exact hi), ?_⟩
      rw [get_eq h i hi]
      exact hm

theorem hstalled_iff {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) :
    hstalled cap r = true ↔ (q.length = cap ∧ ∀ x ∈ q, x.lossy = false) := by
  unfold hstalled
  have hl := h.len_eq
  rcases victim_evict h with ⟨hv, hq⟩ | ⟨v, hv, hvic, hl2, hq⟩
  · rw [hv]
    simp only [Option.isNone_none, Bool.and_true, beq_iff_eq]
    constructor
    · intro hh; exact ⟨by omega, (evictFirstLossy_none q).1 hq⟩
    · intro hh; omega
  · rw [hvic]
    simp only [Option.isNone_some, Bool.and_false]
    constructor
    · intro hh; exact absurd hh (by simp)
    · intro hh; have := hh.2 q[v] (List.getElem_mem hv); simp [hl2] at this

theorem hpush_rep {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) (ev : E) :
    Rep cap (hpush cap ev r) (hSpec cap ev q) := by
  have hlen := h.len_eq
  have hm := merges_iff h ev
  unfold hpush hSpec
  rw [hm]
  by_cases hmg : (ev.lossy && q.any (fun x => x.sess == ev.sess)) = true
  · rw [if_pos hmg, if_pos hmg]; exact h
  · rw [if_neg hmg, if_neg hmg]
    by_cases hfull : r.len = cap
    · have hfq : q.length = cap := by omega
      have hr : Rep cap { r with dropped := r.dropped + 1 } q :=
        ⟨h.cap_pos, h.head_lt, h.len_eq, h.len_le, h.cell, h.ll_eq⟩
      have hf1 : ({ r with dropped := r.dropped + 1 } : R).len = cap := hfull
      obtain ⟨e1, e2⟩ := evict_rep hr hf1
      rw [if_pos hfull, if_pos hfq]
      rcases victim_evict h with ⟨hv, hq⟩ | ⟨v, hv, hvic, hl2, hq⟩
      · rw [hv, hq]; exact hr
      · rw [hvic, hq]
        have hh := (e1 _ hq).1
        have h1 := hh.len_eq
        have h2 := hh.len_le
        have h3 := evictFirstLossy_length q _ hq
        have hlt : (evict cap { r with dropped := r.dropped + 1 }).len < cap := by omega
        exact append_rep hh hlt ev
    · have hfq : q.length ≠ cap := by omega
      rw [if_neg hfull, if_neg hfq]
      exact append_rep h (by have := h.len_le; omega) ev

theorem hpush_dropped {cap : Nat} {r : R} {q : List E} (h : Rep cap r q) (ev : E) :
    (hpush cap ev r).dropped =
      r.dropped + (if (ev.lossy && q.any (fun x => x.sess == ev.sess)) = true then 0
                   else if q.length = cap then 1 else 0) := by
  have hlen := h.len_eq
  have hm := merges_iff h ev
  unfold hpush
  rw [hm]
  by_cases hmg : (ev.lossy && q.any (fun x => x.sess == ev.sess)) = true
  · rw [if_pos hmg, if_pos hmg]; rfl
  · rw [if_neg hmg, if_neg hmg]
    by_cases hfull : r.len = cap
    · have hfq : q.length = cap := by omega
      rw [if_pos hfull, if_pos hfq]
      cases hv : victim r cap with
      | none => rfl
      | some v => simp [append, evict]
    · have hfq : q.length ≠ cap := by omega
      rw [if_neg hfull, if_neg hfq]
      simp [append]

/-! ## What a push gives up -/

theorem hSpec_keeps (cap : Nat) (ev : E) (q : List E) : ∀ x ∈ q, x.lossy = false → x ∈ hSpec cap ev q := by
  intro x hx hxl
  unfold hSpec
  by_cases hmg : (ev.lossy && q.any (fun x => x.sess == ev.sess)) = true
  · rw [if_pos hmg]; exact hx
  · rw [if_neg hmg]
    by_cases hf : q.length = cap
    · rw [if_pos hf]
      cases hq : evictFirstLossy q with
      | some t => exact List.mem_append_left _ (evictFirstLossy_keeps q t hq x hx hxl)
      | none => exact hx
    · rw [if_neg hf]; exact List.mem_append_left _ hx

theorem hSpec_sublist (cap : Nat) (ev : E) (q : List E) : (hSpec cap ev q).Sublist (q ++ [ev]) := by
  unfold hSpec
  by_cases hmg : (ev.lossy && q.any (fun x => x.sess == ev.sess)) = true
  · rw [if_pos hmg]; exact List.sublist_append_left _ _
  · rw [if_neg hmg]
    by_cases hf : q.length = cap
    · rw [if_pos hf]
      cases hq : evictFirstLossy q with
      | some t => exact (evictFirstLossy_sublist q t hq).append (List.Sublist.refl _)
      | none => exact List.sublist_append_left _ _
    · rw [if_neg hf]; exact List.Sublist.refl _

/-- The new event is refused only by a ring that is full of events the application cannot recover. -/
theorem hSpec_refuses (cap : Nat) (ev : E) (q : List E) (hne : ev ∉ hSpec cap ev q)
    (hmg : ¬ (ev.lossy && q.any (fun x => x.sess == ev.sess)) = true) :
    q.length = cap ∧ ∀ x ∈ q, x.lossy = false := by
  unfold hSpec at hne
  rw [if_neg hmg] at hne
  by_cases hf : q.length = cap
  · refine ⟨hf, ?_⟩
    rw [if_pos hf] at hne
    cases hq : evictFirstLossy q with
    | some t => rw [hq] at hne; exact absurd (List.mem_append_right _ List.mem_cons_self) hne
    | none => exact (evictFirstLossy_none q).1 hq
  · rw [if_neg hf] at hne
    exact absurd (List.mem_append_right _ List.mem_cons_self) hne

/-- A push made while the ring is not stalled holds an unrecoverable event. -/
theorem hSpec_holds (cap : Nat) (ev : E) (q : List E) (hev : ev.lossy = false)
    (hs : ¬ (q.length = cap ∧ ∀ x ∈ q, x.lossy = false)) : ev ∈ hSpec cap ev q := by
  by_cases hin : ev ∈ hSpec cap ev q
  · exact hin
  have hne := hin
  have hmg : ¬ (ev.lossy && q.any (fun x => x.sess == ev.sess)) = true := by simp [hev]
  exact absurd (hSpec_refuses cap ev q hne hmg) hs

/-! ## A run -/

inductive Op where
  | push (ev : E)
  | pop

structure S where
  r : R := {}
  q : List E := []
  pushed : List E := []
  popped : List E := []
  merged : List E := []
  refused : List E := []

def merged (cap : Nat) (ev : E) (q : List E) : Bool := ev.lossy && q.any (fun x => x.sess == ev.sess)

def refusedBy (cap : Nat) (ev : E) (q : List E) : Bool :=
  !merged cap ev q && q.length == cap && (evictFirstLossy q).isNone

def hstep (cap : Nat) (st : S) : Op → S
  | .push ev =>
    { st with
      r := hpush cap ev st.r
      q := hSpec cap ev st.q
      pushed := st.pushed ++ [ev]
      merged := if merged cap ev st.q then st.merged ++ [ev] else st.merged
      refused := if refusedBy cap ev st.q then st.refused ++ [ev] else st.refused }
  | .pop => { st with r := (pop cap st.r).2, q := st.q.tail, popped := st.popped ++ st.q.take 1 }

structure Inv (cap : Nat) (st : S) : Prop where
  rep : Rep cap st.r st.q
  fifo : (st.popped ++ st.q).Sublist st.pushed
  balance : st.pushed.length = st.popped.length + st.merged.length + st.r.dropped + st.q.length
  balance_unrec : nU st.pushed = nU st.popped + nU st.q + nU st.refused
  refused_le : st.refused.length ≤ st.r.dropped
  distinct : st.q.Pairwise (fun a b => a.lossy = true → b.lossy = true → a.sess ≠ b.sess)
  merged_lossy : ∀ x ∈ st.merged, x.lossy = true

theorem inv_init (cap : Nat) (hc : 0 < cap) : Inv cap ({} : S) :=
  ⟨rep_init cap hc, by simp, by simp [R.dropped], by simp [nU], by simp [R.dropped], by simp, by simp⟩

theorem evict_nU {q t : List E} (hq : evictFirstLossy q = some t) : nU t = nU q := by
  have c1 := evictFirstLossy_length q t hq
  have c2 := evictFirstLossy_count q t hq
  have s1 := len_split q
  have s2 := len_split t
  omega

theorem hSpec_cases (cap : Nat) (ev : E) (q : List E) :
    (merged cap ev q = true ∧ hSpec cap ev q = q ∧ refusedBy cap ev q = false) ∨
    (merged cap ev q = false ∧ q.length = cap ∧ evictFirstLossy q = none ∧ hSpec cap ev q = q ∧
      refusedBy cap ev q = true) ∨
    (∃ t, merged cap ev q = false ∧ q.length = cap ∧ evictFirstLossy q = some t ∧
      hSpec cap ev q = t ++ [ev] ∧ refusedBy cap ev q = false) ∨
    (merged cap ev q = false ∧ q.length ≠ cap ∧ hSpec cap ev q = q ++ [ev] ∧ refusedBy cap ev q = false) := by
  by_cases hm : merged cap ev q = true
  · left
    have hm' : (ev.lossy && q.any (fun x => x.sess == ev.sess)) = true := hm
    refine ⟨hm, ?_, ?_⟩
    · unfold hSpec; rw [if_pos hm']
    · simp [refusedBy, hm]
  · have hm0 : merged cap ev q = false := by simpa using hm
    have hm' : ¬ (ev.lossy && q.any (fun x => x.sess == ev.sess)) = true := hm
    right
    by_cases hf : q.length = cap
    · cases hq : evictFirstLossy q with
      | none =>
        left
        refine ⟨hm0, hf, rfl, ?_, ?_⟩
        · unfold hSpec; rw [if_neg hm', if_pos hf, hq]
        · simp [refusedBy, hm0, hf, hq]
      | some t =>
        right; left
        refine ⟨t, hm0, hf, rfl, ?_, ?_⟩
        · unfold hSpec; rw [if_neg hm', if_pos hf, hq]
        · simp [refusedBy, hm0, hf, hq]
    · right; right
      refine ⟨hm0, hf, ?_, ?_⟩
      · unfold hSpec; rw [if_neg hm', if_neg hf]
      · simp [refusedBy, hm0, hf]

theorem pw_snoc {l : List E} {ev : E}
    (h : l.Pairwise (fun a b => a.lossy = true → b.lossy = true → a.sess ≠ b.sess))
    (hn : ∀ x ∈ l, x.lossy = true → ev.lossy = true → x.sess ≠ ev.sess) :
    (l ++ [ev]).Pairwise (fun a b => a.lossy = true → b.lossy = true → a.sess ≠ b.sess) := by
  rw [List.pairwise_append]
  refine ⟨h, by simp, ?_⟩
  intro a ha b hb
  simp at hb
  subst hb
  exact hn a ha

theorem not_merged_ne {cap : Nat} {ev : E} {q : List E} (hm : merged cap ev q = false) :
    ∀ x ∈ q, x.lossy = true → ev.lossy = true → x.sess ≠ ev.sess := by
  intro x hx _ hev hs
  have : merged cap ev q = true := by
    unfold merged
    simp only [Bool.and_eq_true, hev, true_and, List.any_eq_true]
    exact ⟨x, hx, by simp [hs]⟩
  rw [hm] at this
  exact absurd this (by simp)

theorem merged_false {cap : Nat} {ev : E} {q : List E} (hm : merged cap ev q = false) :
    ¬ (ev.lossy && q.any (fun x => x.sess == ev.sess)) = true := by
  intro hh
  have : merged cap ev q = true := hh
  rw [hm] at this
  exact absurd this (by simp)

theorem hstep_push_inv {cap : Nat} {st : S} (h : Inv cap st) (ev : E) : Inv cap (hstep cap st (.push ev)) := by
  have hr := h.rep
  have hd := hpush_dropped hr ev
  have hlen := hr.len_eq
  have hl := hr.len_le
  have hrep := hpush_rep hr ev
  have hfifo : (st.popped ++ hSpec cap ev st.q).Sublist (st.pushed ++ [ev]) := by
    have s := hSpec_sublist (cap := cap) ev st.q
    have h2 : (st.popped ++ hSpec cap ev st.q).Sublist (st.popped ++ (st.q ++ [ev])) :=
      (List.Sublist.refl _).append s
    rw [← List.append_assoc] at h2
    exact h2.trans (h.fifo.append (List.Sublist.refl [ev]))
  have hnu1 := nU_single ev
  have hnu2 := nU_append st.pushed [ev]
  have hbal := h.balance
  have hbu := h.balance_unrec
  have hrl := h.refused_le
  rcases hSpec_cases cap ev st.q with ⟨hm1, hs1, hr1⟩ | ⟨hm1, hf, hq, hs1, hr1⟩ |
      ⟨t, hm1, hf, hq, hs1, hr1⟩ | ⟨hm1, hf, hs1, hr1⟩
  · -- a repeat of a recoverable event merges
    have hc : (ev.lossy && st.q.any (fun x => x.sess == ev.sess)) = true := hm1
    have hev : ev.lossy = true := by simp at hc; exact hc.1
    rw [if_pos hc] at hd
    rw [hs1] at hrep hfifo
    simp only [hev, Bool.true_eq_false, if_false] at hnu1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hstep, hs1]; exact hrep
    · simp only [hstep, hs1]; exact hfifo
    · simp only [hstep, hs1, hm1, hr1, if_true, Bool.false_eq_true, if_false, List.length_append,
        List.length_singleton]
      omega
    · simp only [hstep, hs1, hm1, hr1, if_true, Bool.false_eq_true, if_false]
      rw [hnu2, hnu1]; omega
    · simp only [hstep, hs1, hm1, hr1, if_true, Bool.false_eq_true, if_false]; omega
    · simp only [hstep, hs1]; exact h.distinct
    · simp only [hstep, hm1, if_true]
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h.merged_lossy x hx
      · simp at hx; rw [hx]; exact hev
  · -- a full ring with nothing recoverable refuses the event
    have hc := merged_false hm1
    rw [if_neg hc, if_pos hf] at hd
    rw [hs1] at hrep hfifo
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hstep, hs1]; exact hrep
    · simp only [hstep, hs1]; exact hfifo
    · simp only [hstep, hs1, hm1, hr1, if_true, Bool.false_eq_true, if_false, List.length_append,
        List.length_singleton]
      omega
    · simp only [hstep, hs1, hm1, hr1, if_true, Bool.false_eq_true, if_false]
      rw [hnu2, nU_append]; omega
    · simp only [hstep, hs1, hm1, hr1, if_true, Bool.false_eq_true, if_false, List.length_append,
        List.length_singleton]
      omega
    · simp only [hstep, hs1]; exact h.distinct
    · simp only [hstep, hm1, Bool.false_eq_true, if_false]; exact h.merged_lossy
  · -- a full ring gives up its oldest recoverable event
    have hc := merged_false hm1
    rw [if_neg hc, if_pos hf] at hd
    have hnt := evict_nU hq
    have hlt := evictFirstLossy_length st.q t hq
    rw [hs1] at hrep hfifo
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hstep, hs1]; exact hrep
    · simp only [hstep, hs1]; exact hfifo
    · simp only [hstep, hs1, hm1, hr1, Bool.false_eq_true, if_false, List.length_append, List.length_singleton]
      omega
    · simp only [hstep, hs1, hm1, hr1, Bool.false_eq_true, if_false]
      rw [hnu2, nU_append]; omega
    · simp only [hstep, hs1, hm1, hr1, Bool.false_eq_true, if_false]; omega
    · simp only [hstep, hs1]
      exact pw_snoc (List.Pairwise.sublist (evictFirstLossy_sublist st.q t hq) h.distinct)
        (fun x hx => not_merged_ne hm1 x ((evictFirstLossy_sublist st.q t hq).subset hx))
    · simp only [hstep, hm1, Bool.false_eq_true, if_false]; exact h.merged_lossy
  · -- room: the event is held
    have hc := merged_false hm1
    rw [if_neg hc, if_neg hf] at hd
    rw [hs1] at hrep hfifo
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hstep, hs1]; exact hrep
    · simp only [hstep, hs1]; exact hfifo
    · simp only [hstep, hs1, hm1, hr1, Bool.false_eq_true, if_false, List.length_append, List.length_singleton]
      omega
    · simp only [hstep, hs1, hm1, hr1, Bool.false_eq_true, if_false]
      rw [hnu2, nU_append]; omega
    · simp only [hstep, hs1, hm1, hr1, Bool.false_eq_true, if_false]; omega
    · simp only [hstep, hs1]
      exact pw_snoc h.distinct (fun x hx => not_merged_ne hm1 x hx)
    · simp only [hstep, hm1, Bool.false_eq_true, if_false]; exact h.merged_lossy

theorem hstep_inv {cap : Nat} {st : S} (h : Inv cap st) (op : Op) : Inv cap (hstep cap st op) := by
  cases op with
  | push ev => exact hstep_push_inv h ev
  | pop =>
    have hr := h.rep
    cases hq : st.q with
    | nil =>
      have hp := pop_empty (hq ▸ hr : Rep cap st.r [])
      have hst : hstep cap st .pop = st := by
        obtain ⟨r, q, a, b, c, d⟩ := st
        simp only at hq hp
        subst hq
        simp [hstep, hp]
      rw [hst]; exact h
    | cons e t =>
      have hp := pop_rep (hq ▸ hr : Rep cap st.r (e :: t))
      obtain ⟨_, hrep, hd, hl⟩ := hp
      have hbal := h.balance
      have hbu := h.balance_unrec
      have hfifo := h.fifo
      have hdis := h.distinct
      have hrl := h.refused_le
      rw [hq] at hbal hbu hfifo hdis
      simp only [List.length_cons] at hbal
      rw [nU_cons] at hbu
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [hstep, hq, List.tail_cons]; exact hrep
      · simp only [hstep, hq, List.take_succ_cons, List.take_zero, List.tail_cons]
        simpa [List.append_assoc] using hfifo
      · simp only [hstep, hq, List.take_succ_cons, List.take_zero, List.tail_cons, List.length_append,
          List.length_singleton, List.length_nil, hd]
        omega
      · simp only [hstep, hq, List.take_succ_cons, List.take_zero, List.tail_cons]
        rw [nU_append, nU_single]
        have := nU_single e
        omega
      · simp only [hstep, hd]; omega
      · simp only [hstep, hq, List.tail_cons]; exact (List.pairwise_cons.1 hdis).2
      · simp only [hstep]; exact h.merged_lossy

/-- The refused events: a refusal is a counted drop of an event the ring was full of unrecoverable events for. -/
theorem refused_needs_stall {cap : Nat} {st : S} (h : Inv cap st) (ev : E)
    (hs : ¬ (st.q.length = cap ∧ ∀ x ∈ st.q, x.lossy = false)) :
    (hstep cap st (.push ev)).refused = st.refused := by
  simp only [hstep]
  have : refusedBy cap ev st.q = false := by
    unfold refusedBy
    by_cases hm : merged cap ev st.q = true
    · simp [hm]
    · by_cases hf : st.q.length = cap
      · cases hq : evictFirstLossy st.q with
        | none => exact absurd ⟨hf, (evictFirstLossy_none st.q).1 hq⟩ hs
        | some t => simp [hq]
      · simp [hf]
  rw [this]; simp

/-- Over any run, the invariant holds. -/
theorem run_inv {cap : Nat} (hc : 0 < cap) (ops : List Op) : Inv cap (ops.foldl (hstep cap) ({} : S)) := by
  suffices ∀ (st : S), Inv cap st → Inv cap (ops.foldl (hstep cap) st) from this _ (inv_init cap hc)
  induction ops with
  | nil => intro st h; exact h
  | cons op t ih => intro st h; exact ih _ (hstep_inv h op)

#audit_axioms Vinc.CoreHeld.hpush_rep
#audit_axioms Vinc.CoreHeld.hpush_dropped
#audit_axioms Vinc.CoreHeld.hstalled_iff
#audit_axioms Vinc.CoreHeld.hSpec_keeps
#audit_axioms Vinc.CoreHeld.hSpec_refuses
#audit_axioms Vinc.CoreHeld.hSpec_holds
#audit_axioms Vinc.CoreHeld.hstep_inv
#audit_axioms Vinc.CoreHeld.refused_needs_stall
#audit_axioms Vinc.CoreHeld.run_inv

end Vinc.CoreHeld
