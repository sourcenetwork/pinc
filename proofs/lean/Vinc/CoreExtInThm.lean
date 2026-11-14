import Vinc.Axioms
import Vinc.CoreExtIn

/-!
# The extension ring: the bound, the body limit, order, and which frame goes

What the model proves about `ExtRing`, for any number of places and any run of puts and takes (`Inv`, kept by
`step`):

- the ring never grows: at most `cap` frames, the head stays below `cap` (`eput_len`, `eput_head`, `Inv.len_le`);
- a body longer than `mx` is never stored: the put changes nothing and returns `None` (`eput_big`, `eput_ok_iff`),
  and every frame held is short enough (`eput_short`, `Inv.short`);
- the rule of a put: onto a ring with room the frame is appended and the put returns `some 0`; onto a full ring the
  oldest frame goes, the frame is appended and the put returns `some 1`, so the newest frame is always the last one
  held (`eput_room`, `eput_full`, `eput_last`); the evicted frame is never the one just put, and no frame but the
  oldest is lost (`eput_full`);
- the rule of a take: an empty ring gives nothing; a frame longer than the buffer changes nothing and reports its
  length; otherwise the oldest frame goes (`etake_empty`, `etake_stay`, `etake_ok`);
- frames leave in the order they arrived: what was taken, followed by what is held, is a subsequence of the frames
  kept, in order (`Inv.fifo`); every frame kept is taken, dropped by a full ring or held (`Inv.balance`), where
  `dropped` is the sum of what the puts returned; and every frame lost is counted: what the endpoint adds to its
  count (the put's return, or 1 for a refused body) is the frames dropped plus the bodies refused (`Inv.counted`).
-/

namespace Vinc.CoreExtIn

theorem eput_big {cap mx : Nat} {x : X} {f : F} (h : mx < f.len) : eput cap mx x f = (none, x) := by
  simp [eput, h]

theorem eput_ok_iff (cap mx : Nat) (x : X) (f : F) : (eput cap mx x f).1.isSome = decide (f.len ≤ mx) := by
  unfold eput
  by_cases h : f.len ≤ mx
  · simp [h, Nat.not_lt.2 h]
  · simp [h, Nat.lt_of_not_le h]

theorem eput_room {cap mx : Nat} {x : X} {f : F} (h : f.len ≤ mx) (hr : x.q.length ≠ cap) :
    eput cap mx x f = (some 0, { head := x.head, q := x.q ++ [f] }) := by
  simp [eput, Nat.not_lt.2 h, hr]

theorem eput_full {cap mx : Nat} {x : X} {f : F} (h : f.len ≤ mx) (hr : x.q.length = cap) :
    eput cap mx x f = (some 1, { head := (x.head + 1) % cap, q := x.q.tail ++ [f] }) := by
  simp [eput, Nat.not_lt.2 h, hr]

theorem eput_last {cap mx : Nat} {x : X} {f : F} (h : f.len ≤ mx) :
    (eput cap mx x f).2.q.getLast? = some f := by
  by_cases hr : x.q.length = cap
  · rw [eput_full h hr]; simp
  · rw [eput_room h hr]; simp

theorem eput_len {cap mx : Nat} {x : X} {f : F} (hc : 0 < cap) (h : x.q.length ≤ cap) :
    (eput cap mx x f).2.q.length ≤ cap := by
  by_cases hf : f.len ≤ mx
  · by_cases hr : x.q.length = cap
    · rw [eput_full hf hr]; simp; omega
    · rw [eput_room hf hr]; simp; omega
  · rw [eput_big (Nat.lt_of_not_le hf)]; exact h

theorem eput_head {cap mx : Nat} {x : X} {f : F} (hc : 0 < cap) (h : x.head < cap) :
    (eput cap mx x f).2.head < cap := by
  by_cases hf : f.len ≤ mx
  · by_cases hr : x.q.length = cap
    · rw [eput_full hf hr]; exact Nat.mod_lt _ hc
    · rw [eput_room hf hr]; exact h
  · rw [eput_big (Nat.lt_of_not_le hf)]; exact h

theorem eput_short {cap mx : Nat} {x : X} {f : F} (h : ∀ g ∈ x.q, g.len ≤ mx) :
    ∀ g ∈ (eput cap mx x f).2.q, g.len ≤ mx := by
  by_cases hf : f.len ≤ mx
  · intro g hg
    by_cases hr : x.q.length = cap
    · rw [eput_full hf hr] at hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact h g (List.mem_of_mem_tail hg)
      · exact hf
    · rw [eput_room hf hr] at hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact h g hg
      · exact hf
  · rw [eput_big (Nat.lt_of_not_le hf)]; exact h

theorem etake_empty (cap oc : Nat) (x : X) (h : x.q = []) : etake cap oc x = (.none, x) := by
  simp [etake, h]

theorem etake_stay {cap oc : Nat} {x : X} {f : F} {_t : List F} (h : x.q = f :: _t) (hl : oc < f.len) :
    etake cap oc x = (.err f.len, x) := by
  simp [etake, h, hl]

theorem etake_ok {cap oc : Nat} {x : X} {f : F} {t : List F} (h : x.q = f :: t) (hl : f.len ≤ oc) :
    etake cap oc x = (.ok f, { head := (x.head + 1) % cap, q := t }) := by
  simp [etake, h, Nat.not_lt.2 hl]

/-! ## Runs -/

inductive Op where
  | put (f : F)
  | take (oc : Nat)

/-- A run: the ring, the frames kept and taken, what the puts returned as given up (`dropped`), the bodies refused (a
ghost), and what the endpoint adds to its count of frames lost (`lost`: the put's return, or 1 for a refused body). -/
structure S where
  x : X := {}
  acc : List F := []
  taken : List F := []
  dropped : Nat := 0
  refused : Nat := 0
  lost : Nat := 0

def step (cap mx : Nat) : Op → S → S
  | .put f, s =>
    if f.len ≤ mx then
      { s with x := (eput cap mx s.x f).2, acc := s.acc ++ [f],
               dropped := s.dropped + (eput cap mx s.x f).1.getD 0, lost := s.lost + (eput cap mx s.x f).1.getD 1 }
    else { s with refused := s.refused + 1, lost := s.lost + (eput cap mx s.x f).1.getD 1 }
  | .take oc, s =>
    match s.x.q with
    | [] => s
    | f :: _ =>
      if f.len ≤ oc then { s with x := (etake cap oc s.x).2, taken := s.taken ++ [f] } else s

def run (cap mx : Nat) (s : S) : List Op → S
  | [] => s
  | o :: os => run cap mx (step cap mx o s) os

structure Inv (cap mx : Nat) (s : S) : Prop where
  len_le : s.x.q.length ≤ cap
  head_lt : s.x.head < cap
  short : ∀ g ∈ s.x.q, g.len ≤ mx
  fifo : (s.taken ++ s.x.q).Sublist s.acc
  balance : s.acc.length = s.taken.length + s.dropped + s.x.q.length
  counted : s.lost = s.dropped + s.refused

theorem inv_init (cap mx : Nat) (hc : 0 < cap) : Inv cap mx ({} : S) :=
  ⟨by simp, hc, by simp, by simp, by simp, rfl⟩

theorem inv_step {cap mx : Nat} (hc : 0 < cap) {s : S} (h : Inv cap mx s) (o : Op) : Inv cap mx (step cap mx o s) := by
  cases o with
  | put f =>
    dsimp only [step]
    by_cases hf : f.len ≤ mx
    · simp only [hf, ↓reduceIte]
      by_cases hr : s.x.q.length = cap
      · have e := eput_full (cap := cap) (x := s.x) hf hr
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e]; simp; omega
        · simp only [e]; exact Nat.mod_lt _ hc
        · have := eput_short (cap := cap) (f := f) h.short
          exact this
        · simp only [e]
          have h1 : (s.taken ++ s.x.q.tail).Sublist (s.taken ++ s.x.q) :=
            List.Sublist.append_left (List.tail_sublist _) _
          have h2 := (h1.trans h.fifo).append (List.Sublist.refl [f])
          simpa [List.append_assoc] using h2
        · simp only [e]; simp
          have := h.balance
          have hl : s.x.q.tail.length = s.x.q.length - 1 := List.length_tail
          have : 0 < s.x.q.length := by omega
          omega
        · simp only [e]; simp
          have := h.counted
          omega
      · have e := eput_room (cap := cap) (x := s.x) hf hr
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [e]; simp; have := h.len_le; omega
        · simp only [e]; exact h.head_lt
        · exact eput_short (cap := cap) (f := f) h.short
        · simp only [e]
          have h2 := h.fifo.append (List.Sublist.refl [f])
          simpa [List.append_assoc] using h2
        · simp only [e]; simp
          have := h.balance
          omega
        · simp only [e]; simp
          have := h.counted
          omega
    · simp only [hf, ↓reduceIte]
      have e := eput_big (cap := cap) (x := s.x) (Nat.lt_of_not_le hf)
      refine ⟨h.len_le, h.head_lt, h.short, h.fifo, h.balance, ?_⟩
      simp only [e]; simp
      have := h.counted
      omega
  | take oc =>
    dsimp only [step]
    cases hq : s.x.q with
    | nil => exact h
    | cons f t =>
      simp only []
      by_cases hl : f.len ≤ oc
      · simp only [hl, ↓reduceIte]
        have e := etake_ok (cap := cap) hq hl
        refine ⟨?_, ?_, ?_, ?_, ?_, h.counted⟩
        · simp only [e]; have := h.len_le; rw [hq] at this; simp at this ⊢; omega
        · simp only [e]; exact Nat.mod_lt _ hc
        · simp only [e]; intro g hg; exact h.short g (by rw [hq]; exact List.mem_cons_of_mem _ hg)
        · simp only [e]
          have := h.fifo
          rw [hq] at this
          simpa using this
        · simp only [e]
          have := h.balance
          rw [hq] at this
          simp at this ⊢
          omega
      · simp only [hl, ↓reduceIte]; exact h

theorem inv_run {cap mx : Nat} (hc : 0 < cap) (s : S) (h : Inv cap mx s) (os : List Op) :
    Inv cap mx (run cap mx s os) := by
  induction os generalizing s with
  | nil => exact h
  | cons o os ih => exact ih _ (inv_step hc h o)

theorem run_inv (cap mx : Nat) (hc : 0 < cap) (os : List Op) : Inv cap mx (run cap mx {} os) :=
  inv_run hc _ (inv_init cap mx hc) os

#audit_axioms Vinc.CoreExtIn.eput_big
#audit_axioms Vinc.CoreExtIn.eput_ok_iff
#audit_axioms Vinc.CoreExtIn.eput_room
#audit_axioms Vinc.CoreExtIn.eput_full
#audit_axioms Vinc.CoreExtIn.eput_last
#audit_axioms Vinc.CoreExtIn.eput_len
#audit_axioms Vinc.CoreExtIn.eput_head
#audit_axioms Vinc.CoreExtIn.eput_short
#audit_axioms Vinc.CoreExtIn.etake_empty
#audit_axioms Vinc.CoreExtIn.etake_stay
#audit_axioms Vinc.CoreExtIn.etake_ok
#audit_axioms Vinc.CoreExtIn.run_inv

end Vinc.CoreExtIn
