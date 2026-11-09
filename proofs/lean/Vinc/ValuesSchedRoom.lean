import Vinc.Axioms
import Vinc.ValuesSchedPart

/-!
# Exact accounting of a run of pushes from the length of the result

A push never shortens a list, so when the list a run of pushes ends with is below capacity, every push of the run was
on a list with room and none widened (`Wid`). This turns the room condition of the exact accounting into a single fact
about the result: `foldl_push_mult_room`, `foldl_pushFront_mult_room`, `retainMissing_mult_room`, and for the
head/tail cut of a steal `ssNW_of_room`. `ValuesSchedExact` builds the run-wide exact partition on them.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Vinc.ValuesSched

theorem push_length_ge (n : Nat) (l : List Span) (s : Span) : l.length ≤ (push n l s).length := by
  rcases list_snoc l with rfl | ⟨ys, last, rfl⟩
  · rw [push_nil]; split <;> simp
  · rw [push_snoc]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_singleton]
    repeat' split
    all_goals simp

theorem pushFront_length_ge (n : Nat) (l : List Span) (s : Span) : l.length ≤ (pushFront n l s).length := by
  unfold pushFront
  split
  · exact Nat.le_refl _
  · split
    · cases l <;> simp
    · simp

theorem foldl_push_length_ge (n : Nat) (ps : List Span) : ∀ l : List Span, l.length ≤ (ps.foldl (push n) l).length := by
  induction ps with
  | nil => intro l; exact Nat.le_refl _
  | cons p t ih => intro l; exact Nat.le_trans (push_length_ge n l p) (ih _)

theorem foldl_pushFront_length_ge (n : Nat) (ps : List Span) :
    ∀ l : List Span, l.length ≤ (ps.foldl (pushFront n) l).length := by
  induction ps with
  | nil => intro l; exact Nat.le_refl _
  | cons p t ih => intro l; exact Nat.le_trans (pushFront_length_ge n l p) (ih _)

/-- A run of pushes that ends below capacity added each span's bytes once, whatever else the list holds
(the spans overlap neither the list nor each other). -/
theorem foldl_push_mult_room {n : Nat} (ps : List Span) :
    ∀ {l : List Span}, (ps.foldl (push n) l).length < n → (∀ x, mult l x + mult ps x ≤ 1) →
      ∀ x, mult (ps.foldl (push n) l) x = mult l x + mult ps x := by
  induction ps with
  | nil => intro l _ _ x; simp [mult]
  | cons p t ih =>
    intro l hroom hd x
    simp only [List.foldl_cons] at hroom ⊢
    have hl : l.length < n :=
      Nat.lt_of_le_of_lt (Nat.le_trans (push_length_ge n l p) (foldl_push_length_ge n t _)) hroom
    have hdp : ∀ y, p.Mem y → mult l y = 0 := by
      intro y hy
      have := hd y
      simp only [mult, hy, if_true] at this
      omega
    have hpm : ∀ y, mult (push n l p) y = mult l y + (if p.Mem y then 1 else 0) := push_mult hl p hdp
    rw [ih hroom (fun y => by rw [hpm y]; have := hd y; simp only [mult] at this; omega) x, hpm x]
    simp only [mult]; omega

/-- The `push_front` run of an eviction that ends below capacity: the queue gains the share's bytes. -/
theorem foldl_pushFront_mult_room {n : Nat} (r : List Span) :
    ∀ {q : List Span}, (r.foldl (pushFront n) q).length < n →
      ∀ x, mult (r.foldl (pushFront n) q) x = mult q x + mult r x := by
  induction r with
  | nil => intro q _ x; simp [mult]
  | cons p t ih =>
    intro q hroom x
    simp only [List.foldl_cons] at hroom ⊢
    have hl : q.length < n :=
      Nat.lt_of_le_of_lt (Nat.le_trans (pushFront_length_ge n q p) (foldl_pushFront_length_ge n t _)) hroom
    rw [ih hroom x, pushFront_mult_of_room hl p x]
    simp only [mult]; omega

theorem evictQueue_mult_room {n : Nat} (q miss : List Span) (h : (evictQueue n q miss).length < n) (x : Nat) :
    mult (evictQueue n q miss) x = mult q x + mult miss x := by
  unfold evictQueue at h ⊢
  rw [foldl_pushFront_mult_room miss.reverse h x, mult_reverse]

theorem rm_aux_length_ge (st : Store) (n : Nat) (l : List Span) :
    ∀ (acc : List Span), acc.length ≤ (l.foldl (fun out s => (holesOf st s).foldl (push n) out) acc).length := by
  induction l with
  | nil => intro acc; exact Nat.le_refl _
  | cons s t ih => intro acc; exact Nat.le_trans (foldl_push_length_ge n _ acc) (ih _)

theorem rm_aux_mult_room (st : Store) {n : Nat} (l : List Span) :
    ∀ {acc : List Span}, (l.foldl (fun out s => (holesOf st s).foldl (push n) out) acc).length < n →
      (∀ x, mult acc x + (if st.V x then 0 else mult l x) ≤ 1) →
      ∀ x, mult (l.foldl (fun out s => (holesOf st s).foldl (push n) out) acc) x =
        mult acc x + (if st.V x then 0 else mult l x) := by
  induction l with
  | nil => intro acc _ _ x; simp [mult]
  | cons s t ih =>
    intro acc hroom hd x
    simp only [List.foldl_cons] at hroom ⊢
    have hdisj : ∀ y, mult acc y + mult (holesOf st s) y ≤ 1 := by
      intro y
      have := hd y
      rw [holesOf_mult]
      simp only [mult] at this
      by_cases hv : st.V y = true <;> by_cases hm : s.Mem y <;> simp [hv, hm] at this ⊢ <;> omega
    have hl1 : ((holesOf st s).foldl (push n) acc).length < n :=
      Nat.lt_of_le_of_lt (rm_aux_length_ge st n t _) hroom
    have hm1 := foldl_push_mult_room (n := n) (holesOf st s) (l := acc) hl1 hdisj
    rw [ih (acc := (holesOf st s).foldl (push n) acc) hroom ?_ x, hm1 x, holesOf_mult]
    · simp only [mult]
      by_cases hv : st.V x = true <;> by_cases hm : s.Mem x <;> simp [hv, hm] <;> omega
    · intro y
      rw [hm1 y, holesOf_mult]
      have := hd y
      simp only [mult] at this
      by_cases hv : st.V y = true <;> by_cases hm : s.Mem y <;> simp [hv, hm] at this ⊢ <;> omega

/-- `retain_missing` keeps exactly the unverified bytes, each once, when its result is below capacity. -/
theorem retainMissing_mult_room (st : Store) {n : Nat} (l : List Span) (hroom : (retainMissing st n l).length < n)
    (hd : ∀ x, mult l x ≤ 1) (x : Nat) :
    mult (retainMissing st n l) x = if st.V x then 0 else mult l x := by
  have := rm_aux_mult_room (n := n) st l (acc := []) (by simpa [retainMissing] using hroom)
    (fun y => by simp [mult]; have := hd y; split <;> omega) x
  simpa [retainMissing, mult] using this

theorem stealSplit_length_ge (n keep : Nat) :
    ∀ (l : List Span) acc (head tail : List Span),
      head.length ≤ (stealSplit n keep acc l head tail).1.length ∧
      tail.length ≤ (stealSplit n keep acc l head tail).2.length := by
  intro l
  induction l with
  | nil => intro acc head tail; unfold stealSplit; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons s t ih =>
    intro acc head tail
    unfold stealSplit
    by_cases h1 : keep ≤ acc
    · rw [if_pos h1]
      have := ih (acc + s.len) head (push n tail s)
      exact ⟨this.1, Nat.le_trans (push_length_ge n tail s) this.2⟩
    · rw [if_neg h1]
      by_cases h2 : acc + s.len ≤ keep
      · rw [if_pos h2]
        have := ih (acc + s.len) (push n head s) tail
        exact ⟨Nat.le_trans (push_length_ge n head s) this.1, this.2⟩
      · rw [if_neg h2]
        have := ih (acc + s.len) (push n head ⟨s.off, keep - acc⟩) (push n tail ⟨s.off + (keep - acc), s.len - (keep - acc)⟩)
        exact ⟨Nat.le_trans (push_length_ge n head _) this.1, Nat.le_trans (push_length_ge n tail _) this.2⟩

/-- A cut of a steal whose head and tail end below capacity never widened a list. -/
theorem ssNW_of_room {n : Nat} (keep : Nat) :
    ∀ (l : List Span) acc (head tail : List Span),
      (stealSplit n keep acc l head tail).1.length < n → (stealSplit n keep acc l head tail).2.length < n →
      ssNW n keep acc l head tail := by
  intro l
  induction l with
  | nil => intro acc head tail _ _; trivial
  | cons s t ih =>
    intro acc head tail h1 h2
    unfold stealSplit at h1 h2
    unfold ssNW
    by_cases c1 : keep ≤ acc
    · rw [if_pos c1] at h1 h2
      rw [if_pos c1]
      have g := stealSplit_length_ge n keep t (acc + s.len) head (push n tail s)
      exact ⟨not_wid_of_room (Nat.lt_of_le_of_lt (Nat.le_trans (push_length_ge n tail s) g.2) h2) s, ih _ _ _ h1 h2⟩
    · rw [if_neg c1] at h1 h2
      rw [if_neg c1]
      by_cases c2 : acc + s.len ≤ keep
      · rw [if_pos c2] at h1 h2
        rw [if_pos c2]
        have g := stealSplit_length_ge n keep t (acc + s.len) (push n head s) tail
        exact ⟨not_wid_of_room (Nat.lt_of_le_of_lt (Nat.le_trans (push_length_ge n head s) g.1) h1) s, ih _ _ _ h1 h2⟩
      · rw [if_neg c2] at h1 h2
        rw [if_neg c2]
        have g := stealSplit_length_ge n keep t (acc + s.len) (push n head ⟨s.off, keep - acc⟩)
          (push n tail ⟨s.off + (keep - acc), s.len - (keep - acc)⟩)
        exact ⟨not_wid_of_room (Nat.lt_of_le_of_lt (Nat.le_trans (push_length_ge n head _) g.1) h1) _,
          not_wid_of_room (Nat.lt_of_le_of_lt (Nat.le_trans (push_length_ge n tail _) g.2) h2) _, ih _ _ _ h1 h2⟩

/-- The head and the tail of a steal that end below capacity partition the victim's list byte for byte. -/
theorem stealSplit_mult_room {n : Nat} (hn : 0 < n) (keep : Nat) (l : List Span) (hd : ∀ x, mult l x ≤ 1)
    (h1 : (stealSplit n keep 0 l [] []).1.length < n) (h2 : (stealSplit n keep 0 l [] []).2.length < n) (x : Nat) :
    mult (stealSplit n keep 0 l [] []).1 x + mult (stealSplit n keep 0 l [] []).2 x = mult l x :=
  (steal_head_tail_total hn keep l hd (ssNW_of_room keep l 0 [] [] h1 h2)).1 x

end Vinc.ValuesSched

#audit_axioms Vinc.ValuesSched.foldl_push_mult_room
#audit_axioms Vinc.ValuesSched.foldl_pushFront_mult_room
#audit_axioms Vinc.ValuesSched.retainMissing_mult_room
#audit_axioms Vinc.ValuesSched.ssNW_of_room
#audit_axioms Vinc.ValuesSched.stealSplit_mult_room
