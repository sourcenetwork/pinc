import Pinc.Axioms
import Pinc.ValuesSchedSplit

/-!
# The moves of work between the queue and the providers

`take_chunk`, the head/tail cut of a steal and the return of an evicted share to the queue front, as functions on span
lists, each with the lemma the schedule needs: no byte that is not verified is lost by a move (`tc_cov`,
`stealSplit_cov`, `evictQueue_cov`), also when a push widens. The exact accounting below capacity (no byte twice, the
bytes moved equal the tail's total) is `tc_mult` in `ValuesSchedExact` and the run-wide exact partition in `ValuesSchedExactRun`.

`take_chunk` is the loop of `fetch/sched.rs`: pop the front span, take it whole or cut it at a group boundary
(`gfloor`, at least one group), keep the rest at the front, and push what the store has not verified (`holes`) onto
the result, until `size` unverified bytes are gathered or the queue is empty. The loop is a function of fuel here; its
properties hold for every fuel, so for the number of steps the real loop takes.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Pinc.ValuesSched

/-- `Fetch::group_floor`: the least group-aligned size of `len` bytes, at least one group. -/
def gfloor (len : Nat) : Nat := if len / G * G = 0 then G else len / G * G

theorem gfloor_pos (len : Nat) : 0 < gfloor len := by
  unfold gfloor; split <;> simp only [G] at * <;> omega

/-- The bytes `take_chunk` takes of the front span `s` when `room` bytes are still wanted. -/
def takeLen (room : Nat) (s : Span) : Nat := if s.len ≤ room then s.len else min (gfloor room) s.len

theorem takeLen_le (room : Nat) (s : Span) : takeLen room s ≤ s.len := by
  unfold takeLen; split <;> omega

theorem takeLen_pos (room : Nat) (s : Span) (h : 0 < s.len) : 0 < takeLen room s := by
  unfold takeLen; split
  · exact h
  · have := gfloor_pos room; omega

/-- `Fetch::take_chunk`: `tc st n size fuel got q out` runs the loop with `got` bytes already gathered. -/
def tc (st : Store) (n size : Nat) : Nat → Nat → List Span → List Span → List Span × List Span
  | 0, _, q, out => (q, out)
  | fuel + 1, got, q, out =>
    if got < size then
      match q with
      | [] => ([], out)
      | s :: rest =>
        tc st n size fuel
          (got + ((holesOf st ⟨s.off, takeLen (size - got) s⟩).map (·.len)).sum)
          (if takeLen (size - got) s < s.len then
            pushFront n rest ⟨s.off + takeLen (size - got) s, s.len - takeLen (size - got) s⟩
           else rest)
          ((holesOf st ⟨s.off, takeLen (size - got) s⟩).foldl (push n) out)
    else (q, out)

theorem tc_cov (st : Store) {n : Nat} (hn : 0 < n) (size : Nat) (x : Nat) (hx : ¬ st.V x) :
    ∀ fuel got (q out : List Span), q.length ≤ n → out.length ≤ n → (cov q x ∨ cov out x) →
      (tc st n size fuel got q out).1.length ≤ n ∧ (tc st n size fuel got q out).2.length ≤ n ∧
      (cov (tc st n size fuel got q out).1 x ∨ cov (tc st n size fuel got q out).2 x) := by
  intro fuel
  induction fuel with
  | zero => intro got q out hq ho h; exact ⟨hq, ho, h⟩
  | succ f ih =>
    intro got q out hq ho h
    unfold tc
    by_cases hg : got < size
    · rw [if_pos hg]
      cases q with
      | nil =>
        simp only
        refine ⟨by simp, ho, ?_⟩
        rcases h with h | h
        · exact absurd h (cov_nil x)
        · exact Or.inr h
      | cons s rest =>
        simp only
        have hrest : rest.length ≤ n := by simp at hq; omega
        have hho : ((holesOf st ⟨s.off, takeLen (size - got) s⟩).foldl (push n) out).length ≤ n :=
          foldl_push_length hn _ ho
        have hq1 : (if takeLen (size - got) s < s.len then
            pushFront n rest ⟨s.off + takeLen (size - got) s, s.len - takeLen (size - got) s⟩ else rest).length ≤ n := by
          split
          · exact pushFront_length_le hn hrest _
          · exact hrest
        apply ih _ _ _ hq1 hho
        have hl := takeLen_le (size - got) s
        rcases h with h | h
        · rw [cov_cons] at h
          rcases h with h | h
          · by_cases hxx : x < s.off + takeLen (size - got) s
            · right
              have hc : cov (holesOf st ⟨s.off, takeLen (size - got) s⟩) x :=
                (holesOf_cov st _ x).2 ⟨⟨h.1, hxx⟩, hx⟩
              exact extend_cov hn ho _ x (Or.inr hc)
            · left
              have hlt : takeLen (size - got) s < s.len := by simp only [Span.Mem] at h; omega
              rw [if_pos hlt]
              exact pushFront_cov hn _ x hrest (Or.inr (by simp only [Span.Mem] at h ⊢; omega))
          · left
            split
            · exact pushFront_cov hn _ x hrest (Or.inl h)
            · exact h
        · right; exact extend_cov hn ho _ x (Or.inl h)
    · rw [if_neg hg]; exact ⟨hq, ho, h⟩

/-- `steal`: split the victim's list at `keep` bytes into the head it keeps and the tail the thief takes. State: the
bytes passed, the head and the tail built so far. -/
def stealSplit (n keep : Nat) : Nat → List Span → List Span → List Span → List Span × List Span
  | _, [], head, tail => (head, tail)
  | acc, s :: rest, head, tail =>
    if keep ≤ acc then stealSplit n keep (acc + s.len) rest head (push n tail s)
    else if acc + s.len ≤ keep then stealSplit n keep (acc + s.len) rest (push n head s) tail
    else stealSplit n keep (acc + s.len) rest (push n head ⟨s.off, keep - acc⟩)
      (push n tail ⟨s.off + (keep - acc), s.len - (keep - acc)⟩)

theorem stealSplit_cov {n : Nat} (hn : 0 < n) (keep : Nat) (x : Nat) :
    ∀ (l : List Span) acc (head tail : List Span), head.length ≤ n → tail.length ≤ n →
      (cov head x ∨ cov tail x ∨ cov l x) →
      (stealSplit n keep acc l head tail).1.length ≤ n ∧ (stealSplit n keep acc l head tail).2.length ≤ n ∧
      (cov (stealSplit n keep acc l head tail).1 x ∨ cov (stealSplit n keep acc l head tail).2 x) := by
  intro l
  induction l with
  | nil => intro acc head tail hh ht h; unfold stealSplit; exact ⟨hh, ht, by rcases h with h | h | h; exact Or.inl h; exact Or.inr h; exact absurd h (cov_nil x)⟩
  | cons s t ih =>
    intro acc head tail hh ht h
    unfold stealSplit
    by_cases h1 : keep ≤ acc
    · rw [if_pos h1]
      apply ih _ _ _ hh (push_length_le hn ht s)
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (push_cov hn ht s x (Or.inl h)))
      · rw [cov_cons] at h
        rcases h with h | h
        · exact Or.inr (Or.inl (push_cov hn ht s x (Or.inr h)))
        · exact Or.inr (Or.inr h)
    · rw [if_neg h1]
      by_cases h2 : acc + s.len ≤ keep
      · rw [if_pos h2]
        apply ih _ _ _ (push_length_le hn hh s) ht
        rcases h with h | h | h
        · exact Or.inl (push_cov hn hh s x (Or.inl h))
        · exact Or.inr (Or.inl h)
        · rw [cov_cons] at h
          rcases h with h | h
          · exact Or.inl (push_cov hn hh s x (Or.inr h))
          · exact Or.inr (Or.inr h)
      · rw [if_neg h2]
        apply ih _ _ _ (push_length_le hn hh _) (push_length_le hn ht _)
        rcases h with h | h | h
        · exact Or.inl (push_cov hn hh _ x (Or.inl h))
        · exact Or.inr (Or.inl (push_cov hn ht _ x (Or.inl h)))
        · rw [cov_cons] at h
          rcases h with h | h
          · by_cases hx : x < s.off + (keep - acc)
            · exact Or.inl (push_cov hn hh _ x (Or.inr (by simp only [Span.Mem] at h ⊢; omega)))
            · exact Or.inr (Or.inl (push_cov hn ht _ x (Or.inr (by simp only [Span.Mem] at h ⊢; omega))))
          · exact Or.inr (Or.inr h)

/-- The evicted share goes back to the queue front: `for s in miss.iter().rev() { queue.push_front(s) }`. -/
def evictQueue (n : Nat) (q miss : List Span) : List Span := miss.reverse.foldl (pushFront n) q

theorem evictQueue_cov {n : Nat} (hn : 0 < n) (x : Nat) (miss : List Span) :
    ∀ (q : List Span), q.length ≤ n → (cov q x ∨ cov miss x) →
      (evictQueue n q miss).length ≤ n ∧ cov (evictQueue n q miss) x := by
  unfold evictQueue
  have key : ∀ (r : List Span) (q : List Span), q.length ≤ n → (cov q x ∨ cov r x) →
      (r.foldl (pushFront n) q).length ≤ n ∧ cov (r.foldl (pushFront n) q) x := by
    intro r
    induction r with
    | nil => intro q hq h; exact ⟨hq, h.elim id (fun h => absurd h (cov_nil x))⟩
    | cons p t ih =>
      intro q hq h
      simp only [List.foldl_cons]
      apply ih _ (pushFront_length_le hn hq p)
      rcases h with h | h
      · exact Or.inl (pushFront_cov hn p x hq (Or.inl h))
      · rw [cov_cons] at h
        rcases h with h | h
        · exact Or.inl (pushFront_cov hn p x hq (Or.inr h))
        · exact Or.inr h
  intro q hq h
  apply key _ _ hq
  rcases h with h | h
  · exact Or.inl h
  · right
    obtain ⟨s, hs, hm⟩ := h
    exact ⟨s, List.mem_reverse.2 hs, hm⟩

theorem tc_length (st : Store) {n : Nat} (hn : 0 < n) (size : Nat) :
    ∀ fuel got (q out : List Span), q.length ≤ n → out.length ≤ n →
      (tc st n size fuel got q out).1.length ≤ n ∧ (tc st n size fuel got q out).2.length ≤ n := by
  intro fuel
  induction fuel with
  | zero => intro got q out hq ho; exact ⟨hq, ho⟩
  | succ f ih =>
    intro got q out hq ho
    unfold tc
    by_cases hg : got < size
    · rw [if_pos hg]
      cases q with
      | nil => simp only; exact ⟨by simp, ho⟩
      | cons s rest =>
        simp only
        have hrest : rest.length ≤ n := by simp at hq; omega
        apply ih _ _ _ _ (foldl_push_length hn _ ho)
        split
        · exact pushFront_length_le hn hrest _
        · exact hrest
    · rw [if_neg hg]; exact ⟨hq, ho⟩

theorem stealSplit_length {n : Nat} (hn : 0 < n) (keep : Nat) :
    ∀ (l : List Span) acc (head tail : List Span), head.length ≤ n → tail.length ≤ n →
      (stealSplit n keep acc l head tail).1.length ≤ n ∧ (stealSplit n keep acc l head tail).2.length ≤ n := by
  intro l
  induction l with
  | nil => intro acc head tail hh ht; unfold stealSplit; exact ⟨hh, ht⟩
  | cons s t ih =>
    intro acc head tail hh ht
    unfold stealSplit
    by_cases h1 : keep ≤ acc
    · rw [if_pos h1]; exact ih _ _ _ hh (push_length_le hn ht s)
    · rw [if_neg h1]
      by_cases h2 : acc + s.len ≤ keep
      · rw [if_pos h2]; exact ih _ _ _ (push_length_le hn hh s) ht
      · rw [if_neg h2]; exact ih _ _ _ (push_length_le hn hh _) (push_length_le hn ht _)

theorem evictQueue_length {n : Nat} (hn : 0 < n) (miss : List Span) :
    ∀ (q : List Span), q.length ≤ n → (evictQueue n q miss).length ≤ n := by
  unfold evictQueue
  have key : ∀ (r : List Span) (q : List Span), q.length ≤ n → (r.foldl (pushFront n) q).length ≤ n := by
    intro r
    induction r with
    | nil => intro q hq; exact hq
    | cons p t ih => intro q hq; exact ih _ (pushFront_length_le hn hq p)
  intro q hq
  exact key _ _ hq

end Pinc.ValuesSched

#audit_axioms Pinc.ValuesSched.tc_cov
#audit_axioms Pinc.ValuesSched.tc_length
#audit_axioms Pinc.ValuesSched.stealSplit_cov
#audit_axioms Pinc.ValuesSched.stealSplit_length
#audit_axioms Pinc.ValuesSched.evictQueue_cov
#audit_axioms Pinc.ValuesSched.evictQueue_length
#audit_axioms Pinc.ValuesSched.takeLen_le
#audit_axioms Pinc.ValuesSched.takeLen_pos
#audit_axioms Pinc.ValuesSched.gfloor_pos
