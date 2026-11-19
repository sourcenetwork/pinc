import Pinc.Encode

/-!
# The 64-entry stacks are never full

`RangeVerifier` and `RangeEncoder` keep their pending nodes on a `Stack<_, 64>` (`STACK_CAP`), and a push on a
full stack is the `StackOverflow` error. Here: for a value of at most `2^64 - 1` bytes and any group-size log
(so at most `2^54` groups, `Sizes.groups_le`), neither stack ever holds more than 55 nodes, whatever stream the
verifier is fed, so no push can fail.

The argument is a potential. A stack of nodes of sizes `c_1` (top) .. `c_k` costs
`max_j (k - j + height c_j + 1)`, where `height c = ceil(log2 c)`. The stack length is at most this cost, popping
a node never raises it, and replacing a node of size `c >= 2` by its left child (height one lower) and its right
child (strictly lower) never raises it, because a left child is pushed on top and the entries below it are the
same ones the parent had below it, plus the right child. The cost of the initial stack, the root alone, is
`height n + 1 <= 55`.
-/

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Pinc.Bounds
open Pinc.Layout Pinc.Tree Pinc.Encode

/-- The cost of a stack of node sizes, top first. -/
def pot : List Nat → Nat
  | [] => 0
  | c :: r => max (r.length + hh c + 1) (pot r)

theorem len_le_pot (st : List Nat) : st.length ≤ pot st := by
  induction st with
  | nil => simp [pot]
  | cons c r ih => simp only [pot, List.length_cons]; omega

theorem pot_pop (c : Nat) (r : List Nat) : pot r ≤ pot (c :: r) := by
  simp only [pot]; omega

/-- Replacing a node of `c >= 2` groups by any of its children (left on top) does not raise the cost. -/
theorem pot_step (c : Nat) (r : List Nat) (A B : Prop) [Decidable A] [Decidable B] (h : 2 ≤ c) :
    pot ((if A then [leftGroups c] else []) ++ (if B then [c - leftGroups c] else []) ++ r) ≤ pot (c :: r) := by
  have h1 := hh_leftGroups c h
  have h2 := hh_right c h
  by_cases a : A <;> by_cases b : B <;> simp only [a, b, ite_true, ite_false, List.nil_append, List.cons_append, List.append_nil] <;>
    simp only [pot, List.length_cons] <;> omega

section
variable {Cv D : Type} [DecidableEq Cv]

/-- The sizes of the pending nodes of a verifier stack. -/
def sz (st : List (Node Cv)) : List Nat := st.map fun x => x.hi - x.lo

theorem feed_pot (H : Hash Cv D) (n first last : Nat) (s : State Cv D) (it : Raw Cv D)
    (hI : ∀ nd ∈ s.stack, nd.lo < nd.hi) (B : Nat) (hp : pot (sz s.stack) ≤ B) :
    pot (sz (feed H n first last s it).stack) ≤ B := by
  by_cases hf : s.failed = true
  · simpa [feed, hf] using hp
  · rcases hs : s.stack with _ | ⟨nd, rest⟩
    · simpa [feed, hf, hs] using hp
    · rw [hs] at hp hI
      have hnd := hI nd (List.mem_cons_self ..)
      unfold feed
      simp only [hf, hs, Bool.false_eq_true, ite_false]
      by_cases hleaf : nd.hi - nd.lo = 1
      · simp only [hleaf, ite_true]
        by_cases hh : H.leaf (isRoot n nd.lo nd.hi) nd.lo it.d = nd.cv
        · simp only [hh, ite_true]
          exact Nat.le_trans (pot_pop _ _) (by simpa [sz] using hp)
        · simp only [hh, ite_false]; simpa [hs] using hp
      · simp only [hleaf, ite_false]
        by_cases hh : H.parent (isRoot n nd.lo nd.hi) it.l it.r = nd.cv
        · simp only [hh, ite_true]
          have h2 : 2 ≤ nd.hi - nd.lo := by omega
          have h1 := leftGroups_pos _ h2
          have h3 := leftGroups_lt _ h2
          have hstep := pot_step (nd.hi - nd.lo) (sz rest) (first < nd.lo + leftGroups (nd.hi - nd.lo))
            (nd.lo + leftGroups (nd.hi - nd.lo) < last) h2
          refine Nat.le_trans ?_ (Nat.le_trans hstep (by simpa [sz] using hp))
          have e : sz ((if first < nd.lo + leftGroups (nd.hi - nd.lo)
                then [⟨it.l, nd.lo, nd.lo + leftGroups (nd.hi - nd.lo)⟩] else []) ++
              (if nd.lo + leftGroups (nd.hi - nd.lo) < last
                then [⟨it.r, nd.lo + leftGroups (nd.hi - nd.lo), nd.hi⟩] else []) ++ rest : List (Node Cv)) =
              (if first < nd.lo + leftGroups (nd.hi - nd.lo) then [leftGroups (nd.hi - nd.lo)] else []) ++
              (if nd.lo + leftGroups (nd.hi - nd.lo) < last then [nd.hi - nd.lo - leftGroups (nd.hi - nd.lo)] else []) ++
              sz rest := by
            by_cases a : first < nd.lo + leftGroups (nd.hi - nd.lo) <;>
              by_cases b : nd.lo + leftGroups (nd.hi - nd.lo) < last <;> simp [sz, a, b] <;> omega
          rw [e]
          exact Nat.le_refl _
        · simp only [hh, ite_false]; simpa [hs] using hp

theorem run_pot (H : Hash Cv D) (n first last : Nat) (hl : last ≤ n) (B : Nat) (items : List (Raw Cv D)) :
    ∀ s : State Cv D, Inv n first last s → pot (sz s.stack) ≤ B →
      pot (sz (run H n first last s items).stack) ≤ B := by
  induction items with
  | nil => intro s _ h; exact h
  | cons it t ih =>
    intro s hI hp
    exact ih _ (feed_inv H n first last s it hl hI)
      (feed_pot H n first last s it (fun nd hnd => (hI.1 nd hnd).1) B hp)

/-- The verifier stack of a value of `n <= 2^54` groups never holds more than 55 nodes, whatever stream it is
fed and whatever the root. So the pushes of `RangeVerifier::feed` (two at most per item, after a pop) never reach
the 64-entry capacity, and `StackOverflow` is unreachable. -/
theorem verifier_stack_le (H : Hash Cv D) (n first last : Nat) (hl : last ≤ n) (hn : n ≤ 2 ^ 54) (root : Cv)
    (items : List (Raw Cv D)) :
    (run H n first last (init root n first last) items).stack.length ≤ 55 := by
  have hb : hh n + 1 ≤ 55 := by
    have : hh n ≤ 54 := by
      unfold hh
      by_cases h : n ≤ 1
      · simp [h]
      · simp only [h, ite_false]
        have := (Nat.log2_lt (n := n - 1) (k := 54) (by omega)).2 (by omega)
        omega
    omega
  have hp : pot (sz (run H n first last (init root n first last) items).stack) ≤ 55 := by
    refine run_pot H n first last hl 55 items _ (init_inv root n first last hl) ?_
    by_cases hf : first < last
    · simp [init, sz, pot, hf]; omega
    · simp [init, sz, pot, hf]
  have := len_le_pot (sz (run H n first last (init root n first last) items).stack)
  simpa [sz] using Nat.le_trans this hp

/-- The same for a value of at most `2^64 - 1` bytes and any group-size log (`Sizes.groups_le`). -/
theorem verifier_stack_le_len (H : Hash Cv D) (len log first last : Nat) (hlen : len ≤ u64Max)
    (hl : last ≤ groups len log) (root : Cv) (items : List (Raw Cv D)) :
    (run H (groups len log) first last (init root (groups len log) first last) items).stack.length ≤ 55 :=
  verifier_stack_le H _ first last hl (groups_le len log hlen) root items

/-- The nodes of an encoder stack are nonempty intervals. -/
def Pos (E : List ENode) : Prop := ∀ e ∈ E, e.lo < e.hi

def szE (E : List ENode) : List Nat := E.map fun x => x.hi - x.lo

theorem encPeak_le (len log first last : Nat) (B : Nat) :
    ∀ (f : Nat) (E : List ENode), Pos E → pot (szE E) ≤ B → encPeak len log first last f E ≤ B := by
  intro f
  induction f with
  | zero =>
    intro E _ hp
    simp only [encPeak]
    have := len_le_pot (szE E)
    simpa [szE] using Nat.le_trans this hp
  | succ f ih =>
    intro E hPos hp
    cases E with
    | nil => simp [encPeak]
    | cons e E =>
      have hlen := len_le_pot (szE (e :: E))
      have hlen' : (e :: E).length ≤ B := by simpa [szE] using Nat.le_trans hlen hp
      have hnd := hPos e (List.mem_cons_self ..)
      simp only [encPeak]
      refine Nat.max_le.2 ⟨hlen', ?_⟩
      by_cases hleaf : e.hi - e.lo = 1
      · have hst : (encStep len log first last e).2 = [] := by simp [encStep, hleaf]
        rw [hst, List.nil_append]
        exact ih E (fun x hx => hPos x (List.mem_cons_of_mem _ hx))
          (Nat.le_trans (pot_pop _ _) (by simpa [szE] using hp))
      · have h2 : 2 ≤ e.hi - e.lo := by omega
        have h1 := leftGroups_pos _ h2
        have h3 := leftGroups_lt _ h2
        have hst : (encStep len log first last e).2 =
            (if first < e.lo + leftGroups (e.hi - e.lo) then [⟨e.lo, e.lo + leftGroups (e.hi - e.lo), e.idx + 1⟩] else []) ++
            (if e.lo + leftGroups (e.hi - e.lo) < last
              then [⟨e.lo + leftGroups (e.hi - e.lo), e.hi, e.idx + leftGroups (e.hi - e.lo)⟩] else []) := by
          simp [encStep, hleaf]
        rw [hst]
        refine ih _ ?_ ?_
        · intro x hx
          simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hx
          rcases hx with (⟨hc, rfl⟩ | ⟨hc, rfl⟩) | hx
          · simp only; omega
          · simp only; omega
          · exact hPos x (List.mem_cons_of_mem _ hx)
        · have hstep := pot_step (e.hi - e.lo) (szE E) (first < e.lo + leftGroups (e.hi - e.lo))
            (e.lo + leftGroups (e.hi - e.lo) < last) h2
          refine Nat.le_trans ?_ (Nat.le_trans hstep (by simpa [szE] using hp))
          have eq : szE (((if first < e.lo + leftGroups (e.hi - e.lo)
                then [⟨e.lo, e.lo + leftGroups (e.hi - e.lo), e.idx + 1⟩] else []) ++
              (if e.lo + leftGroups (e.hi - e.lo) < last
                then [⟨e.lo + leftGroups (e.hi - e.lo), e.hi, e.idx + leftGroups (e.hi - e.lo)⟩] else [])) ++ E) =
              (if first < e.lo + leftGroups (e.hi - e.lo) then [leftGroups (e.hi - e.lo)] else []) ++
              (if e.lo + leftGroups (e.hi - e.lo) < last then [e.hi - e.lo - leftGroups (e.hi - e.lo)] else []) ++
              szE E := by
            by_cases a : first < e.lo + leftGroups (e.hi - e.lo) <;>
              by_cases b : e.lo + leftGroups (e.hi - e.lo) < last <;> simp [szE, a, b] <;> omega
          rw [eq]
          exact Nat.le_refl _

/-- The encoder stack of a value of `n <= 2^54` groups never holds more than 55 nodes, for any number of steps. -/
theorem encoder_stack_le (len log first last : Nat) (hlen : len ≤ u64Max) (hl : last ≤ groups len log) (f : Nat) :
    encPeak len log first last f (encInit len log first last) ≤ 55 := by
  have hn := groups_le len log hlen
  have hb : hh (groups len log) + 1 ≤ 55 := by
    have : hh (groups len log) ≤ 54 := by
      unfold hh
      by_cases h : groups len log ≤ 1
      · simp [h]
      · simp only [h, ite_false]
        have := (Nat.log2_lt (n := groups len log - 1) (k := 54) (by omega)).2 (by omega)
        omega
    omega
  refine encPeak_le len log first last 55 f _ ?_ ?_
  · intro x hx
    unfold encInit at hx
    by_cases h : first < last
    · simp only [h, ite_true, List.mem_singleton] at hx
      subst hx
      show 0 < groups len log
      omega
    · simp [h] at hx
  · unfold encInit
    by_cases h : first < last
    · simp [h, szE, pot]; omega
    · simp [h, szE, pot]

end

end Pinc.Bounds

#audit_axioms Pinc.Bounds.verifier_stack_le
#audit_axioms Pinc.Bounds.encoder_stack_le
#audit_axioms Pinc.Bounds.verifier_stack_le_len
