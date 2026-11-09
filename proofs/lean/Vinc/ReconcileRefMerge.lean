import Vinc.ReconcileRefIds2

/-!
# Reconcile refinement, part 2h: the lazy merge is the merge of two sorted lists

`mergeGo` reads the peer's items one at a time out of the message. On an honest ascending list it produces exactly the
events of the textbook merge `mergeEv` of our slice and the peer's list, in order, and ends with the reader past the list.
-/

namespace Vinc.Reconcile

/-- The events of a merge of our items with the peer's ascending list; `k` is the position in the peer's list. -/
def mergeEv : List Item → List Item → Nat → List Cmp
  | [], [], _ => []
  | m :: ms, [], k => .mine m :: mergeEv ms [] k
  | [], t :: ts, k => .theirs t :: mergeEv [] ts (k + 1)
  | m :: ms, t :: ts, k =>
    if lexLt m t then .mine m :: mergeEv ms (t :: ts) k
    else if m = t then .both k :: mergeEv ms ts (k + 1)
    else .theirs t :: mergeEv (m :: ms) ts (k + 1)
termination_by ms ts _ => ms.length + ts.length

/-- The events folded through the handler `f`. -/
def evFold {α : Type} (f : Cmp → α → Except Err α) (acc : α) (evs : List Cmp) : Except Err α :=
  evs.foldlM (fun a e => f e a) acc

theorem evFold_nil {α : Type} (f : Cmp → α → Except Err α) (acc : α) : evFold f acc [] = .ok acc := rfl

theorem evFold_cons {α : Type} (f : Cmp → α → Except Err α) (acc : α) (e : Cmp) (evs : List Cmp) :
    evFold f acc (e :: evs) = (f e acc >>= fun a => evFold f a evs) := rfl

theorem stageBytes_cons (x : Item) (xs : List Item) : stageBytes (x :: xs) = venc x.length ++ (x ++ stageBytes xs) := by
  simp [stageBytes]

theorem next_stream (mx : Nat) (ts : List Item) (rest : List Nat) (h : ∀ t ∈ ts, t.length ≤ mx ∧ t.length < 2 ^ 63) :
    IS.next mx ⟨ts.length, stageBytes ts ++ rest⟩ =
      .ok (match ts with
        | [] => none
        | t :: ts' => some (t, ⟨ts'.length, stageBytes ts' ++ rest⟩)) := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
    have ht := h t (List.mem_cons_self ..)
    have := next_ok mx ts'.length t (stageBytes ts' ++ rest) ht.1 ht.2
    simpa [stageBytes_cons, List.append_assoc] using this

theorem next_nil' (mx : Nat) (rest : List Nat) : IS.next mx ⟨([] : List Item).length, stageBytes ([] : List Item) ++ rest⟩ = .ok none := rfl

theorem next_cons' (mx : Nat) (t : Item) (ts : List Item) (rest : List Nat)
    (h : ∀ y ∈ t :: ts, y.length ≤ mx ∧ y.length < 2 ^ 63) :
    IS.next mx ⟨(t :: ts).length, stageBytes (t :: ts) ++ rest⟩ = .ok (some (t, ⟨ts.length, stageBytes ts ++ rest⟩)) := by
  have ht := h t (List.mem_cons_self ..)
  have := next_ok mx ts.length t (stageBytes ts ++ rest) ht.1 ht.2
  simpa [stageBytes_cons, List.append_assoc] using this

theorem mergeGo_spec {α : Type} (lim : Limits) (S : List Item) (hlen : ∀ x ∈ S, x.length ≤ lim.maxItem)
    (b : Nat) (hb : b ≤ S.length) (f : Cmp → α → Except Err α) (rest : List Nat) :
    ∀ (fuel j k : Nat) (prev : Option Item) (T : List Item) (acc : α), j ≤ b → (b - j) + T.length + 1 ≤ fuel →
      (∀ t ∈ T, t.length ≤ lim.maxItem ∧ t.length < 2 ^ 63) → T.Pairwise (fun x y => lexLt x y = true) →
      (∀ p t, prev = some p → T.head? = some t → lexLt p t = true) →
      mergeGo lim S b f fuel j k prev T.head? ⟨T.tail.length, stageBytes T.tail ++ rest⟩ acc =
        (evFold f acc (mergeEv ((S.drop j).take (b - j)) T k)).map (fun a => (a, rest))
  | 0, j, k, prev, T, acc, _, hf, _, _, _ => by omega
  | fuel + 1, j, k, prev, T, acc, hjb, hf, hT, hasc, hprev => by
    by_cases hj : j < b
    · have hjS : j < S.length := by omega
      have hx := readItem_ok lim S hlen j hjS
      have hms : (S.drop j).take (b - j) = S[j] :: (S.drop (j + 1)).take (b - (j + 1)) := by
        rw [show b - j = (b - (j + 1)) + 1 by omega, List.drop_eq_getElem_cons hjS, List.take_succ_cons]
      cases T with
      | nil =>
        simp only [List.head?_nil, List.tail_nil, List.length_nil] at *
        rw [mergeGo]
        simp only [hj, ite_true, hx, Except.map, bind, Except.bind, pure, Except.pure]
        rw [hms, mergeEv, evFold_cons]
        cases hfx : f (.mine S[j]) acc with
        | error e => simp [Except.map, bind, Except.bind]
        | ok a =>
          simp only [bind, Except.bind]
          exact mergeGo_spec lim S hlen b hb f rest fuel (j + 1) k prev [] a (by omega) (by simp; omega) hT hasc hprev
      | cons t ts =>
        have hth := hT t (List.mem_cons_self ..)
        have hts : ∀ y ∈ ts, y.length ≤ lim.maxItem ∧ y.length < 2 ^ 63 := fun y hy => hT y (List.mem_cons_of_mem _ hy)
        have hasc' := (List.pairwise_cons.mp hasc)
        have hpt : ∀ p, prev = some p → (!lexLt p t) = false := by
          intro p hp; have := hprev p t hp rfl; simp [this]
        rw [mergeGo]
        simp only [hj, ite_true, hx, Except.map, bind, Except.bind, pure, Except.pure, List.head?_cons, List.tail_cons,
          lr, Except.mapError]
        rw [hms, mergeEv]
        have IH := fun (j' k' : Nat) (prev' : Option Item) (T' : List Item) (acc' : α) =>
          mergeGo_spec lim S hlen b hb f rest fuel j' k' prev' T' acc'
        have hS1 : S[j] ∈ S := List.getElem_mem (h := hjS)
        cases prev with
        | none =>
          rcases ts with _ | ⟨t', ts'⟩
          · (by_cases h1 : lexLt S[j] t = true
             · simp only [h1, ite_true]
               cases hfx : f (Cmp.mine S[j]) acc with
               | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
               | ok v =>
                 simp only [evFold_cons, hfx, bind, Except.bind]
                 exact IH (j + 1) k _ (t :: _) v (by omega) (by simp at hf ⊢; omega) hT hasc hprev
             · have h1' : ¬ lexLt S[j] t = true := h1
               simp only [h1', Bool.false_eq_true, ite_false]
               by_cases h2 : S[j] = t
               · simp only [if_pos h2]
                 cases hfx : f (Cmp.both k) acc with
                 | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
                 | ok v =>
                   simp only [evFold_cons, hfx, bind, Except.bind]
                   simp only [next_nil', lr, Except.mapError, bind, Except.bind]
                   exact IH (j + 1) (k + 1) _ [] v (by omega) (by simp at hf ⊢; omega) (by simp) (by simp) (by simp)
               · simp only [if_neg h2]
                 cases hfx : f (Cmp.theirs t) acc with
                 | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
                 | ok v =>
                   simp only [evFold_cons, hfx, bind, Except.bind]
                   simp only [next_nil', lr, Except.mapError, bind, Except.bind]
                   rw [← hms]
                   exact IH j (k + 1) _ [] v hjb (by simp at hf ⊢; omega) (by simp) (by simp) (by simp))
          · (by_cases h1 : lexLt S[j] t = true
             · simp only [h1, ite_true]
               cases hfx : f (Cmp.mine S[j]) acc with
               | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
               | ok v =>
                 simp only [evFold_cons, hfx, bind, Except.bind]
                 exact IH (j + 1) k _ (t :: _) v (by omega) (by simp at hf ⊢; omega) hT hasc hprev
             · have h1' : ¬ lexLt S[j] t = true := h1
               simp only [h1', Bool.false_eq_true, ite_false]
               by_cases h2 : S[j] = t
               · simp only [if_pos h2]
                 cases hfx : f (Cmp.both k) acc with
                 | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
                 | ok v =>
                   simp only [evFold_cons, hfx, bind, Except.bind]
                   simp only [next_cons' lim.maxItem t' ts' rest hts, lr, Except.mapError, bind, Except.bind]
                   exact IH (j + 1) (k + 1) _ (t' :: ts') v (by omega) (by simp at hf ⊢; omega) hts hasc'.2 (by simp [hasc'.1])
               · simp only [if_neg h2]
                 cases hfx : f (Cmp.theirs t) acc with
                 | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
                 | ok v =>
                   simp only [evFold_cons, hfx, bind, Except.bind]
                   simp only [next_cons' lim.maxItem t' ts' rest hts, lr, Except.mapError, bind, Except.bind]
                   rw [← hms]
                   exact IH j (k + 1) _ (t' :: ts') v hjb (by simp at hf ⊢; omega) hts hasc'.2 (by simp [hasc'.1]))
        | some p =>
          have hp' := hpt p rfl
          rcases ts with _ | ⟨t', ts'⟩
          · (by_cases h1 : lexLt S[j] t = true
             · simp only [h1, ite_true]
               cases hfx : f (Cmp.mine S[j]) acc with
               | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
               | ok v =>
                 simp only [evFold_cons, hfx, bind, Except.bind]
                 exact IH (j + 1) k _ (t :: _) v (by omega) (by simp at hf ⊢; omega) hT hasc hprev
             · have h1' : ¬ lexLt S[j] t = true := h1
               simp only [h1', Bool.false_eq_true, ite_false]
               by_cases h2 : S[j] = t
               · simp only [if_pos h2]
                 cases hfx : f (Cmp.both k) acc with
                 | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
                 | ok v =>
                   simp only [evFold_cons, hfx, bind, Except.bind]
                   simp only [hp', next_nil', lr, Except.mapError, bind, Except.bind]
                   exact IH (j + 1) (k + 1) _ [] v (by omega) (by simp at hf ⊢; omega) (by simp) (by simp) (by simp)
               · simp only [if_neg h2]
                 cases hfx : f (Cmp.theirs t) acc with
                 | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
                 | ok v =>
                   simp only [evFold_cons, hfx, bind, Except.bind]
                   simp only [hp', next_nil', lr, Except.mapError, bind, Except.bind]
                   rw [← hms]
                   exact IH j (k + 1) _ [] v hjb (by simp at hf ⊢; omega) (by simp) (by simp) (by simp))
          · (by_cases h1 : lexLt S[j] t = true
             · simp only [h1, ite_true]
               cases hfx : f (Cmp.mine S[j]) acc with
               | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
               | ok v =>
                 simp only [evFold_cons, hfx, bind, Except.bind]
                 exact IH (j + 1) k _ (t :: _) v (by omega) (by simp at hf ⊢; omega) hT hasc hprev
             · have h1' : ¬ lexLt S[j] t = true := h1
               simp only [h1', Bool.false_eq_true, ite_false]
               by_cases h2 : S[j] = t
               · simp only [if_pos h2]
                 cases hfx : f (Cmp.both k) acc with
                 | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
                 | ok v =>
                   simp only [evFold_cons, hfx, bind, Except.bind]
                   simp only [hp', next_cons' lim.maxItem t' ts' rest hts, lr, Except.mapError, bind, Except.bind]
                   exact IH (j + 1) (k + 1) _ (t' :: ts') v (by omega) (by simp at hf ⊢; omega) hts hasc'.2 (by simp [hasc'.1])
               · simp only [if_neg h2]
                 cases hfx : f (Cmp.theirs t) acc with
                 | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
                 | ok v =>
                   simp only [evFold_cons, hfx, bind, Except.bind]
                   simp only [hp', next_cons' lim.maxItem t' ts' rest hts, lr, Except.mapError, bind, Except.bind]
                   rw [← hms]
                   exact IH j (k + 1) _ (t' :: ts') v hjb (by simp at hf ⊢; omega) hts hasc'.2 (by simp [hasc'.1]))
    · have hjeq : j = b := by omega
      have hms0 : (S.drop j).take (b - j) = [] := by simp [hjeq]
      cases T with
      | nil =>
        rw [mergeGo]
        simp only [hj, ite_false, pure, Except.pure, bind, Except.bind, List.head?_nil, List.tail_nil, List.length_nil,
          stageBytes, List.nil_append, hms0, mergeEv, evFold_nil, Except.map]
        rfl
      | cons t ts =>
        have hts : ∀ y ∈ ts, y.length ≤ lim.maxItem ∧ y.length < 2 ^ 63 := fun y hy => hT y (List.mem_cons_of_mem _ hy)
        have hasc' := (List.pairwise_cons.mp hasc)
        have hpt : ∀ p, prev = some p → (!lexLt p t) = false := by
          intro p hp; have := hprev p t hp rfl; simp [this]
        have IH := fun (j' k' : Nat) (prev' : Option Item) (T' : List Item) (acc' : α) =>
          mergeGo_spec lim S hlen b hb f rest fuel j' k' prev' T' acc'
        rw [mergeGo]
        simp only [hj, ite_false, Except.map, bind, Except.bind, pure, Except.pure, List.head?_cons, List.tail_cons,
          lr, Except.mapError]
        rw [hms0, mergeEv]
        cases prev with
        | none =>
          rcases ts with _ | ⟨t', ts'⟩
          · cases hfx : f (Cmp.theirs t) acc with
            | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
            | ok v =>
              simp only [evFold_cons, hfx, bind, Except.bind]
              simp only [next_nil', lr, Except.mapError, bind, Except.bind]
              have hh := IH j (k + 1) (some t) [] v hjb (by simp at hf ⊢; omega) (by simp) (by simp) (by simp)
              rw [hms0] at hh
              exact hh
          · cases hfx : f (Cmp.theirs t) acc with
            | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
            | ok v =>
              simp only [evFold_cons, hfx, bind, Except.bind]
              simp only [next_cons' lim.maxItem t' ts' rest hts, lr, Except.mapError, bind, Except.bind]
              have hh := IH j (k + 1) (some t) (t' :: ts') v hjb (by simp at hf ⊢; omega) hts hasc'.2 (by simp [hasc'.1])
              rw [hms0] at hh
              exact hh
        | some p =>
          have hp' := hpt p rfl
          rcases ts with _ | ⟨t', ts'⟩
          · cases hfx : f (Cmp.theirs t) acc with
            | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
            | ok v =>
              simp only [evFold_cons, hfx, bind, Except.bind]
              simp only [hp', next_nil', lr, Except.mapError, bind, Except.bind]
              have hh := IH j (k + 1) (some t) [] v hjb (by simp at hf ⊢; omega) (by simp) (by simp) (by simp)
              rw [hms0] at hh
              exact hh
          · cases hfx : f (Cmp.theirs t) acc with
            | error e => simp [evFold_cons, hfx, Except.map, bind, Except.bind]
            | ok v =>
              simp only [evFold_cons, hfx, bind, Except.bind]
              simp only [hp', next_cons' lim.maxItem t' ts' rest hts, lr, Except.mapError, bind, Except.bind]
              have hh := IH j (k + 1) (some t) (t' :: ts') v hjb (by simp at hf ⊢; omega) hts hasc'.2 (by simp [hasc'.1])
              rw [hms0] at hh
              exact hh

/-- The merge of our slice `a..b` with an honest ascending list read from the message. -/
theorem merge_spec {α : Type} (lim : Limits) (S : List Item) (hlen : ∀ x ∈ S, x.length ≤ lim.maxItem)
    (a b : Nat) (hab : a ≤ b) (hb : b ≤ S.length) (f : Cmp → α → Except Err α) (rest : List Nat) (acc : α)
    (xs : List Item) (hx : ∀ t ∈ xs, t.length ≤ lim.maxItem ∧ t.length < 2 ^ 63)
    (hasc : xs.Pairwise (fun x y => lexLt x y = true)) :
    merge lim S a b ⟨xs.length, stageBytes xs ++ rest⟩ f acc =
      (evFold f acc (mergeEv ((S.drop a).take (b - a)) xs 0)).map (fun v => (v, rest)) := by
  unfold merge
  cases xs with
  | nil =>
    simp only [lr, next_nil', Except.mapError, bind, Except.bind]
    have := mergeGo_spec lim S hlen b hb f rest ((b - a) + ([] : List Item).length + 2) a 0 none [] acc hab
      (by simp) (by simp) (by simp) (by simp)
    exact this
  | cons t ts =>
    simp only [lr, next_cons' lim.maxItem t ts rest hx, Except.mapError, bind, Except.bind]
    have := mergeGo_spec lim S hlen b hb f rest ((b - a) + (t :: ts).length + 2) a 0 none (t :: ts) acc hab
      (by omega) hx hasc (by simp)
    exact this

theorem drain_stream (mx : Nat) (rest : List Nat) :
    ∀ (xs : List Item) (fuel : Nat), (∀ t ∈ xs, t.length ≤ mx ∧ t.length < 2 ^ 63) → xs.length < fuel →
      drain mx fuel ⟨xs.length, stageBytes xs ++ rest⟩ = .ok rest
  | [], fuel, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [drain]
    rw [show IS.next mx ⟨([] : List Item).length, stageBytes ([] : List Item) ++ rest⟩ = .ok none from rfl]
    simp [stageBytes]
  | t :: ts, fuel, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have := next_cons' mx t ts rest h
    simp only [drain, this]
    exact drain_stream mx rest ts f (fun y hy => h y (List.mem_cons_of_mem _ hy)) (by simp at hf; omega)

end Vinc.Reconcile