import Vinc.Axioms
import Vinc.CoreReach

/-!
# The reach ring: the bound, one body per session and it is the latest, which body goes

What the model proves about `ReachRing`, for any number of places and any run of puts (`Inv`, kept by `rput`):

- the ring never grows (`n` places) and `next` stays below `n` (`Inv.len_eq`, `Inv.next_lt`);
- a body longer than `mx` is never stored: the put changes nothing (`rput_big`, `Inv.short`);
- at most one body per session (`Inv.uniq`), and it is the latest put for that session: a get after a put of a body
  returns it (`rget_rput`), and a put leaves the body of every other session it does not overwrite as it was;
- the rule of a put: a session that is held gets its own place and no other place changes; a session that is not
  held takes the place `next` and no other place changes, so a full ring loses exactly the body in the place
  `next`; `next` moves on by one, modulo `n`, exactly when the place written was `next` (`rput_held`,
  `rput_new`);
- while the ring has an empty place, a session that is not held never overwrites another body: `next` is the first
  empty place (`Inv.room`, `rput_new_room`).

The code keeps no count of the bodies a put overwrites or refuses.
-/

namespace Vinc.CoreReach

theorem cellAt_cons_zero (c : Option C) (cs : List (Option C)) : cellAt (c :: cs) 0 = c := by
  simp [cellAt]

theorem cellAt_cons_succ (c : Option C) (cs : List (Option C)) (i : Nat) : cellAt (c :: cs) (i + 1) = cellAt cs i := by
  simp [cellAt]

theorem cellAt_set (l : List (Option C)) (a : Nat) (v : Option C) (i : Nat) :
    cellAt (l.set a v) i = if a = i ∧ a < l.length then v else cellAt l i := by
  unfold cellAt
  rw [List.getElem?_set]
  by_cases h : a = i
  · subst h
    by_cases h2 : a < l.length
    · simp [h2]
    · have : l[a]? = none := by
        apply List.getElem?_eq_none; omega
      simp [h2, this]
  · simp [h]

theorem cellAt_ge (l : List (Option C)) (i : Nat) (h : l.length ≤ i) : cellAt l i = none := by
  unfold cellAt
  rw [List.getElem?_eq_none h]; rfl

theorem pos_some {s : Nat} {cells : List (Option C)} {i : Nat} (h : pos s cells = some i) :
    ∃ c, cellAt cells i = some c ∧ c.sess = s := by
  induction cells generalizing i with
  | nil => simp [pos] at h
  | cons c cs ih =>
    cases c with
    | none =>
      simp only [pos] at h
      cases hp : pos s cs with
      | none => simp [hp] at h
      | some j =>
        simp [hp] at h
        subst h
        obtain ⟨c, hc, hs⟩ := ih hp
        exact ⟨c, by rw [cellAt_cons_succ]; exact hc, hs⟩
    | some c' =>
      simp only [pos] at h
      by_cases hs : c'.sess = s
      · simp [hs] at h
        subst h
        exact ⟨c', by rw [cellAt_cons_zero], hs⟩
      · simp only [hs, ite_false] at h
        cases hp : pos s cs with
        | none => simp [hp] at h
        | some j =>
          simp [hp] at h
          subst h
          obtain ⟨c, hc, hs⟩ := ih hp
          exact ⟨c, by rw [cellAt_cons_succ]; exact hc, hs⟩

theorem pos_none {s : Nat} {cells : List (Option C)} (h : pos s cells = none) :
    ∀ i c, cellAt cells i = some c → c.sess ≠ s := by
  induction cells with
  | nil => intro i c hc; simp [cellAt] at hc
  | cons c0 cs ih =>
    intro i c hc
    cases i with
    | zero =>
      rw [cellAt_cons_zero] at hc
      subst hc
      intro hs
      simp [pos, hs] at h
    | succ i =>
      rw [cellAt_cons_succ] at hc
      have hp : pos s cs = none := by
        cases c0 with
        | none => simpa [pos] using h
        | some c' =>
          simp only [pos] at h
          by_cases hs : c'.sess = s
          · simp [hs] at h
          · simp only [hs, ite_false] at h
            simpa using h
      exact ih hp i c hc

theorem pos_lt {s : Nat} {cells : List (Option C)} {i : Nat} (h : pos s cells = some i) : i < cells.length := by
  obtain ⟨c, hc, _⟩ := pos_some h
  refine Nat.lt_of_not_le fun hl => ?_
  rw [cellAt_ge _ _ hl] at hc
  simp at hc

theorem rget_pos (s : Nat) (cells : List (Option C)) : rget s cells = (pos s cells).bind (cellAt cells) := by
  induction cells with
  | nil => simp [rget, pos]
  | cons c cs ih =>
    cases c with
    | none =>
      have : rget s (none :: cs) = rget s cs := by simp [rget]
      rw [this, ih]
      simp only [pos]
      cases hp : pos s cs <;> simp [cellAt_cons_succ]
    | some c' =>
      by_cases hs : c'.sess = s
      · simp [rget, pos, hs, cellAt_cons_zero]
      · have : rget s (some c' :: cs) = rget s cs := by simp [rget, hs]
        rw [this, ih]
        simp only [pos, hs, ite_false]
        cases hp : pos s cs <;> simp [cellAt_cons_succ]

/-! ## The put -/

def Uniq (cells : List (Option C)) : Prop :=
  ∀ i j a b, cellAt cells i = some a → cellAt cells j = some b → a.sess = b.sess → i = j

/-- Either every place is filled, or the filled places are exactly those before `next`. -/
def Room (n : Nat) (r : R) : Prop :=
  full r.cells ∨ ∀ i, i < n → (cellAt r.cells i = none ↔ r.next ≤ i)

structure Inv (n mx : Nat) (r : R) : Prop where
  len_eq : r.cells.length = n
  next_lt : r.next < n
  uniq : Uniq r.cells
  short : ∀ i c, cellAt r.cells i = some c → c.len ≤ mx
  room : Room n r

theorem inv_init (n mx : Nat) (hn : 0 < n) :
    Inv n mx { cells := List.replicate n none, next := 0 } := by
  refine ⟨by simp, hn, ?_, ?_, Or.inr ?_⟩
  · intro i j a b ha
    simp [cellAt] at ha
    rcases hi : (List.replicate n (none : Option C))[i]? with _ | v
    · simp [hi] at ha
    · have := List.eq_of_mem_replicate (List.mem_of_getElem? hi)
      simp [hi, this] at ha
  · intro i c hc
    simp [cellAt] at hc
    rcases hi : (List.replicate n (none : Option C))[i]? with _ | v
    · simp [hi] at hc
    · have := List.eq_of_mem_replicate (List.mem_of_getElem? hi)
      simp [hi, this] at hc
  · intro i hi
    simp only [cellAt]
    have : (List.replicate n (none : Option C))[i]? = some none := by simp [hi]
    simp [this]

theorem rput_big {n mx : Nat} {r : R} {c : C} (h : mx < c.len) : rput n mx r c = r := by
  simp [rput, h]

/-- A session that is held gets its own place; no other place changes; `next` moves on exactly when the place was
`next`. -/
theorem rput_held {n mx : Nat} {r : R} {c : C} {p : Nat} (hm : c.len ≤ mx) (hp : pos c.sess r.cells = some p) :
    cellAt (rput n mx r c).cells p = some c ∧ (∀ i, i ≠ p → cellAt (rput n mx r c).cells i = cellAt r.cells i) ∧
    (rput n mx r c).next = if p = r.next then (r.next + 1) % n else r.next := by
  have e : rput n mx r c = { cells := r.cells.set p (some c), next := if p = r.next then (r.next + 1) % n else r.next } := by
    simp [rput, Nat.not_lt.2 hm, hp]
  rw [e]
  refine ⟨?_, ?_, rfl⟩
  · rw [cellAt_set]; simp [pos_lt hp]
  · intro i hi; rw [cellAt_set]; simp [Ne.symm hi]

/-- A session that is not held takes the place `next`; no other place changes; `next` moves on. -/
theorem rput_new {n mx : Nat} {r : R} {c : C} (hm : c.len ≤ mx) (hp : pos c.sess r.cells = none)
    (hl : r.next < r.cells.length) :
    cellAt (rput n mx r c).cells r.next = some c ∧ (∀ i, i ≠ r.next → cellAt (rput n mx r c).cells i = cellAt r.cells i) ∧
    (rput n mx r c).next = (r.next + 1) % n := by
  have e : rput n mx r c = { cells := r.cells.set r.next (some c), next := (r.next + 1) % n } := by
    simp [rput, Nat.not_lt.2 hm, hp]
  rw [e]
  refine ⟨?_, ?_, rfl⟩
  · rw [cellAt_set]; simp [hl]
  · intro i hi; rw [cellAt_set]; simp [Ne.symm hi]

/-- While the ring has an empty place, a session that is not held takes an empty one: nothing is overwritten. -/
theorem rput_new_room {n mx : Nat} {r : R} (h : Inv n mx r) (hnf : ¬ full r.cells) :
    cellAt r.cells r.next = none := by
  rcases h.room with hf | hr
  · exact absurd hf hnf
  · exact (hr r.next h.next_lt).2 (Nat.le_refl _)

theorem isSome_of_ne {x : Option C} (h : x ≠ none) : x.isSome = true := by
  cases x with
  | none => exact absurd rfl h
  | some _ => rfl

theorem rput_inv {n mx : Nat} {r : R} (h : Inv n mx r) (c : C) : Inv n mx (rput n mx r c) := by
  have hn : 0 < n := by have := h.next_lt; omega
  by_cases hm : c.len ≤ mx
  · cases hp : pos c.sess r.cells with
    | some p =>
      obtain ⟨hc, ho, hnx⟩ := rput_held (n := n) (mx := mx) (r := r) hm hp
      have hpl := pos_lt hp
      obtain ⟨c0, hc0, hs0⟩ := pos_some hp
      have hlen : (rput n mx r c).cells.length = n := by
        simp [rput, Nat.not_lt.2 hm, hp, h.len_eq]
      refine ⟨hlen, ?_, ?_, ?_, ?_⟩
      · rw [hnx]
        by_cases hq : p = r.next
        · simp only [hq, ite_true]; exact Nat.mod_lt _ hn
        · simp only [hq, ite_false]; exact h.next_lt
      · intro i j a b ha hb hs
        by_cases hi : i = p
        · by_cases hj : j = p
          · omega
          · subst hi
            rw [hc] at ha
            rw [ho j hj] at hb
            have : i = j := h.uniq i j c0 b hc0 hb (by rw [hs0]; cases ha; exact hs)
            exact absurd this.symm hj
        · by_cases hj : j = p
          · subst hj
            rw [hc] at hb
            rw [ho i hi] at ha
            have : i = j := h.uniq i j a c0 ha hc0 (by rw [hs0]; cases hb; exact hs)
            exact absurd this hi
          · rw [ho i hi] at ha
            rw [ho j hj] at hb
            exact h.uniq i j a b ha hb hs
      · intro i c' hc'
        by_cases hi : i = p
        · subst hi; rw [hc] at hc'; cases hc'; exact hm
        · rw [ho i hi] at hc'; exact h.short i c' hc'
      · rcases h.room with hf | hr
        · left
          intro i hi
          by_cases hip : i = p
          · subst hip; rw [hc]; rfl
          · rw [ho i hip]; exact hf i (by rw [hlen] at hi; rw [h.len_eq]; exact hi)
        · right
          have hpocc : p < r.next := by
            have := (hr p (by rw [← h.len_eq]; exact hpl))
            rw [hc0] at this
            simp at this
            omega
          have hq : p ≠ r.next := by omega
          rw [hnx]
          simp only [hq, ite_false]
          intro i hi
          by_cases hip : i = p
          · subst hip; rw [hc]; simp; omega
          · rw [ho i hip]; exact hr i hi
    | none =>
      have hl : r.next < r.cells.length := by rw [h.len_eq]; exact h.next_lt
      obtain ⟨hc, ho, hnx⟩ := rput_new (n := n) (mx := mx) hm hp hl
      have hlen : (rput n mx r c).cells.length = n := by
        simp [rput, Nat.not_lt.2 hm, hp, h.len_eq]
      refine ⟨hlen, ?_, ?_, ?_, ?_⟩
      · rw [hnx]; exact Nat.mod_lt _ hn
      · intro i j a b ha hb hs
        by_cases hi : i = r.next
        · by_cases hj : j = r.next
          · omega
          · subst hi
            rw [hc] at ha
            rw [ho j hj] at hb
            cases ha
            exact absurd hs.symm (pos_none hp j b hb)
        · by_cases hj : j = r.next
          · subst hj
            rw [hc] at hb
            rw [ho i hi] at ha
            cases hb
            exact absurd hs (pos_none hp i a ha)
          · rw [ho i hi] at ha
            rw [ho j hj] at hb
            exact h.uniq i j a b ha hb hs
      · intro i c' hc'
        by_cases hi : i = r.next
        · subst hi; rw [hc] at hc'; cases hc'; exact hm
        · rw [ho i hi] at hc'; exact h.short i c' hc'
      · rcases h.room with hf | hr
        · left
          intro i hi
          by_cases hip : i = r.next
          · subst hip; rw [hc]; rfl
          · rw [ho i hip]; exact hf i (by rw [hlen] at hi; rw [h.len_eq]; exact hi)
        · have hnone : cellAt r.cells r.next = none := (hr r.next h.next_lt).2 (Nat.le_refl _)
          by_cases hlt : r.next + 1 < n
          · right
            have : (r.next + 1) % n = r.next + 1 := Nat.mod_eq_of_lt hlt
            rw [hnx, this]
            intro i hi
            by_cases hip : i = r.next
            · subst hip; rw [hc]; simp
            · rw [ho i hip]
              have := hr i hi
              rw [this]; omega
          · left
            have : (r.next + 1) = n := by have := h.next_lt; omega
            intro i hi
            by_cases hip : i = r.next
            · subst hip; rw [hc]; rfl
            · rw [ho i hip]
              have hi' : i < r.next := by rw [hlen] at hi; omega
              have h2 := hr i (by omega)
              apply isSome_of_ne
              intro hnn
              have := h2.1 hnn
              omega
  · rw [rput_big (Nat.lt_of_not_le hm)]; exact h

theorem rget_of_uniq {cells : List (Option C)} (hu : Uniq cells) {p : Nat} {c : C} (hc : cellAt cells p = some c) :
    rget c.sess cells = some c := by
  rw [rget_pos]
  cases hq : pos c.sess cells with
  | none => exact absurd rfl (pos_none hq p c hc)
  | some j =>
    obtain ⟨c', hc', hs⟩ := pos_some hq
    have := hu j p c' c hc' hc hs
    subst this
    simp [hc', hc]
    rw [hc] at hc'; exact (Option.some.inj hc').symm

theorem rget_rput {n mx : Nat} {r : R} {c : C} (h : Inv n mx r) (hm : c.len ≤ mx) :
    rget c.sess (rput n mx r c).cells = some c := by
  have hi := rput_inv h c
  cases hp : pos c.sess r.cells with
  | some p =>
    obtain ⟨hc, _, _⟩ := rput_held (n := n) (mx := mx) (r := r) hm hp
    exact rget_of_uniq hi.uniq hc
  | none =>
    have hl : r.next < r.cells.length := by rw [h.len_eq]; exact h.next_lt
    obtain ⟨hc, _, _⟩ := rput_new (n := n) (mx := mx) hm hp hl
    exact rget_of_uniq hi.uniq hc

#audit_axioms Vinc.CoreReach.rput_big
#audit_axioms Vinc.CoreReach.rput_held
#audit_axioms Vinc.CoreReach.rput_new
#audit_axioms Vinc.CoreReach.rput_new_room
#audit_axioms Vinc.CoreReach.rput_inv
#audit_axioms Vinc.CoreReach.rget_rput
#audit_axioms Vinc.CoreReach.inv_init

end Vinc.CoreReach
