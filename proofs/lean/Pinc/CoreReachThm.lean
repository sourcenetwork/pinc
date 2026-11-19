import Pinc.Axioms
import Pinc.CoreReach

/-!
# The reach ring: the bound, one body per session and it is the latest, which body goes, every loss counted

What the model proves about `ReachRing`, for any number of places and any run of puts (`Inv`, kept by `rput`):

- the ring never grows (`n` places) and no stamp passes the counter (`Inv.len_eq`, `Inv.stamp_le`);
- a body longer than `mx` is never stored: the put changes no place, moves the counter on and returns 1
  (`rput_big`, `Inv.short`);
- at most one body per session (`Inv.uniq`), and it is the latest put for that session: a get after a put of a body
  returns it (`rget_rput`);
- the filled places come first (`Inv.prefix_`): a place is empty only if every place after it is;
- the rule of a put: a session that is held gets its own place, stamped with the counter, no other place changes and
  the put returns 0 (`rput_held_cells`); a session that is not held takes the first empty place and returns 0
  (`rput_free_cells`), or, in a full ring, the place whose stamp is the smallest of all, the body put longest ago,
  and returns 1 (`rput_full_cells`); no other place changes;
- every body is counted: over any run of puts from an empty ring the counter is the number of puts, so a place's
  stamp is the number of the put that wrote it, and the puts are the bodies held, the refreshes (a body replaced by a
  later one of its session) and the bodies the puts returned as lost, which the endpoint adds to its count
  (`run_counted`).
-/

namespace Pinc.CoreReach

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

theorem cellAt_replicate (n i : Nat) : cellAt (List.replicate n (none : Option C)) i = none := by
  unfold cellAt
  rcases h : (List.replicate n (none : Option C))[i]? with _ | v
  · rfl
  · have := List.eq_of_mem_replicate (List.mem_of_getElem? h)
    simp [this]

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

/-! ## The first empty place, and the place put longest ago -/

theorem free_some {l : List (Option C)} {p : Nat} (h : free l = some p) :
    p < l.length ∧ cellAt l p = none ∧ ∀ j, j < p → cellAt l j ≠ none := by
  induction l generalizing p with
  | nil => simp [free] at h
  | cons c cs ih =>
    cases c with
    | none =>
      simp only [free, Option.some.injEq] at h
      subst h
      exact ⟨by simp, by rw [cellAt_cons_zero], fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | some c' =>
      simp only [free] at h
      cases hf : free cs with
      | none => simp [hf] at h
      | some q =>
        simp [hf] at h
        subst h
        obtain ⟨h1, h2, h3⟩ := ih hf
        refine ⟨by simp only [List.length_cons]; omega, by rw [cellAt_cons_succ]; exact h2, fun j hj => ?_⟩
        cases j with
        | zero => rw [cellAt_cons_zero]; simp
        | succ j => rw [cellAt_cons_succ]; exact h3 j (by omega)

theorem free_none {l : List (Option C)} (h : free l = none) : ∀ i, i < l.length → cellAt l i ≠ none := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons c cs ih =>
    intro i hi
    cases c with
    | none => simp [free] at h
    | some c' =>
      simp only [free] at h
      have hf : free cs = none := by
        cases hq : free cs with
        | none => rfl
        | some q => simp [hq] at h
      cases i with
      | zero => rw [cellAt_cons_zero]; simp
      | succ i => rw [cellAt_cons_succ]; exact ih hf i (by simp only [List.length_cons] at hi; omega)

theorem minAt_cons_isSome (c : Option C) (cs : List (Option C)) : (minAt (c :: cs)).isSome = true := by
  simp only [minAt]
  cases minAt cs with
  | none => rfl
  | some jk =>
    obtain ⟨j, k⟩ := jk
    simp only [minStep]
    split <;> rfl

theorem minAt_none {l : List (Option C)} (h : minAt l = none) : l = [] := by
  cases l with
  | nil => rfl
  | cons c cs =>
    have := minAt_cons_isSome c cs
    rw [h] at this
    simp at this

/-- `min_by_key` finds a place whose key is at most every place's key. -/
theorem minAt_spec {l : List (Option C)} {j k : Nat} (h : minAt l = some (j, k)) :
    j < l.length ∧ key (cellAt l j) = k ∧ ∀ i, i < l.length → k ≤ key (cellAt l i) := by
  induction l generalizing j k with
  | nil => simp [minAt] at h
  | cons c cs ih =>
    cases hm : minAt cs with
    | none =>
      simp only [minAt, hm, minStep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hcs : cs = [] := minAt_none hm
      subst hcs
      refine ⟨by simp, by rw [cellAt_cons_zero], fun i hi => ?_⟩
      have : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
      subst this
      rw [cellAt_cons_zero]
      exact Nat.le_refl _
    | some jk =>
      obtain ⟨j', k'⟩ := jk
      obtain ⟨h1, h2, h3⟩ := ih hm
      simp only [minAt, hm, minStep] at h
      by_cases hc : key c ≤ k'
      · simp only [hc, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simp, by rw [cellAt_cons_zero], fun i hi => ?_⟩
        cases i with
        | zero => rw [cellAt_cons_zero]; exact Nat.le_refl _
        | succ i =>
          rw [cellAt_cons_succ]
          exact Nat.le_trans hc (h3 i (by simp only [List.length_cons] at hi; omega))
      · simp only [hc, ite_false, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simp only [List.length_cons]; omega, by rw [cellAt_cons_succ]; exact h2, fun i hi => ?_⟩
        cases i with
        | zero => rw [cellAt_cons_zero]; omega
        | succ i => rw [cellAt_cons_succ]; exact h3 i (by simp only [List.length_cons] at hi; omega)

/-! ## The put -/

theorem rput_big {mx : Nat} {r : R} {b : B} (h : mx < b.len) : rput mx r b = (1, { r with clock := r.clock + 1 }) := by
  simp [rput, h]

theorem rput_held {mx : Nat} {r : R} {b : B} {p : Nat} (hm : b.len ≤ mx) (hp : pos b.sess r.cells = some p) :
    rput mx r b = (0, { cells := r.cells.set p (some (newC r b)), clock := r.clock + 1 }) := by
  simp [rput, Nat.not_lt.2 hm, hp]

theorem rput_free {mx : Nat} {r : R} {b : B} {p : Nat} (hm : b.len ≤ mx) (hp : pos b.sess r.cells = none)
    (hf : free r.cells = some p) :
    rput mx r b = (0, { cells := r.cells.set p (some (newC r b)), clock := r.clock + 1 }) := by
  simp [rput, Nat.not_lt.2 hm, hp, hf]

theorem rput_full {mx : Nat} {r : R} {b : B} {p k : Nat} (hm : b.len ≤ mx) (hp : pos b.sess r.cells = none)
    (hf : free r.cells = none) (hq : minAt r.cells = some (p, k)) :
    rput mx r b = (1, { cells := r.cells.set p (some (newC r b)), clock := r.clock + 1 }) := by
  simp [rput, Nat.not_lt.2 hm, hp, hf, hq]

theorem rput_none {mx : Nat} {r : R} {b : B} (hm : b.len ≤ mx) (hp : pos b.sess r.cells = none)
    (hf : free r.cells = none) (hq : minAt r.cells = none) :
    rput mx r b = (1, { r with clock := r.clock + 1 }) := by
  simp [rput, Nat.not_lt.2 hm, hp, hf, hq]

/-- A session that is held gets its own place, stamped with the counter; no other place changes; nothing is lost. -/
theorem rput_held_cells {mx : Nat} {r : R} {b : B} {p : Nat} (hm : b.len ≤ mx) (hp : pos b.sess r.cells = some p) :
    (rput mx r b).1 = 0 ∧ (rput mx r b).2.clock = r.clock + 1 ∧
    cellAt (rput mx r b).2.cells p = some (newC r b) ∧
    (∀ i, i ≠ p → cellAt (rput mx r b).2.cells i = cellAt r.cells i) := by
  rw [rput_held hm hp]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [cellAt_set]; simp [pos_lt hp]
  · intro i hi; rw [cellAt_set]; simp [Ne.symm hi]

/-- A session that is not held, while the ring has an empty place, takes the first one; no other place changes;
nothing is lost. -/
theorem rput_free_cells {mx : Nat} {r : R} {b : B} {p : Nat} (hm : b.len ≤ mx) (hp : pos b.sess r.cells = none)
    (hf : free r.cells = some p) :
    (rput mx r b).1 = 0 ∧ (rput mx r b).2.clock = r.clock + 1 ∧
    cellAt r.cells p = none ∧ (∀ j, j < p → cellAt r.cells j ≠ none) ∧
    cellAt (rput mx r b).2.cells p = some (newC r b) ∧
    (∀ i, i ≠ p → cellAt (rput mx r b).2.cells i = cellAt r.cells i) := by
  obtain ⟨h1, h2, h3⟩ := free_some hf
  rw [rput_free hm hp hf]
  refine ⟨rfl, rfl, h2, h3, ?_, ?_⟩
  · rw [cellAt_set]; simp [h1]
  · intro i hi; rw [cellAt_set]; simp [Ne.symm hi]

/-- A session that is not held, in a full ring, takes the place of the smallest stamp, the body put longest ago,
which is lost (the put returns 1); no other place changes. -/
theorem rput_full_cells {mx : Nat} {r : R} {b : B} (hm : b.len ≤ mx) (hp : pos b.sess r.cells = none)
    (hf : free r.cells = none) (hl : 0 < r.cells.length) :
    ∃ p, p < r.cells.length ∧ cellAt r.cells p ≠ none ∧
      (∀ i, i < r.cells.length → key (cellAt r.cells p) ≤ key (cellAt r.cells i)) ∧
      (rput mx r b).1 = 1 ∧ (rput mx r b).2.clock = r.clock + 1 ∧
      cellAt (rput mx r b).2.cells p = some (newC r b) ∧
      (∀ i, i ≠ p → cellAt (rput mx r b).2.cells i = cellAt r.cells i) := by
  cases hq : minAt r.cells with
  | none =>
    have := minAt_none hq
    rw [this] at hl
    simp at hl
  | some pk =>
    obtain ⟨p, k⟩ := pk
    obtain ⟨h1, h2, h3⟩ := minAt_spec hq
    rw [rput_full hm hp hf hq]
    refine ⟨p, h1, free_none hf p h1, fun i hi => by rw [h2]; exact h3 i hi, rfl, rfl, ?_, ?_⟩
    · rw [cellAt_set]; simp [h1]
    · intro i hi; rw [cellAt_set]; simp [Ne.symm hi]

/-! ## The invariant -/

def Uniq (cells : List (Option C)) : Prop :=
  ∀ i j a b, cellAt cells i = some a → cellAt cells j = some b → a.sess = b.sess → i = j

structure Inv (n mx : Nat) (r : R) : Prop where
  len_eq : r.cells.length = n
  uniq : Uniq r.cells
  short : ∀ i c, cellAt r.cells i = some c → c.len ≤ mx
  stamp_le : ∀ i c, cellAt r.cells i = some c → c.stamp ≤ r.clock
  prefix_ : ∀ i j, i < j → cellAt r.cells i = none → cellAt r.cells j = none

theorem inv_init (n mx : Nat) : Inv n mx { cells := List.replicate n none, clock := 0 } := by
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · intro i j a b ha
    rw [cellAt_replicate] at ha
    simp at ha
  · intro i c hc
    rw [cellAt_replicate] at hc
    simp at hc
  · intro i c hc
    rw [cellAt_replicate] at hc
    simp at hc
  · intro i j _ _
    exact cellAt_replicate n j

theorem inv_clock {n mx : Nat} {r : R} (h : Inv n mx r) : Inv n mx { r with clock := r.clock + 1 } :=
  ⟨h.len_eq, h.uniq, h.short, fun i c hc => Nat.le_succ_of_le (h.stamp_le i c hc), h.prefix_⟩

/-- Writing a short body into a place that no other place's session shares, after only filled places. -/
theorem inv_set {n mx : Nat} {r : R} (h : Inv n mx r) (b : B) (p : Nat) (hm : b.len ≤ mx)
    (hpl : p < r.cells.length) (hu : ∀ i c, i ≠ p → cellAt r.cells i = some c → c.sess ≠ b.sess)
    (hpre : ∀ j, j < p → cellAt r.cells j ≠ none) :
    Inv n mx { cells := r.cells.set p (some (newC r b)), clock := r.clock + 1 } := by
  have hat : cellAt (r.cells.set p (some (newC r b))) p = some (newC r b) := by
    rw [cellAt_set]; simp [hpl]
  have hot : ∀ i, i ≠ p → cellAt (r.cells.set p (some (newC r b))) i = cellAt r.cells i := by
    intro i hi; rw [cellAt_set]; simp [Ne.symm hi]
  refine ⟨by simp [h.len_eq], ?_, ?_, ?_, ?_⟩
  · intro i j a c ha hc hs
    try dsimp only at ha hc
    by_cases hi : i = p
    · by_cases hj : j = p
      · rw [hi, hj]
      · subst hi
        rw [hat] at ha
        rw [hot j hj] at hc
        cases ha
        exact absurd hs.symm (hu j c hj hc)
    · by_cases hj : j = p
      · subst hj
        rw [hat] at hc
        rw [hot i hi] at ha
        cases hc
        exact absurd hs (hu i a hi ha)
      · rw [hot i hi] at ha
        rw [hot j hj] at hc
        exact h.uniq i j a c ha hc hs
  · intro i c hc
    try dsimp only at hc
    by_cases hi : i = p
    · subst hi; rw [hat] at hc; cases hc; exact hm
    · rw [hot i hi] at hc; exact h.short i c hc
  · intro i c hc
    try dsimp only at hc ⊢
    by_cases hi : i = p
    · subst hi; rw [hat] at hc; cases hc; exact Nat.le_refl _
    · rw [hot i hi] at hc; exact Nat.le_succ_of_le (h.stamp_le i c hc)
  · intro i j hij hn
    try dsimp only at hn ⊢
    have hip : i ≠ p := by
      intro e; subst e; rw [hat] at hn; cases hn
    rw [hot i hip] at hn
    have hpi : p < i := by
      rcases Nat.lt_or_ge i p with h1 | h1
      · exact absurd hn (hpre i h1)
      · omega
    rw [hot j (by omega)]
    exact h.prefix_ i j hij hn

theorem rput_inv {n mx : Nat} {r : R} (h : Inv n mx r) (b : B) : Inv n mx (rput mx r b).2 := by
  by_cases hm : b.len ≤ mx
  · cases hp : pos b.sess r.cells with
    | some p =>
      rw [rput_held hm hp]
      obtain ⟨c0, hc0, hs0⟩ := pos_some hp
      refine inv_set h b p hm (pos_lt hp)
        (fun i c hi hc hs => hi (h.uniq i p c c0 hc hc0 (by rw [hs, hs0]))) ?_
      intro j hj hn
      have := h.prefix_ j p hj hn
      rw [hc0] at this
      cases this
    | none =>
      cases hf : free r.cells with
      | some p =>
        rw [rput_free hm hp hf]
        obtain ⟨h1, -, h3⟩ := free_some hf
        exact inv_set h b p hm h1 (fun i c _ hc => pos_none hp i c hc) h3
      | none =>
        cases hq : minAt r.cells with
        | some pk =>
          obtain ⟨p, k⟩ := pk
          rw [rput_full hm hp hf hq]
          obtain ⟨h1, -, -⟩ := minAt_spec hq
          exact inv_set h b p hm h1 (fun i c _ hc => pos_none hp i c hc) (fun j hj => free_none hf j (by omega))
        | none =>
          rw [rput_none hm hp hf hq]
          exact inv_clock h
  · rw [rput_big (Nat.lt_of_not_le hm)]
    exact inv_clock h

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

/-- A get after the put of a short body returns that body (in a ring of at least one place). -/
theorem rget_rput {n mx : Nat} {r : R} {b : B} (h : Inv n mx r) (hm : b.len ≤ mx) (hn : 0 < n) :
    rget b.sess (rput mx r b).2.cells = some (newC r b) := by
  have hi := rput_inv h b
  have hc : ∃ p, cellAt (rput mx r b).2.cells p = some (newC r b) := by
    cases hp : pos b.sess r.cells with
    | some p => exact ⟨p, (rput_held_cells hm hp).2.2.1⟩
    | none =>
      cases hf : free r.cells with
      | some p => exact ⟨p, (rput_free_cells hm hp hf).2.2.2.2.1⟩
      | none =>
        obtain ⟨p, -, -, -, -, -, hc, -⟩ := rput_full_cells hm hp hf (by rw [h.len_eq]; exact hn)
        exact ⟨p, hc⟩
  obtain ⟨p, hp⟩ := hc
  exact rget_of_uniq hi.uniq hp

/-! ## Every body is counted -/

theorem occ_replicate (n : Nat) : occ (List.replicate n (none : Option C)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, occ, ih]

theorem occ_set_none (l : List (Option C)) (p : Nat) (c : C) (hp : p < l.length) (hn : cellAt l p = none) :
    occ (l.set p (some c)) = occ l + 1 := by
  induction l generalizing p with
  | nil => simp at hp
  | cons x xs ih =>
    cases p with
    | zero =>
      rw [cellAt_cons_zero] at hn
      subst hn
      simp only [List.set, occ]
    | succ p =>
      rw [cellAt_cons_succ] at hn
      have := ih p (by simp only [List.length_cons] at hp; omega) hn
      cases x <;> simp only [List.set, occ, this]

theorem occ_set_some (l : List (Option C)) (p : Nat) (c : C) (hp : p < l.length) (hs : cellAt l p ≠ none) :
    occ (l.set p (some c)) = occ l := by
  induction l generalizing p with
  | nil => simp at hp
  | cons x xs ih =>
    cases p with
    | zero =>
      rw [cellAt_cons_zero] at hs
      cases x with
      | none => exact absurd rfl hs
      | some y => simp only [List.set, occ]
    | succ p =>
      rw [cellAt_cons_succ] at hs
      have := ih p (by simp only [List.length_cons] at hp; omega) hs
      cases x <;> simp only [List.set, occ, this]

/-- A run of puts, with the ghosts: the puts made, the refreshes (a held session gets a new body) and what the puts
returned as lost (what the endpoint adds to its count). -/
structure S where
  r : R := {}
  puts : Nat := 0
  refreshed : Nat := 0
  dropped : Nat := 0

def step (mx : Nat) (s : S) (b : B) : S :=
  { r := (rput mx s.r b).2, puts := s.puts + 1,
    refreshed := s.refreshed + (if b.len ≤ mx ∧ (pos b.sess s.r.cells).isSome = true then 1 else 0),
    dropped := s.dropped + (rput mx s.r b).1 }

def run (mx : Nat) (s : S) : List B → S
  | [] => s
  | b :: bs => run mx (step mx s b) bs

/-- The empty ring of `n` places. -/
def S.init (n : Nat) : S := { r := { cells := List.replicate n none, clock := 0 } }

structure Counted (s : S) : Prop where
  clock : s.r.clock = s.puts
  balance : s.puts = s.refreshed + s.dropped + occ s.r.cells

theorem counted_step {mx : Nat} {s : S} (h : Counted s) (b : B) : Counted (step mx s b) := by
  have hb := h.balance
  have hc := h.clock
  by_cases hm : b.len ≤ mx
  · cases hp : pos b.sess s.r.cells with
    | some p =>
      obtain ⟨c0, hc0, -⟩ := pos_some hp
      have ho := occ_set_some s.r.cells p (newC s.r b) (pos_lt hp) (by rw [hc0]; simp)
      constructor
      · simp only [step, rput_held hm hp]; omega
      · simp only [step, rput_held hm hp]; rw [ho]; simp [hm, hp]; omega
    | none =>
      cases hf : free s.r.cells with
      | some p =>
        obtain ⟨h1, h2, -⟩ := free_some hf
        have ho := occ_set_none s.r.cells p (newC s.r b) h1 h2
        constructor
        · simp only [step, rput_free hm hp hf]; omega
        · simp only [step, rput_free hm hp hf]; rw [ho]; simp [hm, hp]; omega
      | none =>
        cases hq : minAt s.r.cells with
        | some pk =>
          obtain ⟨p, k⟩ := pk
          obtain ⟨h1, -, -⟩ := minAt_spec hq
          have ho := occ_set_some s.r.cells p (newC s.r b) h1 (free_none hf p h1)
          constructor
          · simp only [step, rput_full hm hp hf hq]; omega
          · simp only [step, rput_full hm hp hf hq]; rw [ho]; simp [hm, hp]; omega
        | none =>
          constructor
          · simp only [step, rput_none hm hp hf hq]; omega
          · simp only [step, rput_none hm hp hf hq]; simp [hm, hp]; omega
  · have hlt := Nat.lt_of_not_le hm
    constructor
    · simp only [step, rput_big hlt]; omega
    · simp only [step, rput_big hlt]; simp [hm]; omega

theorem counted_run {n mx : Nat} (s : S) (hi : Inv n mx s.r) (h : Counted s) (bs : List B) :
    Inv n mx (run mx s bs).r ∧ Counted (run mx s bs) := by
  induction bs generalizing s with
  | nil => exact ⟨hi, h⟩
  | cons b bs ih => exact ih (step mx s b) (rput_inv hi b) (counted_step h b)

/-- Over any run of puts from the empty ring: the invariant holds, the counter is the number of puts, and every body
put is held, replaced by a later body of its session, or counted as lost by the put that lost it. -/
theorem run_counted (n mx : Nat) (bs : List B) :
    Inv n mx (run mx (S.init n) bs).r ∧ (run mx (S.init n) bs).r.clock = (run mx (S.init n) bs).puts ∧
    (run mx (S.init n) bs).puts =
      (run mx (S.init n) bs).refreshed + (run mx (S.init n) bs).dropped + occ (run mx (S.init n) bs).r.cells := by
  have h0 : Counted (S.init n) := ⟨rfl, by simp [S.init, occ_replicate]⟩
  obtain ⟨hi, hc⟩ := counted_run (S.init n) (inv_init n mx) h0 bs
  exact ⟨hi, hc.clock, hc.balance⟩

#audit_axioms Pinc.CoreReach.rput_big
#audit_axioms Pinc.CoreReach.rput_held_cells
#audit_axioms Pinc.CoreReach.rput_free_cells
#audit_axioms Pinc.CoreReach.rput_full_cells
#audit_axioms Pinc.CoreReach.rput_inv
#audit_axioms Pinc.CoreReach.rget_rput
#audit_axioms Pinc.CoreReach.inv_init
#audit_axioms Pinc.CoreReach.run_counted

end Pinc.CoreReach
