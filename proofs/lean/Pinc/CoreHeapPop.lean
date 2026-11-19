import Pinc.CoreHeapSet

/-!
# The deadline heap, part 4: the root and the pops

- `peek_min`: the root is the earliest of the pairs `(deadline, id)` held, the lowest id among equal deadlines
  (`root_le`).
- `drain_spec`: removing the root over and over (what a run of `poll_timeout` and `set id None` does) gives the pairs
  held in strictly increasing order, each once, and no other (a heap sort), after any run of calls (`drain_run`).
-/

namespace Pinc.CoreHeap

/-! ## The earliest -/

/-- The root is not later than any element of the heap. -/
theorem root_le (s : S) (h : Inv s) : ∀ j, j < s.len → Le (key s 0) (key s j) := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro hj
    by_cases hj0 : j = 0
    · subst hj0; exact Le_refl _
    · have h1 := ih ((j - 1) / 2) (by omega) (by omega)
      exact Le_trans h1 (h.ord j (by omega) hj)

/-- `peek` gives the earliest of the pairs `(deadline, id)` held, the lowest id among equal deadlines: an id that is
held, with its deadline, not later (in that order) than any pair held. -/
theorem peek_min (s : S) (h : Inv s) (t id : Nat) (hp : peek s = some (t, id)) :
    (s.pos id).isSome = true ∧ t = s.dl id ∧
    ∀ a, (s.pos a).isSome = true → Le (t, id) (s.dl a, a) := by
  unfold peek at hp
  split at hp
  · cases hp
  · rename_i hl
    have hlen : 0 < s.len := by omega
    have e := Option.some.inj hp
    have e1 : s.dl (s.heap 0) = t := (Prod.mk.inj e).1
    have e2 : s.heap 0 = id := (Prod.mk.inj e).2
    subst e1; subst e2
    refine ⟨?_, rfl, ?_⟩
    · rw [h.pos.pa 0 hlen]; rfl
    · intro a ha
      obtain ⟨p, hpa⟩ := Option.isSome_iff_exists.mp ha
      obtain ⟨hpl, hph⟩ := h.pos.pb a p hpa
      have := root_le s h p hpl
      simp only [key, hph] at this
      exact this

/-! ## Draining the heap: a heap sort -/

theorem drain_spec : ∀ (f : Nat) (s : S), Inv s → s.len ≤ f →
    (drain f s).Pairwise Lt ∧ (drain f s).length = s.len ∧
    ∀ x, x ∈ drain f s ↔ ∃ a, (s.pos a).isSome = true ∧ x = (s.dl a, a) := by
  have empty : ∀ s : S, Inv s → s.len = 0 → ∀ x : Nat × Nat, ¬ ∃ a, (s.pos a).isSome = true ∧ x = (s.dl a, a) := by
    intro s h h0 x ⟨a, ha, _⟩
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ha
    have := (h.pos.pb a p hp).1
    omega
  intro f
  induction f with
  | zero =>
    intro s h hl
    have h0 : s.len = 0 := by omega
    simp only [drain]
    refine ⟨List.Pairwise.nil, by simp [h0], fun x => ?_⟩
    simp only [List.not_mem_nil, false_iff]
    exact empty s h h0 x
  | succ f ih =>
    intro s h hl
    unfold drain
    cases hpk : peek s with
    | none =>
      have h0 : s.len = 0 := by
        unfold peek at hpk; split at hpk
        · assumption
        · cases hpk
      simp only
      refine ⟨List.Pairwise.nil, by simp [h0], fun x => ?_⟩
      simp only [List.not_mem_nil, false_iff]
      exact empty s h h0 x
    | some tid =>
      obtain ⟨t, id⟩ := tid
      simp only
      obtain ⟨hpres, ht, hmin⟩ := peek_min s h t id hpk
      obtain ⟨p, hpos⟩ := Option.isSome_iff_exists.mp hpres
      have hid : id < s.n := (h.pos.pb id p hpos).2 ▸ h.pos.hlt p (h.pos.pb id p hpos).1
      have hlenpos : 0 < s.len := by have := (h.pos.pb id p hpos).1; omega
      have F := set_rem s h id p hid hpos
      have hlen' : (set s id none).len = s.len - 1 := by
        have := F.len; simpa [hpos] using this
      obtain ⟨ihp, ihl, ihm⟩ := ih (set s id none) F.inv (by omega)
      have hnone : (set s id none).pos id = none := by
        have := F.here; simpa using this
      have hrdl : ∀ a, (set s id none).dl a = s.dl a := fun a => by rw [F.dl]
      refine ⟨?_, ?_, ?_⟩
      · refine List.Pairwise.cons ?_ ihp
        intro y hy
        obtain ⟨a, ha, rfl⟩ := (ihm y).mp hy
        have hai : a ≠ id := by
          rintro rfl; rw [hnone] at ha; simp at ha
        have has : (s.pos a).isSome = true := by rw [← F.others a hai]; exact ha
        have := hmin a has
        rw [hrdl]
        unfold Le at this; unfold Lt; simp only at this ⊢
        omega
      · simp [ihl, hlen']; omega
      · intro y
        rw [List.mem_cons, ihm y]
        constructor
        · rintro (rfl | ⟨a, ha, rfl⟩)
          · exact ⟨id, hpres, by rw [ht]⟩
          · have hai : a ≠ id := by
              rintro rfl; rw [hnone] at ha; simp at ha
            exact ⟨a, by rw [← F.others a hai]; exact ha, by rw [hrdl]⟩
        · rintro ⟨a, ha, rfl⟩
          by_cases hai : a = id
          · subst hai; left; rw [ht]
          · right; exact ⟨a, by rw [F.others a hai]; exact ha, by rw [hrdl]⟩

/-- What the pops of any run of calls give out: the pairs held, in strictly increasing order, each once. -/
theorem drain_run (n : Nat) (ops : List (Nat × Option Nat)) :
    let s := run (init n) ops
    (drain n s).Pairwise Lt ∧ ∀ x, x ∈ drain n s ↔ ∃ a, (s.pos a).isSome = true ∧ x = (s.dl a, a) := by
  have hI := run_inv (init n) (init_inv n) ops
  have hn : (run (init n) ops).len ≤ n := by
    have := len_le _ hI.pos
    rw [run_n (init n) (init_inv n) ops] at this
    exact this
  have := drain_spec n (run (init n) ops) hI hn
  exact ⟨this.1, this.2.2⟩

#audit_axioms Pinc.CoreHeap.peek_min
#audit_axioms Pinc.CoreHeap.drain_spec
#audit_axioms Pinc.CoreHeap.drain_run

end Pinc.CoreHeap
