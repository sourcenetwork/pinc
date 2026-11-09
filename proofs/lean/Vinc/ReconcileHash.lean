import Vinc.ReconcileAlgebra

/-!
# Reconcile hash: the XOR fingerprint and the final check

`xorH` is the fingerprint of a list of items: the XOR of their 128-bit hashes. The model assumption on the keyed hash
is `Indep`: the item hashes are independent over XOR (no list of items whose hashes XOR to zero has an item an odd
number of times), which is what a 128-bit keyed hash gives except with probability 2^-128 per comparison. Under it,
`check_iff` is the whole content of the final check of the protocol: the fingerprint
`fp(A) ^ fp(here) ^ fp(there)` that the initiator sends equals `fp(B)` exactly when `here = B \\ A` and `there = A \\ B`,
for every pair of arenas that hold only items of the right side, each once.
-/

namespace Vinc.Reconcile

/-- The item hashes are independent over XOR (the 2^-128 assumption, stated). -/
def Indep (o : Oracle) : Prop := ∀ L : List Item, xorH o L = 0 → ∀ x, L.count x % 2 = 0

theorem foldl_xor_init (o : Oracle) (xs : List Item) (a : Nat) :
    xs.foldl (fun acc x => acc ^^^ o.H x) a = a ^^^ xs.foldl (fun acc x => acc ^^^ o.H x) 0 := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_xor]
    rw [ih (a ^^^ o.H x), ih (o.H x)]
    simp [Nat.xor_assoc]

theorem xorH_nil (o : Oracle) : xorH o [] = 0 := rfl

theorem xorH_cons (o : Oracle) (x : Item) (xs : List Item) : xorH o (x :: xs) = o.H x ^^^ xorH o xs := by
  unfold xorH
  simp only [List.foldl_cons, Nat.zero_xor]
  rw [foldl_xor_init]

theorem xorH_append (o : Oracle) (xs ys : List Item) : xorH o (xs ++ ys) = xorH o xs ^^^ xorH o ys := by
  induction xs with
  | nil => simp [xorH_nil]
  | cons x xs ih => rw [List.cons_append, xorH_cons, xorH_cons, ih, Nat.xor_assoc]

theorem xorH_perm (o : Oracle) {xs ys : List Item} (h : xs.Perm ys) : xorH o xs = xorH o ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [xorH_cons, xorH_cons, ih]
  | swap x y l => rw [xorH_cons, xorH_cons, xorH_cons, xorH_cons, ← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_comm (o.H y)]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem xorH_self_append (o : Oracle) (xs : List Item) : xorH o (xs ++ xs) = 0 := by
  rw [xorH_append]; exact Nat.xor_self _

/-- The fingerprint of a nodup list is its set: equal fingerprints of two nodup lists mean equal members. -/
theorem fp_inj {o : Oracle} (hi : Indep o) {xs ys : List Item} (hx : xs.Nodup) (hy : ys.Nodup)
    (h : xorH o xs = xorH o ys) : ∀ x, x ∈ xs ↔ x ∈ ys := by
  have h0 : xorH o (xs ++ ys) = 0 := by rw [xorH_append, h]; exact Nat.xor_self _
  intro x
  have := hi _ h0 x
  rw [List.count_append, hx.count, hy.count] at this
  by_cases a : x ∈ xs <;> by_cases b : x ∈ ys <;> simp_all

/-- A list of the members of `A` that are not in `B`, and so on: the report is exact. -/
def ExactReport (A B here there : List Item) : Prop :=
  (∀ x, x ∈ here ↔ x ∈ B ∧ x ∉ A) ∧ (∀ x, x ∈ there ↔ x ∈ A ∧ x ∉ B) ∧ here.Nodup ∧ there.Nodup

/-- The arenas only ever hold items of the right side: `here` items of `B` that `A` lacks, `there` items of `A`, once each. -/
def Safe (A B here there : List Item) : Prop :=
  (∀ x ∈ here, x ∈ B ∧ x ∉ A) ∧ (∀ x ∈ there, x ∈ A) ∧ here.Nodup ∧ there.Nodup

/-- The final check detects every wrong result: if the fingerprint the initiator sends is the responder's, the
report is exact. -/
theorem check_detects_wrong {o : Oracle} (hi : Indep o) {A B here there : List Item}
    (hA : A.Nodup) (hB : B.Nodup) (hs : Safe A B here there)
    (h : xorH o A ^^^ xorH o here ^^^ xorH o there = xorH o B) : ExactReport A B here there := by
  obtain ⟨h1, h2, hn1, hn2⟩ := hs
  have h0 : xorH o (A ++ here ++ there ++ B) = 0 := by
    rw [xorH_append, xorH_append, xorH_append, h]; exact Nat.xor_self _
  have par : ∀ x, (A.count x + here.count x + there.count x + B.count x) % 2 = 0 := by
    intro x; have := hi _ h0 x; simpa [List.count_append, Nat.add_assoc] using this
  refine ⟨fun x => ⟨h1 x, fun hx => ?_⟩, fun x => ⟨fun ht => ⟨h2 x ht, fun hB' => ?_⟩, fun hx => ?_⟩, hn1, hn2⟩
  · have hxB := hx.1; have hxA := hx.2
    have := par x
    rw [hA.count, hB.count] at this
    by_cases ht : x ∈ there
    · exact absurd (h2 x ht) hxA
    · by_cases hh : x ∈ here
      · exact hh
      · simp [hxA, hxB, ht, hh, List.count_eq_zero_of_not_mem, List.count_eq_zero.mpr] at this
  · have hxA := h2 x ht
    have hh : x ∉ here := fun hh => (h1 x hh).2 hxA
    have := par x
    rw [hA.count, hB.count] at this
    simp [hxA, hB', ht, hh, List.count_eq_zero.mpr, hn1.count, hn2.count] at this
  · have hxA := hx.1; have hxB := hx.2
    have := par x
    rw [hA.count, hB.count] at this
    by_cases hh : x ∈ here
    · exact absurd (h1 x hh).1 hxB
    · by_cases ht : x ∈ there
      · exact ht
      · simp [hxA, hxB, ht, hh, List.count_eq_zero.mpr] at this

/-- An exact report passes the final check. -/
theorem exact_passes_check (o : Oracle) {A B here there : List Item}
    (hA : A.Nodup) (hB : B.Nodup) (hx : ExactReport A B here there) :
    xorH o A ^^^ xorH o here ^^^ xorH o there = xorH o B := by
  obtain ⟨h1, h2, hn1, hn2⟩ := hx
  have p1 : here.Perm (B.filter (fun x => !A.contains x)) := by
    rw [List.perm_ext_iff_of_nodup hn1 (hB.filter _)]
    intro x; simp [h1 x, and_comm]
  have p2 : there.Perm (A.filter (fun x => !B.contains x)) := by
    rw [List.perm_ext_iff_of_nodup hn2 (hA.filter _)]
    intro x; simp [h2 x, and_comm]
  have pA : A.Perm (A.filter (fun x => B.contains x) ++ A.filter (fun x => !B.contains x)) := by
    simpa using (List.filter_append_perm (fun x => B.contains x) A).symm
  have pB : B.Perm (B.filter (fun x => A.contains x) ++ B.filter (fun x => !A.contains x)) := by
    simpa using (List.filter_append_perm (fun x => A.contains x) B).symm
  have pI : (A.filter (fun x => B.contains x)).Perm (B.filter (fun x => A.contains x)) := by
    rw [List.perm_ext_iff_of_nodup (hA.filter _) (hB.filter _)]
    intro x; simp [and_comm]
  rw [xorH_perm o pA, xorH_perm o pB, xorH_perm o p1, xorH_perm o p2, xorH_append, xorH_append, xorH_perm o pI]
  generalize xorH o (B.filter (fun x => A.contains x)) = u
  generalize xorH o (B.filter (fun x => !A.contains x)) = v
  generalize xorH o (A.filter (fun x => !B.contains x)) = w
  calc u ^^^ w ^^^ v ^^^ w = u ^^^ v ^^^ (w ^^^ w) := by
        simp only [Nat.xor_assoc]; rw [Nat.xor_comm v w, ← Nat.xor_assoc w w v, Nat.xor_self, Nat.zero_xor, Nat.xor_zero]
    _ = u ^^^ v := by simp

end Vinc.Reconcile
