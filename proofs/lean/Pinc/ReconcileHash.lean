import Pinc.ReconcileAlgebra

/-!
# Reconcile hash: the sum fingerprint and the final check

`sumH` is the sum of a list of items, its signed multiset (`Sum`: the coefficient of every item), and the fingerprint
of a list of `n` items is `enc (sumH xs) n`, the 32 bytes the wire carries. The one model assumption on the hash is
`EncInj`, stated as a definition that the theorems take as a hypothesis. Under it, `check_detects_wrong` and
`exact_passes_check` are the whole content of the final check of the protocol: the fingerprint
`enc (sum A + sum here - sum there) (|A| + |here| - |there|)` that the initiator sends equals the responder's
`enc (sum B) |B|` exactly when `here = B \\ A` and `there = A \\ B`, for every pair of arenas that hold only items of
the right side, each once. `exact_passes_check` needs no assumption on the hash. `encInj_exists` shows `EncInj` is not
vacuous.
-/

namespace Pinc.Reconcile

/-- The fingerprint does not collide on the sums that lists produce: two fingerprints of signed multisets `P - N` and
`P' - N'` (of any counts) that are equal come from the same multiset. This is the collision resistance of the whole
construction as a function of the signed multiset. For the real code it rests on the discrete logarithm in the
Ristretto group (two different multisets with the same group sum, about 2^125 work) and on the collision resistance
of the 256-bit hash (about 2^128 work). It replaces XOR independence, which did not hold against chosen items. It is
stated over the sums of lists, not over every function from items to integers, which no oracle could satisfy. It is
an idealisation: lists give more sums than there are 256-bit values, so an oracle whose values stay below `2 ^ 256`
cannot have it for all lists, and the real hash has it only against a bounded adversary. No theorem takes it together
with the bound on the values (`HBound`), and `encInj_exists` gives an oracle that has it. -/
def EncInj (o : Oracle) : Prop :=
  ∀ (P N P' N' : List Item) (c c' : Nat),
    o.enc (sumH P - sumH N) c = o.enc (sumH P' - sumH N') c' → sumH P - sumH N = sumH P' - sumH N'

theorem sumH_nil : sumH [] = (fun _ => 0 : Sum) := by funext y; simp [sumH]

theorem Sum.add_apply (f g : Sum) (y : Item) : (f + g) y = f y + g y := rfl

theorem Sum.sub_apply (f g : Sum) (y : Item) : (f - g) y = f y - g y := rfl

/-- Append is addition. -/
theorem sumH_append (xs ys : List Item) : sumH (xs ++ ys) = sumH xs + sumH ys := by
  funext y
  simp only [Sum.add_apply, sumH, List.count_append]
  omega

/-- A permutation has the same sum. -/
theorem sumH_perm {xs ys : List Item} (h : xs.Perm ys) : sumH xs = sumH ys := by
  funext y; simp only [sumH, h.count_eq]

/-- Equal sums are equal counts. -/
theorem count_of_sumH {xs ys : List Item} (h : sumH xs = sumH ys) (x : Item) : xs.count x = ys.count x := by
  have := congrFun h x
  simp only [sumH] at this
  omega

theorem sumH_sub_nil (xs : List Item) : sumH xs - sumH [] = sumH xs := by
  funext y; simp only [Sum.sub_apply, sumH, List.count_nil]; omega

/-- The fingerprint of a range is the encoding of the sum and the count of the slice, when the range lies in the list. -/
theorem fpRange_eq (o : Oracle) (S : List Item) {a b : Nat} (hb : b ≤ S.length) :
    fpRange o S a b = o.enc (sumH ((S.drop a).take (b - a))) ((S.drop a).take (b - a)).length := by
  unfold fpRange
  congr 1
  simp only [List.length_take, List.length_drop]
  omega

/-- The fingerprint of a nodup list is its set: equal fingerprints of two nodup lists mean equal members. -/
theorem fp_inj {o : Oracle} (he : EncInj o) {xs ys : List Item} (hx : xs.Nodup) (hy : ys.Nodup)
    (h : o.enc (sumH xs) xs.length = o.enc (sumH ys) ys.length) : ∀ x, x ∈ xs ↔ x ∈ ys := by
  intro x
  have h' : o.enc (sumH xs - sumH []) xs.length = o.enc (sumH ys - sumH []) ys.length := by
    rw [sumH_sub_nil, sumH_sub_nil]; exact h
  have e := he _ _ _ _ _ _ h'
  rw [sumH_sub_nil, sumH_sub_nil] at e
  have := count_of_sumH e x
  rw [hx.count, hy.count] at this
  by_cases a : x ∈ xs <;> by_cases b : x ∈ ys <;> simp_all

/-- A list of the members of `A` that are not in `B`, and so on: the report is exact. -/
def ExactReport (A B here there : List Item) : Prop :=
  (∀ x, x ∈ here ↔ x ∈ B ∧ x ∉ A) ∧ (∀ x, x ∈ there ↔ x ∈ A ∧ x ∉ B) ∧ here.Nodup ∧ there.Nodup

/-- The arenas only ever hold items of the right side: `here` items of `B` that `A` lacks, `there` items of `A`, once each. -/
def Safe (A B here there : List Item) : Prop :=
  (∀ x ∈ here, x ∈ B ∧ x ∉ A) ∧ (∀ x ∈ there, x ∈ A) ∧ here.Nodup ∧ there.Nodup

/-- The final check detects every wrong result: if the fingerprint the initiator sends is the responder's, the
report is exact. -/
theorem check_detects_wrong {o : Oracle} {A B here there : List Item} (he : EncInj o)
    (hA : A.Nodup) (hB : B.Nodup) (hs : Safe A B here there)
    (h : checkFp o A A.length here there = o.enc (sumH B) B.length) : ExactReport A B here there := by
  obtain ⟨h1, h2, hn1, hn2⟩ := hs
  have hc : o.enc (sumH (A ++ here) - sumH there) (A.length + here.length - there.length) =
      o.enc (sumH B - sumH []) B.length := by
    rw [sumH_sub_nil, sumH_append]; simpa [checkFp] using h
  have hsum := he _ _ _ _ _ _ hc
  have par : ∀ x, A.count x + here.count x = B.count x + there.count x := by
    intro x
    have := congrFun hsum x
    simp only [sumH_append, Sum.add_apply, Sum.sub_apply, sumH, List.count_nil] at this
    omega
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
    simp [hxA, hB', ht, hh, List.count_eq_zero.mpr, hn2.count] at this
  · have hxA := hx.1; have hxB := hx.2
    have := par x
    rw [hA.count, hB.count] at this
    by_cases hh : x ∈ here
    · exact absurd (h1 x hh).1 hxB
    · by_cases ht : x ∈ there
      · exact ht
      · simp [hxA, hxB, ht, hh, List.count_eq_zero.mpr] at this

/-- An exact report passes the final check (no assumption on the hash: the two sums are equal). -/
theorem exact_passes_check (o : Oracle) {A B here there : List Item}
    (hA : A.Nodup) (hB : B.Nodup) (hx : ExactReport A B here there) :
    checkFp o A A.length here there = o.enc (sumH B) B.length := by
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
  have hsum : sumH A + sumH here - sumH there = sumH B := by
    rw [sumH_perm pA, sumH_perm pB, sumH_perm p1, sumH_perm p2, sumH_append, sumH_append, sumH_perm pI]
    funext y
    simp only [Sum.add_apply, Sum.sub_apply]
    omega
  have hlen : A.length + here.length - there.length = B.length := by
    have e1 := pA.length_eq; have e2 := pB.length_eq; have e3 := p1.length_eq; have e4 := p2.length_eq
    have e5 := pI.length_eq
    simp only [List.length_append] at e1 e2
    omega
  simp only [checkFp, List.drop_zero, List.take_length]
  rw [hsum, hlen]

/-! ## `EncInj` is not vacuous -/

/-- An injective code of a list of numbers (`f` injective on the entries): each entry is a power of two times an odd
number, the odd number carrying the code of the rest. -/
def codeL {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: l => 2 ^ f a * (2 * codeL f l + 1)

theorem two_pow_succ_mul (k m : Nat) : 2 ^ (k + 1) * (2 * m + 1) = 2 * (2 ^ k * (2 * m + 1)) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]

theorem two_pow_odd_inj : ∀ (a b m n : Nat), 2 ^ a * (2 * m + 1) = 2 ^ b * (2 * n + 1) → a = b ∧ m = n
  | 0, 0, m, n, h => by simp at h; omega
  | 0, k + 1, m, n, h => by rw [two_pow_succ_mul] at h; simp at h; omega
  | k + 1, 0, m, n, h => by rw [two_pow_succ_mul] at h; simp at h; omega
  | k + 1, j + 1, m, n, h => by
    rw [two_pow_succ_mul, two_pow_succ_mul] at h
    have := two_pow_odd_inj k j m n (by omega)
    omega

theorem codeL_inj {α : Type} (f : α → Nat) (hf : ∀ a b, f a = f b → a = b) :
    ∀ l l' : List α, codeL f l = codeL f l' → l = l'
  | [], [], _ => rfl
  | [], b :: l', h => by
    have : 0 < 2 ^ f b := Nat.two_pow_pos _
    have : 0 < 2 ^ f b * (2 * codeL f l' + 1) := Nat.mul_pos this (by omega)
    simp only [codeL] at h; omega
  | a :: l, [], h => by
    have : 0 < 2 ^ f a := Nat.two_pow_pos _
    have : 0 < 2 ^ f a * (2 * codeL f l + 1) := Nat.mul_pos this (by omega)
    simp only [codeL] at h; omega
  | a :: l, b :: l', h => by
    obtain ⟨h1, h2⟩ := two_pow_odd_inj _ _ _ _ h
    rw [hf a b h1, codeL_inj f hf l l' (by omega)]

open Classical in
/-- A list difference with the given sum, when there is one. -/
noncomputable def reprOf (s : Sum) : List Item × List Item :=
  if h : ∃ p : List Item × List Item, s = sumH p.1 - sumH p.2 then Classical.choose h else ([], [])

theorem reprOf_spec (P N : List Item) : sumH P - sumH N = sumH (reprOf (sumH P - sumH N)).1 - sumH (reprOf (sumH P - sumH N)).2 := by
  have h : ∃ p : List Item × List Item, sumH P - sumH N = sumH p.1 - sumH p.2 := ⟨(P, N), rfl⟩
  simp only [reprOf, h, ↓reduceDIte]
  exact Classical.choose_spec h

/-- Some oracle satisfies `EncInj`: encode the canonical pair of lists of a sum with an injective code of lists of
lists of numbers. (Its outputs are unbounded; a 256-bit output cannot be injective on all the sums of lists, so the real
hash meets `EncInj` as a statement about the sums of one session, with the bounds stated in its doc comment.) -/
theorem encInj_exists : ∃ o : Oracle, EncInj o := by
  let c1 : Item → Nat := codeL id
  let c2 : List Item → Nat := codeL c1
  let c3 : List (List Item) → Nat := codeL c2
  have i1 : ∀ a b, c1 a = c1 b → a = b := fun a b h => codeL_inj id (fun _ _ h => h) a b h
  have i2 : ∀ a b, c2 a = c2 b → a = b := fun a b h => codeL_inj c1 i1 a b h
  have i3 : ∀ a b, c3 a = c3 b → a = b := fun a b h => codeL_inj c2 i2 a b h
  refine ⟨⟨fun s _ => c3 [(reprOf s).1, (reprOf s).2], fun _ => 0⟩, fun P N P' N' c c' h => ?_⟩
  have := i3 _ _ h
  simp only [List.cons.injEq, and_true] at this
  rw [reprOf_spec P N, reprOf_spec P' N', this.1, this.2]

end Pinc.Reconcile
