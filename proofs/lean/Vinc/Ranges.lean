import Vinc.PartitionPoint

/-!
# Verified ranges

A model of `vinc-dag/src/ranges.rs`: a sorted list of disjoint half-open intervals `(start, end)`, the fixed
capacity set `VerifiedRanges<N>` and the unbounded `VerifiedRangesVec`.

Offsets are `Nat`. The code uses `u64`; every comparison, `min`, `max` and subtraction below is the same on both
as long as the values are `u64`s, and `coveredLen_eq` shows the saturating add of `covered_len` never saturates.
The live slice `items[..len]` is the list; the in-place `copy_within` plus slot assignment of the array insert
and the `Vec::splice` of the vector insert both produce `take from ++ merged :: drop to`.
-/

set_option linter.unusedVariables false

namespace Vinc.Ranges
open Vinc.PP

/-- A half-open interval `[start, end)`. -/
abbrev Interval := Nat × Nat

/-- Where an inserted range lands: it replaces `fromIx..toIx` with `merged`. -/
structure Plan where
  fromIx : Nat
  toIx : Nat
  merged : Interval

/-- `plan`: two `partition_point`s and the merged interval. -/
def plan (items : List Interval) (r : Interval) : Plan :=
  let fromIx := partitionPoint (fun iv => decide (iv.2 < r.1)) items
  let toIx := partitionPoint (fun iv => decide (iv.1 ≤ r.2)) items
  let start := match items[fromIx]? with
    | some iv => min iv.1 r.1
    | none => r.1
  let stop := match toIx with
    | 0 => r.2
    | t + 1 => match items[t]? with
      | some iv => max iv.2 r.2
      | none => r.2
  let merged := if fromIx < toIx then (start, stop) else (r.1, r.2)
  { fromIx, toIx, merged }

/-- The new live slice after replacing `fromIx..toIx` by `merged`. -/
def splice (items : List Interval) (p : Plan) : List Interval :=
  items.take p.fromIx ++ p.merged :: items.drop p.toIx

/-- `VerifiedRangesVec::insert`. -/
def insertVec (items : List Interval) (r : Interval) : List Interval :=
  if r.1 ≥ r.2 then items else splice items (plan items r)

/-- `VerifiedRanges<N>::insert`: `none` is `Err(CapacityError)`, with the set unchanged. -/
def insertFixed (cap : Nat) (items : List Interval) (r : Interval) : Option (List Interval) :=
  if r.1 ≥ r.2 then some items
  else
    let p := plan items r
    let newLen := items.length - (p.toIx - p.fromIx) + 1
    if newLen > cap then none else some (splice items p)

/-- The state after `insert` on a `&mut self`: unchanged on a capacity failure. -/
def insertState (cap : Nat) (items : List Interval) (r : Interval) : List Interval :=
  (insertFixed cap items r).getD items

/-- `find`: the interval containing `offset`. -/
def find (items : List Interval) (offset : Nat) : Option Interval :=
  let at_ := partitionPoint (fun iv => decide (iv.2 ≤ offset)) items
  match items[at_]? with
  | some iv => if iv.1 ≤ offset then some iv else none
  | none => none

/-- `contains`. -/
def contains (items : List Interval) (offset : Nat) : Bool := (find items offset).isSome

/-- `contains_range`. -/
def containsRange (items : List Interval) (r : Interval) : Bool :=
  decide (r.1 ≥ r.2) || match find items r.1 with
    | some iv => decide (iv.2 ≥ r.2)
    | none => false

/-- `u64::MAX`. -/
def u64Max : Nat := 2 ^ 64 - 1

/-- `acc.saturating_add(x)`. -/
def satAdd (a b : Nat) : Nat := min (a + b) u64Max

/-- `covered_len`. -/
def coveredLen (items : List Interval) : Nat :=
  items.foldl (fun acc iv => satAdd acc (iv.2 - iv.1)) 0

/-! ## The canonical invariant -/

/-- Each start is below its end and neighbours are strictly separated: `prev.end < next.start`. -/
def Canon : List Interval → Prop
  | [] => True
  | [a] => a.1 < a.2
  | a :: b :: t => a.1 < a.2 ∧ a.2 < b.1 ∧ Canon (b :: t)

/-- Every interval is valid and every earlier interval ends before every later one starts. -/
def Sound (l : List Interval) : Prop :=
  (∀ iv ∈ l, iv.1 < iv.2) ∧ l.Pairwise (fun a b => a.2 < b.1)

theorem canon_iff (l : List Interval) : Canon l ↔ Sound l := by
  induction l with
  | nil => simp [Canon, Sound]
  | cons a t ih =>
    cases t with
    | nil => simp [Canon, Sound]
    | cons b t =>
      constructor
      · rintro ⟨h1, h2, h3⟩
        obtain ⟨hv, hp⟩ := ih.1 h3
        refine ⟨?_, List.pairwise_cons.2 ⟨?_, hp⟩⟩
        · intro iv hiv
          rcases List.mem_cons.1 hiv with rfl | h
          · exact h1
          · exact hv iv h
        · intro c hc
          rcases List.mem_cons.1 hc with rfl | h
          · exact h2
          · have h4 := hv b (List.mem_cons_self ..)
            have h5 := (List.pairwise_cons.1 hp).1 c h
            omega
      · rintro ⟨hv, hp⟩
        have hp' := List.pairwise_cons.1 hp
        refine ⟨hv a (List.mem_cons_self ..), hp'.1 b (List.mem_cons_self ..), ih.2 ⟨?_, hp'.2⟩⟩
        intro iv hiv
        exact hv iv (List.mem_cons_of_mem _ hiv)

theorem sound_nil : Sound [] := by simp [Sound]


/-! ## Index facts -/

theorem mem_take_iff {α : Type} (l : List α) (f : Nat) (a : α) :
    a ∈ l.take f ↔ ∃ j, ∃ h : j < l.length, j < f ∧ l[j] = a := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [List.length_take] at hj
    exact ⟨j, by omega, by omega, by simp⟩
  · rintro ⟨j, hj, hf, rfl⟩
    exact ⟨j, by rw [List.length_take]; omega, by simp⟩

theorem mem_drop_iff {α : Type} (l : List α) (t : Nat) (a : α) :
    a ∈ l.drop t ↔ ∃ j, ∃ h : j < l.length, t ≤ j ∧ l[j] = a := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [List.length_drop] at hj
    exact ⟨t + j, by omega, by omega, by simp⟩
  · rintro ⟨j, hj, ht, rfl⟩
    exact ⟨j - t, by rw [List.length_drop]; omega, by simp [show t + (j - t) = j by omega]⟩

theorem sound_lt {l : List Interval} (h : Sound l) {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (hij : i < j) : l[i].2 < l[j].1 :=
  List.pairwise_iff_getElem.1 h.2 i j hi hj hij

theorem sound_valid {l : List Interval} (h : Sound l) {i : Nat} (hi : i < l.length) : l[i].1 < l[i].2 :=
  h.1 _ (List.getElem_mem hi)

theorem sound_start_le {l : List Interval} (h : Sound l) {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (hij : i ≤ j) : l[i].1 ≤ l[j].1 := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact Nat.le_refl _
  · have := sound_lt h hi hj hlt; have := sound_valid h hi; omega

theorem sound_end_le {l : List Interval} (h : Sound l) {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (hij : i ≤ j) : l[i].2 ≤ l[j].2 := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact Nat.le_refl _
  · have := sound_lt h hi hj hlt; have := sound_valid h hj; omega

theorem part_end_lt {l : List Interval} (h : Sound l) (s : Nat) :
    Partitioned (fun iv : Interval => decide (iv.2 < s)) l := by
  intro i j hi hj hij hp
  have := sound_lt h hi hj hij; have := sound_valid h hj
  simp at hp ⊢; omega

theorem part_start_le {l : List Interval} (h : Sound l) (e : Nat) :
    Partitioned (fun iv : Interval => decide (iv.1 ≤ e)) l := by
  intro i j hi hj hij hp
  have := sound_lt h hi hj hij; have := sound_valid h hi
  simp at hp ⊢; omega

theorem part_end_le {l : List Interval} (h : Sound l) (x : Nat) :
    Partitioned (fun iv : Interval => decide (iv.2 ≤ x)) l := by
  intro i j hi hj hij hp
  have := sound_lt h hi hj hij; have := sound_valid h hj
  simp at hp ⊢; omega

/-! ## Coverage -/

/-- `x` lies in one of the intervals. -/
def Covers (l : List Interval) (x : Nat) : Prop := ∃ iv ∈ l, iv.1 ≤ x ∧ x < iv.2

/-- `x` lies in one of the intervals with index in `[a, b)`. -/
def CI (l : List Interval) (a b x : Nat) : Prop :=
  ∃ j, ∃ h : j < l.length, a ≤ j ∧ j < b ∧ l[j].1 ≤ x ∧ x < l[j].2

theorem covers_take (l : List Interval) (f x : Nat) : Covers (l.take f) x ↔ CI l 0 f x := by
  unfold Covers CI
  constructor
  · rintro ⟨iv, hiv, h1, h2⟩
    obtain ⟨j, hj, hf, rfl⟩ := (mem_take_iff l f iv).1 hiv
    exact ⟨j, hj, by omega, hf, h1, h2⟩
  · rintro ⟨j, hj, _, hf, h1, h2⟩
    exact ⟨l[j], (mem_take_iff l f _).2 ⟨j, hj, hf, rfl⟩, h1, h2⟩

theorem covers_drop (l : List Interval) (t x : Nat) : Covers (l.drop t) x ↔ CI l t l.length x := by
  unfold Covers CI
  constructor
  · rintro ⟨iv, hiv, h1, h2⟩
    obtain ⟨j, hj, ht, rfl⟩ := (mem_drop_iff l t iv).1 hiv
    exact ⟨j, hj, ht, hj, h1, h2⟩
  · rintro ⟨j, hj, ht, _, h1, h2⟩
    exact ⟨l[j], (mem_drop_iff l t _).2 ⟨j, hj, ht, rfl⟩, h1, h2⟩

theorem covers_ci (l : List Interval) (x : Nat) : Covers l x ↔ CI l 0 l.length x := by
  have := covers_drop l 0 x
  simpa using this

theorem ci_split (l : List Interval) (f t x : Nat) (h1 : f ≤ t) (h2 : t ≤ l.length) :
    CI l 0 l.length x ↔ CI l 0 f x ∨ CI l f t x ∨ CI l t l.length x := by
  unfold CI
  constructor
  · rintro ⟨j, hj, _, _, h3, h4⟩
    by_cases a : j < f
    · exact Or.inl ⟨j, hj, by omega, a, h3, h4⟩
    · by_cases b : j < t
      · exact Or.inr (Or.inl ⟨j, hj, by omega, b, h3, h4⟩)
      · exact Or.inr (Or.inr ⟨j, hj, by omega, hj, h3, h4⟩)
  · rintro (⟨j, hj, _, _, h3, h4⟩ | ⟨j, hj, _, _, h3, h4⟩ | ⟨j, hj, _, _, h3, h4⟩)
    · exact ⟨j, hj, by omega, hj, h3, h4⟩
    · exact ⟨j, hj, by omega, hj, h3, h4⟩
    · exact ⟨j, hj, by omega, hj, h3, h4⟩

theorem covers_splice (A B : List Interval) (m : Interval) (x : Nat) :
    Covers (A ++ m :: B) x ↔ Covers A x ∨ (m.1 ≤ x ∧ x < m.2) ∨ Covers B x := by
  unfold Covers
  simp only [List.mem_append, List.mem_cons]
  constructor
  · rintro ⟨iv, ((h | h | h)), h1, h2⟩
    · exact Or.inl ⟨iv, h, h1, h2⟩
    · subst h; exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨iv, h, h1, h2⟩)
  · rintro (⟨iv, h, h1, h2⟩ | ⟨h1, h2⟩ | ⟨iv, h, h1, h2⟩)
    · exact ⟨iv, Or.inl h, h1, h2⟩
    · exact ⟨m, Or.inr (Or.inl rfl), h1, h2⟩
    · exact ⟨iv, Or.inr (Or.inr h), h1, h2⟩

/-! ## What `plan` computes -/

theorem plan_spec (l : List Interval) (hl : Sound l) (r : Interval) (hr : r.1 < r.2) :
    ∃ f t, (plan l r).fromIx = f ∧ (plan l r).toIx = t ∧ f ≤ t ∧ t ≤ l.length ∧
      FirstFalse (fun iv : Interval => decide (iv.2 < r.1)) l f ∧
      FirstFalse (fun iv : Interval => decide (iv.1 ≤ r.2)) l t ∧
      (f < t → ∃ a b, l[f]? = some a ∧ l[t - 1]? = some b ∧
        (plan l r).merged = (min a.1 r.1, max b.2 r.2)) ∧
      (¬ f < t → (plan l r).merged = r) := by
  obtain ⟨f, hf⟩ := exists_firstFalse _ l (part_end_lt hl r.1)
  obtain ⟨t, ht⟩ := exists_firstFalse _ l (part_start_le hl r.2)
  have e1 : (plan l r).fromIx = f := partitionPoint_eq _ l f hf
  have e2 : (plan l r).toIx = t := partitionPoint_eq _ l t ht
  have e1' : partitionPoint (fun iv : Interval => decide (iv.2 < r.1)) l = f := e1
  have e2' : partitionPoint (fun iv : Interval => decide (iv.1 ≤ r.2)) l = t := e2
  have hft : f ≤ t := by
    refine Classical.byContradiction fun hc => ?_
    have hlt : t < l.length := by have := hf.le; omega
    have a := hf.pre t hlt (by omega)
    have b := ht.suf t hlt (Nat.le_refl _)
    have := sound_valid hl hlt
    simp at a b; omega
  have htl := ht.le
  refine ⟨f, t, e1, e2, hft, htl, hf, ht, ?_, ?_⟩
  · intro hlt
    have hfl : f < l.length := by omega
    have htl' : t - 1 < l.length := by omega
    refine ⟨l[f], l[t - 1], List.getElem?_eq_getElem hfl, List.getElem?_eq_getElem htl', ?_⟩
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    simp only [plan, e1', e2', hlt, ite_true, List.getElem?_eq_getElem hfl]
    simp [List.getElem?_eq_getElem (show t' < l.length by omega)]
  · intro hn
    simp only [plan, e1', e2', hn, ite_false]


/-! ## Insert: coverage -/

section
variable {l : List Interval} {r : Interval} {f t : Nat}

theorem cls_a (hf : FirstFalse (fun iv : Interval => decide (iv.2 < r.1)) l f) {j : Nat}
    (hj : j < l.length) (h : j < f) : l[j].2 < r.1 := by
  have := hf.pre j hj h; simpa using this

theorem cls_m1 (hf : FirstFalse (fun iv : Interval => decide (iv.2 < r.1)) l f) {j : Nat}
    (hj : j < l.length) (h : f ≤ j) : r.1 ≤ l[j].2 := by
  have := hf.suf j hj h; simp at this; omega

theorem cls_m2 (ht : FirstFalse (fun iv : Interval => decide (iv.1 ≤ r.2)) l t) {j : Nat}
    (hj : j < l.length) (h : j < t) : l[j].1 ≤ r.2 := by
  have := ht.pre j hj h; simpa using this

theorem cls_b (ht : FirstFalse (fun iv : Interval => decide (iv.1 ≤ r.2)) l t) {j : Nat}
    (hj : j < l.length) (h : t ≤ j) : r.2 < l[j].1 := by
  have := ht.suf j hj h; simp at this; omega

end

theorem merged_iff (l : List Interval) (hl : Sound l) (r : Interval) (f t : Nat)
    (hf : FirstFalse (fun iv : Interval => decide (iv.2 < r.1)) l f)
    (ht : FirstFalse (fun iv : Interval => decide (iv.1 ≤ r.2)) l t)
    (hlt : f < t) (a b : Interval) (ha : l[f]? = some a) (hb : l[t - 1]? = some b) (x : Nat) :
    (min a.1 r.1 ≤ x ∧ x < max b.2 r.2) ↔ CI l f t x ∨ (r.1 ≤ x ∧ x < r.2) := by
  have htl := ht.le
  have hfl : f < l.length := by omega
  have htl' : t - 1 < l.length := by omega
  rw [List.getElem?_eq_getElem hfl] at ha
  rw [List.getElem?_eq_getElem htl'] at hb
  have ha' : a = l[f] := (Option.some.inj ha).symm
  have hb' : b = l[t - 1] := (Option.some.inj hb).symm
  subst ha' hb'
  constructor
  · rintro ⟨h1, h2⟩
    by_cases c1 : x < r.1
    · have := cls_m1 hf hfl (Nat.le_refl _)
      exact Or.inl ⟨f, hfl, Nat.le_refl _, hlt, by omega, by omega⟩
    · by_cases c2 : x < r.2
      · exact Or.inr ⟨by omega, c2⟩
      · have := cls_m2 ht htl' (by omega)
        exact Or.inl ⟨t - 1, htl', by omega, by omega, by omega, by omega⟩
  · rintro (⟨j, hj, h1, h2, h3, h4⟩ | ⟨h1, h2⟩)
    · have := sound_start_le hl hfl hj h1
      have := sound_end_le hl hj htl' (by omega)
      omega
    · omega

theorem insertVec_covers (l : List Interval) (hl : Sound l) (r : Interval) (x : Nat) :
    Covers (insertVec l r) x ↔ Covers l x ∨ (r.1 ≤ x ∧ x < r.2) := by
  by_cases hr : r.1 ≥ r.2
  · simp only [insertVec, hr, ite_true]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · omega
  · have hr' : r.1 < r.2 := by omega
    obtain ⟨f, t, e1, e2, hft, htl, hf, ht, hm1, hm2⟩ := plan_spec l hl r hr'
    simp only [insertVec, hr, ite_false, splice, e1, e2]
    rw [covers_splice, covers_take, covers_drop, covers_ci, ci_split l f t x hft htl]
    by_cases hlt : f < t
    · obtain ⟨a, b, ha, hb, hm⟩ := hm1 hlt
      rw [hm]
      have := merged_iff l hl r f t hf ht hlt a b ha hb x
      simp only
      grind
    · rw [hm2 hlt]
      have : ¬ CI l f t x := by
        rintro ⟨j, _, h1, h2, _⟩; omega
      grind


/-! ## Insert: the canonical invariant and the length -/

theorem plan_props (l : List Interval) (hl : Sound l) (r : Interval) (hr : r.1 < r.2) :
    ∃ f t, (plan l r).fromIx = f ∧ (plan l r).toIx = t ∧ f ≤ t ∧ t ≤ l.length ∧
      (plan l r).merged.1 ≤ r.1 ∧ r.2 ≤ (plan l r).merged.2 ∧
      (∀ a ∈ l.take f, a.2 < (plan l r).merged.1) ∧ (∀ b ∈ l.drop t, (plan l r).merged.2 < b.1) := by
  obtain ⟨f, t, e1, e2, hft, htl, hf, ht, hm1, hm2⟩ := plan_spec l hl r hr
  refine ⟨f, t, e1, e2, hft, htl, ?_⟩
  by_cases hlt : f < t
  · obtain ⟨a, b, ha, hb, hm⟩ := hm1 hlt
    have hfl : f < l.length := by omega
    have htl' : t - 1 < l.length := by omega
    rw [List.getElem?_eq_getElem hfl] at ha
    rw [List.getElem?_eq_getElem htl'] at hb
    have ha' : a = l[f] := (Option.some.inj ha).symm
    have hb' : b = l[t - 1] := (Option.some.inj hb).symm
    subst ha' hb'
    rw [hm]
    refine ⟨by simp; omega, by simp; omega, ?_, ?_⟩
    · intro a' ha'
      obtain ⟨j, hj, hjf, rfl⟩ := (mem_take_iff l f a').1 ha'
      have := cls_a hf hj hjf
      have := sound_lt hl hj hfl hjf
      simp; omega
    · intro b' hb'
      obtain ⟨j, hj, htj, rfl⟩ := (mem_drop_iff l t b').1 hb'
      have := cls_b ht hj htj
      have := sound_lt hl htl' hj (by omega)
      simp; omega
  · rw [hm2 hlt]
    refine ⟨Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
    · intro a' ha'
      obtain ⟨j, hj, hjf, rfl⟩ := (mem_take_iff l f a').1 ha'
      exact cls_a hf hj hjf
    · intro b' hb'
      obtain ⟨j, hj, htj, rfl⟩ := (mem_drop_iff l t b').1 hb'
      exact cls_b ht hj htj

theorem insertVec_length (l : List Interval) (hl : Sound l) (r : Interval) (hr : r.1 < r.2) :
    (insertVec l r).length = l.length - ((plan l r).toIx - (plan l r).fromIx) + 1 := by
  obtain ⟨f, t, e1, e2, hft, htl, _⟩ := plan_props l hl r hr
  simp only [insertVec, show ¬ r.1 ≥ r.2 by omega, ite_false, splice, e1, e2, List.length_append,
    List.length_take, List.length_cons, List.length_drop]
  omega

/-- Insert preserves the canonical invariant. -/
theorem insertVec_sound (l : List Interval) (hl : Sound l) (r : Interval) : Sound (insertVec l r) := by
  by_cases hr : r.1 ≥ r.2
  · simpa [insertVec, hr] using hl
  · have hr' : r.1 < r.2 := by omega
    obtain ⟨f, t, e1, e2, hft, htl, hm1, hm2, hA, hB⟩ := plan_props l hl r hr'
    simp only [insertVec, hr, ite_false, splice, e1, e2]
    generalize (plan l r).merged = m at *
    have hAB : ∀ a ∈ l.take f, ∀ b ∈ l.drop t, a.2 < b.1 := by
      intro a ha b hb
      obtain ⟨i, hi, hif, rfl⟩ := (mem_take_iff l f a).1 ha
      obtain ⟨j, hj, htj, rfl⟩ := (mem_drop_iff l t b).1 hb
      exact sound_lt hl hi hj (by omega)
    refine ⟨?_, ?_⟩
    · intro iv hiv
      rcases List.mem_append.1 hiv with h | h
      · exact hl.1 iv (List.mem_of_mem_take h)
      · rcases List.mem_cons.1 h with rfl | h
        · omega
        · exact hl.1 iv (List.mem_of_mem_drop h)
    · refine List.pairwise_append.2 ⟨hl.2.sublist (List.take_sublist _ _),
        List.pairwise_cons.2 ⟨hB, hl.2.sublist (List.drop_sublist _ _)⟩, ?_⟩
      intro a ha y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hA a ha
      · exact hAB a ha y hy

/-- Insert into the fixed-capacity set: the result is `insertVec` unless it needs more than `cap` intervals. -/
theorem insertFixed_eq (cap : Nat) (l : List Interval) (hl : Sound l) (r : Interval) :
    insertFixed cap l r =
      if r.1 ≥ r.2 then some l
      else if (insertVec l r).length > cap then none else some (insertVec l r) := by
  by_cases hr : r.1 ≥ r.2
  · simp [insertFixed, hr]
  · have hr' : r.1 < r.2 := by omega
    have := insertVec_length l hl r hr'
    simp only [insertFixed, insertVec, hr, ite_false] at *
    simp [this]

/-- Failure happens iff the merged set would hold more than `cap` intervals. -/
theorem insertFixed_none_iff (cap : Nat) (l : List Interval) (hl : Sound l) (r : Interval) :
    insertFixed cap l r = none ↔ r.1 < r.2 ∧ cap < (insertVec l r).length := by
  rw [insertFixed_eq cap l hl r]
  by_cases hr : r.1 ≥ r.2
  · simp [hr]; omega
  · by_cases hc : (insertVec l r).length > cap
    · simp [hr, hc]; omega
    · simp [hr, hc]

/-- A failed insert changes nothing. -/
theorem insertState_of_none (cap : Nat) (l : List Interval) (r : Interval)
    (h : insertFixed cap l r = none) : insertState cap l r = l := by
  simp [insertState, h]

/-- A successful insert gives `insertVec`. -/
theorem insertState_of_some (cap : Nat) (l : List Interval) (hl : Sound l) (r : Interval)
    (h : insertFixed cap l r ≠ none) : insertState cap l r = insertVec l r := by
  rw [insertFixed_eq cap l hl r] at h
  rw [insertState, insertFixed_eq cap l hl r]
  by_cases hr : r.1 ≥ r.2
  · simp [hr, insertVec]
  · by_cases hc : (insertVec l r).length > cap
    · simp [hr, hc] at h
    · simp [hr, hc]

/-- The state after an insert keeps the canonical invariant and the capacity bound. -/
theorem insertState_inv (cap : Nat) (l : List Interval) (hl : Sound l) (hlen : l.length ≤ cap)
    (r : Interval) : Sound (insertState cap l r) ∧ (insertState cap l r).length ≤ cap := by
  by_cases h : insertFixed cap l r = none
  · rw [insertState_of_none cap l r h]; exact ⟨hl, hlen⟩
  · rw [insertState_of_some cap l hl r h]
    refine ⟨insertVec_sound l hl r, ?_⟩
    rw [insertFixed_eq cap l hl r] at h
    by_cases hr : r.1 ≥ r.2
    · simpa [insertVec, hr] using hlen
    · by_cases hc : (insertVec l r).length > cap
      · simp [hr, hc] at h
      · omega

/-- On success the coverage is the old coverage plus the range. -/
theorem insertFixed_covers (cap : Nat) (l : List Interval) (hl : Sound l) (r : Interval) (l' : List Interval)
    (h : insertFixed cap l r = some l') (x : Nat) :
    Covers l' x ↔ Covers l x ∨ (r.1 ≤ x ∧ x < r.2) := by
  have : insertState cap l r = l' := by simp [insertState, h]
  rw [insertState_of_some cap l hl r (by simp [h])] at this
  rw [← this]
  exact insertVec_covers l hl r x

/-- Monotonicity: a covered offset stays covered by an insert, also when the insert fails. -/
theorem insertState_mono (cap : Nat) (l : List Interval) (hl : Sound l) (r : Interval) (x : Nat)
    (h : Covers l x) : Covers (insertState cap l r) x := by
  by_cases hn : insertFixed cap l r = none
  · rw [insertState_of_none cap l r hn]; exact h
  · rw [insertState_of_some cap l hl r hn, insertVec_covers l hl r]
    exact Or.inl h

/-- The sets reachable from the empty set by inserts into a set of capacity `cap`. -/
inductive Reach (cap : Nat) : List Interval → Prop where
  | empty : Reach cap []
  | step {l : List Interval} (r : Interval) : Reach cap l → Reach cap (insertState cap l r)

/-- Every reachable set is canonical and within capacity. -/
theorem reach_inv {cap : Nat} {l : List Interval} (h : Reach cap l) : Canon l ∧ l.length ≤ cap := by
  have : Sound l ∧ l.length ≤ cap := by
    induction h with
    | empty => exact ⟨sound_nil, by simp⟩
    | step r _ ih => exact insertState_inv cap _ ih.1 ih.2 r
  exact ⟨(canon_iff l).2 this.1, this.2⟩

/-- Every reachable set only grows: a covered offset stays covered by any later reachable set. -/
theorem reach_mono {cap : Nat} {l : List Interval} (h : Reach cap l) (r : Interval) (x : Nat)
    (hx : Covers l x) : Covers (insertState cap l r) x := by
  have : Sound l := by
    have := reach_inv h
    exact (canon_iff l).1 this.1
  exact insertState_mono cap l this r x hx

/-! ## Queries -/

theorem sound_pair {l : List Interval} (h : Sound l) {a b : Interval} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    a.2 < b.1 ∨ b.2 < a.1 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hb
  rcases Nat.lt_trichotomy i j with c | c | c
  · exact Or.inl (sound_lt h hi hj c)
  · subst c; exact absurd rfl hne
  · exact Or.inr (sound_lt h hj hi c)

theorem find_spec (l : List Interval) (hl : Sound l) (x : Nat) (iv : Interval) :
    find l x = some iv ↔ iv ∈ l ∧ iv.1 ≤ x ∧ x < iv.2 := by
  obtain ⟨k, hk⟩ := exists_firstFalse _ l (part_end_le hl x)
  have ek : partitionPoint (fun iv : Interval => decide (iv.2 ≤ x)) l = k := partitionPoint_eq _ l k hk
  unfold find
  simp only [ek]
  by_cases hkl : k < l.length
  · rw [List.getElem?_eq_getElem hkl]
    have hx : x < l[k].2 := by have := hk.suf k hkl (Nat.le_refl _); simp at this; omega
    constructor
    · intro h
      by_cases hs : l[k].1 ≤ x
      · simp only [hs, ite_true, Option.some.injEq] at h
        subst h
        exact ⟨List.getElem_mem hkl, hs, hx⟩
      · simp [hs] at h
    · rintro ⟨hm, h1, h2⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hm
      have hjk : k ≤ j := by
        refine Classical.byContradiction fun hc => ?_
        have := hk.pre j hj (by omega); simp at this; omega
      have : j = k := by
        refine Classical.byContradiction fun hc => ?_
        have := sound_lt hl hkl hj (by omega); omega
      subst this
      simp [h1]
  · rw [List.getElem?_eq_none (by omega)]
    constructor
    · intro h; simp at h
    · rintro ⟨hm, h1, h2⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hm
      have := hk.pre j hj (by omega); simp at this; omega

theorem contains_iff (l : List Interval) (hl : Sound l) (x : Nat) : contains l x = true ↔ Covers l x := by
  unfold contains
  cases h : find l x with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨iv, hm, h1, h2⟩
    have := (find_spec l hl x iv).2 ⟨hm, h1, h2⟩
    rw [h] at this; simp at this
  | some iv =>
    simp only [Option.isSome_some, true_iff]
    have := (find_spec l hl x iv).1 h
    exact ⟨iv, this.1, this.2.1, this.2.2⟩

theorem containsRange_iff (l : List Interval) (hl : Sound l) (r : Interval) :
    containsRange l r = true ↔ ∀ x, r.1 ≤ x → x < r.2 → Covers l x := by
  unfold containsRange
  by_cases hr : r.1 ≥ r.2
  · simp only [hr, decide_true, Bool.true_or, true_iff]; intro x h1 h2; omega
  · have hr' : r.1 < r.2 := by omega
    simp only [hr, decide_false, Bool.false_or]
    cases h : find l r.1 with
    | none =>
      simp only [Bool.false_eq_true, false_iff]
      intro hall
      obtain ⟨iv, hm, h1, h2⟩ := hall r.1 (Nat.le_refl _) hr'
      have := (find_spec l hl r.1 iv).2 ⟨hm, h1, h2⟩
      rw [h] at this; simp at this
    | some iv =>
      have hiv := (find_spec l hl r.1 iv).1 h
      simp only [decide_eq_true_eq]
      constructor
      · intro h2 x hx1 hx2
        exact ⟨iv, hiv.1, by omega, by omega⟩
      · intro hall
        refine Classical.byContradiction fun hc => ?_
        obtain ⟨iv', hm', h1', h2'⟩ := hall iv.2 (by omega) (by omega)
        have hne : iv' ≠ iv := by intro e; subst e; omega
        rcases sound_pair hl hm' hiv.1 hne with c | c <;> omega

/-! ## `covered_len` -/

open Classical in
/-- How many offsets below `M` satisfy `P`. -/
noncomputable def cnt (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | M + 1 => cnt P M + if P M then 1 else 0

theorem cnt_congr (P Q : Nat → Prop) (M : Nat) (h : ∀ x, x < M → (P x ↔ Q x)) : cnt P M = cnt Q M := by
  induction M with
  | zero => rfl
  | succ M ih =>
    simp only [cnt]
    rw [ih (fun x hx => h x (by omega))]
    have := h M (by omega)
    by_cases hp : P M
    · simp [hp, this.1 hp]
    · have hq : ¬ Q M := fun q => hp (this.2 q)
      simp [hp, hq]

theorem cnt_or (P Q : Nat → Prop) (M : Nat) (h : ∀ x, x < M → ¬ (P x ∧ Q x)) :
    cnt (fun x => P x ∨ Q x) M = cnt P M + cnt Q M := by
  induction M with
  | zero => rfl
  | succ M ih =>
    simp only [cnt]
    rw [ih (fun x hx => h x (by omega))]
    have := h M (by omega)
    by_cases hp : P M <;> by_cases hq : Q M <;> simp_all <;> omega

theorem cnt_interval (a b M : Nat) : cnt (fun x => a ≤ x ∧ x < b) M = min b M - a := by
  induction M with
  | zero => simp [cnt]
  | succ M ih =>
    simp only [cnt, ih]
    by_cases h1 : a ≤ M <;> by_cases h2 : M < b <;> simp [h1, h2] <;> omega

theorem cnt_le (P : Nat → Prop) (M : Nat) : cnt P M ≤ M := by
  induction M with
  | zero => simp [cnt]
  | succ M ih => simp only [cnt]; split <;> omega

/-- The sum of interval lengths. -/
def lenSum (l : List Interval) : Nat := (l.map fun iv => iv.2 - iv.1).sum

theorem lenSum_eq_cnt (l : List Interval) (hl : Sound l) (M : Nat) (hM : ∀ iv ∈ l, iv.2 ≤ M) :
    lenSum l = cnt (Covers l) M := by
  induction l with
  | nil =>
    have : cnt (Covers []) M = 0 := by
      have : cnt (Covers []) M = cnt (fun _ => False) M := by
        apply cnt_congr; intro x _; simp [Covers]
      rw [this]
      clear this
      induction M with
      | zero => rfl
      | succ M ih => simp only [cnt]; simp [ih]
    simp [lenSum, this]
  | cons iv t ih =>
    have hp := List.pairwise_cons.1 hl.2
    have hts : Sound t := ⟨fun a ha => hl.1 a (List.mem_cons_of_mem _ ha), hp.2⟩
    have hv := hl.1 iv (List.mem_cons_self ..)
    have hM' := hM iv (List.mem_cons_self ..)
    have e1 : cnt (Covers (iv :: t)) M =
        cnt (fun x => (iv.1 ≤ x ∧ x < iv.2) ∨ Covers t x) M := by
      apply cnt_congr; intro x _
      simp only [Covers, List.mem_cons]
      constructor
      · rintro ⟨a, (rfl | h), h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨a, h, h1, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨a, h, h1, h2⟩)
        · exact ⟨iv, Or.inl rfl, h1, h2⟩
        · exact ⟨a, Or.inr h, h1, h2⟩
    rw [e1, cnt_or _ _ M, cnt_interval, ← ih hts (fun a ha => hM a (List.mem_cons_of_mem _ ha))]
    · simp only [lenSum, List.map_cons, List.sum_cons]
      omega
    · intro x _ ⟨⟨h1, h2⟩, a, ha, h3, h4⟩
      have := hp.1 a ha
      have := hl.1 a (List.mem_cons_of_mem _ ha)
      omega

theorem foldl_sat (l : List Interval) :
    ∀ acc, acc ≤ u64Max → l.foldl (fun acc iv => satAdd acc (iv.2 - iv.1)) acc = min (acc + lenSum l) u64Max := by
  induction l with
  | nil => intro acc h; simp [lenSum]; omega
  | cons iv t ih =>
    intro acc h
    simp only [List.foldl_cons]
    have h2 : satAdd acc (iv.2 - iv.1) ≤ u64Max := by unfold satAdd; omega
    rw [ih _ h2]
    simp only [satAdd, lenSum, List.map_cons, List.sum_cons]
    unfold lenSum at *
    omega

/-- `covered_len` is the number of covered offsets (below `u64::MAX`, which no interval can reach), and the
saturating add never saturates. -/
theorem coveredLen_eq (l : List Interval) (hl : Sound l) (hM : ∀ iv ∈ l, iv.2 ≤ u64Max) :
    coveredLen l = cnt (Covers l) u64Max ∧ coveredLen l ≤ u64Max := by
  have h1 := lenSum_eq_cnt l hl u64Max hM
  have h2 := cnt_le (Covers l) u64Max
  have : coveredLen l = lenSum l := by
    unfold coveredLen
    rw [foldl_sat l 0 (by unfold u64Max; omega)]
    omega
  exact ⟨by omega, by omega⟩

end Vinc.Ranges

#audit_axioms Vinc.Ranges.canon_iff
#audit_axioms Vinc.Ranges.insertVec_sound
#audit_axioms Vinc.Ranges.insertVec_covers
#audit_axioms Vinc.Ranges.insertFixed_none_iff
#audit_axioms Vinc.Ranges.insertState_inv
#audit_axioms Vinc.Ranges.insertState_mono
#audit_axioms Vinc.Ranges.reach_inv
#audit_axioms Vinc.Ranges.contains_iff
#audit_axioms Vinc.Ranges.containsRange_iff
#audit_axioms Vinc.Ranges.coveredLen_eq
