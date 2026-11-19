import Pinc.ValuesPlanFrames

/-!
# `Plan::new` against the reference

`Plan::new(len, spans)` of `crates/pinc-values/src/plan.rs` on `Nat` with every `u64` operation explicit
(`checked_add`, `checked_mul`, `saturating_mul`, `div_ceil`, the `2^62 - 1` limit): `planNew`.

`planNew_eq_spec` proves that it equals `specNew`, the specification written with exact arithmetic over the
reference: a span is dropped when empty, refused (`OutOfBounds`) when it runs past the value, rounded out to whole
groups `[a, b)`, sized as the sum of the bytes of the reference frames of the concatenated range encodings
(`refSize`), and refused (`TooLong`) when the response would pass `2^62 - 1` bytes; the start of a range is the sum
of the sizes of the ranges before it. Equality holds as values of `Except`, so the error kind agrees too: no
overflow happens in the code and no case is refused or accepted differently.

The closed form `(b - a) 16 + (min(len, b G) - a G) + 64 parents_in(0, n, a, b)` for the size of a range, which
the code computes, is `refSize_eq`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Pinc.ValuesPlan
open Pinc.Layout Pinc.Encode

/-- `GROUP_LOG`. -/
abbrev lg : Nat := 4
/-- `GROUP`: 16 KiB. -/
abbrev G : Nat := groupLen lg
theorem G_eq : G = 16384 := by decide
/-- The size of a GROUP header (`GROUP_HDR`). -/
abbrev HDR : Nat := 16
/-- The size of a parent pair (`PARENT_LEN`). -/
abbrev PARL : Nat := 64
/-- The largest stream offset, `2^62 - 1`. -/
def MAXS : Nat := 2 ^ 62 - 1
/-- `MAX_REQ_RANGES`. -/
abbrev MAXR : Nat := 255

theorem G_pos : 0 < G := groupLen_pos lg

/-- The bytes of a reference frame: header, the pairs it opens, the group. -/
def fbytes (f : Frame) : Nat := HDR + f.1.length * PARL + f.2.2

/-- The frames of the encoding of the groups `[a, b)` of a value of `len` bytes (the reference). -/
def refFrames (len a b : Nat) : List Frame := (fs (ref len lg a b 0 (groups len lg) 0) []).1

/-- The length in bytes of the framed encoding of the groups `[a, b)`. -/
def refSize (len a b : Nat) : Nat := ((refFrames len a b).map fbytes).sum

theorem sumTo_add (f g : Nat → Nat) (k : Nat) : sumTo (fun j => f j + g j) k = sumTo f k + sumTo g k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [sumTo]; omega

theorem sumTo_const (c k : Nat) : sumTo (fun _ => c) k = c * k := by
  induction k with
  | zero => simp [sumTo]
  | succ k ih => simp only [sumTo, ih]; rw [Nat.mul_succ]

theorem sumTo_mul (f : Nat → Nat) (c k : Nat) : sumTo (fun j => f j * c) k = sumTo f k * c := by
  induction k with
  | zero => simp [sumTo]
  | succ k ih => simp only [sumTo, ih]; rw [Nat.add_mul]

/-- The closed form of the size of a range. -/
theorem refSize_eq (len a b : Nat) (hlen : len ≤ u64Max) (hab : a < b) (hb : b ≤ groups len lg) :
    refSize len a b = (b - a) * HDR + (min len (b * G) - a * G) + parentsIn a b 0 (groups len lg) * PARL := by
  unfold refSize refFrames
  rw [frames_of_range len lg a b hab hb, tab_sum]
  have h1 : sumTo (fun j => fbytes (frameOf len lg 0 (groups len lg) 0 a [] (a + j))) (b - a) =
      sumTo (fun j => HDR + pendLen (groups len lg) a j * PARL + groupSize len lg (a + j)) (b - a) := by
    apply sumTo_congr
    intro j _
    simp only [fbytes, frameOf, frame_pend len lg _ a j]
    rw [← frame_pend len lg _ a j]
    simp [frameOf]
  rw [h1, sumTo_add, sumTo_add, sumTo_const, sumTo_mul, ← parentsIn_sum len lg a b hab hb]
  have hlt : a * groupLen lg ≤ len := by
    have := (lt_groups_iff len lg a).1 (by omega)
    omega
  rw [sumTo_groupSize len lg a hlen _ hlt, show a + (b - a) = b by omega]
  have hc := Nat.mul_comm HDR (b - a)
  have e1 : b * G = b * groupLen lg := rfl
  have e2 : a * G = a * groupLen lg := rfl
  omega

/-- A range holds at most as many parents as the tree. -/
theorem parentsIn_le (a b : Nat) : ∀ (n lo hi : Nat), hi - lo = n → parentsIn a b lo hi ≤ hi - lo - 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro lo hi hn
    by_cases h : hi - lo < 2 ∨ b ≤ lo ∨ hi ≤ a
    · rw [parentsIn_stop _ _ _ _ h]; omega
    · by_cases hc : a ≤ lo ∧ hi ≤ b
      · rw [parentsIn_full _ _ _ _ h hc]; exact Nat.le_refl _
      · have h2 : hi - lo ≥ 2 := by omega
        have h1 := leftGroups_pos (hi - lo) h2
        have h3 := leftGroups_lt (hi - lo) h2
        rw [parentsIn_rec _ _ _ _ h hc]
        have iL := ih (leftGroups (hi - lo)) (by omega) lo (lo + leftGroups (hi - lo)) (by omega)
        have iR := ih (hi - (lo + leftGroups (hi - lo))) (by omega) (lo + leftGroups (hi - lo)) hi rfl
        omega

/-! ### `Plan::new` -/

inductive PErr where
  | outOfBounds
  | tooManyRanges
  | tooLong
  deriving DecidableEq, Repr

/-- A range of a plan: the group interval and the stream offset of its first byte. -/
structure PR where
  first : Nat
  last : Nat
  start : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A plan: the value length, the non-empty ranges and the response length. -/
structure PlanM where
  len : Nat
  rs : List PR
  total : Nat

def cadd (x y : Nat) : Option Nat := if x + y ≤ u64Max then some (x + y) else none
def cmul (x y : Nat) : Option Nat := if x * y ≤ u64Max then some (x * y) else none
def satMul (x y : Nat) : Nat := min (x * y) u64Max
def divCeil (x y : Nat) : Nat := (x + y - 1) / y

/-- The body of the loop of `Plan::new` for one non-empty-or-empty span `(off, len)`. -/
def newStep (len n : Nat) (st : Nat × List PR) (s : Nat × Nat) : Except PErr (Nat × List PR) :=
  if s.2 = 0 then .ok st else
  match cadd s.1 s.2 with
  | none => .error .outOfBounds
  | some e =>
    if e ≤ len then
      let first := s.1 / G
      let last := divCeil e G
      let data := min (satMul last G) len - first * G
      match (cmul (last - first) HDR).bind (fun h => (cadd h data).bind (fun d =>
          (cmul (parentsIn first last 0 n) PARL).bind (fun p => cadd d p))) with
      | none => .error .tooLong
      | some size =>
        match cadd st.1 size with
        | some t => if t ≤ MAXS then .ok (t, st.2 ++ [⟨first, last, st.1⟩]) else .error .tooLong
        | none => .error .tooLong
    else .error .outOfBounds

/-- `Plan::new`. -/
def planNew (len : Nat) (spans : List (Nat × Nat)) : Except PErr PlanM :=
  if spans.length > MAXR then .error .tooManyRanges
  else (spans.foldlM (newStep len (groups len lg)) (0, [])).map (fun st => ⟨len, st.2, st.1⟩)

/-- The specification of one span: exact arithmetic over the reference. -/
def specStep (len : Nat) (st : Nat × List PR) (s : Nat × Nat) : Except PErr (Nat × List PR) :=
  if s.2 = 0 then .ok st
  else if s.1 + s.2 > len then .error .outOfBounds
  else
    let a := s.1 / G
    let b := divCeil (s.1 + s.2) G
    if st.1 + refSize len a b > MAXS then .error .tooLong
    else .ok (st.1 + refSize len a b, st.2 ++ [⟨a, b, st.1⟩])

/-- The specification of the plan. -/
def specNew (len : Nat) (spans : List (Nat × Nat)) : Except PErr PlanM :=
  if spans.length > MAXR then .error .tooManyRanges
  else (spans.foldlM (specStep len) (0, [])).map (fun st => ⟨len, st.2, st.1⟩)

theorem divCeil_bounds (e len : Nat) (he : 0 < e) (hel : e ≤ len) :
    divCeil e G ≤ groups len lg ∧ e ≤ divCeil e G * G ∧ (divCeil e G - 1) * G < e := by
  have hg := G_pos
  unfold divCeil
  have hd := Nat.div_add_mod (e + G - 1) G
  have hm := Nat.mod_lt (e + G - 1) hg
  have hq : 1 ≤ (e + G - 1) / G := by rw [Nat.le_div_iff_mul_le hg]; omega
  rw [Nat.mul_comm G] at hd
  have h3 : ((e + G - 1) / G - 1) * G < e := by
    rw [Nat.sub_mul]
    generalize (e + G - 1) / G = q at *
    generalize (e + G - 1) % G = r at *
    generalize q * G = w at *
    omega
  refine ⟨?_, ?_, h3⟩
  · have h3' : ((e + G - 1) / G - 1) * groupLen lg < e := h3
    have := (lt_groups_iff len lg ((e + G - 1) / G - 1)).2 (by omega)
    omega
  · generalize (e + G - 1) / G = q at *
    generalize (e + G - 1) % G = r at *
    generalize q * G = w at *
    omega

theorem M_lt : MAXS < u64Max := by unfold MAXS u64Max; decide

/-- The checked arithmetic that sizes a range succeeds exactly when the exact size fits a `u64`. -/
theorem size_opt (len first last : Nat) (hlen : len ≤ u64Max) (hab : first < last) (hb : last ≤ groups len lg) :
    ((cmul (last - first) HDR).bind (fun h => (cadd h (min (satMul last G) len - first * G)).bind (fun d =>
        (cmul (parentsIn first last 0 (groups len lg)) PARL).bind (fun p => cadd d p)))) =
      if refSize len first last ≤ u64Max then some (refSize len first last) else none := by
  have hn := groups_le len lg hlen
  have hP := parentsIn_le first last (groups len lg - 0) 0 (groups len lg) rfl
  have h1 : cmul (last - first) HDR = some ((last - first) * HDR) := by
    unfold cmul u64Max HDR; simp only [ite_eq_left_iff]; intro h; exfalso; apply h
    have : (last - first) * 16 ≤ 2 ^ 54 * 16 := Nat.mul_le_mul_right 16 (show last - first ≤ 2 ^ 54 by omega)
    omega
  have h2 : cmul (parentsIn first last 0 (groups len lg)) PARL = some (parentsIn first last 0 (groups len lg) * PARL) := by
    unfold cmul u64Max PARL; simp only [ite_eq_left_iff]; intro h; exfalso; apply h
    have : parentsIn first last 0 (groups len lg) * 64 ≤ 2 ^ 54 * 64 := Nat.mul_le_mul_right 64 (show parentsIn first last 0 (groups len lg) ≤ 2 ^ 54 by omega)
    omega
  have hd : min (satMul last G) len = min len (last * G) := by
    unfold satMul; unfold u64Max at hlen ⊢; omega
  rw [h1, h2, hd, refSize_eq len first last hlen hab hb]
  simp only [Option.bind_some, cadd]
  by_cases hf : (last - first) * HDR + (min len (last * G) - first * G) + parentsIn first last 0 (groups len lg) * PARL ≤ u64Max
  · have : (last - first) * HDR + (min len (last * G) - first * G) ≤ u64Max := by omega
    simp [hf, this]
  · by_cases this : (last - first) * HDR + (min len (last * G) - first * G) ≤ u64Max
    · simp [hf, this]
    · simp [hf, this]

theorem newStep_eq_spec (len : Nat) (hlen : len ≤ u64Max) (st : Nat × List PR) (s : Nat × Nat) :
    newStep len (groups len lg) st s = specStep len st s := by
  unfold newStep specStep
  by_cases h0 : s.2 = 0
  · simp [h0]
  have hM := M_lt
  by_cases hov : s.1 + s.2 ≤ u64Max
  · have hc : cadd s.1 s.2 = some (s.1 + s.2) := by simp [cadd, hov]
    rw [hc]
    by_cases hel : s.1 + s.2 ≤ len
    · have hb := divCeil_bounds (s.1 + s.2) len (by omega) hel
      have hg := G_pos
      have hab : s.1 / G < divCeil (s.1 + s.2) G := by
        rw [Nat.div_lt_iff_lt_mul hg]
        have := hb.2.1
        have := Nat.mul_comm (divCeil (s.1 + s.2) G) G
        omega
      simp only [h0, hel, ite_true, ite_false, show ¬ s.1 + s.2 > len by omega]
      rw [size_opt len _ _ hlen hab hb.1]
      generalize refSize len (s.1 / G) (divCeil (s.1 + s.2) G) = R
      by_cases hr : R ≤ u64Max
      · simp only [hr, ite_true]
        by_cases h1 : st.1 + R ≤ MAXS
        · have : cadd st.1 R = some (st.1 + R) := by simp [cadd]; omega
          simp [this, h1]
        · by_cases h2 : st.1 + R ≤ u64Max
          · have : cadd st.1 R = some (st.1 + R) := by simp [cadd, h2]
            simp [this, h1]
          · have : cadd st.1 R = none := by simp [cadd, h2]
            simp [this, h1]
      · simp only [hr, ite_false]
        have : st.1 + R > MAXS := by omega
        simp [this]
    · simp only [h0, hel, ite_true, ite_false, show s.1 + s.2 > len by omega]
  · have hc : cadd s.1 s.2 = none := by simp [cadd, hov]
    rw [hc]
    simp only [h0, ite_false, show s.1 + s.2 > len by omega, ite_true]

theorem planNew_eq_spec (len : Nat) (hlen : len ≤ u64Max) (spans : List (Nat × Nat)) :
    planNew len spans = specNew len spans := by
  unfold planNew specNew
  have : spans.foldlM (newStep len (groups len lg)) (0, []) = spans.foldlM (specStep len) (0, []) := by
    have h : ∀ (l : List (Nat × Nat)) (st : Nat × List PR),
        l.foldlM (newStep len (groups len lg)) st = l.foldlM (specStep len) st := by
      intro l
      induction l with
      | nil => intro st; rfl
      | cons x t ih => intro st; simp only [List.foldlM, newStep_eq_spec len hlen, ih]
    exact h spans (0, [])
  rw [this]

end Pinc.ValuesPlan
