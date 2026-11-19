import Pinc.DtnGfField
import Pinc.DtnCauchy

/-!
# The Reed-Solomon code of `rs.rs`, one byte column at a time

`Rs::encode` and `Rs::reconstruct` act on symbols of `len` bytes with `mul_add` and `scale`, which work on every byte
position alike (`DtnGfSlice`), and the control flow never looks at a byte, so a block is `len` independent columns.
The model below is the algorithm on one column, a list of `k + m` field elements, step for step: the missing data
indices `ys`, the first `e` present parity rows, the syndromes scaled by `G`, the data symbols solved with the Cauchy
combination scaled by `F`, and the final `encode` of the repaired data. The same column function is replayed against
the real code on every byte column of recorded blocks (`TraceDtnRs`). `Pinc.DtnRsSym` lifts it to whole symbols:
the symbol-level algorithm built from the slice kernels has the column model's output in every byte column.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Pinc.DtnRs
open Pinc.DtnGf Pinc.DtnCauchy Lean.Grind

/-- `u8::try_from(n).unwrap_or(0)` as a field element. -/
def b8 (n : Nat) : GF := if n < 256 then GF.ofNat n else GF.ofNat 0

/-- `coef(k, parity, data) = inv((k + parity) ^ data)`. -/
def coef (k j i : Nat) : GF := (b8 (k + j) + b8 i)⁻¹

/-- The accumulation `acc ^= term` over a list of indices, from 0. -/
def sumL (f : Nat → GF) (l : List Nat) : GF := l.foldl (fun acc t => acc + f t) 0

/-- Parity symbol `j` of the data `d`: `p = 0; for i: p += coef(k, j, i) * d_i`. -/
def parityOf (k : Nat) (d : List GF) (j : Nat) : GF := sumL (fun i => coef k j i * d.getD i 0) (List.range k)

/-- `Rs::encode` on one column: the data prefix then the parity symbols. -/
def encodeCol (k m : Nat) (blk : List GF) : List GF := blk.take k ++ (List.range m).map (parityOf k blk)

/-- Why a call was refused. -/
inductive Err where
  | buffer
  | incomplete
  deriving DecidableEq, Repr

/-- The indices of the missing data symbols, ascending. -/
def ysOf (k : Nat) (present : List Bool) : List Nat := (List.range k).filter fun i => !present.getD i false

/-- The present parity rows used: the first `e` of them, ascending. -/
def rowsOf (k m : Nat) (present : List Bool) : List Nat :=
  ((List.range m).filter fun j => present.getD (k + j) false).take (ysOf k present).length

/-- The `x` nodes (present parity rows) of a solve, as field elements. -/
def xsOf (k m : Nat) (present : List Bool) : List GF := (rowsOf k m present).map fun j => b8 (k + j)

/-- The `y` nodes (missing data indices) of a solve, as field elements. -/
def ygOf (k : Nat) (present : List Bool) : List GF := (ysOf k present).map b8

/-- The syndrome of the `t`-th used parity row, scaled by `G_t`: the parity symbol minus every known data symbol. -/
def synOf (k m : Nat) (blk : List GF) (present : List Bool) (t : Nat) : GF :=
  gF (xsOf k m present) (ygOf k present) t *
    (blk.getD (k + (rowsOf k m present).getD t 0) 0 +
      sumL (fun i => coef k ((rowsOf k m present).getD t 0) i * blk.getD i 0)
        ((List.range k).filter fun i => !(ysOf k present).contains i))

/-- The `s`-th missing data symbol: `F_s` times the Cauchy combination of the scaled syndromes. -/
def outOf (k m : Nat) (present : List Bool) (syns : List GF) (s : Nat) : GF :=
  fF (xsOf k m present) (ygOf k present) s *
    sumL (fun t => ((xsOf k m present).getD t 0 + (ygOf k present).getD s 0)⁻¹ * syns.getD t 0)
      (List.range (ysOf k present).length)

/-- The data symbols after the solve: the missing ones replaced, the others untouched. -/
def solveData (k m : Nat) (blk : List GF) (present : List Bool) : List GF :=
  let syns := (List.range (ysOf k present).length).map (synOf k m blk present)
  (List.range k).map fun i => if (ysOf k present).contains i then outOf k m present syns ((ysOf k present).idxOf i)
    else blk.getD i 0

/-- `Rs::reconstruct` on one column: the checks, the solve, then `encode` of the repaired data. -/
def reconCol (k m : Nat) (blk : List GF) (present : List Bool) : Except Err (List GF) :=
  if present.length ≠ k + m ∨ blk.length ≠ k + m then .error .buffer
  else if present.countP id < k then .error .incomplete
  else .ok (encodeCol k m (solveData k m blk present))

/-- `Rs::new`: `k` is at least 1 and `k + m` at most 255. -/
def validParams (k m : Nat) : Bool := !(k == 0 || decide (k + m > 255))

/-! ### Sums -/

/-- The sum of a list. -/
def sumList (l : List GF) : GF := l.foldr (· + ·) 0

theorem foldl_add (l : List GF) : ∀ a : GF, l.foldl (· + ·) a = a + sumList l := by
  induction l with
  | nil => intro a; simp [sumList]; grind
  | cons x l ih => intro a; simp only [List.foldl_cons, sumList, List.foldr_cons] at *; rw [ih]; grind

theorem sumL_eq (f : Nat → GF) (l : List Nat) : sumL f l = sumList (l.map f) := by
  unfold sumL
  have : ∀ a : GF, l.foldl (fun acc t => acc + f t) a = a + sumList (l.map f) := by
    induction l with
    | nil => intro a; simp [sumList]; grind
    | cons x l ih => intro a; simp only [List.foldl_cons, List.map_cons, sumList, List.foldr_cons] at *; rw [ih]; grind
  rw [this]; grind

theorem sumList_append (a b : List GF) : sumList (a ++ b) = sumList a + sumList b := by
  induction a with
  | nil => simp [sumList]; grind
  | cons x a ih => simp only [List.cons_append, sumList, List.foldr_cons] at *; rw [ih]; grind

theorem sumList_range (f : Nat → GF) : ∀ n, sumList ((List.range n).map f) = sumTo n f := by
  intro n
  induction n generalizing f with
  | zero => simp [sumList, sumTo]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [sumList, List.foldr_cons, sumTo_succ] at *
    rw [← ih (fun t => f (t + 1))]; rfl

theorem sumList_idx (h : Nat → GF) (l : List Nat) : sumList (l.map h) = sumTo l.length (fun s => h (l.getD s 0)) := by
  rw [← sumList_range]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2 : i < l.length)]

theorem sumList_congr (f g : Nat → GF) (l : List Nat) (h : ∀ x ∈ l, f x = g x) : sumList (l.map f) = sumList (l.map g) := by
  congr 1; exact List.map_congr_left h

theorem sumList_partition (f : Nat → GF) (p : Nat → Bool) (l : List Nat) :
    sumList (l.map f) = sumList ((l.filter p).map f) + sumList ((l.filter fun x => !p x).map f) := by
  induction l with
  | nil => simp [sumList]; grind
  | cons x l ih =>
    by_cases hp : p x = true
    · simp only [List.filter_cons, hp, if_true, List.map_cons, sumList, List.foldr_cons, Bool.not_true] at *
      simp; rw [ih]; grind
    · have hp' : p x = false := by simpa using hp
      simp only [List.filter_cons, hp', List.map_cons, sumList, List.foldr_cons, Bool.not_false] at *
      simp; rw [ih]; grind

theorem sumTo_zero_fn (n : Nat) : sumTo n (fun _ => (0 : GF)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo_succ, ih]; grind

theorem sumTo_ite (n s : Nat) (c : Nat → GF) (hs : s < n) :
    sumTo n (fun r => if s = r then c r else 0) = c s := by
  induction n generalizing s c with
  | zero => omega
  | succ n ih =>
    rw [sumTo_succ]
    cases s with
    | zero =>
      have : sumTo n (fun t => if 0 = t + 1 then c (t + 1) else 0) = 0 := by
        exact (sumTo_congr n _ (fun _ => (0 : GF)) (fun t _ => by simp)).trans (sumTo_zero_fn n)
      simp only [if_true]; rw [this]; grind
    | succ s =>
      have := ih s (fun t => c (t + 1)) (by omega)
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_inj]
      rw [this]; grind

theorem sumTo_comm (n m : Nat) (f : Nat → Nat → GF) : sumTo n (fun t => sumTo m (fun r => f t r)) = sumTo m (fun r => sumTo n (fun t => f t r)) := by
  induction n generalizing f with
  | zero =>
    have : ∀ m, sumTo m (fun r => (0 : GF)) = 0 := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => rw [sumTo_succ, ih]; grind
    simp only [sumTo_zero]; rw [this]
  | succ n ih =>
    rw [sumTo_succ, ih (fun t r => f (t + 1) r)]
    have := sumTo_add m (fun r => f 0 r) (fun r => sumTo n (fun t => f (t + 1) r))
    rw [← this]
    apply sumTo_congr; intro r _; rw [sumTo_succ]


/-! ### Counting the missing and the present -/

theorem ysOf_mem (k : Nat) (present : List Bool) (i : Nat) :
    i ∈ ysOf k present ↔ i < k ∧ present.getD i false = false := by
  simp [ysOf]

theorem ysOf_nodup (k : Nat) (present : List Bool) : (ysOf k present).Nodup :=
  List.Pairwise.filter _ List.nodup_range

theorem ysOf_lt (k : Nat) (present : List Bool) : ∀ i ∈ ysOf k present, i < k := fun i hi => ((ysOf_mem k present i).1 hi).1

theorem present_eq (n : Nat) (present : List Bool) (h : present.length = n) :
    present = (List.range n).map (fun i => present.getD i false) := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    have this := h1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]

/-- The number of present symbols is the present data plus the present parity. -/
theorem held_split (k m : Nat) (present : List Bool) (h : present.length = k + m) :
    present.countP id = (List.range k).countP (fun i => present.getD i false) +
      (List.range m).countP (fun j => present.getD (k + j) false) := by
  rw [show present.countP id = ((List.range (k + m)).map (fun i => present.getD i false)).countP id from
    congrArg (List.countP id) (present_eq _ present h)]
  rw [List.countP_map, List.range_add, List.countP_append, List.countP_map]
  rfl

theorem ysOf_length (k : Nat) (present : List Bool) :
    (ysOf k present).length + (List.range k).countP (fun i => present.getD i false) = k := by
  have := List.length_eq_countP_add_countP (p := fun i => present.getD i false) (l := List.range k)
  have h2 : (ysOf k present).length = (List.range k).countP (fun i => !present.getD i false) := by
    simp [ysOf, List.countP_eq_length_filter]
  have h3 : (fun a => decide ¬present.getD a false = true) = (fun i => !present.getD i false) := by
    funext a; cases present.getD a false <;> simp
  rw [h3, List.length_range] at this
  omega

/-- With at least `k` symbols present, enough parity rows are present for the missing data. -/
theorem rows_length (k m : Nat) (present : List Bool) (h : present.length = k + m) (hk : k ≤ present.countP id) :
    (rowsOf k m present).length = (ysOf k present).length := by
  have h1 := held_split k m present h
  have h2 := ysOf_length k present
  have h3 : ((List.range m).filter fun j => present.getD (k + j) false).length =
      (List.range m).countP (fun j => present.getD (k + j) false) := (List.countP_eq_length_filter).symm
  simp only [rowsOf, List.length_take, h3]
  omega

theorem rowsOf_mem (k m : Nat) (present : List Bool) (j : Nat) (hj : j ∈ rowsOf k m present) :
    j < m ∧ present.getD (k + j) false = true := by
  have := List.mem_of_mem_take hj
  simpa using this

theorem rowsOf_nodup (k m : Nat) (present : List Bool) : (rowsOf k m present).Nodup :=
  List.Nodup.sublist (List.take_sublist _ _) (List.Pairwise.filter _ List.nodup_range)

/-- The bounds of the `ys` buffer: at most 127 erasures. -/
theorem erasures_le (k m : Nat) (present : List Bool) (hn : k + m ≤ 255) (h : present.length = k + m)
    (hk : k ≤ present.countP id) : (ysOf k present).length ≤ 127 := by
  have h1 := held_split k m present h
  have h2 := ysOf_length k present
  have h3 : (List.range m).countP (fun j => present.getD (k + j) false) ≤ m := by
    have := List.countP_le_length (p := fun j => present.getD (k + j) false) (l := List.range m)
    simpa using this
  omega


/-! ### The nodes of a solve are distinct -/

theorem b8_v (n : Nat) (h : n < 256) : (b8 n).v = n := by
  simp only [b8, if_pos h]; exact GF.ofNat_v n h

theorem b8_inj {a b : Nat} (ha : a < 256) (hb : b < 256) (h : b8 a = b8 b) : a = b := by
  have := congrArg GF.v h; rwa [b8_v a ha, b8_v b hb] at this

theorem getD_map_lt {α : Type} (l : List α) (f : α → GF) (t : Nat) (w : α) (ht : t < l.length) :
    (l.map f).getD t 0 = f (l.getD t w) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

theorem nodup_map_on {l : List Nat} {f : Nat → GF} (h : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (hl : l.Nodup) :
    (l.map f).Nodup := by
  unfold List.Nodup; rw [List.pairwise_map]
  exact List.Pairwise.imp_of_mem (fun hx hy hne heq => hne (h _ hx _ hy heq)) hl


theorem nodes_of (k m : Nat) (present : List Bool) (hn : k + m ≤ 255) (h : present.length = k + m)
    (hk : k ≤ present.countP id) : Nodes (xsOf k m present) (ygOf k present) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine nodup_map_on ?_ (rowsOf_nodup k m present)
    intro x hx y hy hxy
    have := (rowsOf_mem k m present x hx).1
    have := (rowsOf_mem k m present y hy).1
    have := b8_inj (by omega) (by omega) hxy
    omega
  · refine nodup_map_on ?_ (ysOf_nodup k present)
    intro x hx y hy hxy
    have := ysOf_lt k present x hx
    have := ysOf_lt k present y hy
    exact b8_inj (by omega) (by omega) hxy
  · intro x hx y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    have h1 := (rowsOf_mem k m present j hj).1
    have h2 := ysOf_lt k present i hi
    intro hz
    have := b8_inj (by omega) (by omega) (eq_of_add_zero hz)
    omega
  · simp [xsOf, ygOf, rows_length k m present h hk]

/-! ### The closed-form solve inverts the syndromes -/

theorem solve_id {xs ys : List GF} (h : Nodes xs ys) (D : Nat → GF) (s : Nat) (hs : s < ys.length) :
    fF xs ys s * sumTo xs.length (fun t => (xs.getD t 0 + ys.getD s 0)⁻¹ *
      (gF xs ys t * sumTo xs.length (fun r => (xs.getD t 0 + ys.getD r 0)⁻¹ * D r))) = D s := by
  have hs' : s < xs.length := by rw [h.len]; exact hs
  have e1 : fF xs ys s * sumTo xs.length (fun t => (xs.getD t 0 + ys.getD s 0)⁻¹ *
      (gF xs ys t * sumTo xs.length (fun r => (xs.getD t 0 + ys.getD r 0)⁻¹ * D r))) =
      sumTo xs.length (fun t => sumTo xs.length (fun r => D r * (cB xs ys s t * cA xs ys t r))) := by
    rw [← sumTo_mul]
    apply sumTo_congr; intro t ht
    rw [← sumTo_mul, ← sumTo_mul, ← sumTo_mul]
    apply sumTo_congr; intro r hr
    simp only [cB, cA]; grind
  rw [e1, sumTo_comm]
  have e2 : ∀ r, r < xs.length → sumTo xs.length (fun t => D r * (cB xs ys s t * cA xs ys t r)) =
      if s = r then D r else 0 := by
    intro r hr
    rw [sumTo_mul, cauchy_BA h s r hs (by rw [← h.len]; exact hr)]
    by_cases hsr : s = r
    · simp [hsr]; grind
    · simp [hsr]; grind
  rw [sumTo_congr _ _ _ (fun r hr => e2 r hr)]
  exact sumTo_ite _ s D hs'


/-! ### Decoding recovers the block -/

/-- The code word of the data `d`. -/
def codeword (k m : Nat) (d : List GF) : List GF := d ++ (List.range m).map (parityOf k d)

theorem getD_nat_mem (l : List Nat) (t : Nat) (h : t < l.length) : l.getD t 0 ∈ l := by
  simp [List.getD_eq_getElem?_getD, h]

theorem codeword_data (k m : Nat) (d : List GF) (hd : d.length = k) (i : Nat) (hi : i < k) :
    (codeword k m d).getD i 0 = d.getD i 0 := by
  unfold codeword
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < d.length by omega)]

theorem codeword_parity (k m : Nat) (d : List GF) (hd : d.length = k) (j : Nat) (hj : j < m) :
    (codeword k m d).getD (k + j) 0 = parityOf k d j := by
  unfold codeword
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show d.length ≤ k + j by omega), hd, hj]

theorem codeword_length (k m : Nat) (d : List GF) (hd : d.length = k) : (codeword k m d).length = k + m := by
  simp [codeword, hd]

theorem ys_contains (k : Nat) (present : List Bool) (i : Nat) (hi : i < k) :
    (ysOf k present).contains i = !present.getD i false := by
  by_cases h : present.getD i false = true
  · have : i ∉ ysOf k present := fun hm => by have := ((ysOf_mem k present i).1 hm).2; simp_all
    rw [h]; simpa [List.contains_iff_mem] using this
  · have h' : present.getD i false = false := by simpa using h
    have : i ∈ ysOf k present := (ysOf_mem k present i).2 ⟨hi, h'⟩
    rw [h']; simpa [List.contains_iff_mem] using this

variable {k m : Nat} {d blk : List GF} {present : List Bool}

/-- The known data symbols are the data. -/
theorem known_eq (hd : d.length = k)
    (hag : ∀ s, s < k + m → present.getD s false = true → blk.getD s 0 = (codeword k m d).getD s 0)
    (hp : present.length = k + m) (i : Nat) (hi : i < k) (hc : (ysOf k present).contains i = false) :
    blk.getD i 0 = d.getD i 0 := by
  rw [ys_contains k present i hi] at hc
  have : present.getD i false = true := by simpa using hc
  rw [hag i (by omega) this, codeword_data k m d hd i hi]

theorem syn_part (hd : d.length = k) (hp : present.length = k + m)
    (hag : ∀ s, s < k + m → present.getD s false = true → blk.getD s 0 = (codeword k m d).getD s 0)
    (r0 : Nat) (hrm : r0 < m) (hrp : present.getD (k + r0) false = true) :
    blk.getD (k + r0) 0 + sumL (fun i => coef k r0 i * blk.getD i 0) ((List.range k).filter fun i => !(ysOf k present).contains i) =
      sumTo (ysOf k present).length (fun r => (b8 (k + r0) + (ygOf k present).getD r 0)⁻¹ *
        d.getD ((ysOf k present).getD r 0) 0) := by
  rw [hag (k + r0) (by omega) hrp, codeword_parity k m d hd r0 hrm]
  have hF : parityOf k d r0 = sumList ((List.range k).map fun i => coef k r0 i * d.getD i 0) := by
    unfold parityOf; rw [sumL_eq]
  have hK : sumL (fun i => coef k r0 i * blk.getD i 0) ((List.range k).filter fun i => !(ysOf k present).contains i) =
      sumList (((List.range k).filter fun i => !(ysOf k present).contains i).map fun i => coef k r0 i * d.getD i 0) := by
    rw [sumL_eq]
    apply sumList_congr
    intro i hi
    have hi' := List.mem_filter.mp hi
    have hik : i < k := by simpa using hi'.1
    have hc : (ysOf k present).contains i = false := by simpa using hi'.2
    rw [known_eq hd hag hp i hik hc]
  have hM : ((List.range k).filter fun i => !!(ysOf k present).contains i) = ysOf k present := by
    refine (List.filter_congr (q := fun i => !present.getD i false) ?_).trans rfl
    intro x hx
    have hxk : x < k := by simpa using hx
    rw [ys_contains k present x hxk]; simp
  have hpart := sumList_partition (fun i => coef k r0 i * d.getD i 0) (fun i => !(ysOf k present).contains i) (List.range k)
  simp only [hM] at hpart
  rw [hF, hK, hpart]
  have hMs : sumList ((ysOf k present).map fun i => coef k r0 i * d.getD i 0) =
      sumTo (ysOf k present).length (fun r => (b8 (k + r0) + (ygOf k present).getD r 0)⁻¹ *
        d.getD ((ysOf k present).getD r 0) 0) := by
    rw [sumList_idx]
    apply sumTo_congr
    intro r hr
    unfold ygOf coef
    rw [getD_map_lt _ _ r 0 hr]
  rw [← hMs]
  grind

theorem syn_eq (hk1 : 1 ≤ k) (hn : k + m ≤ 255) (hd : d.length = k) (hp : present.length = k + m)
    (hheld : k ≤ present.countP id)
    (hag : ∀ s, s < k + m → present.getD s false = true → blk.getD s 0 = (codeword k m d).getD s 0)
    (t : Nat) (ht : t < (ysOf k present).length) :
    synOf k m blk present t = gF (xsOf k m present) (ygOf k present) t *
      sumTo (ysOf k present).length (fun r => ((xsOf k m present).getD t 0 + (ygOf k present).getD r 0)⁻¹ *
        d.getD ((ysOf k present).getD r 0) 0) := by
  have hrl := rows_length k m present hp hheld
  have htr : t < (rowsOf k m present).length := by omega
  have hr0 := getD_nat_mem _ t htr
  obtain ⟨hrm, hrp⟩ := rowsOf_mem k m present _ hr0
  have hx : (xsOf k m present).getD t 0 = b8 (k + (rowsOf k m present).getD t 0) := by
    unfold xsOf; exact getD_map_lt _ _ t 0 htr
  rw [hx]
  unfold synOf
  rw [← syn_part hd hp hag _ hrm hrp]

theorem syns_getD (e : Nat) (f : Nat → GF) (t : Nat) (ht : t < e) :
    ((List.range e).map f).getD t 0 = f t := by
  simp [List.getD_eq_getElem?_getD, ht]

theorem out_eq (hk1 : 1 ≤ k) (hn : k + m ≤ 255) (hd : d.length = k) (hp : present.length = k + m)
    (hheld : k ≤ present.countP id)
    (hag : ∀ s, s < k + m → present.getD s false = true → blk.getD s 0 = (codeword k m d).getD s 0)
    (s : Nat) (hs : s < (ysOf k present).length) :
    outOf k m present ((List.range (ysOf k present).length).map (synOf k m blk present)) s =
      d.getD ((ysOf k present).getD s 0) 0 := by
  have hN := nodes_of k m present hn hp hheld
  have hxe : (xsOf k m present).length = (ysOf k present).length := by
    have := hN.len; simpa [ygOf] using this
  have hsy : s < (ygOf k present).length := by simpa [ygOf] using hs
  unfold outOf
  rw [sumL_eq, sumList_range]
  have e1 : sumTo (ysOf k present).length (fun t => ((xsOf k m present).getD t 0 + (ygOf k present).getD s 0)⁻¹ *
      ((List.range (ysOf k present).length).map (synOf k m blk present)).getD t 0) =
      sumTo (xsOf k m present).length (fun t => ((xsOf k m present).getD t 0 + (ygOf k present).getD s 0)⁻¹ *
        (gF (xsOf k m present) (ygOf k present) t * sumTo (xsOf k m present).length (fun r =>
          ((xsOf k m present).getD t 0 + (ygOf k present).getD r 0)⁻¹ * d.getD ((ysOf k present).getD r 0) 0))) := by
    rw [hxe]
    apply sumTo_congr; intro t ht
    rw [syns_getD _ _ t ht, syn_eq hk1 hn hd hp hheld hag t ht]
  rw [e1]
  exact solve_id hN (fun r => d.getD ((ysOf k present).getD r 0) 0) s hsy

theorem solveData_eq (hk1 : 1 ≤ k) (hn : k + m ≤ 255) (hd : d.length = k) (hb : blk.length = k + m)
    (hp : present.length = k + m) (hheld : k ≤ present.countP id)
    (hag : ∀ s, s < k + m → present.getD s false = true → blk.getD s 0 = (codeword k m d).getD s 0) :
    solveData k m blk present = d := by
  apply List.ext_getElem
  · simp [solveData, hd]
  · intro i h1 h2
    have hik : i < k := by simpa [solveData] using h1
    have hdi : d[i] = d.getD i 0 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rw [hdi]
    simp only [solveData, List.getElem_map, List.getElem_range]
    by_cases hc : (ysOf k present).contains i = true
    · rw [if_pos hc]
      have hmem : i ∈ ysOf k present := by simpa [List.contains_iff_mem] using hc
      have hidx : (ysOf k present).idxOf i < (ysOf k present).length := List.idxOf_lt_length_iff.2 hmem
      rw [out_eq hk1 hn hd hp hheld hag _ hidx]
      congr 1
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, List.getElem_idxOf]
    · rw [if_neg hc]
      exact known_eq hd hag hp i hik (by simpa using hc)

/-- **Decoding recovers every block from any `k` of its symbols.** If the bytes of the present symbols are the
symbols of a code word (and the absent ones are anything), `reconstruct` returns the whole code word. -/
theorem reconCol_ok (hk1 : 1 ≤ k) (hn : k + m ≤ 255) (hd : d.length = k) (hb : blk.length = k + m)
    (hp : present.length = k + m) (hheld : k ≤ present.countP id)
    (hag : ∀ s, s < k + m → present.getD s false = true → blk.getD s 0 = (codeword k m d).getD s 0) :
    reconCol k m blk present = .ok (codeword k m d) := by
  unfold reconCol
  rw [if_neg (by simp [hb, hp]), if_neg (by omega), solveData_eq hk1 hn hd hb hp hheld hag]
  unfold encodeCol codeword
  rw [List.take_of_length_le (by omega)]

theorem reconCol_buffer (h : present.length ≠ k + m ∨ blk.length ≠ k + m) :
    reconCol k m blk present = .error .buffer := by
  unfold reconCol; rw [if_pos h]

theorem reconCol_incomplete (hb : blk.length = k + m) (hp : present.length = k + m) (h : present.countP id < k) :
    reconCol k m blk present = .error .incomplete := by
  unfold reconCol; rw [if_neg (by simp [hb, hp]), if_pos h]

/-- **MDS.** Two data vectors whose code words agree on any `k` (or more) positions are equal: every `k` symbols of a
block determine it. (A linear map on `k` coordinates that is injective has an invertible matrix; `cauchy_BA` and
`cauchy_AB` give the explicit two-sided inverse of the Cauchy block.) -/
theorem mds (hk1 : 1 ≤ k) (hn : k + m ≤ 255) {d' : List GF} (hd : d.length = k) (hd' : d'.length = k)
    (hp : present.length = k + m) (hheld : k ≤ present.countP id)
    (heq : ∀ s, s < k + m → present.getD s false = true → (codeword k m d).getD s 0 = (codeword k m d').getD s 0) :
    d = d' := by
  have h1 := reconCol_ok (blk := codeword k m d') hk1 hn hd (codeword_length k m d' hd') hp hheld
    (fun s hs hs' => (heq s hs hs').symm)
  have h2 := reconCol_ok (blk := codeword k m d') hk1 hn hd' (codeword_length k m d' hd') hp hheld
    (fun s hs hs' => rfl)
  rw [h1] at h2
  have h3 : codeword k m d = codeword k m d' := Except.ok.inj h2
  have h4 := congrArg (List.take k) h3
  simp only [codeword, List.take_left' hd, List.take_left' hd'] at h4
  exact h4

/-- With every data symbol present nothing is solved: the data stay as they are. -/
theorem solveData_none (hall : ∀ i, i < k → present.getD i false = true) :
    solveData k m blk present = (List.range k).map fun i => blk.getD i 0 := by
  have : ∀ i, i < k → (ysOf k present).contains i = false := by
    intro i hi; rw [ys_contains k present i hi, hall i hi]; rfl
  unfold solveData
  apply List.map_congr_left
  intro i hi
  rw [this i (by simpa using hi)]; rfl

/-- `Rs::new`: valid exactly for `1 <= k` and `k + m <= 255`, and then both fit a byte. -/
theorem validParams_iff (k m : Nat) : validParams k m = true ↔ 1 ≤ k ∧ k + m ≤ 255 := by
  unfold validParams; simp; omega


#audit_axioms Pinc.DtnRs.reconCol_ok
#audit_axioms Pinc.DtnRs.mds
#audit_axioms Pinc.DtnRs.erasures_le
#audit_axioms Pinc.DtnRs.validParams_iff

end Pinc.DtnRs
