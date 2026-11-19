import Pinc.DtnRs
import Pinc.DtnGfSlice

/-!
# The Reed-Solomon code of `rs.rs` on whole symbols

`DtnRs` models `Rs::encode` and `Rs::reconstruct` on one byte column. The code works on symbols of `len` bytes with the
slice kernels `mul_add` and `scale` (`DtnGfSlice`, proved equal to the pointwise operation, including the eight bytes at
a time path). This file states the symbol-level algorithm with those kernels, loop for loop, and proves that **every
byte column of its output is the column model's output**: `reconSym_col` (for each byte position `t`, `Rs::reconstruct`
on the symbols restricted to column `t` is `reconCol` on that column), and so, by the theorem of `DtnRs` that a column is
recovered from any `k` of its symbols, `reconSym_recovers`: whole symbols are recovered from any `k` of the block's.

In `solve` the code updates the block in place; the model is the dataflow of those updates, which is the same
computation: a syndrome is the parity slot with the known data symbols added in and then scaled; a missing data symbol
is zero plus the Cauchy combination of the syndromes, scaled; the slots that are written (the parity rows of the used
syndromes, the missing data) are never read before they are final, since the accumulations read known data symbols and
syndromes only. `encode` writes the parity symbols from the data symbols, which `reconstruct` finishes with.
A symbol is a list of byte values (`Nat` below 256), a field element is `GF` (`GF.ofNat` of a byte).
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Pinc.DtnRsSym
open Pinc.DtnGf Pinc.DtnGfSlice Pinc.DtnRs Pinc.DtnCauchy

/-- A symbol: its bytes. -/
abbrev Sym := List Nat

/-- A well-formed symbol of `len` bytes. -/
def OkSym (len : Nat) (s : Sym) : Prop := s.length = len ∧ ∀ x ∈ s, x < 256

/-- Byte `t` of a symbol as a field element (zero past the end). -/
def at_ (s : Sym) (t : Nat) : GF := GF.ofNat (s.getD t 0)

/-- The column `t` of a block: byte `t` of every symbol. -/
def colOf (blk : List Sym) (t : Nat) : List GF := blk.map (at_ · t)

theorem getD_byte {s : Sym} (hs : ∀ x ∈ s, x < 256) (t : Nat) : s.getD t 0 < 256 := by
  by_cases h : t < s.length
  · have : s.getD t 0 ∈ s := by simp [List.getD_eq_getElem?_getD, h]
    exact hs _ this
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : s.length ≤ t)]

theorem at_v {s : Sym} (hs : ∀ x ∈ s, x < 256) (t : Nat) : (at_ s t).v = s.getD t 0 :=
  GF.ofNat_v _ (getD_byte hs t)

theorem at_nil (t : Nat) : at_ [] t = 0 := by
  apply GF.ext'
  show (GF.ofNat (([] : Sym).getD t 0)).v = 0
  simp [GF.ofNat]

theorem colOf_getD (blk : List Sym) (t i : Nat) : (colOf blk t).getD i 0 = at_ (blk.getD i []) t := by
  unfold colOf
  by_cases h : i < blk.length
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : blk.length ≤ i), at_nil]

theorem zipWith_getD (f : Nat → Nat → Nat) (d s : Sym) (t : Nat) (hd : t < d.length) (hs : t < s.length) :
    (List.zipWith f d s).getD t 0 = f (d.getD t 0) (s.getD t 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem hd, List.getElem?_eq_getElem hs]

/-! ### The kernels, column by column -/

theorem zero_ok (len : Nat) : OkSym len (List.replicate len 0) :=
  ⟨by simp, fun x hx => by simp at hx; omega⟩

theorem zero_at (len t : Nat) : at_ (List.replicate len 0) t = 0 := by
  apply GF.ext'
  rw [at_v (zero_ok len).2]
  by_cases h : t < len
  · simp [List.getD_eq_getElem?_getD, h]; rfl
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h : (List.replicate len 0).length ≤ t)]; rfl

/-- `mul_add`: well formed, and on every column `dst + c * src`. -/
theorem mulAdd_spec (len : Nat) (c : GF) (d s : Sym) (hd : OkSym len d) (hs : OkSym len s) :
    OkSym len (mulAdd d s c.v) ∧ ∀ t, t < len → at_ (mulAdd d s c.v) t = at_ d t + c * at_ s t := by
  rw [mulAdd_eq c.v c.lt d s hd.2 hs.2]
  unfold refMulAdd
  have hl : d.length = s.length := by rw [hd.1, hs.1]
  rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  have hbyte : ∀ a b, a < 256 → b < 256 → (a ^^^ mulT c.v b) < 256 := fun a b ha hb => by
    have := mulT_lt256 c.v b c.lt hb
    simpa using Nat.xor_lt_two_pow (n := 8) ha this
  refine ⟨⟨by simp [hl, hd.1, hs.1], fun x hx => ?_⟩, fun t ht => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.getElem_zipWith]
    exact hbyte _ _ (hd.2 _ (List.getElem_mem _)) (hs.2 _ (List.getElem_mem _))
  · apply GF.ext'
    have h1 : (List.zipWith (fun a b => a ^^^ mulT c.v b) d s).getD t 0 =
        d.getD t 0 ^^^ mulT c.v (s.getD t 0) :=
      zipWith_getD _ d s t (by have := hd.1; omega) (by have := hs.1; omega)
    unfold at_
    rw [h1, GF.add_v, GF.mul_v, GF.ofNat_v _ (getD_byte hd.2 t), GF.ofNat_v _ (getD_byte hs.2 t)]
    exact GF.ofNat_v _ (hbyte _ _ (getD_byte hd.2 t) (getD_byte hs.2 t))

/-- `scale`: well formed, and on every column `c * buf`. -/
theorem scale_spec (len : Nat) (c : GF) (b : Sym) (hb : OkSym len b) :
    OkSym len (scaleL b c.v) ∧ ∀ t, t < len → at_ (scaleL b c.v) t = c * at_ b t := by
  rw [scale_eq c.v c.lt b hb.2]
  refine ⟨⟨by simp [hb.1], fun x hx => ?_⟩, fun t ht => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact mulT_lt256 c.v y c.lt (hb.2 y hy)
  · apply GF.ext'
    have hbt : t < b.length := by have := hb.1; omega
    have h1 : (b.map (mulT c.v)).getD t 0 = mulT c.v (b.getD t 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbt]
    unfold at_
    rw [h1, GF.mul_v, GF.ofNat_v _ (getD_byte hb.2 t)]
    exact GF.ofNat_v _ (mulT_lt256 c.v _ c.lt (getD_byte hb.2 t))

/-- `p += sum_i c_i * src_i` by `mul_add`, in the order of the list. -/
def accum (src : Nat → Sym) (c : Nat → GF) (l : List Nat) (p : Sym) : Sym :=
  l.foldl (fun p i => mulAdd p (src i) (c i).v) p

theorem accum_spec (len : Nat) (src : Nat → Sym) (c : Nat → GF) :
    ∀ (l : List Nat) (p : Sym), OkSym len p → (∀ i ∈ l, OkSym len (src i)) →
      OkSym len (accum src c l p) ∧
        ∀ t, t < len → at_ (accum src c l p) t = l.foldl (fun acc i => acc + c i * at_ (src i) t) (at_ p t) := by
  intro l
  induction l with
  | nil => intro p hp _; exact ⟨hp, fun t _ => rfl⟩
  | cons i l ih =>
    intro p hp hs
    obtain ⟨h1, h2⟩ := mulAdd_spec len (c i) p (src i) hp (hs i (List.mem_cons_self ..))
    obtain ⟨h3, h4⟩ := ih _ h1 (fun j hj => hs j (List.mem_cons_of_mem _ hj))
    refine ⟨h3, fun t ht => ?_⟩
    show at_ (accum src c l (mulAdd p (src i) (c i).v)) t = _
    rw [h4 t ht, h2 t ht]
    rfl

theorem foldl_start (f : Nat → GF) : ∀ (l : List Nat) (a : GF),
    l.foldl (fun acc i => acc + f i) a = a + sumL f l := by
  intro l
  induction l with
  | nil => intro a; simp [sumL]; grind
  | cons x l ih =>
    intro a
    have h1 : sumL f (x :: l) = f x + sumL f l := by
      simp only [sumL, List.foldl_cons]
      rw [ih (0 + f x)]; grind
    rw [h1, List.foldl_cons, ih]; grind

/-! ### Encode -/

/-- Parity symbol `j`: zero, then `mul_add` of every data symbol with `coef(k, j, i)`. -/
def parSym (k len : Nat) (data : Nat → Sym) (j : Nat) : Sym :=
  accum data (fun i => coef k j i) (List.range k) (List.replicate len 0)

/-- `Rs::encode`: the data symbols, then the parity symbols. -/
def encodeSym (k m len : Nat) (data : List Sym) : List Sym :=
  data.take k ++ (List.range m).map (parSym k len fun i => data.getD i [])

/-- A list of symbols that are all well formed. -/
def OkBlk (len : Nat) (blk : List Sym) : Prop := ∀ s ∈ blk, OkSym len s

theorem okBlk_getD {len : Nat} {blk : List Sym} (h : OkBlk len blk) (i : Nat) (hi : i < blk.length) :
    OkSym len (blk.getD i []) := by
  have : blk.getD i [] ∈ blk := by simp [List.getD_eq_getElem?_getD, hi]
  exact h _ this

theorem sumL_congr (f g : Nat → GF) (l : List Nat) (h : ∀ x ∈ l, f x = g x) : sumL f l = sumL g l := by
  rw [sumL_eq, sumL_eq]; exact sumList_congr f g l h

/-- `Rs::encode` on whole symbols: well formed, `k + m` symbols, and every column is `encodeCol` of the data column. -/
theorem encodeSym_spec (k m len : Nat) (data : List Sym) (hd : data.length = k) (hok : OkBlk len data) :
    OkBlk len (encodeSym k m len data) ∧ (encodeSym k m len data).length = k + m ∧
      ∀ t, t < len → colOf (encodeSym k m len data) t = encodeCol k m (colOf data t) := by
  have hpar : ∀ j, OkSym len (parSym k len (fun i => data.getD i []) j) ∧
      ∀ t, t < len → at_ (parSym k len (fun i => data.getD i []) j) t = parityOf k (colOf data t) j := by
    intro j
    obtain ⟨h1, h2⟩ := accum_spec len (fun i => data.getD i []) (fun i => coef k j i) (List.range k)
      (List.replicate len 0) (zero_ok len)
      (fun i hi => okBlk_getD hok i (by have := List.mem_range.1 hi; omega))
    refine ⟨h1, fun t ht => ?_⟩
    unfold parSym
    rw [h2 t ht, zero_at, foldl_start]
    unfold parityOf
    have : (0 : GF) + sumL (fun i => coef k j i * at_ (data.getD i []) t) (List.range k) =
        sumL (fun i => coef k j i * at_ (data.getD i []) t) (List.range k) := by grind
    rw [this]
    exact sumL_congr _ _ _ (fun i _ => by rw [colOf_getD])
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    unfold encodeSym at hx
    rcases List.mem_append.1 hx with h | h
    · exact hok _ (List.mem_of_mem_take h)
    · obtain ⟨j, -, rfl⟩ := List.mem_map.1 h
      exact (hpar j).1
  · simp [encodeSym, hd]
  · intro t ht
    unfold encodeSym encodeCol
    rw [colOf, List.map_append, List.map_map, List.take_of_length_le (by omega : data.length ≤ k)]
    have : (colOf data t).take k = colOf data t := List.take_of_length_le (by simp [colOf, hd])
    rw [this]
    congr 1
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.getElem_map, Function.comp]
      exact (hpar _).2 t ht

/-! ### Reconstruct -/

/-- The syndrome symbol of the `t`-th used parity row: the parity symbol plus the known data symbols times their
coefficients, scaled by `G_t`. -/
def synSym (k m : Nat) (blk : List Sym) (present : List Bool) (t : Nat) : Sym :=
  scaleL (accum (fun i => blk.getD i []) (fun i => coef k ((rowsOf k m present).getD t 0) i)
      ((List.range k).filter fun i => !(ysOf k present).contains i) (blk.getD (k + (rowsOf k m present).getD t 0) []))
    (gF (xsOf k m present) (ygOf k present) t).v

/-- The missing data symbol `s`: zero plus the Cauchy combination of the syndromes, scaled by `F_s`. -/
def outSym (k m len : Nat) (blk : List Sym) (present : List Bool) (s : Nat) : Sym :=
  scaleL (accum (synSym k m blk present)
      (fun t => ((xsOf k m present).getD t 0 + (ygOf k present).getD s 0)⁻¹)
      (List.range (ysOf k present).length) (List.replicate len 0))
    (fF (xsOf k m present) (ygOf k present) s).v

/-- The data symbols after the solve: the missing ones replaced, the others untouched. -/
def solveSym (k m len : Nat) (blk : List Sym) (present : List Bool) : List Sym :=
  (List.range k).map fun i =>
    if (ysOf k present).contains i then outSym k m len blk present ((ysOf k present).idxOf i) else blk.getD i []

/-- `Rs::reconstruct` on whole symbols (the checks, which do not read a byte, are those of `reconCol`): the solve, then
`encode` of the repaired data. -/
def reconSym (k m len : Nat) (blk : List Sym) (present : List Bool) : List Sym :=
  encodeSym k m len (solveSym k m len blk present)

theorem synSym_spec (k m len : Nat) (blk : List Sym) (present : List Bool) (hb : blk.length = k + m)
    (hok : OkBlk len blk) (hp : present.length = k + m) (hk : k ≤ present.countP id) (t : Nat)
    (ht : t < (ysOf k present).length) :
    OkSym len (synSym k m blk present t) ∧ ∀ τ, τ < len →
      at_ (synSym k m blk present t) τ = synOf k m (colOf blk τ) present t := by
  have hrl := rows_length k m present hp hk
  have hrm : (rowsOf k m present).getD t 0 ∈ rowsOf k m present := getD_nat_mem _ t (by omega)
  have hrj := (rowsOf_mem k m present _ hrm).1
  obtain ⟨h1, h2⟩ := accum_spec len (fun i => blk.getD i []) (fun i => coef k ((rowsOf k m present).getD t 0) i)
    ((List.range k).filter fun i => !(ysOf k present).contains i) (blk.getD (k + (rowsOf k m present).getD t 0) [])
    (okBlk_getD hok _ (by omega))
    (fun i hi => okBlk_getD hok i (by have := List.mem_range.1 (List.mem_filter.1 hi).1; omega))
  obtain ⟨h3, h4⟩ := scale_spec len (gF (xsOf k m present) (ygOf k present) t) _ h1
  refine ⟨h3, fun τ hτ => ?_⟩
  unfold synSym
  rw [h4 τ hτ, h2 τ hτ, foldl_start]
  unfold synOf
  rw [colOf_getD]
  congr 2
  exact sumL_congr _ _ _ (fun i _ => by rw [colOf_getD])

theorem outSym_spec (k m len : Nat) (blk : List Sym) (present : List Bool) (hb : blk.length = k + m)
    (hok : OkBlk len blk) (hp : present.length = k + m) (hk : k ≤ present.countP id) (s : Nat) :
    OkSym len (outSym k m len blk present s) ∧ ∀ τ, τ < len →
      at_ (outSym k m len blk present s) τ =
        outOf k m present ((List.range (ysOf k present).length).map (synOf k m (colOf blk τ) present)) s := by
  obtain ⟨h1, h2⟩ := accum_spec len (synSym k m blk present)
    (fun t => ((xsOf k m present).getD t 0 + (ygOf k present).getD s 0)⁻¹)
    (List.range (ysOf k present).length) (List.replicate len 0) (zero_ok len)
    (fun t ht => (synSym_spec k m len blk present hb hok hp hk t (List.mem_range.1 ht)).1)
  obtain ⟨h3, h4⟩ := scale_spec len (fF (xsOf k m present) (ygOf k present) s) _ h1
  refine ⟨h3, fun τ hτ => ?_⟩
  unfold outSym
  rw [h4 τ hτ, h2 τ hτ, zero_at, foldl_start]
  unfold outOf
  congr 1
  have : (0 : GF) + sumL (fun t => ((xsOf k m present).getD t 0 + (ygOf k present).getD s 0)⁻¹ *
      at_ (synSym k m blk present t) τ) (List.range (ysOf k present).length) =
      sumL (fun t => ((xsOf k m present).getD t 0 + (ygOf k present).getD s 0)⁻¹ *
      at_ (synSym k m blk present t) τ) (List.range (ysOf k present).length) := by grind
  rw [this]
  exact sumL_congr _ _ _ (fun t ht => by
    have ht' := List.mem_range.1 ht
    rw [syns_getD _ _ t ht', (synSym_spec k m len blk present hb hok hp hk t ht').2 τ hτ])

theorem solveSym_spec (k m len : Nat) (blk : List Sym) (present : List Bool) (hb : blk.length = k + m)
    (hok : OkBlk len blk) (hp : present.length = k + m) (hk : k ≤ present.countP id) :
    (solveSym k m len blk present).length = k ∧ OkBlk len (solveSym k m len blk present) ∧
      ∀ τ, τ < len → colOf (solveSym k m len blk present) τ = solveData k m (colOf blk τ) present := by
  have hlen : (solveSym k m len blk present).length = k := by simp [solveSym]
  refine ⟨hlen, ?_, fun τ hτ => ?_⟩
  · intro x hx
    unfold solveSym at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    split
    · exact (outSym_spec k m len blk present hb hok hp hk _).1
    · exact okBlk_getD hok i (by have := List.mem_range.1 hi; omega)
  · apply List.ext_getElem
    · simp [colOf, hlen, solveData]
    · intro i h1 h2
      have hik : i < k := by simpa [colOf, solveSym] using h1
      have e1 : (colOf (solveSym k m len blk present) τ)[i] =
          (colOf (solveSym k m len blk present) τ).getD i 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
      rw [e1, colOf_getD]
      simp only [solveSym, solveData, List.getElem_map, List.getElem_range]
      have e2 : ((List.range k).map fun i => if (ysOf k present).contains i then outSym k m len blk present
          ((ysOf k present).idxOf i) else blk.getD i []).getD i [] =
          (if (ysOf k present).contains i then outSym k m len blk present ((ysOf k present).idxOf i)
            else blk.getD i []) := by
        simp [List.getD_eq_getElem?_getD, hik]
      rw [e2]
      split
      · exact (outSym_spec k m len blk present hb hok hp hk _).2 τ hτ
      · exact (colOf_getD blk τ i).symm

theorem reconSym_col (k m len : Nat) (blk : List Sym) (present : List Bool) (hb : blk.length = k + m)
    (hok : OkBlk len blk) (hp : present.length = k + m) (hk : k ≤ present.countP id) :
    OkBlk len (reconSym k m len blk present) ∧ (reconSym k m len blk present).length = k + m ∧
      ∀ τ, τ < len → reconCol k m (colOf blk τ) present = .ok (colOf (reconSym k m len blk present) τ) := by
  obtain ⟨hl, hs, hc⟩ := solveSym_spec k m len blk present hb hok hp hk
  obtain ⟨e1, e2, e3⟩ := encodeSym_spec k m len _ hl hs
  refine ⟨e1, e2, fun τ hτ => ?_⟩
  have hbl : (colOf blk τ).length = k + m := by simp [colOf, hb]
  unfold reconCol reconSym
  rw [if_neg (by simp [hbl, hp]), if_neg (by omega), e3 τ hτ, hc τ hτ]

/-- Two well-formed blocks of the same shape with the same columns are the same. -/
theorem block_ext (len : Nat) (S S' : List Sym) (hs : OkBlk len S) (hs' : OkBlk len S') (hl : S.length = S'.length)
    (h : ∀ τ, τ < len → colOf S τ = colOf S' τ) : S = S' := by
  apply List.ext_getElem hl
  intro i h1 h2
  have o1 := hs _ (List.getElem_mem h1)
  have o2 := hs' _ (List.getElem_mem h2)
  apply List.ext_getElem (by rw [o1.1, o2.1])
  intro τ t1 t2
  have hτ : τ < len := by have := o1.1; omega
  have e := congrArg (fun c => c.getD i 0) (h τ hτ)
  simp only [colOf_getD] at e
  have e1 : S.getD i [] = S[i] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  have e2 : S'.getD i [] = S'[i] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rw [e1, e2] at e
  have := congrArg GF.v e
  rw [at_v o1.2, at_v o2.2] at this
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem t1, List.getElem?_eq_getElem t2] using this

/-- **Whole symbols are recovered from any `k` of the block's symbols.** If the present symbols are those of the code
word of the data symbols `D` (the absent ones are anything), `reconstruct` on symbols of `len` bytes returns the whole
code word. -/
theorem reconSym_recovers (k m len : Nat) (hk1 : 1 ≤ k) (hn : k + m ≤ 255) (D : List Sym) (hD : D.length = k)
    (hDok : OkBlk len D) (blk : List Sym) (hb : blk.length = k + m) (hok : OkBlk len blk) (present : List Bool)
    (hp : present.length = k + m) (hk : k ≤ present.countP id)
    (hag : ∀ s, s < k + m → present.getD s false = true → blk.getD s [] = (encodeSym k m len D).getD s []) :
    reconSym k m len blk present = encodeSym k m len D := by
  obtain ⟨o1, l1, c1⟩ := reconSym_col k m len blk present hb hok hp hk
  obtain ⟨o2, l2, c2⟩ := encodeSym_spec k m len D hD hDok
  apply block_ext len _ _ o1 o2 (by rw [l1, l2])
  intro τ hτ
  have hdl : (colOf D τ).length = k := by simp [colOf, hD]
  have hcw : encodeCol k m (colOf D τ) = codeword k m (colOf D τ) := by
    unfold encodeCol codeword
    rw [List.take_of_length_le (by omega)]
  have hr := reconCol_ok (k := k) (m := m) (d := colOf D τ) (blk := colOf blk τ) (present := present) hk1 hn hdl
    (by simp [colOf, hb]) hp hk (fun s hs hps => by
      rw [colOf_getD, hag s hs hps, ← colOf_getD, c2 τ hτ, hcw])
  rw [c1 τ hτ] at hr
  have := Except.ok.inj hr
  rw [this, c2 τ hτ, hcw]

#print axioms mulAdd_spec
#print axioms scale_spec
#print axioms encodeSym_spec
#print axioms reconSym_col
#print axioms reconSym_recovers

end Pinc.DtnRsSym
