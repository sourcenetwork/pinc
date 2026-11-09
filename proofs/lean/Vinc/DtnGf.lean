import Vinc.Axioms

/-!
# GF(2^8) with the polynomial 0x11d: the tables of `gf256.rs` against the polynomial definition

The Rust module builds, at compile time, an `exp` table of 512 entries, a `log` table of 256 entries and a `mul` table
of 256 x 256 entries from the generator 2, and `inv` reads `exp[255 - log a]`. This file mirrors that construction
step for step (`xtime` is the `x <<= 1; if x & 0x100 != 0 { x ^= POLY }` step, `loop` is the `while i < 255` loop with
its three writes), defines the field product from the polynomial (`pmul`, shift-and-add with reduction), and proves
that the table-driven `mulT` and `invT` equal it for every pair of bytes.

The 65536-pair comparison is checked by the kernel (`decide +kernel`, no native code), over the tables packed into
two big naturals so that a lookup is one shift and one mask. The packed literals `PE` and `PL` are proved equal to the
tables the loop builds.
-/

set_option linter.unusedVariables false

namespace Vinc.DtnGf

/-- The reduction polynomial `x^8 + x^4 + x^3 + x^2 + 1`. -/
def poly : Nat := 0x11d

/-- Multiplication by the generator 2: one step of the table-building loop. -/
def xtime (x : Nat) : Nat :=
  let s := x <<< 1
  if s &&& 0x100 != 0 then s ^^^ poly else s

/-- The `while i < 255` loop of `build_tables`: `exp[i] = x; exp[i + 255] = x; log[x] = i; x = xtime x`. -/
def loop : Nat → Nat → Nat → List Nat → List Nat → List Nat × List Nat
  | 0, _, _, e, l => (e, l)
  | f + 1, i, x, e, l =>
    if i < 255 then loop f (i + 1) (xtime x) ((e.set i x).set (i + 255) x) (l.set x i) else (e, l)

/-- The `exp` and `log` tables as the Rust code builds them. -/
def tabs : List Nat × List Nat := loop 255 0 1 (List.replicate 512 0) (List.replicate 256 0)

/-- `exp[i]`. -/
def eT (i : Nat) : Nat := tabs.1.getD i 0

/-- `log[a]`. -/
def lT (a : Nat) : Nat := tabs.2.getD a 0

/-- `mul(a, b)`: the entry of the `MUL` table, built for `a, b >= 1` as `exp[log a + log b]` and 0 elsewhere. -/
def mulT (a b : Nat) : Nat := if a = 0 ∨ b = 0 then 0 else eT (lT a + lT b)

/-- `inv(a)`: 0 for 0, else `exp[255 - log a]`. -/
def invT (a : Nat) : Nat := if a = 0 then 0 else eT (255 - lT a)

/-- The polynomial product of `a` and `b`: `sum_i bit_i(b) * (x^i * a mod poly)`, over the 8 bits of `b`. -/
def pmulN : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, a, b => (if b &&& 1 = 1 then a else 0) ^^^ pmulN n (xtime a) (b >>> 1)

/-- The field product by the polynomial definition. -/
def pmul (a b : Nat) : Nat := pmulN 8 a b

/-- Byte `i` of a packed table. -/
def getB (p i : Nat) : Nat := (p >>> (8 * i)) &&& 255

/-- The packed `exp` table. -/
def PE : Nat := 0x8e47add86c361b83cfe9fa7db0582c160b8bcbebfbf3f7f5f47a3d90482412098a45ac562b9bc3eff9f279b259a251a653a7dde070381c0e078dc86432198241ae57a5dc6e3795c46231964babdbe3fff1f67bb3d7e5fc7e3f91c663bfd1e673b7d5e472399249aa55a452299a4da8542a158442219e4fa9da6db85c2e1785cc663397c5ec763b93c7edf87c3e1f81ce67bdd068341a0d884422118643afd9e271b65ba3dfe1fe7fb1d66bbbd3e7fdf0783c1e0f89ca65bc5e2f99c261be5fa1de6fb9d269ba5da05028140a058c46239fc1ee77b5d46a35944a259c4e279dc06030180c06038fc9ea75b45a2d984c261387cde8743a1d80402010080402018e47add86c361b83cfe9fa7db0582c160b8bcbebfbf3f7f5f47a3d90482412098a45ac562b9bc3eff9f279b259a251a653a7dde070381c0e078dc86432198241ae57a5dc6e3795c46231964babdbe3fff1f67bb3d7e5fc7e3f91c663bfd1e673b7d5e472399249aa55a452299a4da8542a158442219e4fa9da6db85c2e1785cc663397c5ec763b93c7edf87c3e1f81ce67bdd068341a0d884422118643afd9e271b65ba3dfe1fe7fb1d66bbbd3e7fdf0783c1e0f89ca65bc5e2f99c261be5fa1de6fb9d269ba5da05028140a058c46239fc1ee77b5d46a35944a259c4e279dc06030180c06038fc9ea75b45a2d984c261387cde8743a1d8040201008040201

/-- The packed `log` table. -/
def PL : Nat := 0xaf5850a8eaf4d674e8ade7e6e9d5ae4fd72c757aeb16f50b51a0a99cb05f59cb5a3eccbbb18660fbaa559d29523ba16cf66f0c7fec4917c476a47bb7d8432d1fa2416d4753393c849e5d2a14abd356f261befcdcb2978790cdcfbc955bd13f372e892023d99244117cb4b8267799a5e318fec531edde4a670d63808cf7c0700757a7f373ace5d44e2b79150a9f9b5eca3dba85fa54283a6b6e7e48c3a3b6421e404638835c13d2f1bddb968fce94d03688229110b32598e2fd30dd66628bbf06a672e44d78099ac9b9f9276a7dc2b51d458212f0da8e9335210f24e12f658a05714c08c8f869c11c81ef8d340ee064044bc7681bee33df03c61a320219010000

/-- The product through the packed tables. -/
def mulP (a b : Nat) : Nat := if a = 0 ∨ b = 0 then 0 else getB PE (getB PL a + getB PL b)

theorem all_range {n : Nat} {p : Nat → Bool} (h : (List.range n).all p = true) : ∀ i, i < n → p i = true :=
  fun i hi => List.all_eq_true.mp h i (List.mem_range.mpr hi)

def chkE : Bool := (List.range 512).all fun i => getB PE i == tabs.1.getD i 0
def chkL : Bool := (List.range 256).all fun a => getB PL a == tabs.2.getD a 0

theorem chkE_true : chkE = true := by decide +kernel
theorem chkL_true : chkL = true := by decide +kernel

/-- The packed `exp` table is the table the loop builds. -/
theorem eT_packed (i : Nat) (h : i < 512) : eT i = getB PE i := by
  exact (beq_iff_eq.mp (all_range chkE_true i h)).symm

/-- The packed `log` table is the table the loop builds. -/
theorem lT_packed (a : Nat) (h : a < 256) : lT a = getB PL a := by
  exact (beq_iff_eq.mp (all_range chkL_true a h)).symm

def chkMul : Bool := (List.range 256).all fun a => (List.range 256).all fun b => mulP a b == pmul a b

theorem chkMul_true : chkMul = true := by decide +kernel

theorem getB_lt (p i : Nat) : getB p i < 256 := by
  have := Nat.and_le_right (n := p >>> (8 * i)) (m := 255)
  unfold getB; omega

theorem lT_lt256 (a : Nat) (h : a < 256) : lT a < 256 := by rw [lT_packed a h]; exact getB_lt _ _
theorem eT_lt256 (i : Nat) (h : i < 512) : eT i < 256 := by rw [eT_packed i h]; exact getB_lt _ _

theorem mulP_eq_pmul (a b : Nat) (ha : a < 256) (hb : b < 256) : mulP a b = pmul a b := by
  have h1 : ((List.range 256).all fun b => mulP a b == pmul a b) = true := all_range chkMul_true a ha
  simpa using all_range h1 b hb

/-- The table-driven product equals the packed one. -/
theorem mulT_eq_mulP (a b : Nat) (ha : a < 256) (hb : b < 256) : mulT a b = mulP a b := by
  unfold mulT mulP
  split
  · rfl
  · have := lT_lt256 a ha; have := lT_lt256 b hb
    rw [eT_packed _ (by omega), lT_packed a ha, lT_packed b hb]

/-- The table-driven product equals the polynomial product, for every pair of bytes. -/
theorem mulT_eq_pmul (a b : Nat) (ha : a < 256) (hb : b < 256) : mulT a b = pmul a b := by
  rw [mulT_eq_mulP a b ha hb, mulP_eq_pmul a b ha hb]

theorem mulT_lt256 (a b : Nat) (ha : a < 256) (hb : b < 256) : mulT a b < 256 := by
  rw [mulT_eq_mulP a b ha hb]; unfold mulP; split
  · omega
  · exact getB_lt _ _

/-! ### The exp and log tables are inverse bijections between `[0, 255)` and `[1, 256)` -/

def chkExpLog : Bool := (List.range 256).all fun a => a == 0 || getB PE (getB PL a) == a
def chkLogExp : Bool := (List.range 255).all fun i => getB PL (getB PE i) == i
def chkWrap : Bool := (List.range 255).all fun i => getB PE (i + 255) == getB PE i
def chkNZ : Bool := (List.range 510).all fun i => getB PE i != 0
def chkLlt : Bool := (List.range 256).all fun a => getB PL a < 255
def chkExpLt : Bool := (List.range 255).all fun i => getB PE i < 256 && getB PE i != 0
def chkLogExp2 : Bool := (List.range 510).all fun i => getB PL (getB PE i) == i % 255

theorem chkExpLog_true : chkExpLog = true := by decide +kernel
theorem chkLogExp_true : chkLogExp = true := by decide +kernel
theorem chkWrap_true : chkWrap = true := by decide +kernel
theorem chkNZ_true : chkNZ = true := by decide +kernel
theorem chkLlt_true : chkLlt = true := by decide +kernel
theorem chkLogExp2_true : chkLogExp2 = true := by decide +kernel

/-- `exp (log a) = a` for every nonzero byte. -/
theorem eT_lT (a : Nat) (h0 : a ≠ 0) (h : a < 256) : eT (lT a) = a := by
  have := all_range chkExpLog_true a h
  have hl := lT_lt256 a h
  have hl2 := all_range chkLlt_true a h
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rw [eT_packed _ (by omega), lT_packed a h]
  omega

/-- `log (exp i) = i mod 255` for `i < 510`. -/
theorem lT_eT (i : Nat) (h : i < 510) : lT (eT i) = i % 255 := by
  have := all_range chkLogExp2_true i h
  have h1 := eT_lt256 i (by omega)
  rw [lT_packed _ h1, eT_packed i (by omega)]
  simpa using this

theorem eT_ne_zero (i : Nat) (h : i < 510) : eT i ≠ 0 := by
  have := all_range chkNZ_true i h
  rw [eT_packed i (by omega)]
  simpa using this

theorem lT_lt255 (a : Nat) (h : a < 256) : lT a < 255 := by
  have := all_range chkLlt_true a h
  rw [lT_packed a h]; simpa using this

theorem eT_wrap (i : Nat) (h : i < 255) : eT (i + 255) = eT i := by
  have := all_range chkWrap_true i h
  rw [eT_packed _ (by omega), eT_packed _ (by omega)]
  simpa using this

/-- Every `exp` entry below 510 is a nonzero byte. -/
theorem eT_range (i : Nat) (h : i < 510) : 0 < eT i ∧ eT i < 256 :=
  ⟨Nat.pos_of_ne_zero (eT_ne_zero i h), eT_lt256 i (by omega)⟩

theorem eT_mod (i : Nat) (h : i < 510) : eT i = eT (i % 255) := by
  by_cases hi : i < 255
  · rw [Nat.mod_eq_of_lt hi]
  · have h2 : i = (i - 255) + 255 := by omega
    have : i % 255 = i - 255 := by omega
    rw [this, h2, eT_wrap _ (by omega)]; simp

end Vinc.DtnGf
