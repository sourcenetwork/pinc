import Vinc.DtnGf

/-!
# GF(2^8) as a field

The byte type `GF` with `+` the xor, `*` the table product `mulT` and `⁻¹` the table inverse `invT`, proved a field of
characteristic 2 (`Lean.Grind.Field` and `Lean.Grind.IsCharP`), so that the generic Cauchy development (`DtnCauchy`)
applies to the bytes the Reed-Solomon code works on.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Vinc.DtnGf

theorem eT_zero : eT 0 = 1 := by decide +kernel

theorem lT_one : lT 1 = 0 := by
  have := lT_eT 0 (by omega)
  rw [eT_zero] at this; simpa using this

theorem mulT_comm (a b : Nat) : mulT a b = mulT b a := by
  unfold mulT; by_cases h : a = 0 ∨ b = 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega), Nat.add_comm]

theorem mulT_zero_left (b : Nat) : mulT 0 b = 0 := by simp [mulT]
theorem mulT_zero_right (a : Nat) : mulT a 0 = 0 := by simp [mulT]

theorem mulT_one (a : Nat) (h : a < 256) : mulT a 1 = a := by
  by_cases h0 : a = 0
  · subst h0; exact mulT_zero_left 1
  · unfold mulT; rw [if_neg (by omega), lT_one, Nat.add_zero, eT_lT a h0 h]

theorem mulT_ne_zero (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a < 256) (hb' : b < 256) : mulT a b ≠ 0 := by
  unfold mulT; rw [if_neg (by omega)]
  exact eT_ne_zero _ (by have := lT_lt255 a ha'; have := lT_lt255 b hb'; omega)

theorem lT_mulT (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a < 256) (hb' : b < 256) :
    lT (mulT a b) = (lT a + lT b) % 255 := by
  unfold mulT; rw [if_neg (by omega)]
  exact lT_eT _ (by have := lT_lt255 a ha'; have := lT_lt255 b hb'; omega)

theorem mulT_nz (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) : mulT a b = eT (lT a + lT b) := by
  unfold mulT; rw [if_neg (by omega)]

theorem mulT_assoc (a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    mulT (mulT a b) c = mulT a (mulT b c) := by
  by_cases h0 : a = 0 ∨ b = 0 ∨ c = 0
  · rcases h0 with h | h | h <;> subst h <;> simp [mulT_zero_left, mulT_zero_right]
  · have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hc0 : c ≠ 0 := by omega
    have hab := mulT_ne_zero a b ha0 hb0 ha hb
    have hbc := mulT_ne_zero b c hb0 hc0 hb hc
    have la := lT_lt255 a ha; have lb := lT_lt255 b hb; have lc := lT_lt255 c hc
    rw [mulT_nz _ _ hab hc0, mulT_nz _ _ ha0 hbc, lT_mulT a b ha0 hb0 ha hb, lT_mulT b c hb0 hc0 hb hc,
      eT_mod _ (by omega), eT_mod (lT a + _) (by omega)]
    have h : ((lT a + lT b) % 255 + lT c) % 255 = (lT a + (lT b + lT c) % 255) % 255 := by omega
    rw [h]

theorem xor_lc (x y z : Nat) : x ^^^ (y ^^^ z) = y ^^^ (x ^^^ z) := by
  rw [← Nat.xor_assoc, Nat.xor_comm x y, Nat.xor_assoc]

theorem xx (x y : Nat) : x ^^^ (x ^^^ y) = y := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem pmulN_xor : ∀ (n a b c : Nat), pmulN n a (b ^^^ c) = pmulN n a b ^^^ pmulN n a c := by
  intro n
  induction n with
  | zero => intros; simp [pmulN]
  | succ n ih =>
    intro a b c
    simp only [pmulN]
    rw [Nat.shiftRight_xor_distrib, ih, Nat.and_xor_distrib_right, Nat.and_one_is_mod b, Nat.and_one_is_mod c]
    have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
    have hc : c % 2 = 0 ∨ c % 2 = 1 := by omega
    rcases hb with h1 | h1 <;> rcases hc with h2 | h2 <;>
      simp [h1, h2, Nat.xor_assoc, xor_lc, xx]

theorem mulT_xor (a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    mulT a (b ^^^ c) = mulT a b ^^^ mulT a c := by
  have hbc : b ^^^ c < 256 := by simpa using Nat.xor_lt_two_pow (n := 8) hb hc
  rw [mulT_eq_pmul a _ ha hbc, mulT_eq_pmul a b ha hb, mulT_eq_pmul a c ha hc]
  exact pmulN_xor 8 a b c

theorem invT_lt256 (a : Nat) : invT a < 256 := by
  unfold invT; split
  · omega
  · exact eT_lt256 _ (by omega)

theorem invT_ne_zero (a : Nat) (h0 : a ≠ 0) (h : a < 256) : invT a ≠ 0 := by
  unfold invT; rw [if_neg h0]
  exact eT_ne_zero _ (by omega)

theorem mulT_invT (a : Nat) (h0 : a ≠ 0) (h : a < 256) : mulT a (invT a) = 1 := by
  have hn := invT_ne_zero a h0 h
  have la := lT_lt255 a h
  have hi : invT a = eT (255 - lT a) := by unfold invT; rw [if_neg h0]
  rw [mulT_nz a _ h0 hn, hi, lT_eT _ (by omega)]
  by_cases hl : lT a = 0
  · rw [hl]; simp; exact eT_zero
  · have : (255 - lT a) % 255 = 255 - lT a := by omega
    rw [this, show lT a + (255 - lT a) = 0 + 255 by omega, eT_wrap 0 (by omega)]
    exact eT_zero

/-- A byte of GF(2^8). -/
structure GF where
  /-- The byte value. -/
  v : Nat
  /-- It is a byte. -/
  lt : v < 256

theorem GF.ext' {a b : GF} (h : a.v = b.v) : a = b := by
  cases a; cases b; simp at h; subst h; rfl

def GF.zero : GF := ⟨0, by omega⟩
def GF.one : GF := ⟨1, by omega⟩
def GF.add (a b : GF) : GF := ⟨a.v ^^^ b.v, by simpa using Nat.xor_lt_two_pow (n := 8) a.lt b.lt⟩
def GF.mul (a b : GF) : GF := ⟨mulT a.v b.v, mulT_lt256 _ _ a.lt b.lt⟩
def GF.inv (a : GF) : GF := ⟨invT a.v, invT_lt256 _⟩
def GF.natC (n : Nat) : GF := if n % 2 = 0 then GF.zero else GF.one
def GF.npow (a : GF) : Nat → GF
  | 0 => GF.one
  | n + 1 => GF.mul (GF.npow a n) a


open Lean.Grind in
def GF.zpow (a : GF) : Int → GF
  | Int.ofNat n => GF.npow a n
  | Int.negSucc n => GF.inv (GF.npow a (n + 1))

theorem GF.natC_zero : GF.natC 0 = GF.zero := by simp [GF.natC]
theorem GF.natC_one : GF.natC 1 = GF.one := by simp [GF.natC]
theorem GF.add_zero' (a : GF) : GF.add a GF.zero = a := GF.ext' (by simp [GF.add, GF.zero])
theorem GF.add_comm' (a b : GF) : GF.add a b = GF.add b a := GF.ext' (Nat.xor_comm _ _)
theorem GF.add_assoc' (a b c : GF) : GF.add (GF.add a b) c = GF.add a (GF.add b c) := GF.ext' (Nat.xor_assoc _ _ _)
theorem GF.add_self' (a : GF) : GF.add a a = GF.zero := GF.ext' (by simp [GF.add, GF.zero])
theorem GF.mul_comm' (a b : GF) : GF.mul a b = GF.mul b a := GF.ext' (mulT_comm _ _)
theorem GF.mul_assoc' (a b c : GF) : GF.mul (GF.mul a b) c = GF.mul a (GF.mul b c) :=
  GF.ext' (mulT_assoc _ _ _ a.lt b.lt c.lt)
theorem GF.mul_one' (a : GF) : GF.mul a GF.one = a := GF.ext' (mulT_one _ a.lt)
theorem GF.zero_mul' (a : GF) : GF.mul GF.zero a = GF.zero := GF.ext' (mulT_zero_left a.v)
theorem GF.left_distrib' (a b c : GF) : GF.mul a (GF.add b c) = GF.add (GF.mul a b) (GF.mul a c) :=
  GF.ext' (mulT_xor _ _ _ a.lt b.lt c.lt)
theorem GF.natC_succ (n : Nat) : GF.natC (n + 1) = GF.add (GF.natC n) GF.one := by
  unfold GF.natC
  by_cases h : n % 2 = 0
  · rw [if_pos h, if_neg (by omega)]; exact (GF.ext' (by simp [GF.add, GF.zero, GF.one])).symm
  · rw [if_neg h, if_pos (by omega)]; exact (GF.ext' (by simp [GF.add, GF.zero, GF.one])).symm
theorem GF.inv_zero' : GF.inv GF.zero = GF.zero := by apply GF.ext'; simp [GF.inv, GF.zero, invT]
theorem GF.mul_inv' (a : GF) (h : a ≠ GF.zero) : GF.mul a (GF.inv a) = GF.one :=
  GF.ext' (mulT_invT a.v (fun e => h (GF.ext' (b := GF.zero) e)) a.lt)
theorem GF.inv_one' : GF.inv GF.one = GF.one := by
  have := GF.mul_inv' GF.one (fun e => by cases e)
  rw [GF.mul_comm', GF.mul_one'] at this; exact this
theorem GF.inv_inv' (a : GF) : GF.inv (GF.inv a) = a := by
  by_cases h : a = GF.zero
  · subst h; rw [GF.inv_zero', GF.inv_zero']
  · have h1 := GF.mul_inv' a h
    have h2 : GF.inv a ≠ GF.zero := fun e => by
      rw [e] at h1; rw [GF.mul_comm', GF.zero_mul'] at h1; cases h1
    have h3 := GF.mul_inv' _ h2
    calc GF.inv (GF.inv a) = GF.mul (GF.inv (GF.inv a)) GF.one := (GF.mul_one' _).symm
      _ = GF.mul (GF.inv (GF.inv a)) (GF.mul (GF.inv a) a) := by rw [GF.mul_comm' (GF.inv a) a, h1]
      _ = GF.mul (GF.mul (GF.inv (GF.inv a)) (GF.inv a)) a := (GF.mul_assoc' _ _ _).symm
      _ = a := by rw [GF.mul_comm' (GF.inv (GF.inv a)) (GF.inv a), h3, GF.mul_comm', GF.mul_one']

open Lean.Grind in
instance : Lean.Grind.Field GF where
  add := GF.add
  mul := GF.mul
  natCast := ⟨GF.natC⟩
  ofNat := fun n => ⟨GF.natC n⟩
  nsmul := ⟨fun n a => GF.mul (GF.natC n) a⟩
  npow := ⟨GF.npow⟩
  add_zero := GF.add_zero'
  add_comm := GF.add_comm'
  add_assoc := GF.add_assoc'
  mul_assoc := GF.mul_assoc'
  mul_one := GF.mul_one'
  left_distrib := GF.left_distrib'
  zero_mul := GF.zero_mul'
  pow_zero := fun _ => rfl
  pow_succ := fun _ _ => rfl
  ofNat_succ := fun n => GF.natC_succ n
  neg := id
  sub := GF.add
  intCast := ⟨fun i => GF.natC i.natAbs⟩
  zsmul := ⟨fun i a => GF.mul (GF.natC i.natAbs) a⟩
  neg_add_cancel := fun a => by
    have := GF.add_self' a
    rw [GF.natC_zero]; exact this
  sub_eq_add_neg := fun _ _ => rfl
  neg_zsmul := fun i a => by
    show GF.mul (GF.natC (-i).natAbs) a = GF.mul (GF.natC i.natAbs) a
    rw [Int.natAbs_neg]
  mul_comm := GF.mul_comm'
  one_mul := fun a => by
    show GF.mul (GF.natC 1) a = a
    rw [GF.natC_one, GF.mul_comm']; exact GF.mul_one' a
  right_distrib := fun a b c => by
    show GF.mul (GF.add a b) c = GF.add (GF.mul a c) (GF.mul b c)
    rw [GF.mul_comm' (GF.add a b) c, GF.left_distrib', GF.mul_comm' c a, GF.mul_comm' c b]
  mul_zero := fun a => by
    show GF.mul a (GF.natC 0) = GF.natC 0
    rw [GF.natC_zero, GF.mul_comm']; exact GF.zero_mul' a
  intCast_neg := fun i => by
    show GF.natC (-i).natAbs = GF.natC i.natAbs
    rw [Int.natAbs_neg]
  inv := GF.inv
  div := fun a b => GF.mul a (GF.inv b)
  zpow := ⟨GF.zpow⟩
  div_eq_mul_inv := fun _ _ => rfl
  zero_ne_one := fun e => by cases e
  inv_zero := by rw [GF.natC_zero]; exact GF.inv_zero'
  mul_inv_cancel := fun {a} h => by rw [GF.natC_one]; exact GF.mul_inv' a h
  zpow_zero := fun _ => rfl
  zpow_succ := fun a n => rfl
  zpow_neg := fun a n => by
    cases n with
    | ofNat k =>
      cases k with
      | zero => show GF.npow a 0 = GF.inv (GF.npow a 0); exact GF.inv_one'.symm
      | succ k => rfl
    | negSucc k => exact (GF.inv_inv' _).symm


instance : Lean.Grind.IsCharP GF 2 where
  ofNat_ext_iff := fun {x y} => by
    show GF.natC x = GF.natC y ↔ x % 2 = y % 2
    unfold GF.natC
    by_cases hx : x % 2 = 0 <;> by_cases hy : y % 2 = 0 <;> simp [hx, hy, GF.zero, GF.one] <;> omega

/-- The byte `n mod 256` as a field element. -/
def GF.ofNat (n : Nat) : GF := ⟨n % 256, Nat.mod_lt _ (by omega)⟩

theorem GF.ofNat_v (n : Nat) (h : n < 256) : (GF.ofNat n).v = n := Nat.mod_eq_of_lt h

/-- Field addition is the xor of the bytes. -/
theorem GF.add_v (a b : GF) : (a + b).v = a.v ^^^ b.v := rfl

/-- Field multiplication is the table product. -/
theorem GF.mul_v (a b : GF) : (a * b).v = mulT a.v b.v := rfl

/-- Field inversion is the table inverse. -/
theorem GF.inv_v (a : GF) : a⁻¹.v = invT a.v := rfl


#audit_axioms Vinc.DtnGf.mulT_assoc
#audit_axioms Vinc.DtnGf.mulT_xor
#audit_axioms Vinc.DtnGf.mulT_invT

end Vinc.DtnGf
