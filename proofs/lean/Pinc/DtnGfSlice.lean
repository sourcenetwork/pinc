import Pinc.DtnGfField

/-!
# The slice kernels of `gf256.rs`

`xor_into`, `mul_add` and `scale` work on whole slices. `mul_add` has three paths: `c = 0` does nothing, `c = 1` is
`xor_into`, and any other `c` looks the bytes up in the row `MUL[c]` and xors them into `dst` eight bytes at a time as
a `u64` (`from_le_bytes`, `^`, `to_le_bytes`), then a byte at a time for the last bytes. This file models the three
paths on byte lists and proves each equals the pointwise operation `dst[i] ^= c * src[i]` on the common length, which
is what lets the Reed-Solomon model (`DtnRs`) treat a block as independent byte columns. Bytes are `Nat` below 256.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Pinc.DtnGfSlice
open Pinc.DtnGf

/-- `u64::from_le_bytes`: the first byte is the least significant. -/
def fromLE : List Nat → Nat
  | [] => 0
  | b :: r => b ||| (fromLE r <<< 8)

/-- `u64::to_le_bytes` of an 8-byte word. -/
def toLE (w : Nat) : List Nat := (List.range 8).map fun i => (w >>> (8 * i)) &&& 255

theorem testBit_byte {b : Nat} (hb : b < 256) (j : Nat) (hj : 8 ≤ j) : b.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (by
    calc 256 = 2 ^ 8 := by decide
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj))

theorem fromLE_xor : ∀ (a b : List Nat), a.length = b.length → (∀ x ∈ a, x < 256) → (∀ x ∈ b, x < 256) →
    fromLE a ^^^ fromLE b = fromLE (List.zipWith (· ^^^ ·) a b) := by
  intro a
  induction a with
  | nil => intro b h _ _; cases b <;> simp_all [fromLE]
  | cons x a ih =>
    intro b h ha hb
    cases b with
    | nil => simp at h
    | cons y b =>
      have hx : x < 256 := ha x (by simp)
      have hy : y < 256 := hb y (by simp)
      have ih' := ih b (by simpa using h) (fun z hz => ha z (by simp [hz])) (fun z hz => hb z (by simp [hz]))
      simp only [fromLE, List.zipWith_cons_cons]
      apply Nat.eq_of_testBit_eq
      intro j
      simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hj : j < 8
      · have : ¬ 8 ≤ j := by omega
        simp [this]
      · have h8 : 8 ≤ j := by omega
        rw [testBit_byte hx j h8, testBit_byte hy j h8, ← ih', Nat.testBit_xor]
        simp [h8]


theorem byte_of_fromLE : ∀ (bs : List Nat) (i : Nat) (h : i < bs.length), (∀ x ∈ bs, x < 256) →
    (fromLE bs >>> (8 * i)) &&& 255 = bs[i] := by
  intro bs
  induction bs with
  | nil => intro i h; simp at h
  | cons x r ih =>
    intro i h hb
    have hx : x < 256 := hb x (by simp)
    cases i with
    | zero =>
      simp only [fromLE, Nat.mul_zero, Nat.shiftRight_zero, List.getElem_cons_zero]
      apply Nat.eq_of_testBit_eq
      intro j
      simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hj : j < 8
      · have : ¬ 8 ≤ j := by omega
        have h255 : (255 : Nat).testBit j = true := by
          revert j; decide +revert
        simp [this, h255]
      · have h8 : 8 ≤ j := by omega
        have h255 : (255 : Nat).testBit j = false := testBit_byte (by omega) j h8
        simp [h255, testBit_byte hx j h8]
    | succ i =>
      have hi : i < r.length := by simpa using h
      have := ih i hi (fun z hz => hb z (by simp [hz]))
      simp only [List.getElem_cons_succ]
      rw [← this]
      apply Nat.eq_of_testBit_eq
      intro j
      simp only [fromLE, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
      have h1 : 8 * (i + 1) = 8 * i + 8 := by omega
      rw [h1]
      rw [testBit_byte hx (8 * i + 8 + j) (by omega), show 8 * i + 8 + j - 8 = 8 * i + j by omega]
      have h8 : 8 ≤ 8 * i + 8 + j := by omega
      simp [h8]

theorem toLE_fromLE (bs : List Nat) (h : bs.length = 8) (hb : ∀ x ∈ bs, x < 256) : toLE (fromLE bs) = bs := by
  apply List.ext_getElem
  · simp [toLE, h]
  · intro i h1 h2
    have hi : i < bs.length := by omega
    simp only [toLE, List.getElem_map, List.getElem_range]
    exact byte_of_fromLE bs i hi hb

theorem zipWith_xor_lt : ∀ (a b : List Nat), (∀ x ∈ a, x < 256) → (∀ x ∈ b, x < 256) →
    ∀ x ∈ List.zipWith (· ^^^ ·) a b, x < 256 := by
  intro a
  induction a with
  | nil => intro b _ _ x hx; simp at hx
  | cons x r ih =>
    intro b ha hb z hz
    cases b with
    | nil => simp at hz
    | cons y t =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Nat.xor_lt_two_pow (n := 8) (ha x (by simp)) (hb y (by simp))
      · exact ih t (fun w hw => ha w (by simp [hw])) (fun w hw => hb w (by simp [hw])) z hz

theorem zipWith_split (f : Nat → Nat → Nat) : ∀ (n : Nat) (d s : List Nat), n ≤ d.length → n ≤ s.length →
    List.zipWith f d s = List.zipWith f (d.take n) (s.take n) ++ List.zipWith f (d.drop n) (s.drop n) := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro d s hd hs
    cases d with
    | nil => simp at hd
    | cons x r =>
      cases s with
      | nil => simp at hs
      | cons y t =>
        simp only [List.zipWith_cons_cons, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
        rw [ih r t (by simpa using hd) (by simpa using hs)]

/-- One eight-byte step of the chunked path: `from_le_bytes(d) ^ from_le_bytes(looked)`, back to bytes. -/
def wordXor (d l : List Nat) : List Nat := toLE (fromLE d ^^^ fromLE l)

theorem wordXor_eq (d l : List Nat) (hd : d.length = 8) (hl : l.length = 8) (hdb : ∀ x ∈ d, x < 256)
    (hlb : ∀ x ∈ l, x < 256) : wordXor d l = List.zipWith (· ^^^ ·) d l := by
  unfold wordXor
  rw [fromLE_xor d l (by omega) hdb hlb]
  apply toLE_fromLE
  · simp [hd, hl]
  · exact zipWith_xor_lt d l hdb hlb

/-- `xor_into`: `dst ^= src` for the common length. -/
def xorInto (dst src : List Nat) : List Nat := List.zipWith (· ^^^ ·) dst src ++ dst.drop src.length

/-- The chunked path of `mul_add` for `c >= 2`, on slices of the same length: eight bytes at a time, then the rest. -/
def chunkedF (c : Nat) : Nat → List Nat → List Nat → List Nat
  | 0, d, _ => d
  | f + 1, d, s =>
    if 8 ≤ d.length then wordXor (d.take 8) ((s.take 8).map (mulT c)) ++ chunkedF c f (d.drop 8) (s.drop 8)
    else List.zipWith (fun a b => a ^^^ mulT c b) d s

/-- `mul_add`: `dst ^= c * src` for the common length, by the three paths of the code. -/
def mulAdd (dst src : List Nat) (c : Nat) : List Nat :=
  if c = 0 then dst
  else if c = 1 then xorInto dst src
  else
    let n := min dst.length src.length
    chunkedF c n (dst.take n) (src.take n) ++ dst.drop n

/-- `scale`: `buf = c * buf`. -/
def scaleL (buf : List Nat) (c : Nat) : List Nat :=
  if c = 1 then buf else if c = 0 then buf.map fun _ => 0 else buf.map (mulT c)

/-- The pointwise operation. -/
def refMulAdd (c : Nat) (dst src : List Nat) : List Nat :=
  List.zipWith (fun a b => a ^^^ mulT c b) dst src ++ dst.drop src.length

theorem mulT_lt (c b : Nat) (hc : c < 256) (hb : b < 256) : mulT c b < 256 := mulT_lt256 c b hc hb

theorem chunkedF_eq (c : Nat) (hc : c < 256) : ∀ (f : Nat) (d s : List Nat), d.length = s.length → d.length ≤ f →
    (∀ x ∈ d, x < 256) → (∀ x ∈ s, x < 256) →
    chunkedF c f d s = List.zipWith (fun a b => a ^^^ mulT c b) d s := by
  intro f
  induction f with
  | zero =>
    intro d s h1 h2 _ _
    have : d = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; simp [chunkedF]
  | succ f ih =>
    intro d s h1 h2 hd hs
    unfold chunkedF
    by_cases h8 : 8 ≤ d.length
    · rw [if_pos h8]
      have hlen : (s.take 8).length = 8 := by rw [List.length_take]; omega
      have hmap : ((s.take 8).map (mulT c)).length = 8 := by rw [List.length_map, hlen]
      rw [wordXor_eq (d.take 8) ((s.take 8).map (mulT c)) (by rw [List.length_take]; omega) hmap
        (fun x hx => hd x (List.mem_of_mem_take hx))
        (fun x hx => by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          exact mulT_lt c b hc (hs b (List.mem_of_mem_take hb)))]
      rw [ih (d.drop 8) (s.drop 8) (by simp; omega) (by simp; omega)
        (fun x hx => hd x (List.mem_of_mem_drop hx)) (fun x hx => hs x (List.mem_of_mem_drop hx))]
      rw [zipWith_split _ 8 d s h8 (by omega)]
      congr 1
      rw [List.zipWith_map_right]
    · rw [if_neg h8]

/-- All three paths of `mul_add` are the pointwise operation. -/
theorem mulAdd_eq (c : Nat) (hc : c < 256) (dst src : List Nat) (hd : ∀ x ∈ dst, x < 256) (hs : ∀ x ∈ src, x < 256) :
    mulAdd dst src c = refMulAdd c dst src := by
  unfold mulAdd
  by_cases h0 : c = 0
  · rw [if_pos h0]; subst h0
    unfold refMulAdd
    have : List.zipWith (fun a b => a ^^^ mulT 0 b) dst src = dst.take src.length := by
      induction dst generalizing src with
      | nil => simp
      | cons x r ih =>
        cases src with
        | nil => simp
        | cons y t =>
          rw [List.zipWith_cons_cons, List.length_cons, List.take_succ_cons,
            ih t (fun z hz => hd z (by simp [hz])) (fun z hz => hs z (by simp [hz])), mulT_zero_left, Nat.xor_zero]
    rw [this, List.take_append_drop]
  · rw [if_neg h0]
    by_cases h1 : c = 1
    · rw [if_pos h1]; subst h1
      unfold xorInto refMulAdd
      congr 1
      have : ∀ (a b : List Nat), (∀ x ∈ b, x < 256) →
          List.zipWith (· ^^^ ·) a b = List.zipWith (fun x y => x ^^^ mulT 1 y) a b := by
        intro a b hb
        induction a generalizing b with
        | nil => simp
        | cons x r ih =>
          cases b with
          | nil => simp
          | cons y t =>
            simp only [List.zipWith_cons_cons]
            rw [mulT_comm, mulT_one y (hb y (by simp)), ih t (fun z hz => hb z (by simp [hz]))]
      exact this dst src hs
    · rw [if_neg h1]
      unfold refMulAdd
      simp only []
      have hn : min dst.length src.length ≤ min dst.length src.length := Nat.le_refl _
      rw [chunkedF_eq c hc _ _ _ (by simp) (by simp) (fun x hx => hd x (List.mem_of_mem_take hx))
        (fun x hx => hs x (List.mem_of_mem_take hx))]
      -- zipping the truncated slices is zipping the slices, and the tail past the common length is untouched
      have hz : ∀ (a b : List Nat), List.zipWith (fun x y => x ^^^ mulT c y) (a.take (min a.length b.length))
          (b.take (min a.length b.length)) = List.zipWith (fun x y => x ^^^ mulT c y) a b := by
        intro a b
        induction a generalizing b with
        | nil => simp
        | cons x r ih =>
          cases b with
          | nil => simp
          | cons y t =>
            simp only [List.length_cons, Nat.add_min_add_right, List.take_succ_cons, List.zipWith_cons_cons]
            rw [ih t]
      rw [hz]
      congr 1
      cases Nat.le_total dst.length src.length with
      | inl h => simp [Nat.min_eq_left h, List.drop_eq_nil_of_le h]
      | inr h => simp [Nat.min_eq_right h]

/-- `scale` is the pointwise product. -/
theorem scale_eq (c : Nat) (hc : c < 256) (buf : List Nat) (hb : ∀ x ∈ buf, x < 256) :
    scaleL buf c = buf.map (mulT c) := by
  unfold scaleL
  by_cases h1 : c = 1
  · rw [if_pos h1]; subst h1
    have : buf.map (mulT 1) = buf.map id :=
      List.map_congr_left (fun x hx => by rw [mulT_comm]; exact mulT_one x (hb x hx))
    rw [this]; simp
  · rw [if_neg h1]
    by_cases h0 : c = 0
    · rw [if_pos h0]; subst h0; simp [mulT_zero_left]
    · rw [if_neg h0]

/-- The kernels never leave the byte range. -/
theorem mulAdd_len (c : Nat) (hc : c < 256) (dst src : List Nat) (hd : ∀ x ∈ dst, x < 256) (hs : ∀ x ∈ src, x < 256) :
    (mulAdd dst src c).length = dst.length := by
  rw [mulAdd_eq c hc dst src hd hs]; unfold refMulAdd
  simp only [List.length_append, List.length_zipWith, List.length_drop]; omega

#audit_axioms Pinc.DtnGfSlice.mulAdd_eq
#audit_axioms Pinc.DtnGfSlice.scale_eq
#audit_axioms Pinc.DtnGfSlice.wordXor_eq

end Pinc.DtnGfSlice
