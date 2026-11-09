import Vinc.ConnectTicketText

/-!
# Base32 of the ticket text: round trip and canonical form

`b32enc` and `b32dec` (the loops of `to_text` and `from_text` over the `u32` accumulator) are shown to be the block
codes they implement: five bytes make eight symbols, and the accumulator returns to no pending bit after every
block, whatever junk its high bits hold. A byte string of `5q + k` bytes makes `8q` symbols and then `0, 2, 4, 5` or
`7` for `k = 0` to `4`; the decoder returns it, and refuses every other number of symbols, any leftover bit that is
set, and a result of more than 144 bytes.

* `b32_roundtrip`: decoding the symbols of a byte string of at most 144 bytes returns it.
* `b32dec_inv`: a symbol string that decodes is the symbols of the bytes it returned (`b32Of`), so a text has one
  accepted spelling up to case.
-/

namespace Vinc.ConnCodec

theorem drain_lt (acc bits : Nat) (out : List Nat) (h : bits < 5) : b32drain acc bits out = (bits, out) := by
  rw [b32drain]; simp [Nat.not_le.2 h]

theorem drain_ge (acc bits : Nat) (out : List Nat) (h : 5 ≤ bits) :
    b32drain acc bits out = b32drain acc (bits - 5) (out ++ [(acc / 2 ^ (bits - 5)) % 32]) := by
  rw [b32drain]; simp [h]

/-- The accumulator after taking byte `b` (`acc << 8 | b` on a `u32`). -/
def stepAcc (acc b : Nat) : Nat := (acc * 256) % 2 ^ 32 + b

/-- The accumulator after taking symbol `s` (`acc << 5 | s` on a `u32`). -/
def stepDec (acc s : Nat) : Nat := (acc * 32) % 2 ^ 32 + s

/-- The symbols of five bytes. -/
def e5 (b0 b1 b2 b3 b4 : Nat) : List Nat :=
  [b0 / 8, (b0 % 8) * 4 + b1 / 64, (b1 / 2) % 32, (b1 % 2) * 16 + b2 / 16, (b2 % 16) * 2 + b3 / 128, (b3 / 4) % 32,
    (b3 % 4) * 8 + b4 / 32, b4 % 32]

/-- The symbols of one to four bytes at the end of a string: the last symbol is padded with zero bits. -/
def etail : List Nat → List Nat
  | [b0] => [b0 / 8, (b0 % 8) * 4]
  | [b0, b1] => [b0 / 8, (b0 % 8) * 4 + b1 / 64, (b1 / 2) % 32, (b1 % 2) * 16]
  | [b0, b1, b2] => [b0 / 8, (b0 % 8) * 4 + b1 / 64, (b1 / 2) % 32, (b1 % 2) * 16 + b2 / 16, (b2 % 16) * 2]
  | [b0, b1, b2, b3] =>
    [b0 / 8, (b0 % 8) * 4 + b1 / 64, (b1 / 2) % 32, (b1 % 2) * 16 + b2 / 16, (b2 % 16) * 2 + b3 / 128, (b3 / 4) % 32,
      (b3 % 4) * 8]
  | _ => []

/-- The symbols of a byte string, block by block. -/
def symsOf : List Nat → List Nat
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => e5 b0 b1 b2 b3 b4 ++ symsOf rest
  | bs => etail bs

theorem enc0 (acc b : Nat) (bs out : List Nat) :
    b32enc (b :: bs) acc 0 out = b32enc bs (stepAcc acc b) 3 (out ++ [(stepAcc acc b / 8) % 32]) := by
  simp [b32enc, stepAcc, drain_ge, drain_lt]

theorem enc3 (acc b : Nat) (bs out : List Nat) :
    b32enc (b :: bs) acc 3 out =
      b32enc bs (stepAcc acc b) 1 (out ++ [(stepAcc acc b / 64) % 32, (stepAcc acc b / 2) % 32]) := by
  simp [b32enc, stepAcc, drain_ge, drain_lt]

theorem enc1 (acc b : Nat) (bs out : List Nat) :
    b32enc (b :: bs) acc 1 out = b32enc bs (stepAcc acc b) 4 (out ++ [(stepAcc acc b / 16) % 32]) := by
  simp [b32enc, stepAcc, drain_ge, drain_lt]

theorem enc4 (acc b : Nat) (bs out : List Nat) :
    b32enc (b :: bs) acc 4 out =
      b32enc bs (stepAcc acc b) 2 (out ++ [(stepAcc acc b / 128) % 32, (stepAcc acc b / 4) % 32]) := by
  simp [b32enc, stepAcc, drain_ge, drain_lt]

theorem enc2 (acc b : Nat) (bs out : List Nat) :
    b32enc (b :: bs) acc 2 out =
      b32enc bs (stepAcc acc b) 0 (out ++ [(stepAcc acc b / 32) % 32, stepAcc acc b % 32]) := by
  simp [b32enc, stepAcc, drain_ge, drain_lt]

theorem enc_nil (acc bits : Nat) (out : List Nat) :
    b32enc [] acc bits out = if 0 < bits then out ++ [(acc * 2 ^ (5 - bits)) % 32] else out := by
  simp [b32enc]

theorem enc_block (acc : Nat) (out rest : List Nat) (b0 b1 b2 b3 b4 : Nat) (h0 : b0 < 256) (h1 : b1 < 256)
    (h2 : b2 < 256) (h3 : b3 < 256) (h4 : b4 < 256) :
    b32enc (b0 :: b1 :: b2 :: b3 :: b4 :: rest) acc 0 out =
      b32enc rest (stepAcc (stepAcc (stepAcc (stepAcc (stepAcc acc b0) b1) b2) b3) b4) 0
        (out ++ e5 b0 b1 b2 b3 b4) := by
  rw [enc0, enc3, enc1, enc4, enc2]
  simp only [List.append_assoc, stepAcc, e5, List.cons_append, List.nil_append]
  congr 2
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem enc_tail (acc : Nat) (out : List Nat) (bs : List Nat) (hl : bs.length ≤ 4) (hb : ∀ b ∈ bs, b < 256) :
    b32enc bs acc 0 out = out ++ etail bs := by
  match bs, hl with
  | [], _ => simp [enc_nil, etail]
  | [b0], _ =>
    have := hb b0 (by simp)
    rw [enc0, enc_nil]; simp [stepAcc, etail]; omega
  | [b0, b1], _ =>
    have := hb b0 (by simp); have := hb b1 (by simp)
    rw [enc0, enc3, enc_nil]; simp [stepAcc, etail]; omega
  | [b0, b1, b2], _ =>
    have := hb b0 (by simp); have := hb b1 (by simp); have := hb b2 (by simp)
    rw [enc0, enc3, enc1, enc_nil]; simp [stepAcc, etail]; omega
  | [b0, b1, b2, b3], _ =>
    have := hb b0 (by simp); have := hb b1 (by simp); have := hb b2 (by simp); have := hb b3 (by simp)
    rw [enc0, enc3, enc1, enc4, enc_nil]; simp [stepAcc, etail]; omega
  | _ :: _ :: _ :: _ :: _ :: _, h => simp at h

/-- The encoder is the block code, whatever the junk in the accumulator. -/
theorem enc_syms : ∀ (bs : List Nat), (∀ b ∈ bs, b < 256) → ∀ acc out, b32enc bs acc 0 out = out ++ symsOf bs
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest, hb, acc, out => by
    rw [enc_block _ _ _ _ _ _ _ _ (hb b0 (by simp)) (hb b1 (by simp)) (hb b2 (by simp)) (hb b3 (by simp))
      (hb b4 (by simp))]
    rw [enc_syms rest (fun b hb' => hb b (by simp [hb'])) _ _]
    simp [symsOf, List.append_assoc]
  | [], _, acc, out => by simp [enc_nil, symsOf, etail]
  | [b0], hb, acc, out => by rw [enc_tail _ _ _ (by simp) hb]; simp [symsOf]
  | [b0, b1], hb, acc, out => by rw [enc_tail _ _ _ (by simp) hb]; simp [symsOf]
  | [b0, b1, b2], hb, acc, out => by rw [enc_tail _ _ _ (by simp) hb]; simp [symsOf]
  | [b0, b1, b2, b3], hb, acc, out => by rw [enc_tail _ _ _ (by simp) hb]; simp [symsOf]

theorem b32Of_eq (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) : b32Of bs = symsOf bs := by
  simpa [b32Of] using enc_syms bs hb 0 []

/-! ## The decoder -/

theorem dec0 (acc s : Nat) (ss out : List Nat) : b32dec (s :: ss) acc 0 out = b32dec ss (stepDec acc s) 5 out := by
  simp [b32dec, stepDec]

theorem dec5 (acc s : Nat) (ss out : List Nat) (h : out.length < 144) :
    b32dec (s :: ss) acc 5 out = b32dec ss (stepDec acc s) 2 (out ++ [(stepDec acc s / 4) % 256]) := by
  simp [b32dec, stepDec, Nat.not_le.2 h]

theorem dec2 (acc s : Nat) (ss out : List Nat) : b32dec (s :: ss) acc 2 out = b32dec ss (stepDec acc s) 7 out := by
  simp [b32dec, stepDec]

theorem dec7 (acc s : Nat) (ss out : List Nat) (h : out.length < 144) :
    b32dec (s :: ss) acc 7 out = b32dec ss (stepDec acc s) 4 (out ++ [(stepDec acc s / 16) % 256]) := by
  simp [b32dec, stepDec, Nat.not_le.2 h]

theorem dec4 (acc s : Nat) (ss out : List Nat) (h : out.length < 144) :
    b32dec (s :: ss) acc 4 out = b32dec ss (stepDec acc s) 1 (out ++ [(stepDec acc s / 2) % 256]) := by
  simp [b32dec, stepDec, Nat.not_le.2 h]

theorem dec1 (acc s : Nat) (ss out : List Nat) : b32dec (s :: ss) acc 1 out = b32dec ss (stepDec acc s) 6 out := by
  simp [b32dec, stepDec]

theorem dec6 (acc s : Nat) (ss out : List Nat) (h : out.length < 144) :
    b32dec (s :: ss) acc 6 out = b32dec ss (stepDec acc s) 3 (out ++ [(stepDec acc s / 8) % 256]) := by
  simp [b32dec, stepDec, Nat.not_le.2 h]

theorem dec3 (acc s : Nat) (ss out : List Nat) (h : out.length < 144) :
    b32dec (s :: ss) acc 3 out = b32dec ss (stepDec acc s) 0 (out ++ [stepDec acc s % 256]) := by
  simp [b32dec, stepDec, Nat.not_le.2 h]

theorem dec5e (acc s : Nat) (ss out : List Nat) (h : 144 ≤ out.length) : b32dec (s :: ss) acc 5 out = .error .text := by
  simp [b32dec, h]

theorem dec7e (acc s : Nat) (ss out : List Nat) (h : 144 ≤ out.length) : b32dec (s :: ss) acc 7 out = .error .text := by
  simp [b32dec, h]

theorem dec4e (acc s : Nat) (ss out : List Nat) (h : 144 ≤ out.length) : b32dec (s :: ss) acc 4 out = .error .text := by
  simp [b32dec, h]

theorem dec6e (acc s : Nat) (ss out : List Nat) (h : 144 ≤ out.length) : b32dec (s :: ss) acc 6 out = .error .text := by
  simp [b32dec, h]

theorem dec3e (acc s : Nat) (ss out : List Nat) (h : 144 ≤ out.length) : b32dec (s :: ss) acc 3 out = .error .text := by
  simp [b32dec, h]

theorem decEnd (acc bits : Nat) (out : List Nat) :
    b32dec [] acc bits out = if 5 ≤ bits ∨ acc % 2 ^ bits ≠ 0 then .error .text else .ok out := by
  simp [b32dec]

/-- The five bytes of eight symbols. -/
def d5 (s0 s1 s2 s3 s4 s5 s6 s7 : Nat) : List Nat :=
  [s0 * 8 + s1 / 4, (s1 % 4) * 64 + s2 * 2 + s3 / 16, (s3 % 16) * 16 + s4 / 2, (s4 % 2) * 128 + s5 * 4 + s6 / 8,
    (s6 % 8) * 32 + s7]

theorem dec_block (acc : Nat) (out rest : List Nat) (s0 s1 s2 s3 s4 s5 s6 s7 : Nat) (h0 : s0 < 32) (h1 : s1 < 32)
    (h2 : s2 < 32) (h3 : s3 < 32) (h4 : s4 < 32) (h5 : s5 < 32) (h6 : s6 < 32) (h7 : s7 < 32) :
    b32dec (s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: s6 :: s7 :: rest) acc 0 out =
      if out.length + 5 ≤ 144 then
        b32dec rest (stepDec (stepDec (stepDec (stepDec (stepDec (stepDec (stepDec (stepDec acc s0) s1) s2) s3) s4) s5) s6) s7)
          0 (out ++ d5 s0 s1 s2 s3 s4 s5 s6 s7)
      else .error .text := by
  by_cases hl : out.length + 5 ≤ 144
  · rw [if_pos hl, dec0, dec5 _ _ _ _ (by omega), dec2, dec7 _ _ _ _ (by simp; omega), dec4 _ _ _ _ (by simp; omega),
      dec1, dec6 _ _ _ _ (by simp; omega), dec3 _ _ _ _ (by simp; omega)]
    simp only [List.append_assoc, stepDec, d5, List.cons_append, List.nil_append]
    congr 2
    simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · rw [if_neg hl, dec0]
    rcases (by omega : 144 ≤ out.length ∨ out.length = 143 ∨ out.length = 142 ∨ out.length = 141 ∨ out.length = 140)
      with h | h | h | h | h
    · rw [dec5e _ _ _ _ h]
    · rw [dec5 _ _ _ _ (by omega), dec2, dec7e _ _ _ _ (by simp; omega)]
    · rw [dec5 _ _ _ _ (by omega), dec2, dec7 _ _ _ _ (by simp; omega), dec4e _ _ _ _ (by simp; omega)]
    · rw [dec5 _ _ _ _ (by omega), dec2, dec7 _ _ _ _ (by simp; omega), dec4 _ _ _ _ (by simp; omega), dec1,
        dec6e _ _ _ _ (by simp; omega)]
    · rw [dec5 _ _ _ _ (by omega), dec2, dec7 _ _ _ _ (by simp; omega), dec4 _ _ _ _ (by simp; omega), dec1,
        dec6 _ _ _ _ (by simp; omega), dec3e _ _ _ _ (by simp; omega)]

theorem dec5' (acc s : Nat) (ss out : List Nat) : b32dec (s :: ss) acc 5 out =
    if out.length < 144 then b32dec ss (stepDec acc s) 2 (out ++ [(stepDec acc s / 4) % 256]) else .error .text := by
  by_cases h : out.length < 144
  · rw [if_pos h, dec5 _ _ _ _ h]
  · rw [if_neg h, dec5e _ _ _ _ (by omega)]

theorem dec7' (acc s : Nat) (ss out : List Nat) : b32dec (s :: ss) acc 7 out =
    if out.length < 144 then b32dec ss (stepDec acc s) 4 (out ++ [(stepDec acc s / 16) % 256]) else .error .text := by
  by_cases h : out.length < 144
  · rw [if_pos h, dec7 _ _ _ _ h]
  · rw [if_neg h, dec7e _ _ _ _ (by omega)]

theorem dec4' (acc s : Nat) (ss out : List Nat) : b32dec (s :: ss) acc 4 out =
    if out.length < 144 then b32dec ss (stepDec acc s) 1 (out ++ [(stepDec acc s / 2) % 256]) else .error .text := by
  by_cases h : out.length < 144
  · rw [if_pos h, dec4 _ _ _ _ h]
  · rw [if_neg h, dec4e _ _ _ _ (by omega)]

theorem dec6' (acc s : Nat) (ss out : List Nat) : b32dec (s :: ss) acc 6 out =
    if out.length < 144 then b32dec ss (stepDec acc s) 3 (out ++ [(stepDec acc s / 8) % 256]) else .error .text := by
  by_cases h : out.length < 144
  · rw [if_pos h, dec6 _ _ _ _ h]
  · rw [if_neg h, dec6e _ _ _ _ (by omega)]

theorem dtail0 (acc : Nat) (out : List Nat) : b32dec [] acc 0 out = .ok out := by
  simp [decEnd, Nat.mod_one]

theorem dtail1 (acc s0 : Nat) (out : List Nat) : b32dec [s0] acc 0 out = .error .text := by
  rw [dec0, decEnd]; simp

theorem dtail2 (acc s0 s1 : Nat) (out : List Nat) (h0 : s0 < 32) (h1 : s1 < 32) :
    b32dec [s0, s1] acc 0 out =
      if out.length < 144 then (if s1 % 4 = 0 then .ok (out ++ [s0 * 8 + s1 / 4]) else .error .text) else .error .text := by
  rw [dec0, dec5', decEnd]
  by_cases hl : out.length < 144
  · rw [if_pos hl, if_pos hl]
    by_cases h4 : s1 % 4 = 0
    · rw [if_pos h4, if_neg (by simp [stepDec]; omega)]
      simp [stepDec]; omega
    · rw [if_neg h4, if_pos (by simp [stepDec]; omega)]
  · rw [if_neg hl, if_neg hl]

theorem dtail3 (acc s0 s1 s2 : Nat) (out : List Nat) (h0 : s0 < 32) (h1 : s1 < 32) (h2 : s2 < 32) :
    b32dec [s0, s1, s2] acc 0 out = .error .text := by
  rw [dec0, dec5', dec2, decEnd]
  by_cases hl : out.length < 144
  · rw [if_pos hl]; simp
  · rw [if_neg hl]

theorem dtail4 (acc s0 s1 s2 s3 : Nat) (out : List Nat) (h0 : s0 < 32) (h1 : s1 < 32) (h2 : s2 < 32) (h3 : s3 < 32) :
    b32dec [s0, s1, s2, s3] acc 0 out =
      if out.length + 1 < 144 then
        (if s3 % 16 = 0 then .ok (out ++ [s0 * 8 + s1 / 4, (s1 % 4) * 64 + s2 * 2 + s3 / 16]) else .error .text)
      else .error .text := by
  rw [dec0, dec5', dec2, dec7', decEnd]
  by_cases hl : out.length < 144
  · rw [if_pos hl]
    by_cases hl2 : out.length + 1 < 144
    · rw [if_pos hl2, if_pos (by simp; omega)]
      by_cases h4 : s3 % 16 = 0
      · rw [if_pos h4, if_neg (by simp [stepDec]; omega)]
        simp [stepDec]; omega
      · rw [if_neg h4, if_pos (by simp [stepDec]; omega)]
    · rw [if_neg hl2, if_neg (by simp; omega)]
  · rw [if_neg hl, if_neg (by omega)]

theorem dtail5 (acc s0 s1 s2 s3 s4 : Nat) (out : List Nat) (h0 : s0 < 32) (h1 : s1 < 32) (h2 : s2 < 32)
    (h3 : s3 < 32) (h4 : s4 < 32) :
    b32dec [s0, s1, s2, s3, s4] acc 0 out =
      if out.length + 2 < 144 then
        (if s4 % 2 = 0 then
          .ok (out ++ [s0 * 8 + s1 / 4, (s1 % 4) * 64 + s2 * 2 + s3 / 16, (s3 % 16) * 16 + s4 / 2])
        else .error .text)
      else .error .text := by
  rw [dec0, dec5', dec2, dec7', dec4', decEnd]
  by_cases hl : out.length < 144
  · rw [if_pos hl]
    by_cases hl2 : out.length + 1 < 144
    · rw [if_pos (by simpa using hl2)]
      by_cases hl3 : out.length + 2 < 144
      · rw [if_pos (by simp; omega), if_pos hl3]
        by_cases h5 : s4 % 2 = 0
        · rw [if_pos h5, if_neg (by simp [stepDec]; omega)]
          simp [stepDec]; omega
        · rw [if_neg h5, if_pos (by simp [stepDec]; omega)]
      · rw [if_neg (by simp; omega), if_neg hl3]
    · rw [if_neg (by simpa using hl2), if_neg (by omega)]
  · rw [if_neg hl, if_neg (by omega)]

theorem dtail6 (acc s0 s1 s2 s3 s4 s5 : Nat) (out : List Nat) (h0 : s0 < 32) (h1 : s1 < 32) (h2 : s2 < 32)
    (h3 : s3 < 32) (h4 : s4 < 32) (h5 : s5 < 32) : b32dec [s0, s1, s2, s3, s4, s5] acc 0 out = .error .text := by
  rw [dec0, dec5', dec2, dec7', dec4', dec1, decEnd]
  by_cases hl : out.length < 144 <;> by_cases hl2 : out.length + 1 < 144 <;> by_cases hl3 : out.length + 2 < 144 <;>
    simp_all <;> omega

theorem dtail7 (acc s0 s1 s2 s3 s4 s5 s6 : Nat) (out : List Nat) (h0 : s0 < 32) (h1 : s1 < 32) (h2 : s2 < 32)
    (h3 : s3 < 32) (h4 : s4 < 32) (h5 : s5 < 32) (h6 : s6 < 32) :
    b32dec [s0, s1, s2, s3, s4, s5, s6] acc 0 out =
      if out.length + 3 < 144 then
        (if s6 % 8 = 0 then
          .ok (out ++ [s0 * 8 + s1 / 4, (s1 % 4) * 64 + s2 * 2 + s3 / 16, (s3 % 16) * 16 + s4 / 2,
            (s4 % 2) * 128 + s5 * 4 + s6 / 8])
        else .error .text)
      else .error .text := by
  rw [dec0, dec5', dec2, dec7', dec4', dec1, dec6', decEnd]
  by_cases hl : out.length < 144
  · rw [if_pos hl]
    by_cases hl2 : out.length + 1 < 144
    · rw [if_pos (by simpa using hl2)]
      by_cases hl3 : out.length + 2 < 144
      · rw [if_pos (by simp; omega)]
        by_cases hl4 : out.length + 3 < 144
        · rw [if_pos (by simp; omega), if_pos hl4]
          by_cases h7 : s6 % 8 = 0
          · rw [if_pos h7, if_neg (by simp [stepDec]; omega)]
            simp [stepDec]; omega
          · rw [if_neg h7, if_pos (by simp [stepDec]; omega)]
        · rw [if_neg (by simp; omega), if_neg hl4]
      · rw [if_neg (by simp; omega), if_neg (by omega)]
    · rw [if_neg (by simpa using hl2), if_neg (by omega)]
  · rw [if_neg hl, if_neg (by omega)]

/-- The decoder reads the symbols of a byte string of at most 144 bytes back. -/
theorem dec_syms : ∀ (bs : List Nat), (∀ b ∈ bs, b < 256) → ∀ acc (out : List Nat), out.length + bs.length ≤ 144 →
    b32dec (symsOf bs) acc 0 out = .ok (out ++ bs)
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest, hb, acc, out, hl => by
    have h0 := hb b0 (by simp); have h1 := hb b1 (by simp); have h2 := hb b2 (by simp); have h3 := hb b3 (by simp)
    have h4 := hb b4 (by simp)
    simp only [symsOf, e5, List.cons_append, List.nil_append]
    rw [dec_block _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]
    rw [if_pos (by simp at hl; omega)]
    have hd : d5 (b0 / 8) ((b0 % 8) * 4 + b1 / 64) ((b1 / 2) % 32) ((b1 % 2) * 16 + b2 / 16)
        ((b2 % 16) * 2 + b3 / 128) ((b3 / 4) % 32) ((b3 % 4) * 8 + b4 / 32) (b4 % 32) = [b0, b1, b2, b3, b4] := by
      simp only [d5, List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
    rw [hd]
    rw [dec_syms rest (fun b hb' => hb b (by simp [hb'])) _ (out ++ [b0, b1, b2, b3, b4])
      (by simp at hl ⊢; omega)]
    simp
  | [], _, acc, out, _ => by simp [symsOf, etail, dtail0]
  | [b0], hb, acc, out, hl => by
    have h0 := hb b0 (by simp)
    simp only [symsOf, etail]
    rw [dtail2 _ _ _ _ (by omega) (by omega), if_pos (by simp at hl; omega), if_pos (by omega)]
    have : b0 / 8 * 8 + (b0 % 8 * 4) / 4 = b0 := by omega
    rw [this]
  | [b0, b1], hb, acc, out, hl => by
    have h0 := hb b0 (by simp); have h1 := hb b1 (by simp)
    simp only [symsOf, etail]
    rw [dtail4 _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega), if_pos (by simp at hl; omega),
      if_pos (by omega)]
    have e1 : b0 / 8 * 8 + (b0 % 8 * 4 + b1 / 64) / 4 = b0 := by omega
    have e2 : (b0 % 8 * 4 + b1 / 64) % 4 * 64 + b1 / 2 % 32 * 2 + b1 % 2 * 16 / 16 = b1 := by omega
    rw [e1, e2]
  | [b0, b1, b2], hb, acc, out, hl => by
    have h0 := hb b0 (by simp); have h1 := hb b1 (by simp); have h2 := hb b2 (by simp)
    simp only [symsOf, etail]
    rw [dtail5 _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega), if_pos (by simp at hl; omega),
      if_pos (by omega)]
    have e1 : b0 / 8 * 8 + (b0 % 8 * 4 + b1 / 64) / 4 = b0 := by omega
    have e2 : (b0 % 8 * 4 + b1 / 64) % 4 * 64 + b1 / 2 % 32 * 2 + (b1 % 2 * 16 + b2 / 16) / 16 = b1 := by omega
    have e3 : (b1 % 2 * 16 + b2 / 16) % 16 * 16 + b2 % 16 * 2 / 2 = b2 := by omega
    rw [e1, e2, e3]
  | [b0, b1, b2, b3], hb, acc, out, hl => by
    have h0 := hb b0 (by simp); have h1 := hb b1 (by simp); have h2 := hb b2 (by simp); have h3 := hb b3 (by simp)
    simp only [symsOf, etail]
    rw [dtail7 _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      if_pos (by simp at hl; omega), if_pos (by omega)]
    have e1 : b0 / 8 * 8 + (b0 % 8 * 4 + b1 / 64) / 4 = b0 := by omega
    have e2 : (b0 % 8 * 4 + b1 / 64) % 4 * 64 + b1 / 2 % 32 * 2 + (b1 % 2 * 16 + b2 / 16) / 16 = b1 := by omega
    have e3 : (b1 % 2 * 16 + b2 / 16) % 16 * 16 + (b2 % 16 * 2 + b3 / 128) / 2 = b2 := by omega
    have e4 : (b2 % 16 * 2 + b3 / 128) % 2 * 128 + b3 / 4 % 32 * 4 + b3 % 4 * 8 / 8 = b3 := by omega
    rw [e1, e2, e3, e4]

/-- A symbol string of fewer than eight symbols that decodes is the symbols of the bytes it returned. -/
theorem dec_inv_small (ss : List Nat) (hl : ss.length < 8) (hs : ∀ s ∈ ss, s < 32) (acc : Nat) (out bs : List Nat)
    (h : b32dec ss acc 0 out = .ok bs) : ∃ ts, ss = symsOf ts ∧ (∀ b ∈ ts, b < 256) ∧ bs = out ++ ts := by
  match ss, hl with
  | [], _ =>
    rw [dtail0] at h
    simp only [Except.ok.injEq] at h
    exact ⟨[], by simp [symsOf, etail], by simp, by simp [h]⟩
  | [s0], _ => rw [dtail1] at h; simp at h
  | [s0, s1], _ =>
    have h0 := hs s0 (by simp); have h1 := hs s1 (by simp)
    rw [dtail2 _ _ _ _ h0 h1] at h
    split at h
    · split at h
      · rename_i _ h4
        simp only [Except.ok.injEq] at h
        exact ⟨[s0 * 8 + s1 / 4], by simp [symsOf, etail]; omega, by simp; omega, by simp [h]⟩
      · simp at h
    · simp at h
  | [s0, s1, s2], _ =>
    have h0 := hs s0 (by simp); have h1 := hs s1 (by simp); have h2 := hs s2 (by simp)
    rw [dtail3 _ _ _ _ _ h0 h1 h2] at h; simp at h
  | [s0, s1, s2, s3], _ =>
    have h0 := hs s0 (by simp); have h1 := hs s1 (by simp); have h2 := hs s2 (by simp); have h3 := hs s3 (by simp)
    rw [dtail4 _ _ _ _ _ _ h0 h1 h2 h3] at h
    split at h
    · split at h
      · rename_i _ h4
        simp only [Except.ok.injEq] at h
        exact ⟨[s0 * 8 + s1 / 4, (s1 % 4) * 64 + s2 * 2 + s3 / 16], by simp [symsOf, etail]; omega,
          by simp; omega, by simp [h]⟩
      · simp at h
    · simp at h
  | [s0, s1, s2, s3, s4], _ =>
    have h0 := hs s0 (by simp); have h1 := hs s1 (by simp); have h2 := hs s2 (by simp); have h3 := hs s3 (by simp)
    have h4 := hs s4 (by simp)
    rw [dtail5 _ _ _ _ _ _ _ h0 h1 h2 h3 h4] at h
    split at h
    · split at h
      · rename_i _ h5
        simp only [Except.ok.injEq] at h
        exact ⟨[s0 * 8 + s1 / 4, (s1 % 4) * 64 + s2 * 2 + s3 / 16, (s3 % 16) * 16 + s4 / 2],
          by simp [symsOf, etail]; omega, by simp; omega, by simp [h]⟩
      · simp at h
    · simp at h
  | [s0, s1, s2, s3, s4, s5], _ =>
    have h0 := hs s0 (by simp); have h1 := hs s1 (by simp); have h2 := hs s2 (by simp); have h3 := hs s3 (by simp)
    have h4 := hs s4 (by simp); have h5 := hs s5 (by simp)
    rw [dtail6 _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5] at h; simp at h
  | [s0, s1, s2, s3, s4, s5, s6], _ =>
    have h0 := hs s0 (by simp); have h1 := hs s1 (by simp); have h2 := hs s2 (by simp); have h3 := hs s3 (by simp)
    have h4 := hs s4 (by simp); have h5 := hs s5 (by simp); have h6 := hs s6 (by simp)
    rw [dtail7 _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6] at h
    split at h
    · split at h
      · rename_i _ h7
        simp only [Except.ok.injEq] at h
        exact ⟨[s0 * 8 + s1 / 4, (s1 % 4) * 64 + s2 * 2 + s3 / 16, (s3 % 16) * 16 + s4 / 2,
          (s4 % 2) * 128 + s5 * 4 + s6 / 8], by simp [symsOf, etail]; omega, by simp; omega, by simp [h]⟩
      · simp at h
    · simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, hl =>
    exact absurd hl (by simp only [List.length_cons]; omega)

theorem dec_inv : ∀ (n : Nat) (ss : List Nat), ss.length ≤ n → (∀ s ∈ ss, s < 32) → ∀ (acc : Nat) (out bs : List Nat),
    b32dec ss acc 0 out = .ok bs → ∃ ts, ss = symsOf ts ∧ (∀ b ∈ ts, b < 256) ∧ bs = out ++ ts := by
  intro n
  induction n with
  | zero =>
    intro ss hl hs acc out bs h
    exact dec_inv_small ss (by omega) hs acc out bs h
  | succ n ih =>
    intro ss hl hs acc out bs h
    by_cases h8 : ss.length < 8
    · exact dec_inv_small ss h8 hs acc out bs h
    · rcases ss with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | ⟨s4, _ | ⟨s5, _ | ⟨s6, _ | ⟨s7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
        try (simp at h8; done)
      have e0 := hs s0 (by simp); have e1 := hs s1 (by simp); have e2 := hs s2 (by simp); have e3 := hs s3 (by simp)
      have e4 := hs s4 (by simp); have e5' := hs s5 (by simp); have e6 := hs s6 (by simp); have e7 := hs s7 (by simp)
      rw [dec_block _ _ _ _ _ _ _ _ _ _ _ e0 e1 e2 e3 e4 e5' e6 e7] at h
      split at h
      · obtain ⟨ts, hts, hb, hbs⟩ := ih rest (by simp at hl; omega) (fun s hs' => hs s (by simp [hs'])) _ _ _ h
        refine ⟨d5 s0 s1 s2 s3 s4 s5 s6 s7 ++ ts, ?_, ?_, by simp [hbs]⟩
        · simp only [d5, List.cons_append, List.nil_append, symsOf, e5]
          rw [← hts]
          simp only [List.cons.injEq, and_true]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
        · intro b hb'
          simp only [List.mem_append, d5, List.mem_cons, List.not_mem_nil, or_false] at hb'
          rcases hb' with (rfl | rfl | rfl | rfl | rfl) | hb'
          all_goals first | omega | exact hb b hb'
      · simp at h

end Vinc.ConnCodec
