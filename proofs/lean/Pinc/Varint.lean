import Pinc.Axioms

/-!
# Varint

A step-for-step model of `pinc-wire/src/varint.rs`, the multiformats unsigned varint: at most 9 bytes, values
below 2^63, no trailing zero continuation byte.

Values are `Nat`; bytes are `Nat`s below 256 (`ValidBytes`). A `u64` value below 2^63 and a shift of at most
`7 * 8` bits never overflow, so the `Nat` arithmetic is exactly the `u64` arithmetic of the code. The Rust
`b & 0x7f`, `b & 0x80` and `group | 0x80` are kept as the same bitwise operations on `Nat`.
-/

namespace Pinc.Varint

/-- The longest valid varint, in bytes (`MAX_LEN`). -/
def maxLen : Nat := 9

/-- The first value that cannot be encoded (`LIMIT`). -/
def limit : Nat := 2 ^ 63

/-- `WireError` variants a varint operation returns. `Truncated` always has `needed = 1` in `decode`. -/
inductive Error where
  | tooLong
  | truncated
  | nonMinimal
  | overflow
  | bufferTooSmall (needed : Nat)
  deriving DecidableEq, Repr

/-- Every element is a byte. -/
def ValidBytes (bs : List Nat) : Prop := ∀ b ∈ bs, b < 256

/-- `value.bit_width()`. -/
def bitWidth (v : Nat) : Nat := if v = 0 then 0 else v.log2 + 1

/-- `encoded_len`. -/
def encodedLen (v : Nat) : Nat :=
  let bits := bitWidth v
  if bits = 0 then 1 else (bits + 6) / 7

/-- The bytes `encode` writes for `value < 2^63`: group `i` of 7 bits, with the continuation bit on all but
the last. -/
def encodeBytes (v : Nat) : List Nat :=
  let n := encodedLen v
  (List.range n).map fun i =>
    let group := (v >>> (7 * i)) &&& 0x7f
    if i + 1 < n then group ||| 0x80 else group

/-- `encode` into a buffer of `cap` bytes: the bytes written, or the error that leaves the buffer untouched. -/
def encodeInto (cap : Nat) (v : Nat) : Except Error (List Nat) :=
  if v ≥ limit then .error .overflow
  else
    let n := encodedLen v
    if n > cap then .error (.bufferTooSmall (n - cap)) else .ok (encodeBytes v)

/-- The loop body of `decode` over `input.iter().take(MAX_LEN).enumerate()`; `none` when the loop ends without
returning. -/
def decodeLoop : Nat → Nat → List Nat → Option (Except Error (Nat × Nat))
  | _, _, [] => none
  | i, value, b :: bs =>
    let value := value ||| ((b &&& 0x7f) <<< (7 * i))
    if b &&& 0x80 = 0 then
      if b = 0 ∧ i > 0 then some (.error .nonMinimal) else some (.ok (value, i + 1))
    else decodeLoop (i + 1) value bs

/-- `decode`: the value and the bytes consumed. -/
def decode (input : List Nat) : Except Error (Nat × Nat) :=
  match decodeLoop 0 0 (input.take maxLen) with
  | some r => r
  | none => if input.length ≥ maxLen then .error .tooLong else .error .truncated

/-! ## A recursive reference encoding -/

/-- The reference encoding: low 7 bits with the continuation bit, then the rest. -/
def encRec (v : Nat) : List Nat :=
  if v < 128 then [v] else (v % 128 + 128) :: encRec (v / 128)
termination_by v
decreasing_by omega

theorem encRec_lt (v : Nat) (h : v < 128) : encRec v = [v] := by
  rw [encRec]; simp [h]

theorem encRec_ge (v : Nat) (h : 128 ≤ v) : encRec v = (v % 128 + 128) :: encRec (v / 128) := by
  rw [encRec]; simp; omega

theorem encRec_valid (v : Nat) : ValidBytes (encRec v) := by
  induction v using Nat.strongRecOn with
  | _ v ih =>
    by_cases h : v < 128
    · rw [encRec_lt v h]; intro b hb; simp at hb; omega
    · rw [encRec_ge v (by omega)]
      intro b hb
      simp at hb
      rcases hb with hb | hb
      · omega
      · exact ih (v / 128) (by omega) b hb

theorem lt_pow_encRec (v : Nat) : v < 128 ^ (encRec v).length := by
  induction v using Nat.strongRecOn with
  | _ v ih =>
    by_cases h : v < 128
    · rw [encRec_lt v h]; simpa using h
    · rw [encRec_ge v (by omega)]
      have h2 : v / 128 < 128 ^ (encRec (v / 128)).length := ih (v / 128) (by omega)
      simp only [List.length_cons, Nat.pow_succ]
      generalize 128 ^ (encRec (v / 128)).length = P at h2 ⊢
      omega

/-! ## `encodedLen` and `encodeBytes` agree with the reference -/

theorem encodedLen_lt (v : Nat) (h : v < 128) : encodedLen v = 1 := by
  unfold encodedLen bitWidth
  by_cases h0 : v = 0
  · simp [h0]
  · have : v.log2 < 7 := (Nat.log2_lt h0).2 (by simpa using h)
    simp [h0]; omega

theorem encodedLen_ge (v : Nat) (h : 128 ≤ v) : encodedLen v = encodedLen (v / 128) + 1 := by
  have hv : v ≠ 0 := by omega
  have hd : v / 128 ≠ 0 := by omega
  have h7 : 7 ≤ v.log2 := (Nat.le_log2 hv).2 (by simpa using h)
  have hk : (v / 128).log2 = v.log2 - 7 := by
    rw [Nat.log2_eq_iff hd]
    have a := @Nat.log2_self_le v hv
    have b := @Nat.lt_log2_self v
    obtain ⟨k, hk⟩ : ∃ k, v.log2 = k + 7 := ⟨v.log2 - 7, by omega⟩
    rw [hk] at a b
    have e1 : 2 ^ (k + 7) = 2 ^ k * 128 := by rw [Nat.pow_add]
    have e2 : 2 ^ (k + 7 + 1) = 2 ^ k * 128 * 2 := by rw [Nat.pow_succ, e1]
    have e3 : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
    rw [hk, show k + 7 - 7 = k by omega]
    constructor <;> omega
  unfold encodedLen bitWidth
  simp [hv, hd, hk]
  omega

theorem encodedLen_pos (v : Nat) : 0 < encodedLen v := by
  by_cases h : v < 128
  · rw [encodedLen_lt v h]; omega
  · rw [encodedLen_ge v (by omega)]; omega

theorem shr_succ (v i : Nat) : v >>> (7 * (i + 1)) = (v / 128) >>> (7 * i) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    show 7 * (i + 1) = 7 + 7 * i by omega, Nat.pow_add]

theorem and127 (x : Nat) : x &&& 0x7f = x % 128 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 7
  simpa using this

theorem or128 (g : Nat) (h : g < 128) : g ||| 0x80 = g + 128 := by
  have := Nat.shiftLeft_add_eq_or_of_lt (i := 7) (b := g) (by simpa using h) 1
  rw [Nat.or_comm]
  simpa [Nat.add_comm] using this.symm

theorem encodeBytes_eq (v : Nat) : encodeBytes v = encRec v := by
  induction v using Nat.strongRecOn with
  | _ v ih =>
    by_cases h : v < 128
    · rw [encRec_lt v h]
      unfold encodeBytes
      rw [encodedLen_lt v h]
      simp [and127, Nat.mod_eq_of_lt h]
    · have ihv := ih (v / 128) (by omega)
      rw [encRec_ge v (by omega), ← ihv]
      unfold encodeBytes
      dsimp only
      have hl := encodedLen_ge v (by omega)
      have hp := encodedLen_pos (v / 128)
      generalize encodedLen (v / 128) = m at hl hp ⊢
      rw [hl, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      congr 1
      · have c : (0 : Nat) + 1 < m + 1 := by omega
        simp only [c, ite_true, and127, or128 _ (Nat.mod_lt _ (by omega : 128 > 0))]
        simp
      · apply List.map_congr_left
        intro i _
        simp only [Function.comp, shr_succ]
        have : (i + 1 + 1 < m + 1) ↔ (i + 1 < m) := by omega
        simp only [this]

theorem length_encodeBytes (v : Nat) : (encodeBytes v).length = encodedLen v := by
  simp [encodeBytes]

/-- (c) the encoding is as long as `encoded_len` says, and at most 9 bytes. -/
theorem encode_length (v : Nat) (hv : v < limit) :
    (encodeBytes v).length = encodedLen v ∧ encodedLen v ≤ maxLen := by
  refine ⟨length_encodeBytes v, ?_⟩
  unfold encodedLen bitWidth maxLen
  by_cases h0 : v = 0
  · simp [h0]
  · have : v.log2 < 63 := (Nat.log2_lt h0).2 hv
    simp [h0]; omega

/-! ## The decode loop -/

theorem and128_iff (b : Nat) (hb : b < 256) : b &&& 0x80 = 0 ↔ b < 128 := by
  have : ∀ b, b < 256 → (b &&& 0x80 = 0 ↔ b < 128) := by decide +kernel
  exact this b hb

theorem step_or (value i b : Nat) (h : value < 2 ^ (7 * i)) :
    value ||| ((b &&& 0x7f) <<< (7 * i)) = value + 2 ^ (7 * i) * (b % 128) := by
  have := Nat.shiftLeft_add_eq_or_of_lt h (b % 128)
  rw [Nat.or_comm, and127, ← this, Nat.shiftLeft_eq, Nat.add_comm, Nat.mul_comm]

/-- Soundness of the loop: what a successful return means. -/
theorem decodeLoop_sound (bs : List Nat) (hv : ValidBytes bs) :
    ∀ i value v n, value < 2 ^ (7 * i) →
      decodeLoop i value bs = some (.ok (v, n)) →
      ∃ x, v = value + 2 ^ (7 * i) * x ∧ i < n ∧ n - i ≤ bs.length ∧
        bs.take (n - i) = encRec x ∧ (0 < i → 1 ≤ x) := by
  induction bs with
  | nil => intro i value v n _ h; simp [decodeLoop] at h
  | cons b bs ih =>
    intro i value v n hval h
    have hb : b < 256 := hv b (by simp)
    have hbs : ValidBytes bs := fun c hc => hv c (by simp [hc])
    have hstep := step_or value i b hval
    unfold decodeLoop at h
    simp only [hstep] at h
    by_cases hb0 : b &&& 0x80 = 0
    · have hlt : b < 128 := (and128_iff b hb).1 hb0
      simp only [hb0, ite_true] at h
      by_cases hz : b = 0 ∧ i > 0
      · simp [hz] at h
      · simp only [hz, ite_false] at h
        simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨b, ?_, by omega, by simp, ?_, ?_⟩
        · rw [Nat.mod_eq_of_lt hlt]
        · rw [show i + 1 - i = 1 by omega, encRec_lt b hlt]; simp
        · intro hi; omega
    · have hge : 128 ≤ b := by
        rcases Nat.lt_or_ge b 128 with hc | hc
        · exact absurd ((and128_iff b hb).2 hc) hb0
        · exact hc
      simp only [hb0, ite_false] at h
      have hlt : value + 2 ^ (7 * i) * (b % 128) < 2 ^ (7 * (i + 1)) := by
        have : 2 ^ (7 * (i + 1)) = 2 ^ (7 * i) * 128 := by
          rw [show 7 * (i + 1) = 7 * i + 7 by omega, Nat.pow_add]
        rw [this]
        have := Nat.mod_lt b (show 128 > 0 by omega)
        generalize 2 ^ (7 * i) = P at hval ⊢
        have : P * (b % 128) + P ≤ P * 128 := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
        omega
      obtain ⟨x', hx, hin, hlen, htake, hpos⟩ := ih hbs (i + 1) _ v n hlt h
      have hpow : 2 ^ (7 * (i + 1)) = 2 ^ (7 * i) * 128 := by
        rw [show 7 * (i + 1) = 7 * i + 7 by omega, Nat.pow_add]
      have hx1 := hpos (by omega)
      refine ⟨b % 128 + 128 * x', ?_, by omega, by simp; omega, ?_, by omega⟩
      · rw [hx, hpow]; grind
      · rw [encRec_ge _ (by omega)]
        have e1 : (b % 128 + 128 * x') % 128 = b % 128 := by omega
        have e2 : (b % 128 + 128 * x') / 128 = x' := by omega
        rw [e1, e2, ← htake, show n - i = (n - (i + 1)) + 1 by omega]
        simp
        omega

/-- Completeness of the loop: an encoding is accepted, with the value and length it denotes. -/
theorem decodeLoop_enc (x : Nat) : ∀ i value rest, value < 2 ^ (7 * i) → (0 < i → 1 ≤ x) →
    decodeLoop i value (encRec x ++ rest) =
      some (.ok (value + 2 ^ (7 * i) * x, i + (encRec x).length)) := by
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro i value rest hval hpos
    by_cases hx : x < 128
    · rw [encRec_lt x hx]
      have hstep := step_or value i x hval
      simp only [List.singleton_append, decodeLoop, hstep, Nat.mod_eq_of_lt hx]
      have : x &&& 0x80 = 0 := (and128_iff x (by omega)).2 hx
      have hz : ¬ (x = 0 ∧ i > 0) := by
        intro ⟨h1, h2⟩; have := hpos h2; omega
      simp [this, hz]
    · have hstep := step_or value i (x % 128 + 128) hval
      have hlt : value + 2 ^ (7 * i) * ((x % 128 + 128) % 128) < 2 ^ (7 * (i + 1)) := by
        have : 2 ^ (7 * (i + 1)) = 2 ^ (7 * i) * 128 := by
          rw [show 7 * (i + 1) = 7 * i + 7 by omega, Nat.pow_add]
        rw [this, show (x % 128 + 128) % 128 = x % 128 by omega]
        have := Nat.mod_lt x (show 128 > 0 by omega)
        generalize 2 ^ (7 * i) = P at hval ⊢
        have : P * (x % 128) + P ≤ P * 128 := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
        omega
      have hih := ih (x / 128) (by omega) (i + 1) _ rest hlt (fun _ => by omega)
      rw [encRec_ge x (by omega), List.cons_append]
      have hnot : ¬ ((x % 128 + 128) &&& 0x80 = 0) := by
        rw [and128_iff _ (by omega)]; omega
      simp only [decodeLoop, hstep, hnot, ite_false]
      rw [hih]
      simp only [List.length_cons, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq]
      constructor
      · have hpow : 2 ^ (7 * (i + 1)) = 2 ^ (7 * i) * 128 := by
          rw [show 7 * (i + 1) = 7 * i + 7 by omega, Nat.pow_add]
        rw [hpow, show (x % 128 + 128) % 128 = x % 128 by omega]
        generalize 2 ^ (7 * i) = P
        have key : P * x = P * (x % 128) + P * 128 * (x / 128) := by
          rw [Nat.mul_assoc, ← Nat.mul_add]; congr 1; omega
        omega
      · omega

/-! ## The theorems -/

theorem pow7 (n : Nat) : 128 ^ n = 2 ^ (7 * n) := by
  rw [Nat.pow_mul]

/-- (a) Round trip: decoding an encoding followed by anything returns the value and the encoding's length. -/
theorem decode_encode (v : Nat) (rest : List Nat) (hv : v < limit) :
    decode (encodeBytes v ++ rest) = .ok (v, (encodeBytes v).length) := by
  obtain ⟨hlen, hle⟩ := encode_length v hv
  rw [encodeBytes_eq] at hlen ⊢
  have hlen' : (encRec v).length ≤ maxLen := by rw [← encodeBytes_eq, length_encodeBytes]; exact hle
  unfold decode
  rw [List.take_append, List.take_of_length_le hlen']
  have key := decodeLoop_enc v 0 0 (rest.take (maxLen - (encRec v).length)) (by simp) (by simp)
  rw [key]
  simp

/-- (b) Canonicity: whatever prefix `decode` accepts is exactly the encoding of the value, with the length
`encoded_len` gives. So each value has exactly one accepted encoding. -/
theorem decode_canonical (input : List Nat) (hv : ValidBytes input) (v n : Nat)
    (h : decode input = .ok (v, n)) :
    input.take n = encodeBytes v ∧ n = encodedLen v := by
  unfold decode at h
  have hsub : ValidBytes (input.take maxLen) := fun b hb => hv b (List.mem_of_mem_take hb)
  split at h
  · rename_i r hr
    subst h
    obtain ⟨x, hx, hin, hlen, htake, _⟩ := decodeLoop_sound _ hsub 0 0 v n (by simp) hr
    simp only [Nat.sub_zero, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add] at hx htake hlen
    subst hx
    have hn9 : n ≤ maxLen := by
      have : (input.take maxLen).length ≤ maxLen := List.length_take_le ..
      omega
    rw [List.take_take, Nat.min_eq_left hn9] at htake
    refine ⟨by rw [encodeBytes_eq, htake], ?_⟩
    have := congrArg List.length htake
    rw [← encodeBytes_eq, length_encodeBytes] at this
    have h3 := List.length_take (i := maxLen) (l := input)
    simp at this
    omega
  · split at h <;> simp at h

/-- (d) Every decoded value is below 2^63, and the length is at most 9. -/
theorem decode_bounds (input : List Nat) (hv : ValidBytes input) (v n : Nat)
    (h : decode input = .ok (v, n)) : v < limit ∧ n ≤ maxLen := by
  obtain ⟨_, hn⟩ := decode_canonical input hv v n h
  have hn9 : n ≤ maxLen := by
    unfold decode at h
    split at h
    · rename_i r hr
      subst h
      obtain ⟨x, _, _, hlen, _, _⟩ := decodeLoop_sound _ (fun b hb => hv b (List.mem_of_mem_take hb)) 0 0 v n
        (by simp) hr
      have : (input.take maxLen).length ≤ maxLen := List.length_take_le ..
      omega
    · split at h <;> simp at h
  refine ⟨?_, hn9⟩
  obtain ⟨hx, _⟩ := decode_canonical input hv v n h
  have h1 := lt_pow_encRec v
  rw [← encodeBytes_eq, length_encodeBytes, ← hn, pow7] at h1
  calc v < 2 ^ (7 * n) := h1
    _ ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) (by unfold maxLen at hn9; omega)

/-- Every value has exactly one accepted encoding: two byte strings that decode, in full, to the same value are
equal. -/
theorem unique_encoding (a b : List Nat) (ha : ValidBytes a) (hb : ValidBytes b) (v : Nat)
    (hda : decode a = .ok (v, a.length)) (hdb : decode b = .ok (v, b.length)) : a = b := by
  have h1 := (decode_canonical a ha v _ hda).1
  have h2 := (decode_canonical b hb v _ hdb).1
  rw [List.take_length] at h1 h2
  rw [h1, h2]

/-- `encode` reports an overflow or a short buffer, and otherwise writes the encoding. -/
theorem encodeInto_ok_iff (cap v : Nat) :
    (∃ bs, encodeInto cap v = .ok bs) ↔ v < limit ∧ encodedLen v ≤ cap := by
  unfold encodeInto
  by_cases h1 : v ≥ limit
  · simp [h1]; omega
  · by_cases h2 : encodedLen v > cap
    · simp [h1, h2]
    · simp [h1, h2]; omega

/-- Every successful `encode` is the canonical encoding and decodes back. -/
theorem encodeInto_decode (cap v : Nat) (bs : List Nat) (h : encodeInto cap v = .ok bs) :
    bs = encodeBytes v ∧ decode bs = .ok (v, bs.length) := by
  unfold encodeInto at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h
      subst h
      rename_i hl _
      exact ⟨rfl, by simpa using decode_encode v [] (by omega)⟩

/-! ## Error cases -/

theorem decode_empty : decode [] = .error .truncated := by
  rfl

theorem decode_nonminimal : decode [0x80, 0x00] = .error .nonMinimal := by
  rfl

theorem decode_too_long : decode (List.replicate 9 0x80) = .error .tooLong := by
  rfl

theorem decode_truncated : decode (List.replicate 8 0x80) = .error .truncated := by
  rfl

theorem decode_overflow_encode : encodeInto 9 limit = .error .overflow := by
  rfl

end Pinc.Varint

#audit_axioms Pinc.Varint.decode_encode
#audit_axioms Pinc.Varint.decode_canonical
#audit_axioms Pinc.Varint.decode_bounds
#audit_axioms Pinc.Varint.encode_length
#audit_axioms Pinc.Varint.unique_encoding
#audit_axioms Pinc.Varint.encodeInto_decode
