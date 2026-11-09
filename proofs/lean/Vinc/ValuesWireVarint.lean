import Vinc.ValuesWireBase

/-!
# The value wire: the refused stream ids

What the PROOF and PROOF_REQ frames inherit from the varint of their stream id, beyond `Varint.decode_canonical`:
every refused shape of an id, for every continuation run and every rest. A run of `k` continuation bytes (128 to
255) is cut when it ends the input (`k < 9`), too long when it fills 9 bytes, and a trailing zero byte after it is the
non-minimal form; and every strict prefix of an encoding is cut.
-/

namespace Vinc.ValuesWire

open Vinc Varint

/-- Continuation bytes: the high bit set. -/
def Cont (bs : List Nat) : Prop := ∀ b ∈ bs, 128 ≤ b ∧ b < 256

theorem decodeLoop_cont (bs : List Nat) (h : Cont bs) : ∀ i value, decodeLoop i value bs = none := by
  induction bs with
  | nil => intro i value; rfl
  | cons b bs ih =>
    intro i value
    have hb := h b (by simp)
    have hbs : Cont bs := fun c hc => h c (by simp [hc])
    have hne : ¬ b &&& 0x80 = 0 := fun h0 => by have := (and128_iff b hb.2).1 h0; omega
    simp only [decodeLoop, hne, ↓reduceIte]
    exact ih hbs _ _

theorem decodeLoop_cont_zero (cs : List Nat) (h : Cont cs) (rest : List Nat) :
    ∀ i value, 0 < cs.length + i → decodeLoop i value (cs ++ 0 :: rest) = some (.error .nonMinimal) := by
  induction cs with
  | nil =>
    intro i value hi
    simp only [List.length_nil, Nat.zero_add] at hi
    simp [decodeLoop, hi]
  | cons b bs ih =>
    intro i value hi
    have hb := h b (by simp)
    have hbs : Cont bs := fun c hc => h c (by simp [hc])
    have hne : ¬ b &&& 0x80 = 0 := fun h0 => by have := (and128_iff b hb.2).1 h0; omega
    simp only [List.cons_append, decodeLoop, hne, ↓reduceIte]
    exact ih hbs _ _ (by omega)

/-- A run of 1 to 8 continuation bytes followed by a zero byte is the non-minimal form, whatever follows. -/
theorem decode_nonminimal_run (cs rest : List Nat) (hc : Cont cs) (h1 : 1 ≤ cs.length) (h8 : cs.length ≤ 8) :
    decode (cs ++ 0 :: rest) = .error .nonMinimal := by
  unfold decode maxLen
  have e : (cs ++ 0 :: rest).take 9 = cs ++ 0 :: rest.take (8 - cs.length) := by
    rw [List.take_append, List.take_of_length_le (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, 9 - cs.length = k + 1 := ⟨8 - cs.length, by omega⟩
    rw [hk]
    simp only [List.take_succ_cons]
    congr 3; omega
  rw [e, decodeLoop_cont_zero cs hc _ 0 0 (by omega)]

/-- A run of continuation bytes that ends the input before 9 bytes is cut. -/
theorem decode_truncated_run (cs : List Nat) (hc : Cont cs) (h9 : cs.length < 9) :
    decode cs = .error .truncated := by
  unfold decode maxLen
  rw [List.take_of_length_le (by omega), decodeLoop_cont cs hc 0 0]
  have : ¬ cs.length ≥ 9 := by omega
  simp only [this, ↓reduceIte]

/-- Nine continuation bytes are too long, whatever follows. -/
theorem decode_too_long_run (cs rest : List Nat) (hc : Cont cs) (h9 : cs.length = 9) :
    decode (cs ++ rest) = .error .tooLong := by
  unfold decode maxLen
  have e : (cs ++ rest).take 9 = cs := by
    rw [← h9]; exact List.take_left'  rfl
  rw [e, decodeLoop_cont cs hc 0 0]
  have : (cs ++ rest).length ≥ 9 := by simp only [List.length_append]; omega
  simp only [this, ↓reduceIte]

theorem encRec_dropLast_cont (v : Nat) : Cont (encRec v).dropLast := by
  induction v using Nat.strongRecOn with
  | _ v ih =>
    by_cases h : v < 128
    · rw [encRec_lt v h]; intro b hb; simp at hb
    · rw [encRec_ge v (by omega)]
      have hne : encRec (v / 128) ≠ [] := by
        intro e
        by_cases h2 : v / 128 < 128
        · rw [encRec_lt _ h2] at e; simp at e
        · rw [encRec_ge _ (by omega)] at e; simp at e
      rw [List.dropLast_cons_of_ne_nil hne]
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · omega
      · exact ih (v / 128) (by omega) b hb

/-- Truncation inside an id: every strict prefix of the encoding of `v` (with anything after it) is cut. -/
theorem decode_cut_truncated (v : Nat) (hv : v < limit) (rest : List Nat) (m : Nat) (hm : m < (encodeBytes v).length) :
    decode ((encodeBytes v ++ rest).take m) = .error .truncated := by
  rw [encodeBytes_eq] at hm ⊢
  have hle : (encRec v).length ≤ maxLen := by
    have := (encode_length v hv).2
    rw [← encodeBytes_eq, length_encodeBytes]; exact this
  rw [List.take_append_of_le_length (by omega)]
  have hd : (encRec v).take m = ((encRec v).dropLast).take m := by
    rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left (by omega)]
  have hcont : Cont ((encRec v).take m) := by
    rw [hd]; intro b hb; exact encRec_dropLast_cont v b (List.mem_of_mem_take hb)
  have hlen : ((encRec v).take m).length < 9 := by
    rw [List.length_take]; unfold maxLen at hle; omega
  exact decode_truncated_run _ hcont hlen

end Vinc.ValuesWire

#audit_axioms Vinc.ValuesWire.decode_nonminimal_run
#audit_axioms Vinc.ValuesWire.decode_truncated_run
#audit_axioms Vinc.ValuesWire.decode_too_long_run
#audit_axioms Vinc.ValuesWire.decode_cut_truncated
