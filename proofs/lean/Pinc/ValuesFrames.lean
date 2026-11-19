import Pinc.Varint

/-!
# The stream id at the head of an extension body

A step-for-step model of `head_sid` and `with_sid` of `pinc-node/src/values_frames.rs`: the body of a range-proof
frame starts with the stream id as a varint; the node reads it (`head_sid`) and rewrites it from the endpoint's id to
its own handle (`with_sid`), copying the rest of the body unchanged into a buffer of `EXT_MAX = 1200 + 16` bytes.

`with_sid body sid out` decodes the varint at the head of `body` (the bytes it used are `used`), encodes `sid` into
`out` (the encoder refuses `sid >= 2^63`; a buffer of `EXT_MAX >= 9` bytes is never too small), and copies
`body[used..]` after it; the copy is refused (`None`) when it does not fit `out`. The result is the length written; here
the bytes written, `out[..n]`, as a list. The varint is `Pinc.Varint`, whose round trip and canonicity are proved there.
-/

namespace Pinc.ValuesFrames
open Pinc.Varint

/-- `EXT_MAX`: `EXT_BODY_MAX + 16`. -/
def extMax : Nat := 1200 + 16

/-- `head_sid`. -/
def headSid (body : List Nat) : Option Nat :=
  match decode body with
  | .ok (v, _) => some v
  | .error _ => none

/-- `with_sid`: the bytes written to `out`, or `none`. -/
def withSid (body : List Nat) (sid : Nat) : Option (List Nat) :=
  match decode body with
  | .error _ => none
  | .ok (_, used) =>
    match encodeInto extMax sid with
    | .error _ => none
    | .ok head => if head.length + (body.drop used).length ≤ extMax then some (head ++ body.drop used) else none

/-- The stream id at the head of an encoding is its value, whatever follows. -/
theorem headSid_enc (v : Nat) (rest : List Nat) (hv : v < limit) : headSid (encodeBytes v ++ rest) = some v := by
  simp [headSid, decode_encode v rest hv]

/-- A head that `head_sid` reads is the one canonical encoding of the id read: the body is that encoding followed by
the rest, and nothing else decodes to it. -/
theorem headSid_canonical (body : List Nat) (hv : ValidBytes body) (v : Nat) (h : headSid body = some v) :
    ∃ rest, body = encodeBytes v ++ rest ∧ v < limit := by
  unfold headSid at h
  split at h
  · rename_i v' used hd
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨h1, _⟩ := decode_canonical body hv v' used hd
    obtain ⟨hb, _⟩ := decode_bounds body hv v' used hd
    exact ⟨body.drop used, by rw [← h1, List.take_append_drop], hb⟩
  · simp at h

/-- Round trip: replacing the head of an encoding followed by `rest` gives the encoding of the new id followed by the
same `rest`, when the ids are below `2^63` and the result fits. -/
theorem withSid_enc (old sid : Nat) (rest : List Nat) (ho : old < limit) (hs : sid < limit)
    (hfit : encodedLen sid + rest.length ≤ extMax) :
    withSid (encodeBytes old ++ rest) sid = some (encodeBytes sid ++ rest) := by
  have hd := decode_encode old rest ho
  have hl := length_encodeBytes old
  have hdrop : (encodeBytes old ++ rest).drop (encodeBytes old).length = rest := List.drop_left ..
  have hs9 : encodedLen sid ≤ 9 := (encode_length sid hs).2
  have hen : encodeInto extMax sid = .ok (encodeBytes sid) := by
    unfold encodeInto
    have : ¬ sid ≥ limit := by omega
    have h2 : ¬ encodedLen sid > extMax := by unfold extMax; omega
    simp [this, h2]
  unfold withSid
  rw [hd]
  simp only [hen]
  rw [hdrop, length_encodeBytes]
  simp [hfit]

/-- A rewrite that succeeds writes a well-formed head: the new id is the one `head_sid` reads from the result, the
result fits `out`, and everything after the head is the old body's rest. -/
theorem withSid_ok (body : List Nat) (sid : Nat) (out : List Nat) (h : withSid body sid = some out) :
    headSid out = some sid ∧ out.length ≤ extMax ∧ sid < limit ∧
    ∃ used, (∃ v, decode body = .ok (v, used)) ∧ out = encodeBytes sid ++ body.drop used := by
  unfold withSid at h
  split at h
  · simp at h
  · rename_i v used hd
    split at h
    · simp at h
    · rename_i head he
      obtain ⟨hb, hdec⟩ := encodeInto_decode _ _ _ he
      have hs : sid < limit := by
        unfold encodeInto at he
        split at he
        · simp at he
        · omega
      split at h
      · rename_i hfit
        simp only [Option.some.injEq] at h
        subst h hb
        refine ⟨?_, ?_, hs, used, ⟨v, hd⟩, rfl⟩
        · exact headSid_enc sid _ hs
        · simpa using hfit
      · simp at h

/-- The new id is exactly `sid` and the rest is exactly the old rest: `head_sid` of the result is `sid`. -/
theorem withSid_head (body : List Nat) (sid : Nat) (out : List Nat) (h : withSid body sid = some out) :
    headSid out = some sid := (withSid_ok body sid out h).1

/-- Replacing the id by itself changes nothing: a body whose head `head_sid` reads is unchanged by `with_sid` of that
id (one encoding), when it fits `out`. -/
theorem withSid_self (body : List Nat) (hv : ValidBytes body) (v : Nat) (h : headSid body = some v)
    (hfit : body.length ≤ extMax) : withSid body v = some body := by
  obtain ⟨rest, hb, hl⟩ := headSid_canonical body hv v h
  subst hb
  have hlen : (encodeBytes v ++ rest).length = encodedLen v + rest.length := by
    simp [length_encodeBytes]
  have := withSid_enc v v rest hl hl (by omega)
  exact this

/-- `with_sid` refuses exactly when the head is not a varint, the id is `2^63` or more, or the result would not fit. -/
theorem withSid_none_iff (body : List Nat) (sid : Nat) :
    withSid body sid = none ↔
      (∃ e, decode body = .error e) ∨ sid ≥ limit ∨
      (∃ v used, decode body = .ok (v, used) ∧ encodedLen sid + (body.drop used).length > extMax) := by
  unfold withSid
  cases hd : decode body with
  | error e => simp
  | ok r =>
    obtain ⟨v, used⟩ := r
    simp only [reduceCtorEq, exists_false, false_or, Except.ok.injEq, Prod.mk.injEq]
    by_cases hs : sid ≥ limit
    · have : encodeInto extMax sid = .error .overflow := by simp [encodeInto, hs]
      simp [this, hs]
    · by_cases h2 : encodedLen sid > extMax
      · have : encodeInto extMax sid = .error (.bufferTooSmall (encodedLen sid - extMax)) := by
          simp [encodeInto, hs, h2]
        have h9 : encodedLen sid ≤ 9 := (encode_length sid (by omega)).2
        unfold extMax at h2; omega
      · have : encodeInto extMax sid = .ok (encodeBytes sid) := by simp [encodeInto, hs, h2]
        simp only [this, length_encodeBytes, hs, false_or]
        by_cases hf : encodedLen sid + (body.drop used).length ≤ extMax
        · simp only [hf, ↓reduceIte]
          constructor
          · intro h; cases h
          · rintro ⟨v', u', ⟨_, rfl⟩, hgt⟩; omega
        · simp only [hf, ↓reduceIte]
          exact ⟨fun _ => ⟨v, used, ⟨rfl, rfl⟩, by omega⟩, fun _ => trivial⟩

end Pinc.ValuesFrames

#audit_axioms Pinc.ValuesFrames.headSid_enc
#audit_axioms Pinc.ValuesFrames.headSid_canonical
#audit_axioms Pinc.ValuesFrames.withSid_enc
#audit_axioms Pinc.ValuesFrames.withSid_ok
#audit_axioms Pinc.ValuesFrames.withSid_self
#audit_axioms Pinc.ValuesFrames.withSid_none_iff
