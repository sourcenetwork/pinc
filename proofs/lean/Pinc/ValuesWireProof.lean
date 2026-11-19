import Pinc.ValuesWireBase

/-!
# The value wire: the PROOF and PROOF_REQ extension frames

A model of `ProofFrame::parse`, `ProofFrame::write_head`, `ProofReq::parse` and `ProofReq::encode` (`wire.rs`).
The stream id is a `pinc-wire` varint (`Pinc.Varint`), read by `readVarint`. `pfTail` and `prTail` are the code after
the id; `pfTail_eq` and `prTail_eq` are their decision procedures in closed form (the first field that does not fit
gives the `Truncated` shortfall, then the proof length rule, then the trailing-byte rule).

`write_head` and `ProofReq::encode` build the frame head in a 30-byte scratch buffer and copy it whole, so a
refusal leaves the caller's buffer untouched: `pfWriteHead` and `prEncode` return the buffer afterwards.
-/

namespace Pinc.ValuesWire

open Pinc Varint

/-- A parsed PROOF body: the stream id, the group-size log, the first offset, the covered bytes, the value length
and the proof (the rest of the body). -/
structure PF where
  sid : Nat
  glog : Nat
  start : Nat
  wn : Nat
  ln : Nat
  proof : List Nat
  deriving DecidableEq, Repr

/-- A parsed PROOF_REQ body. -/
structure PR where
  sid : Nat
  from_ : Nat
  upto : Nat
  deriving DecidableEq, Repr

/-- `ProofFrame::parse` after the stream id: the group log, offset, covered bytes, value length, then the rest of the
body as the proof, which must be a whole number of 64-byte pairs and at most `WT_PMAX = 1100` bytes. -/
def pfTail (sid : Nat) (r1 : List Nat) : Except Err PF :=
  match readBe 1 r1 with
  | .error e => .error e
  | .ok (glog, r2) =>
    match readBe 8 r2 with
    | .error e => .error e
    | .ok (start, r3) =>
      match readBe 4 r3 with
      | .error e => .error e
      | .ok (wn, r4) =>
        match readBe 8 r4 with
        | .error e => .error e
        | .ok (ln, r5) =>
          match readBytes r5.length r5 with
          | .error e => .error e
          | .ok (proof, _) =>
            if proof.length % 64 ≠ 0 ∨ proof.length > 1100 then .error (.unexpected "bad proof length")
            else .ok ⟨sid, glog, start, wn, ln, proof⟩

/-- `ProofFrame::parse`. -/
def pfParse (body : List Nat) : Except Err PF :=
  match readVarint body with
  | .error e => .error e
  | .ok (sid, r1) => pfTail sid r1

/-- `ProofReq::parse` after the stream id: two `u64`s and nothing else. -/
def prTail (sid : Nat) (r1 : List Nat) : Except Err PR :=
  match readBe 8 r1 with
  | .error e => .error e
  | .ok (from_, r2) =>
    match readBe 8 r2 with
    | .error e => .error e
    | .ok (upto, r3) => if r3 ≠ [] then .error (.unexpected "trailing bytes") else .ok ⟨sid, from_, upto⟩

/-- `ProofReq::parse`. -/
def prParse (body : List Nat) : Except Err PR :=
  match readVarint body with
  | .error e => .error e
  | .ok (sid, r1) => prTail sid r1

/-- The bytes of a PROOF body before the proof. -/
def pfHead (f : PF) : List Nat :=
  encodeBytes f.sid ++ [f.glog] ++ beBytes 8 f.start ++ beBytes 4 f.wn ++ beBytes 8 f.ln

/-- The bytes of a PROOF_REQ body. -/
def prBytes (r : PR) : List Nat := encodeBytes r.sid ++ beBytes 8 r.from_ ++ beBytes 8 r.upto

/-- `ProofFrame::write_head` into `out`. The id is encoded first (an id of 2^63 or more is an overflow, a scratch of
30 bytes is never short), then the whole head is copied or nothing is. -/
def pfWriteHead (sid glog start wn ln : Nat) (out : List Nat) : Except Err Nat × List Nat :=
  match encodeInto 30 sid with
  | .error e => (.error (varErr e), out)
  | .ok vb => put (vb ++ [glog] ++ beBytes 8 start ++ beBytes 4 wn ++ beBytes 8 ln) out

/-- `ProofReq::encode` into `out`, the same way. -/
def prEncode (r : PR) (out : List Nat) : Except Err Nat × List Nat :=
  match encodeInto 25 r.sid with
  | .error e => (.error (varErr e), out)
  | .ok vb => put (vb ++ beBytes 8 r.from_ ++ beBytes 8 r.upto) out

/-! ## The tails in closed form -/

theorem pfTail_eq (sid : Nat) (r : List Nat) :
    pfTail sid r =
      if r.length < 1 then .error (.truncated (1 - r.length))
      else if r.length < 9 then .error (.truncated (9 - r.length))
      else if r.length < 13 then .error (.truncated (13 - r.length))
      else if r.length < 21 then .error (.truncated (21 - r.length))
      else if (r.drop 21).length % 64 ≠ 0 ∨ (r.drop 21).length > 1100 then .error (.unexpected "bad proof length")
      else .ok ⟨sid, r.getD 0 0, beVal ((r.drop 1).take 8), beVal ((r.drop 9).take 4), beVal ((r.drop 13).take 8),
        r.drop 21⟩ := by
  by_cases h1 : 1 ≤ r.length
  · have e1 : readBe 1 r = .ok (r.getD 0 0, r.drop 1) := by
      rw [readBe_ok h1, beVal_take_one r (by omega)]
    unfold pfTail
    rw [e1]
    simp only [show ¬ r.length < 1 by omega, ↓reduceIte]
    by_cases h2 : 8 ≤ (r.drop 1).length
    · rw [readBe_ok h2]
      simp only [List.drop_drop, Nat.reduceAdd]
      simp only [List.length_drop] at h2
      simp only [show ¬ r.length < 9 by omega, ↓reduceIte]
      by_cases h3 : 4 ≤ (r.drop 9).length
      · rw [readBe_ok h3]
        simp only [List.drop_drop, Nat.reduceAdd]
        simp only [List.length_drop] at h3
        simp only [show ¬ r.length < 13 by omega, ↓reduceIte]
        by_cases h4 : 8 ≤ (r.drop 13).length
        · rw [readBe_ok h4]
          simp only [List.drop_drop, Nat.reduceAdd]
          simp only [List.length_drop] at h4
          simp only [show ¬ r.length < 21 by omega, ↓reduceIte]
          rw [readBytes_ok (Nat.le_refl _)]
          simp only [List.take_length]
        · rw [readBe_err h4]
          have : 8 - (r.drop 13).length = 21 - r.length := by simp only [List.length_drop]; omega
          have hh2 : r.length < 21 := by simp only [List.length_drop] at h4; omega
          simp only [hh2, ↓reduceIte, this]
      · rw [readBe_err h3]
        have : 4 - (r.drop 9).length = 13 - r.length := by simp only [List.length_drop]; omega
        have hh : r.length < 13 := by simp only [List.length_drop] at h3; omega
        simp only [hh, ↓reduceIte, this]
    · rw [readBe_err h2]
      have : 8 - (r.drop 1).length = 9 - r.length := by simp only [List.length_drop]; omega
      have hh : r.length < 9 := by simp only [List.length_drop] at h2; omega
      simp only [hh, ↓reduceIte, this]
  · unfold pfTail
    rw [readBe_err h1]
    have : r.length < 1 := by omega
    simp only [this, ↓reduceIte]

theorem prTail_eq (sid : Nat) (r : List Nat) :
    prTail sid r =
      if r.length < 8 then .error (.truncated (8 - r.length))
      else if r.length < 16 then .error (.truncated (16 - r.length))
      else if r.length > 16 then .error (.unexpected "trailing bytes")
      else .ok ⟨sid, beVal (r.take 8), beVal ((r.drop 8).take 8)⟩ := by
  by_cases h1 : 8 ≤ r.length
  · unfold prTail
    rw [readBe_ok h1]
    simp only [show ¬ r.length < 8 by omega, ↓reduceIte]
    by_cases h2 : 8 ≤ (r.drop 8).length
    · rw [readBe_ok h2]
      simp only [List.length_drop] at h2
      simp only [show ¬ r.length < 16 by omega, ↓reduceIte, List.drop_drop, Nat.reduceAdd]
      by_cases h3 : r.length > 16
      · have : r.drop 16 ≠ [] := by
          intro h; have := congrArg List.length h; simp at this; omega
        simp only [this, h3, ↓reduceIte, ne_eq, not_false_eq_true]
      · have : r.drop 16 = [] := List.drop_eq_nil_of_le (by omega)
        simp only [this, h3, ↓reduceIte, ne_eq, not_true_eq_false]
    · rw [readBe_err h2]
      have : 8 - (r.drop 8).length = 16 - r.length := by simp only [List.length_drop]; omega
      have hh : r.length < 16 := by simp only [List.length_drop] at h2; omega
      simp only [hh, ↓reduceIte, this]
  · unfold prTail
    rw [readBe_err h1]
    simp only [show r.length < 8 by omega, ↓reduceIte]

end Pinc.ValuesWire
