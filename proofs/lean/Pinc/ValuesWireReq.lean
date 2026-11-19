import Pinc.ValuesWireBase

/-!
# The value wire: REQ

A model of `Req::parse`, `Req::total_len`, `Req::encode` and `Req::ranges` (`wire.rs`), written step for step on the
`Reader` and `Writer` of `ValuesWireBase`. `reqParse_eq` is the whole decision procedure of the parse in closed form
(the accepted shape, the first refusal and its `Truncated` shortfall); the theorems after it are read off it.
-/

namespace Pinc.ValuesWire

open Pinc Varint

/-! The constants of the code are written as numbers: the type byte of a REQ is 1, a REQ without ranges is 34 bytes
(`REQ_FIXED`), at most 255 ranges (`MAX_REQ_RANGES`). -/

/-- A parsed REQ: the root and the raw bytes of the ranges (`Req`, which borrows both). -/
structure Req where
  root : List Nat
  ranges : List Nat
  deriving DecidableEq, Repr

/-- `Req::parse`: the request at the start of `buf` and the bytes it took. Each `match` is a `?`. -/
def reqParse (buf : List Nat) : Except Err (Req × Nat) :=
  match readBe 1 buf with
  | .error e => .error e
  | .ok (t, r1) =>
    if t ≠ 1 then .error (.unexpected "not a request") else
    match readBytes 32 r1 with
    | .error e => .error e
    | .ok (root, r2) =>
      match readBe 1 r2 with
      | .error e => .error e
      | .ok (cnt, r3) =>
        if cnt > 255 then .error (.unexpected "too many ranges") else
        match readBytes (16 * cnt) r3 with
        | .error e => .error e
        | .ok (rg, _) => .ok (⟨root, rg⟩, 34 + 16 * cnt)

/-- `Req::total_len`: how many bytes a REQ whose first 34 bytes are `head` takes in all. -/
def reqTotalLen (head : List Nat) : Except Err Nat :=
  if head.length < 34 then .error (.truncated (34 - head.length))
  else if head.getD 0 0 ≠ 1 ∨ head.getD 33 0 > 255 then .error (.unexpected "bad request header")
  else .ok (34 + 16 * head.getD 33 0)

/-- `Req::ranges`: the `(offset, length)` of each 16-byte chunk, `k` of them. -/
def spansOf : Nat → List Nat → List (Nat × Nat)
  | 0, _ => []
  | k + 1, rg => (beVal (rg.take 8), beVal ((rg.drop 8).take 8)) :: spansOf k (rg.drop 16)

/-- The 16 bytes of one range. -/
def spanBytes (s : Nat × Nat) : List Nat := beBytes 8 s.1 ++ beBytes 8 s.2

/-- The bytes of a REQ of `root` and `spans`. -/
def reqBytes (root : List Nat) (spans : List (Nat × Nat)) : List Nat :=
  [1] ++ root ++ [spans.length] ++ spans.flatMap spanBytes

/-- `Req::encode` into `out`: the result and the buffer afterwards. More than 255 ranges (a count past the `u8` field) is refused before anything else; the room is checked before the first write. -/
def reqEncode (root : List Nat) (spans : List (Nat × Nat)) (out : List Nat) : Except Err Nat × List Nat :=
  if spans.length > 255 then (.error (.unexpected "too many ranges"), out)
  else put (reqBytes root spans) out

/-! ## The parse in closed form -/

theorem reqParse_eq (buf : List Nat) :
    reqParse buf =
      if buf.length = 0 then .error (.truncated 1)
      else if buf.getD 0 0 ≠ 1 then .error (.unexpected "not a request")
      else if buf.length < 33 then .error (.truncated (33 - buf.length))
      else if buf.length = 33 then .error (.truncated 1)
      else if buf.getD 33 0 > 255 then .error (.unexpected "too many ranges")
      else if buf.length < 34 + 16 * buf.getD 33 0 then
        .error (.truncated (34 + 16 * buf.getD 33 0 - buf.length))
      else .ok (⟨(buf.drop 1).take 32, (buf.drop 34).take (16 * buf.getD 33 0)⟩, 34 + 16 * buf.getD 33 0) := by
  by_cases h0 : buf.length = 0
  · have : buf = [] := List.length_eq_zero_iff.mp h0
    subst this
    simp [reqParse, readBe, readBytes]
  have h1 : 1 ≤ buf.length := by omega
  have e1 : readBe 1 buf = .ok (buf.getD 0 0, buf.drop 1) := by
    rw [readBe_ok h1, beVal_take_one buf (by omega)]
  unfold reqParse
  rw [e1]; simp only [h0, ↓reduceIte]
  by_cases ht : buf.getD 0 0 = 1
  · simp only [ht, ne_eq, not_true_eq_false, ite_false]
    by_cases h2 : 32 ≤ (buf.drop 1).length
    · rw [readBytes_ok h2]
      simp only [List.drop_drop, Nat.reduceAdd]
      have hl : 33 ≤ buf.length := by simp only [List.length_drop] at h2; omega
      have hn : ¬ buf.length < 33 := by omega
      simp only [hn, ↓reduceIte]
      by_cases h3 : 1 ≤ (buf.drop 33).length
      · have e3 : readBe 1 (buf.drop 33) = .ok (buf.getD 33 0, buf.drop 34) := by
          rw [readBe_ok h3, beVal_take_one _ (by omega), getD_drop_zero, List.drop_drop]
        rw [e3]
        have hn2 : ¬ buf.length = 33 := by simp only [List.length_drop] at h3; omega
        simp only [hn2, ↓reduceIte]
        by_cases hc : buf.getD 33 0 > 255
        · simp only [hc, ↓reduceIte]
        · simp only [hc, ↓reduceIte]
          by_cases h4 : 16 * buf.getD 33 0 ≤ (buf.drop 34).length
          · rw [readBytes_ok h4]
            have hh : ¬ buf.length < 34 + 16 * buf.getD 33 0 := by simp only [List.length_drop] at h4; omega
            simp only [hh, ↓reduceIte]
          · rw [readBytes_err h4]
            have hh : buf.length < 34 + 16 * buf.getD 33 0 := by simp only [List.length_drop] at h3 h4; omega
            simp only [hh, ↓reduceIte]
            simp only [List.length_drop] at h3 h4 ⊢
            have : 34 + 16 * buf.getD 33 0 - buf.length = 16 * buf.getD 33 0 - (buf.length - 34) := by omega
            rw [this]
      · have e3 : readBe 1 (buf.drop 33) = .error (.truncated 1) := by
          rw [readBe_err h3]; simp only [List.length_drop] at h3 ⊢
          have : 1 - (buf.length - 33) = 1 := by omega
          rw [this]
        rw [e3]
        have hn2 : buf.length = 33 := by simp only [List.length_drop] at h3; omega
        simp only [hn2, ↓reduceIte]
    · rw [readBytes_err h2]
      simp only [List.length_drop] at h2
      have : buf.length < 33 := by omega
      simp only [this, ↓reduceIte]
      simp only [List.length_drop]
      have : 32 - (buf.length - 1) = 33 - buf.length := by omega
      rw [this]
  · simp only [ne_eq, ht, not_false_eq_true, ↓reduceIte]

/-! ## Helper facts -/

theorem length_spansOf (k : Nat) (rg : List Nat) : (spansOf k rg).length = k := by
  induction k generalizing rg with
  | zero => rfl
  | succ k ih => simp [spansOf, ih]

theorem length_spanBytes (s : Nat × Nat) : (spanBytes s).length = 16 := by
  simp [spanBytes, length_beBytes]

theorem length_flatMap_spanBytes (spans : List (Nat × Nat)) : (spans.flatMap spanBytes).length = 16 * spans.length := by
  induction spans with
  | nil => rfl
  | cons s ss ih => simp [List.flatMap_cons, length_spanBytes, ih]; omega

theorem flatMap_spansOf (k : Nat) (rg : List Nat) (hv : ValidBytes rg) (hl : 16 * k ≤ rg.length) :
    (spansOf k rg).flatMap spanBytes = rg.take (16 * k) := by
  induction k generalizing rg with
  | zero => rfl
  | succ k ih =>
    have hv' : ValidBytes (rg.drop 16) := fun b hb => hv b (List.mem_of_mem_drop hb)
    have h8 : (rg.take 8).length = 8 := by simp; omega
    have h8' : ((rg.drop 8).take 8).length = 8 := by simp; omega
    have hv8 : ValidBytes (rg.take 8) := fun b hb => hv b (List.mem_of_mem_take hb)
    have hv8' : ValidBytes ((rg.drop 8).take 8) :=
      fun b hb => hv b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
    simp only [spansOf, List.flatMap_cons, spanBytes]
    rw [beBytes_beVal_of_length 8 _ hv8 h8, beBytes_beVal_of_length 8 _ hv8' h8',
      ih _ hv' (by simp; omega)]
    have : 16 * (k + 1) = 8 + (8 + 16 * k) := by omega
    rw [this, List.take_add, List.take_add, List.drop_drop, List.append_assoc]

theorem spansOf_flatMap (spans : List (Nat × Nat)) (h : ∀ s ∈ spans, s.1 < 2 ^ 64 ∧ s.2 < 2 ^ 64) :
    spansOf spans.length (spans.flatMap spanBytes) = spans := by
  induction spans with
  | nil => rfl
  | cons s ss ih =>
    have hs := h s (by simp)
    have hss : ∀ t ∈ ss, t.1 < 2 ^ 64 ∧ t.2 < 2 ^ 64 := fun t ht => h t (by simp [ht])
    have hF : (s :: ss).flatMap spanBytes = beBytes 8 s.1 ++ (beBytes 8 s.2 ++ ss.flatMap spanBytes) := by
      simp [List.flatMap_cons, spanBytes]
    have hd : (beBytes 8 s.1 ++ (beBytes 8 s.2 ++ ss.flatMap spanBytes)).drop 16 = ss.flatMap spanBytes := by
      rw [← List.append_assoc]
      exact List.drop_left' (by simp [length_beBytes])
    rw [List.length_cons, hF]
    simp only [spansOf]
    rw [List.take_left' (length_beBytes 8 _), List.drop_left' (length_beBytes 8 _),
      List.take_left' (length_beBytes 8 _), hd, beVal_beBytes, beVal_beBytes, ih hss]
    have h256 : (256 : Nat) ^ 8 = 2 ^ 64 := rfl
    rw [h256, Nat.mod_eq_of_lt hs.1, Nat.mod_eq_of_lt hs.2]

end Pinc.ValuesWire
