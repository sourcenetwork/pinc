import Pinc.ValuesWireReq

/-!
# The value wire: REQ theorems

Accepted shape, canonical form, injectivity, round trip, every refusal class, the cut at every length, the encoder
and `total_len` agreeing with the parse, all for every byte string and every field value.
-/

namespace Pinc.ValuesWire

open Pinc Varint

theorem take34 (buf : List Nat) (h : 34 ≤ buf.length) :
    buf.take 34 = [buf.getD 0 0] ++ (buf.drop 1).take 32 ++ [buf.getD 33 0] := by
  have : (34 : Nat) = 1 + (32 + 1) := rfl
  rw [this, List.take_add, List.take_add, List.drop_drop, take_one_eq _ (by omega), take_one_eq _ (by simp; omega),
    getD_drop_zero]
  simp

/-- The parse accepts exactly the strings with the type byte, a count of at most 255 and all the range bytes. -/
theorem req_accept_iff (buf : List Nat) :
    (∃ r n, reqParse buf = .ok (r, n)) ↔
      34 ≤ buf.length ∧ buf.getD 0 0 = 1 ∧ buf.getD 33 0 ≤ 255 ∧ 34 + 16 * buf.getD 33 0 ≤ buf.length := by
  rw [reqParse_eq]
  constructor
  · rintro ⟨r, n, h⟩
    revert h
    repeat' split
    all_goals first | (intro h; exfalso; simp at h; done) | (intro _; omega)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨(buf.drop 1).take 32, (buf.drop 34).take (16 * buf.getD 33 0)⟩, 34 + 16 * buf.getD 33 0, ?_⟩
    have a1 : ¬ buf.length = 0 := by omega
    have a2 : ¬ buf.getD 0 0 ≠ 1 := by omega
    have a3 : ¬ buf.length < 33 := by omega
    have a4 : ¬ buf.length = 33 := by omega
    have a5 : ¬ buf.getD 33 0 > 255 := by omega
    have a6 : ¬ buf.length < 34 + 16 * buf.getD 33 0 := by omega
    simp only [a1, a2, a3, a4, a5, a6, ↓reduceIte]

/-- Totality: every input is either accepted or refused with an error; nothing else can happen. -/
theorem req_total (buf : List Nat) : (∃ r n, reqParse buf = .ok (r, n)) ∨ ∃ e, reqParse buf = .error e := by
  cases h : reqParse buf with
  | error e => exact Or.inr ⟨e, rfl⟩
  | ok p => exact Or.inl ⟨p.1, p.2, rfl⟩

/-- Canonical: what the parse accepts re-encodes to exactly the bytes it consumed. -/
theorem req_canonical (buf : List Nat) (hv : ValidBytes buf) (r : Req) (n : Nat)
    (h : reqParse buf = .ok (r, n)) :
    n ≤ buf.length ∧ n = 34 + r.ranges.length ∧ r.root.length = 32 ∧ r.ranges.length = 16 * (r.ranges.length / 16) ∧
      r.ranges.length / 16 ≤ 255 ∧
      reqBytes r.root (spansOf (r.ranges.length / 16) r.ranges) = buf.take n := by
  have hacc := (req_accept_iff buf).1 ⟨r, n, h⟩
  obtain ⟨h1, h2, h3, h4⟩ := hacc
  rw [reqParse_eq] at h
  have a1 : ¬ buf.length = 0 := by omega
  have a2 : ¬ buf.getD 0 0 ≠ 1 := by omega
  have a3 : ¬ buf.length < 33 := by omega
  have a4 : ¬ buf.length = 33 := by omega
  have a5 : ¬ buf.getD 33 0 > 255 := by omega
  have a6 : ¬ buf.length < 34 + 16 * buf.getD 33 0 := by omega
  simp only [a1, a2, a3, a4, a5, a6, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have t34 := take34 buf h1
  generalize hcd : buf.getD 33 0 = c at *
  simp only [List.length_take, List.length_drop]
  have hl : min (16 * c) (buf.length - 34) = 16 * c := by
    rw [Nat.min_eq_left]; omega
  rw [hl]
  have hc : 16 * c / 16 = c := Nat.mul_div_cancel_left _ (by omega)
  rw [hc]
  refine ⟨h4, rfl, by omega, by omega, h3, ?_⟩
  have hv' : ValidBytes ((buf.drop 34).take (16 * c)) :=
    fun b hb => hv b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
  unfold reqBytes
  rw [length_spansOf, flatMap_spansOf _ _ hv' (by simp; omega)]
  rw [List.take_add, t34, h2]
  simp [List.take_take]

/-- Injective: two inputs that parse to the same request have the same length and the same bytes. -/
theorem req_injective (a b : List Nat) (ha : ValidBytes a) (hb : ValidBytes b) (r : Req) (n m : Nat)
    (h1 : reqParse a = .ok (r, n)) (h2 : reqParse b = .ok (r, m)) : n = m ∧ a.take n = b.take m := by
  obtain ⟨_, e1, _, _, _, c1⟩ := req_canonical a ha r n h1
  obtain ⟨_, e2, _, _, _, c2⟩ := req_canonical b hb r m h2
  exact ⟨by omega, by rw [← c1, ← c2]⟩

theorem length_reqBytes (root : List Nat) (spans : List (Nat × Nat)) (hr : root.length = 32) :
    (reqBytes root spans).length = 34 + 16 * spans.length := by
  simp only [reqBytes, List.length_append, List.length_singleton, hr, length_flatMap_spanBytes]

/-- Round trip: parsing an encoded request, with anything after it, returns the request and its length, and the
ranges read back are the ranges encoded (every offset and length below `2 ^ 64`, the `u64` range). -/
theorem req_roundtrip (root : List Nat) (spans : List (Nat × Nat)) (rest : List Nat) (hr : root.length = 32)
    (hn : spans.length ≤ 255) (hs : ∀ s ∈ spans, s.1 < 2 ^ 64 ∧ s.2 < 2 ^ 64) :
    reqParse (reqBytes root spans ++ rest) = .ok (⟨root, spans.flatMap spanBytes⟩, 34 + 16 * spans.length) ∧
      spansOf spans.length (spans.flatMap spanBytes) = spans := by
  refine ⟨?_, spansOf_flatMap spans hs⟩
  have hF := length_flatMap_spanBytes spans
  have hb : reqBytes root spans ++ rest = 1 :: (root ++ spans.length :: (spans.flatMap spanBytes ++ rest)) := by
    simp [reqBytes]
  have d1 : (reqBytes root spans ++ rest).drop 1 = root ++ spans.length :: (spans.flatMap spanBytes ++ rest) := by
    rw [hb]; rfl
  have d33 : (reqBytes root spans ++ rest).drop 33 = spans.length :: (spans.flatMap spanBytes ++ rest) := by
    rw [show 33 = 1 + 32 from rfl, ← List.drop_drop, d1]
    exact List.drop_left' hr
  have d34 : (reqBytes root spans ++ rest).drop 34 = spans.flatMap spanBytes ++ rest := by
    rw [show 34 = 33 + 1 from rfl, ← List.drop_drop, d33]; rfl
  have hlen : (reqBytes root spans ++ rest).length = 34 + 16 * spans.length + rest.length := by
    simp only [List.length_append, length_reqBytes root spans hr]
  have g0 : (reqBytes root spans ++ rest).getD 0 0 = 1 := by rw [hb]; rfl
  have g33 : (reqBytes root spans ++ rest).getD 33 0 = spans.length := by
    rw [← getD_drop_zero, d33]; rfl
  rw [reqParse_eq, g33, g0]
  have a1 : ¬ (reqBytes root spans ++ rest).length = 0 := by omega
  have a3 : ¬ (reqBytes root spans ++ rest).length < 33 := by omega
  have a4 : ¬ (reqBytes root spans ++ rest).length = 33 := by omega
  have a5 : ¬ spans.length > 255 := by omega
  have a6 : ¬ (reqBytes root spans ++ rest).length < 34 + 16 * spans.length := by omega
  simp only [a1, a3, a4, a5, a6, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [d1, d34, List.take_left' hr, List.take_left' hF]

/-! ## The encoder -/

/-- More than 255 ranges (which does not fit the count byte) is refused and nothing is written. -/
theorem reqEncode_too_many (root : List Nat) (spans : List (Nat × Nat)) (out : List Nat)
    (h : 255 < spans.length) : reqEncode root spans out = (.error (.unexpected "too many ranges"), out) := by
  simp [reqEncode, h]

/-- A buffer shorter than the request is refused with the exact shortfall, and nothing is written. -/
theorem reqEncode_short (root : List Nat) (spans : List (Nat × Nat)) (out : List Nat) (hr : root.length = 32)
    (hn : spans.length ≤ 255) (h : out.length < 34 + 16 * spans.length) :
    reqEncode root spans out = (.error (.bufferTooSmall (34 + 16 * spans.length - out.length)), out) := by
  have hl := length_reqBytes root spans hr
  have : ¬ spans.length > 255 := by omega
  simp only [reqEncode, this, ↓reduceIte]
  rw [put_err (by omega), hl]

/-- Otherwise the encoder writes exactly the request and leaves the rest of the buffer alone. -/
theorem reqEncode_ok (root : List Nat) (spans : List (Nat × Nat)) (out : List Nat) (hr : root.length = 32)
    (hn : spans.length ≤ 255) (h : 34 + 16 * spans.length ≤ out.length) :
    reqEncode root spans out = (.ok (34 + 16 * spans.length), reqBytes root spans ++ out.drop (34 + 16 * spans.length)) := by
  have hl := length_reqBytes root spans hr
  have : ¬ spans.length > 255 := by omega
  simp only [reqEncode, this, ↓reduceIte]
  rw [put_ok (by omega), hl]

/-- What an encode wrote parses back to the request. -/
theorem reqEncode_parse (root : List Nat) (spans : List (Nat × Nat)) (out after : List Nat) (k : Nat)
    (hr : root.length = 32) (hs : ∀ s ∈ spans, s.1 < 2 ^ 64 ∧ s.2 < 2 ^ 64)
    (h : reqEncode root spans out = (.ok k, after)) :
    k = 34 + 16 * spans.length ∧
      reqParse after = .ok (⟨root, spans.flatMap spanBytes⟩, k) ∧ spansOf spans.length (spans.flatMap spanBytes) = spans := by
  by_cases hn : spans.length ≤ 255
  · by_cases ho : 34 + 16 * spans.length ≤ out.length
    · rw [reqEncode_ok root spans out hr hn ho] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := req_roundtrip root spans (out.drop (34 + 16 * spans.length)) hr hn hs
      exact ⟨rfl, h1, h2⟩
    · rw [reqEncode_short root spans out hr hn (by omega)] at h
      simp at h
  · rw [reqEncode_too_many root spans out (by omega)] at h
    simp at h

/-! ## The refusals -/

/-- A wrong type byte is refused as not a request. -/
theorem req_reject_type (t : Nat) (r : List Nat) (h : t ≠ 1) :
    reqParse (t :: r) = .error (.unexpected "not a request") := by
  rw [reqParse_eq]
  simp [h]

/-- A count over 255 is refused, whatever follows. -/
theorem req_reject_count (buf : List Nat) (h1 : 34 ≤ buf.length) (h2 : buf.getD 0 0 = 1) (h3 : 255 < buf.getD 33 0) :
    reqParse buf = .error (.unexpected "too many ranges") := by
  rw [reqParse_eq]
  have a1 : ¬ buf.length = 0 := by omega
  have a3 : ¬ buf.length < 33 := by omega
  have a4 : ¬ buf.length = 33 := by omega
  simp only [a1, a3, a4, h2, ne_eq, not_true_eq_false, ↓reduceIte, gt_iff_lt, h3]

/-- An input shorter than the request its count asks for is refused as truncated, with the shortfall. -/
theorem req_reject_short (buf : List Nat) (h1 : 34 ≤ buf.length) (h2 : buf.getD 0 0 = 1) (h3 : buf.getD 33 0 ≤ 255)
    (h4 : buf.length < 34 + 16 * buf.getD 33 0) :
    reqParse buf = .error (.truncated (34 + 16 * buf.getD 33 0 - buf.length)) := by
  rw [reqParse_eq]
  have a1 : ¬ buf.length = 0 := by omega
  have a3 : ¬ buf.length < 33 := by omega
  have a4 : ¬ buf.length = 33 := by omega
  have a5 : ¬ buf.getD 33 0 > 255 := by omega
  simp only [a1, a3, a4, a5, h2, h4, ne_eq, not_true_eq_false, ↓reduceIte]

/-- Truncation at every length: every strict prefix of an accepted request is refused as truncated, with a
shortfall that is positive and within what is missing. -/
theorem req_prefix_truncated (buf : List Nat) (hv : ValidBytes buf) (r : Req) (n : Nat)
    (h : reqParse buf = .ok (r, n)) (m : Nat) (hm : m < n) :
    ∃ k, 1 ≤ k ∧ k ≤ n - m ∧ reqParse (buf.take m) = .error (.truncated k) := by
  obtain ⟨hn, hne, hroot, hrl, hcnt, _⟩ := req_canonical buf hv r n h
  obtain ⟨h1, h2, h3, h4⟩ := (req_accept_iff buf).1 ⟨r, n, h⟩
  have hnc : n = 34 + 16 * buf.getD 33 0 := by
    rw [reqParse_eq] at h
    have a1 : ¬ buf.length = 0 := by omega
    have a3 : ¬ buf.length < 33 := by omega
    have a4 : ¬ buf.length = 33 := by omega
    have a5 : ¬ buf.getD 33 0 > 255 := by omega
    have a6 : ¬ buf.length < 34 + 16 * buf.getD 33 0 := by omega
    simp only [a1, h2, a3, a4, a5, a6, ne_eq, not_true_eq_false, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  have hlen : (buf.take m).length = m := by simp; omega
  rw [reqParse_eq, hlen]
  by_cases m0 : m = 0
  · subst m0
    exact ⟨1, Nat.le_refl _, by omega, by simp⟩
  have g0 : (buf.take m).getD 0 0 = 1 := by rw [getD_take (by omega)]; exact h2
  by_cases m33 : m < 33
  · refine ⟨33 - m, by omega, by omega, ?_⟩
    simp only [m0, m33, g0, ne_eq, not_true_eq_false, ↓reduceIte]
  by_cases m33' : m = 33
  · subst m33'
    refine ⟨1, Nat.le_refl _, by omega, ?_⟩
    simp only [m0, m33, g0, ne_eq, not_true_eq_false, ↓reduceIte]
  · have g33 : (buf.take m).getD 33 0 = buf.getD 33 0 := getD_take (by omega)
    have a5 : ¬ buf.getD 33 0 > 255 := by omega
    refine ⟨34 + 16 * buf.getD 33 0 - m, by omega, by omega, ?_⟩
    have a6 : m < 34 + 16 * buf.getD 33 0 := by omega
    simp only [m0, m33, m33', g0, g33, a5, a6, ne_eq, not_true_eq_false, ↓reduceIte]

/-! ## `total_len` and the parse agree -/

theorem totalLen_short (head : List Nat) (h : head.length < 34) :
    reqTotalLen head = .error (.truncated (34 - head.length)) := by
  simp [reqTotalLen, h]

theorem totalLen_eq (head : List Nat) (h : 34 ≤ head.length) :
    reqTotalLen head =
      if head.getD 0 0 ≠ 1 ∨ head.getD 33 0 > 255 then .error (.unexpected "bad request header")
      else .ok (34 + 16 * head.getD 33 0) := by
  have : ¬ head.length < 34 := by omega
  unfold reqTotalLen
  simp only [this, ↓reduceIte]

/-- The length a successful parse reports. -/
theorem reqParse_n (buf : List Nat) (r : Req) (n : Nat) (h : reqParse buf = .ok (r, n)) :
    n = 34 + 16 * buf.getD 33 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := (req_accept_iff buf).1 ⟨r, n, h⟩
  rw [reqParse_eq] at h
  have a1 : ¬ buf.length = 0 := by omega
  have a3 : ¬ buf.length < 33 := by omega
  have a4 : ¬ buf.length = 33 := by omega
  have a5 : ¬ buf.getD 33 0 > 255 := by omega
  have a6 : ¬ buf.length < 34 + 16 * buf.getD 33 0 := by omega
  simp only [a1, h2, a3, a4, a5, a6, ne_eq, not_true_eq_false, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

/-- The parse and `total_len` agree on the length of every accepted request. -/
theorem totalLen_of_parse (buf : List Nat) (r : Req) (n : Nat) (h : reqParse buf = .ok (r, n)) :
    reqTotalLen buf = .ok n := by
  obtain ⟨h1, h2, h3, h4⟩ := (req_accept_iff buf).1 ⟨r, n, h⟩
  have hnc := reqParse_n buf r n h
  rw [totalLen_eq buf h1]
  have a : ¬ (buf.getD 0 0 ≠ 1 ∨ buf.getD 33 0 > 255) := by omega
  simp only [a, ↓reduceIte, hnc]

/-- When `total_len` accepts a head, the request is accepted exactly when the input is at least that long, and then
it takes that length; a shorter input is refused as truncated. -/
theorem totalLen_agrees (buf : List Nat) (N : Nat) (h : reqTotalLen buf = .ok N) :
    (N ≤ buf.length → ∃ r, reqParse buf = .ok (r, N)) ∧
      (buf.length < N → ∃ k, reqParse buf = .error (.truncated k)) := by
  by_cases a : buf.length < 34
  · rw [totalLen_short buf a] at h; cases h
  have a' : 34 ≤ buf.length := by omega
  rw [totalLen_eq buf a'] at h
  by_cases hh : buf.getD 0 0 ≠ 1 ∨ buf.getD 33 0 > 255
  · simp only [hh, ↓reduceIte] at h; cases h
  have hh' : ¬ (buf.getD 0 0 ≠ 1 ∨ buf.getD 33 0 > 255) := hh
  simp only [hh', ↓reduceIte, Except.ok.injEq] at h
  have g0 : buf.getD 0 0 = 1 := by omega
  have g33 : buf.getD 33 0 ≤ 255 := by omega
  constructor
  · intro hl
    obtain ⟨r, n, hp⟩ := (req_accept_iff buf).2 ⟨a', g0, g33, by omega⟩
    refine ⟨r, ?_⟩
    rw [hp, reqParse_n buf r n hp, h]
  · intro hl
    exact ⟨_, req_reject_short buf a' g0 g33 (by omega)⟩

/-- A head `total_len` refuses is refused by the parse too. -/
theorem totalLen_reject_parse_reject (buf : List Nat) (m : String) (h : reqTotalLen buf = .error (.unexpected m)) :
    ∃ m', reqParse buf = .error (.unexpected m') := by
  by_cases a : buf.length < 34
  · rw [totalLen_short buf a] at h; cases h
  have a' : 34 ≤ buf.length := by omega
  rw [totalLen_eq buf a'] at h
  by_cases hc : buf.getD 0 0 ≠ 1 ∨ buf.getD 33 0 > 255
  · rcases hc with hc | hc
    · rcases buf with _ | ⟨t, r⟩
      · simp at a'
      · exact ⟨_, req_reject_type t r (by simpa using hc)⟩
    · by_cases g0 : buf.getD 0 0 = 1
      · exact ⟨_, req_reject_count buf a' g0 hc⟩
      · rcases buf with _ | ⟨t, r⟩
        · simp at a'
        · exact ⟨_, req_reject_type t r (by simpa using g0)⟩
  · simp only [hc, ↓reduceIte] at h; cases h

end Pinc.ValuesWire

#audit_axioms Pinc.ValuesWire.reqParse_eq
#audit_axioms Pinc.ValuesWire.req_accept_iff
#audit_axioms Pinc.ValuesWire.req_canonical
#audit_axioms Pinc.ValuesWire.req_injective
#audit_axioms Pinc.ValuesWire.req_roundtrip
#audit_axioms Pinc.ValuesWire.reqEncode_ok
#audit_axioms Pinc.ValuesWire.reqEncode_short
#audit_axioms Pinc.ValuesWire.reqEncode_too_many
#audit_axioms Pinc.ValuesWire.reqEncode_parse
#audit_axioms Pinc.ValuesWire.req_reject_type
#audit_axioms Pinc.ValuesWire.req_reject_count
#audit_axioms Pinc.ValuesWire.req_prefix_truncated
#audit_axioms Pinc.ValuesWire.totalLen_of_parse
#audit_axioms Pinc.ValuesWire.totalLen_agrees
#audit_axioms Pinc.ValuesWire.totalLen_reject_parse_reject
