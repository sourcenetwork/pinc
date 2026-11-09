import Vinc.ValuesWireProof
import Vinc.ValuesWireVarint

/-!
# The value wire: PROOF and PROOF_REQ theorems

Canonical form, injectivity, round trip, the encoders, and every refusal class, for every body and every field value.
-/

namespace Vinc.ValuesWire

open Vinc Varint

theorem pfParse_eq (body : List Nat) (hv : ValidBytes body) :
    pfParse body = match decode body with
      | .error e => .error (varErr e)
      | .ok (sid, n) => pfTail sid (body.drop n) := by
  unfold pfParse
  cases hd : decode body with
  | error e => rw [readVarint_err hd]
  | ok p => rw [readVarint_ok hv (v := p.1) (n := p.2) hd]

theorem prParse_eq (body : List Nat) (hv : ValidBytes body) :
    prParse body = match decode body with
      | .error e => .error (varErr e)
      | .ok (sid, n) => prTail sid (body.drop n) := by
  unfold prParse
  cases hd : decode body with
  | error e => rw [readVarint_err hd]
  | ok p => rw [readVarint_ok hv (v := p.1) (n := p.2) hd]

theorem readVarint_enc (v : Nat) (hv : v < limit) (rest : List Nat) :
    readVarint (encodeBytes v ++ rest) = .ok (v, rest) := by
  simp only [readVarint, decode_encode v rest hv]
  rw [readBytes_append _ _ rfl]

theorem split21 (r : List Nat) (h : 21 ≤ r.length) :
    [r.getD 0 0] ++ (r.drop 1).take 8 ++ (r.drop 9).take 4 ++ (r.drop 13).take 8 ++ r.drop 21 = r := by
  have h2 : r.drop 1 = (r.drop 1).take 8 ++ r.drop 9 := by
    have := List.take_append_drop 8 (r.drop 1)
    rw [List.drop_drop] at this; exact this.symm
  have h3 : r.drop 9 = (r.drop 9).take 4 ++ r.drop 13 := by
    have := List.take_append_drop 4 (r.drop 9)
    rw [List.drop_drop] at this; exact this.symm
  have h4 : r.drop 13 = (r.drop 13).take 8 ++ r.drop 21 := by
    have := List.take_append_drop 8 (r.drop 13)
    rw [List.drop_drop] at this; exact this.symm
  rw [← take_one_eq r (by omega)]
  simp only [List.append_assoc]
  rw [← h4, ← h3, ← h2, List.take_append_drop]

theorem pfTail_short (sid : Nat) (r : List Nat) (h : r.length < 21) :
    ∃ k, 1 ≤ k ∧ k ≤ 21 - r.length ∧ pfTail sid r = .error (.truncated k) := by
  rw [pfTail_eq]
  by_cases c1 : r.length < 1
  · exact ⟨1 - r.length, by omega, by omega, by simp only [c1, ↓reduceIte]⟩
  by_cases c2 : r.length < 9
  · exact ⟨9 - r.length, by omega, by omega, by simp only [c1, c2, ↓reduceIte]⟩
  by_cases c3 : r.length < 13
  · exact ⟨13 - r.length, by omega, by omega, by simp only [c1, c2, c3, ↓reduceIte]⟩
  · exact ⟨21 - r.length, by omega, by omega, by simp only [c1, c2, c3, h, ↓reduceIte]⟩

theorem pfTail_long (sid : Nat) (r : List Nat) (h : 21 ≤ r.length) :
    pfTail sid r =
      if (r.drop 21).length % 64 ≠ 0 ∨ (r.drop 21).length > 1100 then .error (.unexpected "bad proof length")
      else .ok ⟨sid, r.getD 0 0, beVal ((r.drop 1).take 8), beVal ((r.drop 9).take 4), beVal ((r.drop 13).take 8),
        r.drop 21⟩ := by
  rw [pfTail_eq]
  have c1 : ¬ r.length < 1 := by omega
  have c2 : ¬ r.length < 9 := by omega
  have c3 : ¬ r.length < 13 := by omega
  have c4 : ¬ r.length < 21 := by omega
  simp only [c1, c2, c3, c4, ↓reduceIte]

theorem prTail_short (sid : Nat) (r : List Nat) (h : r.length < 16) :
    ∃ k, 1 ≤ k ∧ k ≤ 16 - r.length ∧ prTail sid r = .error (.truncated k) := by
  rw [prTail_eq]
  by_cases c1 : r.length < 8
  · exact ⟨8 - r.length, by omega, by omega, by simp only [c1, ↓reduceIte]⟩
  · exact ⟨16 - r.length, by omega, by omega, by simp only [c1, h, ↓reduceIte]⟩

/-- What a successful PROOF parse looked like: a stream id, then at least the 21 fixed bytes, then a proof of whole
pairs and at most 1100 bytes. -/
theorem pf_shape (body : List Nat) (hv : ValidBytes body) (f : PF) (h : pfParse body = .ok f) :
    ∃ n, decode body = .ok (f.sid, n) ∧ 21 ≤ (body.drop n).length ∧
      f = ⟨f.sid, (body.drop n).getD 0 0, beVal (((body.drop n).drop 1).take 8), beVal (((body.drop n).drop 9).take 4),
        beVal (((body.drop n).drop 13).take 8), (body.drop n).drop 21⟩ ∧
      f.proof.length % 64 = 0 ∧ f.proof.length ≤ 1100 := by
  rw [pfParse_eq body hv] at h
  cases hd : decode body with
  | error e => rw [hd] at h; cases h
  | ok p =>
    rw [hd] at h
    obtain ⟨sid, n⟩ := p
    simp only at h
    by_cases hl : (body.drop n).length < 21
    · obtain ⟨k, _, _, hk⟩ := pfTail_short sid _ hl
      rw [hk] at h; cases h
    rw [pfTail_long sid _ (by omega)] at h
    by_cases hb : ((body.drop n).drop 21).length % 64 ≠ 0 ∨ ((body.drop n).drop 21).length > 1100
    · simp only [hb, ↓reduceIte] at h; cases h
    simp only [hb, ↓reduceIte, Except.ok.injEq] at h
    have hsid : f.sid = sid := by rw [← h]
    have hproof : f.proof = (body.drop n).drop 21 := by rw [← h]
    have hb' : ¬ (f.proof.length % 64 ≠ 0 ∨ f.proof.length > 1100) := by rw [hproof]; exact hb
    refine ⟨n, by simp [hsid, hd], by omega, ?_, by omega, by omega⟩
    rw [hsid]; exact h.symm

/-- Canonical: an accepted PROOF body is exactly its head followed by its proof, so the parse is injective and
re-encoding the fields reproduces the body; every field is in the range of its type. -/
theorem pf_canonical (body : List Nat) (hv : ValidBytes body) (f : PF) (h : pfParse body = .ok f) :
    body = pfHead f ++ f.proof ∧ f.sid < 2 ^ 63 ∧ f.glog < 256 ∧ f.start < 2 ^ 64 ∧ f.wn < 2 ^ 32 ∧ f.ln < 2 ^ 64 ∧
      f.proof.length % 64 = 0 ∧ f.proof.length ≤ 1088 ∧ ValidBytes f.proof := by
  obtain ⟨n, hd, hl, hf, hp1, hp2⟩ := pf_shape body hv f h
  obtain ⟨hcan, hn⟩ := decode_canonical body hv f.sid n hd
  obtain ⟨hlim, _⟩ := decode_bounds body hv f.sid n hd
  have hbody : body = body.take n ++ body.drop n := (List.take_append_drop n body).symm
  have hvr0 : ValidBytes (body.drop n) := fun b hb => hv b (List.mem_of_mem_drop hb)
  generalize body.drop n = r at *
  have hvr : ValidBytes r := hvr0
  have hsplit := split21 r hl
  have vb : ∀ x y, ValidBytes ((r.drop x).take y) :=
    fun x y z hz => hvr z (List.mem_of_mem_drop (List.mem_of_mem_take hz))
  have lb : ∀ x y, x + y ≤ r.length → ((r.drop x).take y).length = y := by
    intro x y hxy; simp; omega
  have hvp : ValidBytes (r.drop 21) := fun b hb => hvr b (List.mem_of_mem_drop hb)
  have hproof : f.proof = r.drop 21 := by rw [hf]
  have hglog : f.glog = r.getD 0 0 := by rw [hf]
  have hstart : f.start = beVal ((r.drop 1).take 8) := by rw [hf]
  have hwn : f.wn = beVal ((r.drop 9).take 4) := by rw [hf]
  have hln : f.ln = beVal ((r.drop 13).take 8) := by rw [hf]
  have hr0 : r.getD 0 0 < 256 := by
    have : r.getD 0 0 ∈ r := by
      have h0 : 0 < r.length := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0]
    exact hvr _ this
  refine ⟨?_, hlim, by omega, ?_, ?_, ?_, hp1, ?_, by rw [hproof]; exact hvp⟩
  · rw [hbody, hcan]
    unfold pfHead
    rw [hglog, hstart, hwn, hln, hproof, beBytes_beVal_of_length 8 _ (vb 1 8) (lb 1 8 (by omega)),
      beBytes_beVal_of_length 4 _ (vb 9 4) (lb 9 4 (by omega)),
      beBytes_beVal_of_length 8 _ (vb 13 8) (lb 13 8 (by omega))]
    calc encodeBytes f.sid ++ r = encodeBytes f.sid ++ ([r.getD 0 0] ++ (r.drop 1).take 8 ++ (r.drop 9).take 4 ++
          (r.drop 13).take 8 ++ r.drop 21) := by rw [split21 r hl]
      _ = _ := by simp only [List.append_assoc]
  · rw [hstart]; have := beVal_lt _ (vb 1 8); rw [lb 1 8 (by omega)] at this; omega
  · rw [hwn]; have := beVal_lt _ (vb 9 4); rw [lb 9 4 (by omega)] at this; omega
  · rw [hln]; have := beVal_lt _ (vb 13 8); rw [lb 13 8 (by omega)] at this; omega
  · omega

/-- Injective: two bodies that parse to the same frame are the same bytes. -/
theorem pf_injective (a b : List Nat) (ha : ValidBytes a) (hb : ValidBytes b) (f : PF)
    (h1 : pfParse a = .ok f) (h2 : pfParse b = .ok f) : a = b := by
  rw [(pf_canonical a ha f h1).1, (pf_canonical b hb f h2).1]

theorem pfR_parts (g : Nat) (A B C P : List Nat) (hA : A.length = 8) (hB : B.length = 4) (hC : C.length = 8) :
    (g :: (A ++ (B ++ (C ++ P)))).getD 0 0 = g ∧ ((g :: (A ++ (B ++ (C ++ P)))).drop 1).take 8 = A ∧
      ((g :: (A ++ (B ++ (C ++ P)))).drop 9).take 4 = B ∧ ((g :: (A ++ (B ++ (C ++ P)))).drop 13).take 8 = C ∧
      (g :: (A ++ (B ++ (C ++ P)))).drop 21 = P := by
  have d9 : (g :: (A ++ (B ++ (C ++ P)))).drop 9 = B ++ (C ++ P) := by
    rw [show 9 = 1 + 8 from rfl, ← List.drop_drop]
    exact List.drop_left' hA
  have d13 : (g :: (A ++ (B ++ (C ++ P)))).drop 13 = C ++ P := by
    rw [show 13 = 9 + 4 from rfl, ← List.drop_drop, d9]
    exact List.drop_left' hB
  have d21 : (g :: (A ++ (B ++ (C ++ P)))).drop 21 = P := by
    rw [show 21 = 13 + 8 from rfl, ← List.drop_drop, d13]
    exact List.drop_left' hC
  refine ⟨rfl, ?_, ?_, ?_, d21⟩
  · exact List.take_left' hA
  · rw [d9]; exact List.take_left' hB
  · rw [d13]; exact List.take_left' hC

/-- Round trip: parsing an encoded head followed by a proof of whole pairs (at most 1100 bytes) returns every field,
and the proof is exactly the bytes after the head. -/
theorem pf_roundtrip (f : PF) (h1 : f.sid < 2 ^ 63) (h2 : f.start < 2 ^ 64) (h3 : f.wn < 2 ^ 32)
    (h4 : f.ln < 2 ^ 64) (h5 : f.proof.length % 64 = 0) (h6 : f.proof.length ≤ 1100) :
    pfParse (pfHead f ++ f.proof) = .ok f := by
  have hl : f.sid < limit := h1
  have hb : pfHead f ++ f.proof = encodeBytes f.sid ++
      (f.glog :: (beBytes 8 f.start ++ (beBytes 4 f.wn ++ (beBytes 8 f.ln ++ f.proof)))) := by
    simp [pfHead]
  obtain ⟨g0, t1, t9, t13, d21⟩ := pfR_parts f.glog (beBytes 8 f.start) (beBytes 4 f.wn) (beBytes 8 f.ln) f.proof
    (length_beBytes _ _) (length_beBytes _ _) (length_beBytes _ _)
  unfold pfParse
  rw [hb, readVarint_enc f.sid hl]
  simp only
  rw [pfTail_long _ _ (by simp [length_beBytes]; omega)]
  have hb' : ¬ ((List.drop 21 (f.glog :: (beBytes 8 f.start ++ (beBytes 4 f.wn ++ (beBytes 8 f.ln ++ f.proof))))).length % 64 ≠ 0 ∨
      (List.drop 21 (f.glog :: (beBytes 8 f.start ++ (beBytes 4 f.wn ++ (beBytes 8 f.ln ++ f.proof))))).length > 1100) := by
    rw [d21]; omega
  simp only [g0, t1, t9, t13, d21, beVal_beBytes]
  have e8 : (256 : Nat) ^ 8 = 2 ^ 64 := rfl
  have e4 : (256 : Nat) ^ 4 = 2 ^ 32 := rfl
  rw [e8, e4, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]
  have hb'' : ¬ (f.proof.length % 64 ≠ 0 ∨ f.proof.length > 1100) := by omega
  simp only [hb'', ↓reduceIte]

theorem length_pfHead (f : PF) : (pfHead f).length = encodedLen f.sid + 21 := by
  simp only [pfHead, List.length_append, List.length_singleton, length_beBytes, Varint.length_encodeBytes]

theorem encodeInto_ok_of_lt (cap v : Nat) (hc : 9 ≤ cap) (hv : v < limit) : encodeInto cap v = .ok (encodeBytes v) := by
  have hl := (encode_length v hv).2
  have h1 : ¬ v ≥ limit := by omega
  have h2 : ¬ encodedLen v > cap := by unfold maxLen at hl; omega
  simp only [encodeInto, h1, h2, ↓reduceIte]

theorem encodeInto_overflow (cap v : Nat) (hv : limit ≤ v) : encodeInto cap v = .error .overflow := by
  have h1 : v ≥ limit := hv
  simp only [encodeInto, h1, ↓reduceIte]

/-- An id of 2^63 or more is refused first, and nothing is written. -/
theorem pfWriteHead_overflow (sid g s w l : Nat) (out : List Nat) (h : 2 ^ 63 ≤ sid) :
    pfWriteHead sid g s w l out = (.error .overflow, out) := by
  have : limit ≤ sid := h
  simp [pfWriteHead, encodeInto_overflow 30 sid this, varErr]

/-- A buffer shorter than the head is refused with the exact shortfall, and nothing is written. -/
theorem pfWriteHead_short (sid g s w l : Nat) (out : List Nat) (h : sid < 2 ^ 63)
    (hs : out.length < encodedLen sid + 21) :
    pfWriteHead sid g s w l out = (.error (.bufferTooSmall (encodedLen sid + 21 - out.length)), out) := by
  have hl : sid < limit := h
  have hlen : (encodeBytes sid ++ [g] ++ beBytes 8 s ++ beBytes 4 w ++ beBytes 8 l).length = encodedLen sid + 21 := by
    simp only [List.length_append, List.length_singleton, length_beBytes, Varint.length_encodeBytes]
  unfold pfWriteHead
  rw [encodeInto_ok_of_lt 30 sid (by omega) hl]
  simp only
  rw [put_err (by omega), hlen]

/-- Otherwise exactly the head is written and the rest of the buffer is left alone. -/
theorem pfWriteHead_ok (sid g s w l : Nat) (out : List Nat) (h : sid < 2 ^ 63)
    (hs : encodedLen sid + 21 ≤ out.length) :
    pfWriteHead sid g s w l out =
      (.ok (encodedLen sid + 21),
        (encodeBytes sid ++ [g] ++ beBytes 8 s ++ beBytes 4 w ++ beBytes 8 l) ++ out.drop (encodedLen sid + 21)) := by
  have hl : sid < limit := h
  have hlen : (encodeBytes sid ++ [g] ++ beBytes 8 s ++ beBytes 4 w ++ beBytes 8 l).length = encodedLen sid + 21 := by
    simp only [List.length_append, List.length_singleton, length_beBytes, Varint.length_encodeBytes]
  unfold pfWriteHead
  rw [encodeInto_ok_of_lt 30 sid (by omega) hl]
  simp only
  rw [put_ok (by omega), hlen]

/-! ### The refusals of a PROOF body -/

/-- A refused id is a refused frame, with the error the varint reports (cut, too long or non-minimal). -/
theorem pf_reject_varint (body : List Nat) (e : Varint.Error) (h : decode body = .error e) :
    pfParse body = .error (varErr e) := by
  unfold pfParse
  rw [readVarint_err h]

/-- A proof that is not a whole number of 64-byte pairs, or is over 1100 bytes, is refused. -/
theorem pf_reject_proof (body : List Nat) (hv : ValidBytes body) (sid n : Nat) (hd : decode body = .ok (sid, n))
    (hl : 21 ≤ (body.drop n).length)
    (hp : ((body.drop n).drop 21).length % 64 ≠ 0 ∨ ((body.drop n).drop 21).length > 1100) :
    pfParse body = .error (.unexpected "bad proof length") := by
  rw [pfParse_eq body hv, hd]
  simp only
  rw [pfTail_long _ _ hl]
  simp only [hp, ↓reduceIte]

/-- Truncation at every length: every strict prefix of an accepted head is refused as truncated, with a shortfall
that is positive and within what is missing. -/
theorem pf_prefix_truncated (body : List Nat) (hv : ValidBytes body) (f : PF) (h : pfParse body = .ok f) (m : Nat)
    (hm : m < (pfHead f).length) :
    ∃ k, 1 ≤ k ∧ k ≤ (pfHead f).length - m ∧ pfParse (body.take m) = .error (.truncated k) := by
  obtain ⟨hbody, hlim, _⟩ := pf_canonical body hv f h
  have hl : f.sid < limit := hlim
  have hvm : ValidBytes (body.take m) := fun b hb => hv b (List.mem_of_mem_take hb)
  have hlen := length_pfHead f
  have hL : (encodeBytes f.sid).length = encodedLen f.sid := Varint.length_encodeBytes _
  obtain ⟨X, hX, hXl⟩ : ∃ X : List Nat, body = encodeBytes f.sid ++ X ∧ 21 ≤ X.length := by
    refine ⟨[f.glog] ++ beBytes 8 f.start ++ beBytes 4 f.wn ++ beBytes 8 f.ln ++ f.proof, ?_, ?_⟩
    · rw [hbody]; simp [pfHead]
    · simp [length_beBytes]; omega
  by_cases hc : m < (encodeBytes f.sid).length
  · refine ⟨1, Nat.le_refl _, by omega, ?_⟩
    rw [pfParse_eq _ hvm]
    have : decode (body.take m) = .error .truncated := by
      rw [hX]; exact decode_cut_truncated f.sid hl X m hc
    rw [this]
    rfl
  · have htk : body.take m = encodeBytes f.sid ++ X.take (m - (encodeBytes f.sid).length) := by
      rw [hX, List.take_append, List.take_of_length_le (by omega)]
    have hd : decode (body.take m) = .ok (f.sid, (encodeBytes f.sid).length) := by
      rw [htk]; exact decode_encode f.sid _ hl
    rw [pfParse_eq _ hvm, hd]
    simp only
    have hYl : (X.take (m - (encodeBytes f.sid).length)).length < 21 := by
      rw [List.length_take]; omega
    obtain ⟨k, hk1, hk2, hk⟩ := pfTail_short f.sid (X.take (m - (encodeBytes f.sid).length)) hYl
    refine ⟨k, hk1, ?_, ?_⟩
    · rw [List.length_take] at hk2; omega
    · rw [htk, List.drop_left' rfl]; exact hk

/-! ## PROOF_REQ -/

theorem prTail_long (sid : Nat) (r : List Nat) (h : 16 ≤ r.length) :
    prTail sid r =
      if r.length > 16 then .error (.unexpected "trailing bytes")
      else .ok ⟨sid, beVal (r.take 8), beVal ((r.drop 8).take 8)⟩ := by
  rw [prTail_eq]
  have c1 : ¬ r.length < 8 := by omega
  have c2 : ¬ r.length < 16 := by omega
  simp only [c1, c2, ↓reduceIte]

/-- What a successful PROOF_REQ parse looked like: an id, then exactly two `u64`s and nothing after. -/
theorem pr_shape (body : List Nat) (hv : ValidBytes body) (r : PR) (h : prParse body = .ok r) :
    ∃ n, decode body = .ok (r.sid, n) ∧ (body.drop n).length = 16 ∧
      r = ⟨r.sid, beVal ((body.drop n).take 8), beVal (((body.drop n).drop 8).take 8)⟩ := by
  rw [prParse_eq body hv] at h
  cases hd : decode body with
  | error e => rw [hd] at h; cases h
  | ok p =>
    rw [hd] at h
    obtain ⟨sid, n⟩ := p
    simp only at h
    by_cases hl : (body.drop n).length < 16
    · obtain ⟨k, _, _, hk⟩ := prTail_short sid _ hl
      rw [hk] at h; cases h
    rw [prTail_long sid _ (by omega)] at h
    by_cases hb : (body.drop n).length > 16
    · simp only [hb, ↓reduceIte] at h; cases h
    simp only [hb, ↓reduceIte, Except.ok.injEq] at h
    have hsid : r.sid = sid := by rw [← h]
    refine ⟨n, by simpa [hsid] using hd, by omega, ?_⟩
    rw [hsid]; exact h.symm

/-- Canonical: an accepted PROOF_REQ body is exactly its encoding, with nothing after it. The parse is injective and
the id is the one canonical varint of its value. -/
theorem pr_canonical (body : List Nat) (hv : ValidBytes body) (r : PR) (h : prParse body = .ok r) :
    body = prBytes r ∧ r.sid < 2 ^ 63 ∧ r.from_ < 2 ^ 64 ∧ r.upto < 2 ^ 64 := by
  obtain ⟨n, hd, hl, hr⟩ := pr_shape body hv r h
  obtain ⟨hcan, hn⟩ := decode_canonical body hv r.sid n hd
  obtain ⟨hlim, _⟩ := decode_bounds body hv r.sid n hd
  have hbody : body = body.take n ++ body.drop n := (List.take_append_drop n body).symm
  have hvr0 : ValidBytes (body.drop n) := fun b hb => hv b (List.mem_of_mem_drop hb)
  generalize body.drop n = x at *
  have vb : ∀ a b, a + b ≤ 16 → ValidBytes ((x.drop a).take b) :=
    fun a b _ z hz => hvr0 z (List.mem_of_mem_drop (List.mem_of_mem_take hz))
  have lb : ∀ a b, a + b ≤ 16 → ((x.drop a).take b).length = b := by
    intro a b hab; simp; omega
  have hx : x = x.take 8 ++ (x.drop 8).take 8 := by
    have : x.drop 8 = (x.drop 8).take 8 := by
      rw [List.take_of_length_le]; simp; omega
    calc x = x.take 8 ++ x.drop 8 := (List.take_append_drop 8 x).symm
      _ = x.take 8 ++ (x.drop 8).take 8 := by rw [← this]
  have v8 : ValidBytes (x.take 8) := fun b hb => hvr0 b (List.mem_of_mem_take hb)
  have v8' : ValidBytes ((x.drop 8).take 8) := vb 8 8 (by omega)
  have l8 : (x.take 8).length = 8 := by simp; omega
  have l8' := lb 8 8 (by omega)
  refine ⟨?_, hlim, ?_, ?_⟩
  · rw [hbody, hcan]
    unfold prBytes
    rw [hr]
    simp only
    rw [beBytes_beVal_of_length 8 _ v8 l8, beBytes_beVal_of_length 8 _ v8' l8', List.append_assoc, ← hx]
  · rw [hr]; have := beVal_lt _ v8; rw [l8] at this; exact this
  · rw [hr]; have := beVal_lt _ v8'; rw [l8'] at this; exact this

theorem pr_injective (a b : List Nat) (ha : ValidBytes a) (hb : ValidBytes b) (r : PR)
    (h1 : prParse a = .ok r) (h2 : prParse b = .ok r) : a = b := by
  rw [(pr_canonical a ha r h1).1, (pr_canonical b hb r h2).1]

/-- Round trip: parsing an encoded body returns the fields. -/
theorem pr_roundtrip (r : PR) (h1 : r.sid < 2 ^ 63) (h2 : r.from_ < 2 ^ 64) (h3 : r.upto < 2 ^ 64) :
    prParse (prBytes r) = .ok r := by
  have hl : r.sid < limit := h1
  have hb : prBytes r = encodeBytes r.sid ++ (beBytes 8 r.from_ ++ beBytes 8 r.upto) := by
    simp [prBytes]
  unfold prParse
  rw [hb, readVarint_enc r.sid hl]
  simp only
  rw [prTail_long _ _ (by simp [length_beBytes])]
  have hlen : (beBytes 8 r.from_ ++ beBytes 8 r.upto).length = 16 := by simp [length_beBytes]
  have c : ¬ (beBytes 8 r.from_ ++ beBytes 8 r.upto).length > 16 := by omega
  have t1 : (beBytes 8 r.from_ ++ beBytes 8 r.upto).take 8 = beBytes 8 r.from_ := List.take_left' (length_beBytes _ _)
  have t2 : ((beBytes 8 r.from_ ++ beBytes 8 r.upto).drop 8).take 8 = beBytes 8 r.upto := by
    rw [List.drop_left' (length_beBytes _ _)]; exact List.take_left' (length_beBytes _ _)
  simp only [c, ↓reduceIte, t1, t2, beVal_beBytes]
  have e8 : (256 : Nat) ^ 8 = 2 ^ 64 := rfl
  rw [e8, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]

/-- A byte after the two fields is refused: a PROOF_REQ is exactly its fields. -/
theorem pr_reject_trailing (r : PR) (h1 : r.sid < 2 ^ 63) (x : Nat) (xs : List Nat) :
    prParse (prBytes r ++ x :: xs) = .error (.unexpected "trailing bytes") := by
  have hl : r.sid < limit := h1
  have hb : prBytes r ++ x :: xs = encodeBytes r.sid ++ (beBytes 8 r.from_ ++ (beBytes 8 r.upto ++ x :: xs)) := by
    simp [prBytes]
  unfold prParse
  rw [hb, readVarint_enc r.sid hl]
  simp only
  have hlen : (beBytes 8 r.from_ ++ (beBytes 8 r.upto ++ x :: xs)).length > 16 := by
    simp [length_beBytes]; omega
  rw [prTail_long _ _ (by omega)]
  simp only [hlen, ↓reduceIte]

/-- A refused id is a refused frame, with the error the varint reports. -/
theorem pr_reject_varint (body : List Nat) (e : Varint.Error) (h : decode body = .error e) :
    prParse body = .error (varErr e) := by
  unfold prParse
  rw [readVarint_err h]

/-- Truncation at every length: every strict prefix of an accepted body is refused as truncated. -/
theorem pr_prefix_truncated (body : List Nat) (hv : ValidBytes body) (r : PR) (h : prParse body = .ok r) (m : Nat)
    (hm : m < (prBytes r).length) :
    ∃ k, 1 ≤ k ∧ k ≤ (prBytes r).length - m ∧ prParse (body.take m) = .error (.truncated k) := by
  obtain ⟨hbody, hlim, _⟩ := pr_canonical body hv r h
  have hl : r.sid < limit := hlim
  have hvm : ValidBytes (body.take m) := fun b hb => hv b (List.mem_of_mem_take hb)
  have hL : (encodeBytes r.sid).length = encodedLen r.sid := Varint.length_encodeBytes _
  have hlen : (prBytes r).length = encodedLen r.sid + 16 := by
    simp only [prBytes, List.length_append, length_beBytes, Varint.length_encodeBytes]
  obtain ⟨X, hX, hXl⟩ : ∃ X : List Nat, body = encodeBytes r.sid ++ X ∧ X.length = 16 := by
    refine ⟨beBytes 8 r.from_ ++ beBytes 8 r.upto, ?_, by simp [length_beBytes]⟩
    rw [hbody]; simp [prBytes]
  by_cases hc : m < (encodeBytes r.sid).length
  · refine ⟨1, Nat.le_refl _, by omega, ?_⟩
    rw [prParse_eq _ hvm]
    have : decode (body.take m) = .error .truncated := by
      rw [hX]; exact decode_cut_truncated r.sid hl X m hc
    rw [this]
    rfl
  · have htk : body.take m = encodeBytes r.sid ++ X.take (m - (encodeBytes r.sid).length) := by
      rw [hX, List.take_append, List.take_of_length_le (by omega)]
    have hd : decode (body.take m) = .ok (r.sid, (encodeBytes r.sid).length) := by
      rw [htk]; exact decode_encode r.sid _ hl
    rw [prParse_eq _ hvm, hd]
    simp only
    have hYl : (X.take (m - (encodeBytes r.sid).length)).length < 16 := by
      rw [List.length_take]; omega
    obtain ⟨k, hk1, hk2, hk⟩ := prTail_short r.sid (X.take (m - (encodeBytes r.sid).length)) hYl
    refine ⟨k, hk1, ?_, ?_⟩
    · rw [List.length_take] at hk2; omega
    · rw [htk, List.drop_left' rfl]; exact hk

/-- `ProofReq::encode`: an id of 2^63 or more is refused first, a short buffer with the exact shortfall, and in both
cases nothing is written; otherwise exactly the body is written and the rest of the buffer is left alone. -/
theorem prEncode_overflow (r : PR) (out : List Nat) (h : 2 ^ 63 ≤ r.sid) : prEncode r out = (.error .overflow, out) := by
  have : limit ≤ r.sid := h
  simp [prEncode, encodeInto_overflow 25 r.sid this, varErr]

theorem prEncode_short (r : PR) (out : List Nat) (h : r.sid < 2 ^ 63) (hs : out.length < encodedLen r.sid + 16) :
    prEncode r out = (.error (.bufferTooSmall (encodedLen r.sid + 16 - out.length)), out) := by
  have hl : r.sid < limit := h
  have hlen : (encodeBytes r.sid ++ beBytes 8 r.from_ ++ beBytes 8 r.upto).length = encodedLen r.sid + 16 := by
    simp only [List.length_append, length_beBytes, Varint.length_encodeBytes]
  unfold prEncode
  rw [encodeInto_ok_of_lt 25 r.sid (by omega) hl]
  simp only
  rw [put_err (by omega), hlen]

theorem prEncode_ok (r : PR) (out : List Nat) (h : r.sid < 2 ^ 63) (hs : encodedLen r.sid + 16 ≤ out.length) :
    prEncode r out = (.ok (encodedLen r.sid + 16), prBytes r ++ out.drop (encodedLen r.sid + 16)) := by
  have hl : r.sid < limit := h
  have hlen : (encodeBytes r.sid ++ beBytes 8 r.from_ ++ beBytes 8 r.upto).length = encodedLen r.sid + 16 := by
    simp only [List.length_append, length_beBytes, Varint.length_encodeBytes]
  unfold prEncode
  rw [encodeInto_ok_of_lt 25 r.sid (by omega) hl]
  simp only
  rw [put_ok (by omega), hlen]
  rfl

end Vinc.ValuesWire

#audit_axioms Vinc.ValuesWire.pfTail_eq
#audit_axioms Vinc.ValuesWire.prTail_eq
#audit_axioms Vinc.ValuesWire.pf_canonical
#audit_axioms Vinc.ValuesWire.pf_injective
#audit_axioms Vinc.ValuesWire.pf_roundtrip
#audit_axioms Vinc.ValuesWire.pfWriteHead_overflow
#audit_axioms Vinc.ValuesWire.pfWriteHead_short
#audit_axioms Vinc.ValuesWire.pfWriteHead_ok
#audit_axioms Vinc.ValuesWire.pf_reject_varint
#audit_axioms Vinc.ValuesWire.pf_reject_proof
#audit_axioms Vinc.ValuesWire.pf_prefix_truncated
#audit_axioms Vinc.ValuesWire.pr_canonical
#audit_axioms Vinc.ValuesWire.pr_injective
#audit_axioms Vinc.ValuesWire.pr_roundtrip
#audit_axioms Vinc.ValuesWire.pr_reject_trailing
#audit_axioms Vinc.ValuesWire.pr_reject_varint
#audit_axioms Vinc.ValuesWire.pr_prefix_truncated
#audit_axioms Vinc.ValuesWire.prEncode_overflow
#audit_axioms Vinc.ValuesWire.prEncode_short
#audit_axioms Vinc.ValuesWire.prEncode_ok
