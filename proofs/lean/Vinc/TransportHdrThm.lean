import Vinc.TransportHdr

namespace Vinc.TransportHdr
open Vinc

/-! ## Bytes -/

theorem byte_form : ∀ b, b < 256 → (b &&& 0xC0 = 0xC0 ↔ 192 ≤ b) := by decide +kernel
theorem byte_hs : ∀ b, b < 256 → b &&& 0xC0 = 0xC0 → (b >>> 4) &&& 3 = 0 → 0xC0 ||| (0 <<< 4) ||| (b &&& 0x0f) = b := by
  decide +kernel
theorem byte_zr : ∀ b, b < 256 → b &&& 0xC0 = 0xC0 → (b >>> 4) &&& 3 = 1 → 0xC0 ||| (1 <<< 4) ||| (b &&& 0x0f) = b := by
  decide +kernel
theorem byte_rt : ∀ b, b < 256 → b &&& 0xC0 = 0xC0 → (b >>> 4) &&& 3 = 2 → 0xC0 ||| (2 <<< 4) ||| (b &&& 0x0f) = b := by
  decide +kernel
theorem low_zr : ∀ low, low < 16 →
    (0xC0 ||| (1 <<< 4) ||| low) &&& 0xC0 = 0xC0 ∧ ((0xC0 ||| (1 <<< 4) ||| low) >>> 4) &&& 3 = 1 ∧
      (0xC0 ||| (1 <<< 4) ||| low) < 256 := by decide +kernel
theorem byte_short : ∀ b, b < 256 → b &&& 0xE0 = 0x40 → b &&& 0x0C = 0 →
    0x40 ||| (if b &&& 0x10 ≠ 0 then 0x10 else 0) ||| ((b &&& 0x03) + 1 - 1) = b := by decide +kernel

theorem fromBits_some (x : Nat) (ty : LongType) (h : LongType.fromBits x = some ty) : x = ty.bits := by
  unfold LongType.fromBits at h
  split at h <;> simp at h <;> subst h <;> rfl

/-! ## The writer -/

theorem andThen_putSlice (cap : Nat) (bs out : List Nat) (h : out.length + bs.length ≤ cap) :
    (WRes.mk none out).andThen (putSlice cap bs) = ⟨none, out ++ bs⟩ := by
  have : bs.length ≤ cap - out.length := by omega
  simp [WRes.andThen, putSlice, this]

theorem andThen_putLen (cap len : Nat) (out : List Nat) (hl : len ≤ 255) (h : out.length + 1 ≤ cap) :
    (WRes.mk none out).andThen (putLen cap len) = ⟨none, out ++ [len]⟩ := by
  have : 1 ≤ cap - out.length := by omega
  simp [WRes.andThen, putLen, putSlice, hl, this]

theorem andThen_putVarint (cap v : Nat) (out : List Nat) (hv : v < Varint.limit)
    (h : out.length + Varint.encodedLen v ≤ cap) :
    (WRes.mk none out).andThen (putVarint cap v) = ⟨none, out ++ Varint.encodeBytes v⟩ := by
  have h1 : ¬ v ≥ Varint.limit := by omega
  have h2 : ¬ Varint.encodedLen v > cap - out.length := by omega
  simp [WRes.andThen, putVarint, Varint.encodeInto, h1, h2]

theorem length_encodeLong (h : LongHeader) (low : Nat) : (encodeLong h low).length = headerLen h := by
  simp [encodeLong, headerLen, Varint.length_encodeBytes]; omega

theorem longPuts_ok (h : LongHeader) (low cap : Nat) (hd : h.dcid.length ≤ 255) (hs : h.scid.length ≤ 255)
    (hv : h.bodyLen < Varint.limit) (hc : headerLen h ≤ cap) : longPuts h low cap = ⟨none, encodeLong h low⟩ := by
  unfold headerLen at hc
  unfold longPuts
  rw [andThen_putSlice _ _ _ (by simp; omega), andThen_putSlice _ _ _ (by simp; omega),
    andThen_putLen _ _ _ hd (by simp; omega), andThen_putSlice _ _ _ (by simp; omega),
    andThen_putLen _ _ _ hs (by simp; omega), andThen_putSlice _ _ _ (by simp; omega),
    andThen_putVarint _ _ _ hv (by simp; omega)]
  simp [encodeLong]

/-! ## Writing a long header -/

/-- A write that succeeds wrote the encoding, `header_len` bytes. -/
theorem writeLong_ok (h : LongHeader) (pnLen cap low : Nat) (hw : h.WF) (hl : lowBits h.ty pnLen = some low)
    (hv : h.bodyLen < Varint.limit) (hc : headerLen h ≤ cap) :
    writeLong h pnLen cap = ⟨none, encodeLong h low⟩ := by
  have h1 : ¬ h.bodyLen ≥ Varint.limit := by omega
  have h2 : ¬ cap < headerLen h := by omega
  unfold LongHeader.WF maxCid at hw
  simp only [writeLong, hl, h1, h2, ite_false]
  exact longPuts_ok h low cap (by omega) (by omega) hv hc

/-- The errors of a write, in the order of the checks: the packet-number length that does not fit the type, the
body length no varint holds, the room. -/
theorem writeLong_err_pn (h : LongHeader) (pnLen cap : Nat) (hl : lowBits h.ty pnLen = none) :
    writeLong h pnLen cap = ⟨some .pnLength, []⟩ := by
  simp [writeLong, hl]

theorem writeLong_err_overflow (h : LongHeader) (pnLen cap low : Nat) (hl : lowBits h.ty pnLen = some low)
    (hv : Varint.limit ≤ h.bodyLen) : writeLong h pnLen cap = ⟨some .varintOverflow, []⟩ := by
  simp [writeLong, hl, hv]

theorem writeLong_err_room (h : LongHeader) (pnLen cap low : Nat) (hl : lowBits h.ty pnLen = some low)
    (hv : h.bodyLen < Varint.limit) (hc : cap < headerLen h) :
    writeLong h pnLen cap = ⟨some (.bufferTooSmall (headerLen h - cap)), []⟩ := by
  have h1 : ¬ h.bodyLen ≥ Varint.limit := by omega
  simp [writeLong, hl, h1, hc]

/-- A refused write writes nothing, whatever the error. -/
theorem writeLong_refused_nothing (h : LongHeader) (pnLen cap : Nat) (hw : h.WF)
    (he : (writeLong h pnLen cap).err ≠ none) : (writeLong h pnLen cap).out = [] := by
  cases hl : lowBits h.ty pnLen with
  | none => rw [writeLong_err_pn h pnLen cap hl]
  | some low =>
    by_cases hv : h.bodyLen < Varint.limit
    · by_cases hc : cap < headerLen h
      · rw [writeLong_err_room h pnLen cap low hl hv hc]
      · rw [writeLong_ok h pnLen cap low hw hl hv (by omega)] at he
        exact absurd rfl he
    · rw [writeLong_err_overflow h pnLen cap low hl (by omega)]

/-- The rule before the fix: with the room check ahead of the length check, a body length of `2^63` is refused
after seven bytes were written (the counterexample `Hdr_late.cfg` finds). -/
theorem late_writes :
    writeLongLate ⟨.handshake, [7, 7], [9], 2 ^ 63⟩ 0 64 = ⟨some .varintOverflow, [0xC0, 1, 2, 7, 7, 1, 9]⟩ := by
  decide +kernel

/-- The same call of the code writes nothing. -/
theorem late_fixed : writeLong ⟨.handshake, [7, 7], [9], 2 ^ 63⟩ 0 64 = ⟨some .varintOverflow, []⟩ := by
  decide +kernel

/-! ## Reading a long header back -/

theorem readCid_append (cid rest : List Nat) (h : cid.length ≤ maxCid) :
    readCid (cid.length :: (cid ++ rest)) = .ok (cid, rest) := by
  have h1 : ¬ cid.length > maxCid := by omega
  simp [readCid, h1]

theorem readCid_ok (r cid rest : List Nat) (h : readCid r = .ok (cid, rest)) :
    r = cid.length :: (cid ++ rest) ∧ cid.length ≤ maxCid := by
  unfold readCid at h
  split at h
  · simp at h
  · rename_i len r'
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        subst h1 h2
        have : min len r'.length = len := by omega
        simp [this]
        omega

/-- The low bits a first byte may carry: none on a handshake or a retry, any four on a 0-RTT packet (they are under header
protection when the header is parsed). -/
def LowOk (ty : LongType) (low : Nat) : Prop :=
  match ty with
  | .handshake => low = 0
  | .zeroRtt => low < 16
  | .retry => low = 0

/-- Round trip: parsing an encoded header, followed by a body that fits and anything after it, gives the fields
and the header length. -/
theorem parse_write (h : LongHeader) (low : Nat) (rest : List Nat) (hw : h.WF) (hlow : LowOk h.ty low)
    (hv : h.bodyLen < Varint.limit) (hr : h.bodyLen ≤ rest.length) :
    parseLong (encodeLong h low ++ rest) = .ok (h, headerLen h) := by
  obtain ⟨ty, dcid, scid, bl⟩ := h
  obtain ⟨hd, hs⟩ := hw
  simp only at hd hs hv hr hlow
  have hfirst : firstLong ty low &&& 0xC0 = 0xC0 ∧ LongType.fromBits ((firstLong ty low >>> 4) &&& 3) = some ty ∧
      ¬ (ty ≠ .zeroRtt ∧ firstLong ty low &&& 0x0f ≠ 0) := by
    cases ty
    · simp only [LowOk] at hlow; subst hlow; decide
    · simp only [LowOk] at hlow
      obtain ⟨a, b, _⟩ := low_zr low hlow
      simp only [firstLong, LongType.bits]
      rw [a, b]
      simp [LongType.fromBits]
    · simp only [LowOk] at hlow; subst hlow; decide
  obtain ⟨f1, f2, f3⟩ := hfirst
  have hdec := Varint.decode_encode bl rest hv
  have hlen := Varint.length_encodeBytes bl
  simp only [encodeLong, List.cons_append, List.nil_append, List.append_assoc, parseLong, f1, f2, f3, version,
    ne_eq, not_true_eq_false, ite_false, readCid_append _ _ hd, readCid_append _ _ hs, hdec]
  have : ¬ bl > (Varint.encodeBytes bl ++ rest).length - Varint.encodedLen bl := by
    simp [hlen]; omega
  simp only [hlen, this, ite_false, headerLen]
  congr 2
  omega

theorem firstLong_eq (first : Nat) (ty : LongType) (hb : first < 256) (hf : first &&& 0xC0 = 0xC0)
    (hty : LongType.fromBits ((first >>> 4) &&& 3) = some ty) : firstLong ty (first &&& 0x0f) = first := by
  have hbits := fromBits_some _ _ hty
  cases ty
  · exact byte_hs first hb hf hbits
  · exact byte_zr first hb hf hbits
  · exact byte_rt first hb hf hbits

/-- Canonical: an accepted header is the encoding of the fields it yields, with the low four bits of its first
byte as they are (zero on a handshake); the ids are at most 20 bytes, the body length is one a varint holds, the
size is `header_len` and the body fits in the input. -/
theorem parse_canonical (p : List Nat) (hp : Varint.ValidBytes p) (h : LongHeader) (n : Nat)
    (hok : parseLong p = .ok (h, n)) :
    h.WF ∧ h.bodyLen < Varint.limit ∧ n = headerLen h ∧ n + h.bodyLen ≤ p.length ∧
      LowOk h.ty (p.headD 0 &&& 0x0f) ∧ p.take n = encodeLong h (p.headD 0 &&& 0x0f) := by
  unfold parseLong at hok
  split at hok
  · simp at hok
  rename_i first r1
  split at hok
  · simp at hok
  rename_i hform
  split at hok
  · simp at hok
  rename_i ty hty
  split at hok
  · simp at hok
  rename_i hres
  split at hok
  · simp at hok
  rename_i v r2
  split at hok
  · simp at hok
  rename_i hver
  split at hok
  · simp at hok
  rename_i dcid r3 hdc
  split at hok
  · simp at hok
  rename_i scid r4 hsc
  split at hok
  · simp at hok
  rename_i bl n' hdecode
  split at hok
  · simp at hok
  rename_i hfit
  simp only [Except.ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨rfl, rfl⟩ := hok
  obtain ⟨rfl, hdl⟩ := readCid_ok _ _ _ hdc
  obtain ⟨rfl, hsl⟩ := readCid_ok _ _ _ hsc
  have hb : first < 256 := hp first (by simp)
  have hv4 : Varint.ValidBytes r4 := fun b hb => hp b (by simp [hb])
  obtain ⟨htake, hn'⟩ := Varint.decode_canonical r4 hv4 bl n' hdecode
  obtain ⟨hlim, _⟩ := Varint.decode_bounds r4 hv4 bl n' hdecode
  have hlen := congrArg List.length htake
  rw [Varint.length_encodeBytes, ← hn', List.length_take] at hlen
  have hf : first &&& 0xC0 = 0xC0 := by simpa using hform
  have hv : v = version := by simpa using hver
  subst hv
  have hfl := firstLong_eq first ty hb hf hty
  refine ⟨⟨hdl, hsl⟩, hlim, ?_, ?_, ?_, ?_⟩
  · simp only [headerLen, ← hn']; omega
  · simp; omega
  · cases ty
    · simp only [LowOk, List.headD_cons]
      simp only [ne_eq, not_and, Decidable.not_not] at hres
      exact hres (by simp)
    · simp only [LowOk, List.headD_cons]
      have := Nat.and_le_right (n := first) (m := 0x0f)
      omega
    · simp only [LowOk, List.headD_cons]
      simp only [ne_eq, not_and, Decidable.not_not] at hres
      exact hres (by simp)
  · simp only [List.headD_cons, encodeLong, hfl, ← htake]
    have e : 1 + 1 + (1 + dcid.length) + (1 + scid.length) + n' = ([first, version, dcid.length] ++ dcid ++ [scid.length] ++ scid).length + n' := by
      simp; omega
    have e2 : first :: version :: dcid.length :: (dcid ++ scid.length :: (scid ++ r4)) = ([first, version, dcid.length] ++ dcid ++ [scid.length] ++ scid) ++ r4 := by
      simp
    rw [e, e2, List.take_length_add_append]

/-- An accepted header begins with the encoding and is followed by at least the body: what comes after does not
matter. -/
theorem parse_append (p s : List Nat) (hp : Varint.ValidBytes p) (h : LongHeader) (n : Nat)
    (hok : parseLong p = .ok (h, n)) : parseLong (p ++ s) = .ok (h, n) := by
  obtain ⟨hw, hlim, hn, hfit, hlow, htake⟩ := parse_canonical p hp h n hok
  have hsplit : p = encodeLong h (p.headD 0 &&& 0x0f) ++ p.drop n := by
    rw [← htake, List.take_append_drop]
  rw [hsplit, List.append_assoc, hn]
  exact parse_write h _ _ hw hlow hlim (by simp; omega)

/-! ## The refusals of the parser, in the order of its checks -/

theorem parse_err_empty : parseLong [] = .error (.truncated 1) := rfl

theorem parse_err_form (first : Nat) (r : List Nat) (h : first &&& 0xC0 ≠ 0xC0) :
    parseLong (first :: r) = .error .form := by
  simp [parseLong, h]

theorem parse_err_type (first : Nat) (r : List Nat) (h : first &&& 0xC0 = 0xC0) (ht : (first >>> 4) &&& 3 = 3) :
    parseLong (first :: r) = .error .longType := by
  have : LongType.fromBits ((first >>> 4) &&& 3) = none := by
    unfold LongType.fromBits
    split <;> simp_all
  simp [parseLong, h, this]

theorem parse_err_reserved (first : Nat) (r : List Nat) (h : first &&& 0xC0 = 0xC0) (ht : (first >>> 4) &&& 3 = 0)
    (hl : first &&& 0x0f ≠ 0) : parseLong (first :: r) = .error .reserved := by
  simp [parseLong, h, ht, LongType.fromBits, hl]

/-- The checks of the first byte passed: it is a long header of type `ty` without a reserved bit. -/
def FirstOk (first : Nat) (ty : LongType) : Prop :=
  first &&& 0xC0 = 0xC0 ∧ LongType.fromBits ((first >>> 4) &&& 3) = some ty ∧
    ¬ (ty ≠ .zeroRtt ∧ first &&& 0x0f ≠ 0)

theorem parse_err_version (first v : Nat) (ty : LongType) (r : List Nat) (hf : FirstOk first ty)
    (hv : v ≠ version) : parseLong (first :: v :: r) = .error (.version v) := by
  obtain ⟨f1, f2, f3⟩ := hf
  simp [parseLong, f1, f2, f3, hv]

theorem parse_err_dcid (first len : Nat) (ty : LongType) (r : List Nat) (hf : FirstOk first ty)
    (hl : maxCid < len) : parseLong (first :: version :: len :: r) = .error .connIdLength := by
  obtain ⟨f1, f2, f3⟩ := hf
  simp [parseLong, f1, f2, f3, readCid, hl]

theorem parse_err_scid (first len : Nat) (ty : LongType) (dcid r : List Nat) (hf : FirstOk first ty)
    (hd : dcid.length ≤ maxCid) (hl : maxCid < len) :
    parseLong (first :: version :: dcid.length :: (dcid ++ len :: r)) = .error .connIdLength := by
  obtain ⟨f1, f2, f3⟩ := hf
  simp only [parseLong, f1, f2, f3, ne_eq, not_true_eq_false, ite_false, readCid_append _ _ hd]
  simp [readCid, hl]

/-- A body length past the end of the input is `Length`. -/
theorem parse_err_length (h : LongHeader) (low : Nat) (rest : List Nat) (hw : h.WF) (hlow : LowOk h.ty low)
    (hv : h.bodyLen < Varint.limit) (hr : rest.length < h.bodyLen) :
    parseLong (encodeLong h low ++ rest) = .error .length := by
  obtain ⟨ty, dcid, scid, bl⟩ := h
  obtain ⟨hd, hs⟩ := hw
  simp only at hd hs hv hr hlow
  have hfirst : firstLong ty low &&& 0xC0 = 0xC0 ∧ LongType.fromBits ((firstLong ty low >>> 4) &&& 3) = some ty ∧
      ¬ (ty ≠ .zeroRtt ∧ firstLong ty low &&& 0x0f ≠ 0) := by
    cases ty
    · simp only [LowOk] at hlow; subst hlow; decide
    · simp only [LowOk] at hlow
      obtain ⟨a, b, _⟩ := low_zr low hlow
      simp only [firstLong, LongType.bits]
      rw [a, b]
      simp [LongType.fromBits]
    · simp only [LowOk] at hlow; subst hlow; decide
  obtain ⟨f1, f2, f3⟩ := hfirst
  have hdec := Varint.decode_encode bl rest hv
  have hlen := Varint.length_encodeBytes bl
  simp only [encodeLong, List.cons_append, List.nil_append, List.append_assoc, parseLong, f1, f2, f3, version,
    ne_eq, not_true_eq_false, ite_false, readCid_append _ _ hd, readCid_append _ _ hs, hdec]
  have : bl > (Varint.encodeBytes bl ++ rest).length - Varint.encodedLen bl := by
    simp [hlen]; omega
  simp only [hlen, this, ite_true]

theorem valid_encodeLong (h : LongHeader) (low : Nat) (hw : h.WF) (hlow : LowOk h.ty low)
    (hd : Varint.ValidBytes h.dcid) (hs : Varint.ValidBytes h.scid) : Varint.ValidBytes (encodeLong h low) := by
  have hf : firstLong h.ty low < 256 := by
    cases hty : h.ty
    · rw [hty] at hlow; simp only [LowOk] at hlow; subst hlow; decide
    · rw [hty] at hlow; simp only [LowOk] at hlow; exact (low_zr low hlow).2.2
    · rw [hty] at hlow; simp only [LowOk] at hlow; subst hlow; decide
  obtain ⟨h1, h2⟩ := hw
  unfold maxCid at h1 h2
  intro b hb
  simp only [encodeLong, List.cons_append, List.nil_append, List.append_assoc, List.mem_cons, List.mem_append] at hb
  rcases hb with rfl | rfl | rfl | hb | rfl | hb | hb
  · exact hf
  · decide
  · omega
  · exact hd b hb
  · omega
  · exact hs b hb
  · rw [Varint.encodeBytes_eq] at hb; exact Varint.encRec_valid _ b hb

/-- A header cut anywhere is refused. -/
theorem parse_cut (h : LongHeader) (low m : Nat) (hw : h.WF) (hlow : LowOk h.ty low)
    (hd : Varint.ValidBytes h.dcid) (hs : Varint.ValidBytes h.scid) (hv : h.bodyLen < Varint.limit)
    (hm : m < headerLen h) : ∃ e, parseLong ((encodeLong h low).take m) = .error e := by
  cases hp : parseLong ((encodeLong h low).take m) with
  | error e => exact ⟨e, rfl⟩
  | ok r =>
    obtain ⟨h', n⟩ := r
    have hval : Varint.ValidBytes ((encodeLong h low).take m) := fun b hb =>
      valid_encodeLong h low hw hlow hd hs b (List.mem_of_mem_take hb)
    have hfit := (parse_canonical _ hval h' n hp).2.2.2.1
    have happ := parse_append _ ((encodeLong h low).drop m ++ List.replicate h.bodyLen 0) hval h' n hp
    rw [← List.append_assoc, List.take_append_drop, parse_write h low _ hw hlow hv (by simp)] at happ
    simp only [Except.ok.injEq, Prod.mk.injEq] at happ
    have hlen : ((encodeLong h low).take m).length ≤ m := by simp; omega
    omega

/-! ## The short header -/

theorem writeShort_ok (h : ShortHeader) (pn : List Nat) (cap : Nat) (hp : 2 ≤ pn.length ∧ pn.length ≤ 3)
    (hc : shortHeaderLen h.dcid.length pn.length ≤ cap) : writeShort h pn cap = ⟨none, encodeShort h pn⟩ := by
  have h2 : ¬ cap < shortHeaderLen h.dcid.length pn.length := by omega
  unfold shortHeaderLen at hc
  simp only [writeShort, hp, h2, and_self, not_true_eq_false, ite_false]
  rw [andThen_putSlice _ _ _ (by simp; omega), andThen_putSlice _ _ _ (by simp; omega),
    andThen_putSlice _ _ _ (by simp; omega)]
  simp [encodeShort]

theorem length_encodeShort (h : ShortHeader) (pn : List Nat) :
    (encodeShort h pn).length = shortHeaderLen h.dcid.length pn.length := by
  simp [encodeShort, shortHeaderLen]; omega

theorem writeShort_err_pn (h : ShortHeader) (pn : List Nat) (cap : Nat) (hp : ¬ (2 ≤ pn.length ∧ pn.length ≤ 3)) :
    writeShort h pn cap = ⟨some .pnLength, []⟩ := by
  simp [writeShort, hp]

theorem writeShort_err_room (h : ShortHeader) (pn : List Nat) (cap : Nat) (hp : 2 ≤ pn.length ∧ pn.length ≤ 3)
    (hc : cap < shortHeaderLen h.dcid.length pn.length) :
    writeShort h pn cap = ⟨some (.bufferTooSmall (shortHeaderLen h.dcid.length pn.length - cap)), []⟩ := by
  simp [writeShort, hp, hc]

/-- A refused write of a short header writes nothing. -/
theorem writeShort_refused_nothing (h : ShortHeader) (pn : List Nat) (cap : Nat)
    (he : (writeShort h pn cap).err ≠ none) : (writeShort h pn cap).out = [] := by
  by_cases hp : 2 ≤ pn.length ∧ pn.length ≤ 3
  · by_cases hc : cap < shortHeaderLen h.dcid.length pn.length
    · rw [writeShort_err_room h pn cap hp hc]
    · rw [writeShort_ok h pn cap hp (by omega)] at he
      exact absurd rfl he
  · rw [writeShort_err_pn h pn cap hp]

theorem first_short : ∀ kp : Bool, ∀ w, 2 ≤ w → w ≤ 3 →
    firstShort kp w &&& 0xE0 = 0x40 ∧ readFirst (firstShort kp w) = .ok (w, kp) := by
  intro kp w h2 h3
  have : w = 2 ∨ w = 3 := by omega
  rcases this with rfl | rfl <;> cases kp <;> exact ⟨by decide, rfl⟩

/-- Round trip: `short_dcid` gives the id back whatever follows the header, and the first byte gives the
packet-number length and the key phase back with no reserved bit. -/
theorem short_roundtrip (h : ShortHeader) (pn rest : List Nat) (hd : h.dcid.length ≤ maxCid)
    (hp : 2 ≤ pn.length ∧ pn.length ≤ 3) :
    shortDcid (encodeShort h pn ++ rest) h.dcid.length = .ok h.dcid ∧
      readFirst (firstShort h.keyPhase pn.length) = .ok (pn.length, h.keyPhase) := by
  obtain ⟨f1, f2⟩ := first_short h.keyPhase pn.length hp.1 hp.2
  refine ⟨?_, f2⟩
  have h1 : ¬ h.dcid.length > maxCid := by omega
  simp [shortDcid, encodeShort, h1, f1]

/-- Canonical: a short header that is accepted (the form bits, no reserved bit, a packet-number length of 2 or 3
that fits) is the encoding of the key phase, the id and the packet-number bytes it yields. -/
theorem short_canonical (p : List Nat) (hp : Varint.ValidBytes p) (dl w : Nat) (d : List Nat) (kp : Bool)
    (hd : shortDcid p dl = .ok d) (hf : readFirst (p.headD 0) = .ok (w, kp)) (hw : 2 ≤ w ∧ w ≤ 3)
    (hl : 1 + dl + w ≤ p.length) :
    d.length = dl ∧ dl ≤ maxCid ∧ p.take (1 + dl + w) = encodeShort ⟨kp, d⟩ ((p.drop (1 + dl)).take w) := by
  unfold shortDcid at hd
  split at hd
  · simp at hd
  rename_i hdl
  split at hd
  · simp at hd
  rename_i first rest
  split at hd
  · simp at hd
  rename_i hform
  split at hd
  · simp at hd
  rename_i hfit
  simp only [Except.ok.injEq] at hd
  subst hd
  have hb : first < 256 := hp first (by simp)
  simp only [List.headD_cons, readFirst] at hf
  by_cases hres : first &&& 0x0C = 0
  · simp only [hres, ne_eq, not_true_eq_false, ite_false, Except.ok.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    have hform' : first &&& 0xE0 = 0x40 := by simpa using hform
    have hfb := byte_short first hb hform' hres
    simp only [List.length_cons] at hl
    have hlen : (rest.take dl).length = dl := by simp; omega
    refine ⟨hlen, by omega, ?_⟩
    have e1 : 1 + dl + ((first &&& 0x03) + 1) = (dl + ((first &&& 0x03) + 1)) + 1 := by omega
    have e2 : 1 + dl = dl + 1 := by omega
    have hlen2 : ((rest.drop dl).take ((first &&& 0x03) + 1)).length = (first &&& 0x03) + 1 := by simp; omega
    rw [e1, e2, List.take_succ_cons, List.drop_succ_cons, List.take_add]
    simp only [encodeShort, firstShort, hlen2, List.cons_append, List.nil_append]
    congr 1
    by_cases h16 : first &&& 0x10 = 0 <;> simp [h16] at hfb ⊢ <;> exact hfb.symm
  · simp [hres] at hf

/-- The refusals of `short_dcid`, in the order of its checks, and the reserved bits of the first byte. -/
theorem short_err_len (p : List Nat) (dl : Nat) (h : maxCid < dl) : shortDcid p dl = .error .connIdLength := by
  simp [shortDcid, h]

theorem short_err_empty (dl : Nat) (h : dl ≤ maxCid) : shortDcid [] dl = .error .tooShort := by
  have : ¬ dl > maxCid := by omega
  simp [shortDcid, this]

theorem short_err_form (first : Nat) (rest : List Nat) (dl : Nat) (h : dl ≤ maxCid) (hf : first &&& 0xE0 ≠ 0x40) :
    shortDcid (first :: rest) dl = .error .form := by
  have : ¬ dl > maxCid := by omega
  simp [shortDcid, this, hf]

theorem short_err_cut (first : Nat) (rest : List Nat) (dl : Nat) (h : dl ≤ maxCid) (hf : first &&& 0xE0 = 0x40)
    (hl : rest.length < dl) : shortDcid (first :: rest) dl = .error .tooShort := by
  have : ¬ dl > maxCid := by omega
  simp [shortDcid, this, hf, hl]

theorem readFirst_reserved (first : Nat) (h : first &&& 0x0C ≠ 0) : readFirst first = .error .reserved := by
  simp [readFirst, h]

/-! ## The associated data -/

theorem sealParts_eq (packet : List Nat) (pnOff pnLen payloadLen : Nat) :
    sealParts packet pnOff pnLen payloadLen =
      if pnLen + payloadLen < sampleSkip then .error .tooShort
      else if packet.length < pnOff + pnLen + payloadLen + tagLen then
        .error (.bufferTooSmall (pnOff + pnLen + payloadLen + tagLen - packet.length))
      else .ok ⟨packet.take (pnOff + pnLen), pnOff + pnLen, pnOff + pnLen + payloadLen,
        pnOff + pnLen + payloadLen + tagLen⟩ := rfl

theorem openParts_eq (packet : List Nat) (pnOff pnLen : Nat) :
    openParts packet pnOff pnLen =
      if packet.length < pnOff + pnLen then .error .tooShort
      else if packet.length - (pnOff + pnLen) < tagLen then .error .tooShort
      else .ok ⟨packet.take (pnOff + pnLen), pnOff + pnLen,
        pnOff + pnLen + (packet.length - (pnOff + pnLen) - tagLen), packet.length⟩ := rfl

/-- `seal` takes the header as written, packet number included, as the associated data, whatever the buffer holds
after the tag. -/
theorem sealParts_ok (hdr payload tag extra : List Nat) (pnOff pnLen : Nat) (hh : hdr.length = pnOff + pnLen)
    (ht : tag.length = tagLen) (hs : sampleSkip ≤ pnLen + payload.length) :
    sealParts (hdr ++ payload ++ tag ++ extra) pnOff pnLen payload.length =
      .ok ⟨hdr, hdr.length, hdr.length + payload.length, hdr.length + payload.length + tagLen⟩ := by
  have h1 : ¬ pnLen + payload.length < sampleSkip := by omega
  have h2 : ¬ (hdr ++ payload ++ tag ++ extra).length < pnOff + pnLen + payload.length + tagLen := by
    simp; omega
  rw [sealParts_eq]
  simp only [h1, h2, ↓reduceIte]
  rw [← hh]
  simp

theorem sealParts_err_short (packet : List Nat) (pnOff pnLen payloadLen : Nat)
    (hs : pnLen + payloadLen < sampleSkip) : sealParts packet pnOff pnLen payloadLen = .error .tooShort := by
  simp [sealParts_eq, hs]

theorem sealParts_err_room (packet : List Nat) (pnOff pnLen payloadLen : Nat)
    (hs : sampleSkip ≤ pnLen + payloadLen) (hl : packet.length < pnOff + pnLen + payloadLen + tagLen) :
    sealParts packet pnOff pnLen payloadLen =
      .error (.bufferTooSmall (pnOff + pnLen + payloadLen + tagLen - packet.length)) := by
  have h1 : ¬ pnLen + payloadLen < sampleSkip := by omega
  simp [sealParts_eq, h1, hl]

/-- `open` takes the first `pn_off + pn_len` bytes of the packet as they are, and the tag is the last 16 bytes. -/
theorem openParts_ok (hdr payload tag : List Nat) (pnOff pnLen : Nat) (hh : hdr.length = pnOff + pnLen)
    (ht : tag.length = tagLen) :
    openParts (hdr ++ payload ++ tag) pnOff pnLen =
      .ok ⟨hdr, hdr.length, hdr.length + payload.length, hdr.length + payload.length + tagLen⟩ := by
  have h1 : ¬ (hdr ++ payload ++ tag).length < pnOff + pnLen := by simp; omega
  have h2 : ¬ (hdr ++ payload ++ tag).length - (pnOff + pnLen) < tagLen := by simp; omega
  rw [openParts_eq]
  simp only [h1, h2, ↓reduceIte]
  rw [← hh]
  simp [ht]
  omega

theorem openParts_err (packet : List Nat) (pnOff pnLen : Nat) (hl : packet.length < pnOff + pnLen + tagLen) :
    openParts packet pnOff pnLen = .error .tooShort := by
  rw [openParts_eq]
  by_cases h1 : packet.length < pnOff + pnLen
  · simp [h1]
  · have : packet.length - (pnOff + pnLen) < tagLen := by omega
    simp [h1, this]

/-- The associated data `open` takes is the bytes of the packet, not a re-encoding of the header. -/
theorem openParts_aad (packet : List Nat) (pnOff pnLen : Nat) (o : Parts) (h : openParts packet pnOff pnLen = .ok o) :
    o.aad = packet.take (pnOff + pnLen) ∧ o.payloadStart = pnOff + pnLen ∧ o.payloadEnd + tagLen = packet.length ∧
      o.total = packet.length := by
  rw [openParts_eq] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp only [Except.ok.injEq] at h
      subst h
      simp
      omega

/-- What `seal` authenticated is what `open` checks: a packet of the sealed length whose first
`pn_off + pn_len` bytes are the ones sealed (header protection removed, `Record.unprotect_protect`) is split the
same way, into the same associated data and the same payload range. -/
theorem open_seal_parts (packet packet' : List Nat) (pnOff pnLen payloadLen : Nat) (s : Parts)
    (hs : sealParts packet pnOff pnLen payloadLen = .ok s) (hl : packet'.length = s.total)
    (hh : packet'.take (pnOff + pnLen) = packet.take (pnOff + pnLen)) : openParts packet' pnOff pnLen = .ok s := by
  rw [sealParts_eq] at hs
  split at hs
  · simp at hs
  · split at hs
    · simp at hs
    · simp only [Except.ok.injEq] at hs
      subst hs
      simp only at hl
      have h1 : ¬ packet'.length < pnOff + pnLen := by omega
      have h2 : ¬ packet'.length - (pnOff + pnLen) < tagLen := by omega
      rw [openParts_eq]
      simp only [h1, h2, ↓reduceIte]
      rw [hh, hl]
      congr 2
      omega

theorem writeShort_none (h : ShortHeader) (pn : List Nat) (cap : Nat) (hdr : List Nat)
    (hw : writeShort h pn cap = ⟨none, hdr⟩) : hdr = encodeShort h pn ∧ 2 ≤ pn.length ∧ pn.length ≤ 3 := by
  by_cases hp : 2 ≤ pn.length ∧ pn.length ≤ 3
  · by_cases hc : cap < shortHeaderLen h.dcid.length pn.length
    · rw [writeShort_err_room h pn cap hp hc] at hw; simp at hw
    · rw [writeShort_ok h pn cap hp (by omega)] at hw
      simp only [WRes.mk.injEq, true_and] at hw
      exact ⟨hw.symm, hp⟩
  · rw [writeShort_err_pn h pn cap hp] at hw; simp at hw

theorem writeLong_none (h : LongHeader) (pnLen cap : Nat) (hdr : List Nat) (hwf : h.WF)
    (hw : writeLong h pnLen cap = ⟨none, hdr⟩) :
    ∃ low, lowBits h.ty pnLen = some low ∧ hdr = encodeLong h low ∧ h.bodyLen < Varint.limit := by
  cases hl : lowBits h.ty pnLen with
  | none => rw [writeLong_err_pn h pnLen cap hl] at hw; simp at hw
  | some low =>
    by_cases hv : h.bodyLen < Varint.limit
    · by_cases hc : cap < headerLen h
      · rw [writeLong_err_room h pnLen cap low hl hv hc] at hw; simp at hw
      · rw [writeLong_ok h pnLen cap low hwf hl hv (by omega)] at hw
        simp only [WRes.mk.injEq, true_and] at hw
        exact ⟨low, rfl, hw.symm, hv⟩
    · rw [writeLong_err_overflow h pnLen cap low hl (by omega)] at hw; simp at hw

/-- A short packet: the associated data given to the AEAD by `seal` and by `open` is the whole header as
`ShortHeader::write` wrote it, the first byte, the id and the packet number. -/
theorem aad_short (h : ShortHeader) (pn : List Nat) (cap : Nat) (hdr payload tag extra : List Nat)
    (hw : writeShort h pn cap = ⟨none, hdr⟩) (ht : tag.length = tagLen) (hs : sampleSkip ≤ pn.length + payload.length) :
    hdr = encodeShort h pn ∧
      sealParts (hdr ++ payload ++ tag ++ extra) (1 + h.dcid.length) pn.length payload.length =
        .ok ⟨hdr, hdr.length, hdr.length + payload.length, hdr.length + payload.length + tagLen⟩ ∧
      openParts (hdr ++ payload ++ tag) (1 + h.dcid.length) pn.length =
        .ok ⟨hdr, hdr.length, hdr.length + payload.length, hdr.length + payload.length + tagLen⟩ := by
  obtain ⟨rfl, _, _⟩ := writeShort_none h pn cap hdr hw
  have hh : (encodeShort h pn).length = 1 + h.dcid.length + pn.length := by
    rw [length_encodeShort, shortHeaderLen]
  exact ⟨rfl, sealParts_ok _ _ _ _ _ _ hh ht hs, openParts_ok _ _ _ _ _ hh ht⟩

/-- A 0-RTT packet: the associated data is the long header as `LongHeader::write` wrote it followed by the two
bytes of the packet number, with `pn_off` the header length. -/
theorem aad_zero_rtt (h : LongHeader) (cap : Nat) (hdr pn payload tag extra : List Nat) (hwf : h.WF)
    (hw : writeLong h 2 cap = ⟨none, hdr⟩) (hp : pn.length = 2) (ht : tag.length = tagLen)
    (hs : 2 ≤ payload.length) :
    hdr = encodeLong h 1 ∧ hdr.length = headerLen h ∧
      sealParts (hdr ++ pn ++ payload ++ tag ++ extra) hdr.length 2 payload.length =
        .ok ⟨hdr ++ pn, hdr.length + 2, hdr.length + 2 + payload.length, hdr.length + 2 + payload.length + tagLen⟩ ∧
      openParts (hdr ++ pn ++ payload ++ tag) hdr.length 2 =
        .ok ⟨hdr ++ pn, hdr.length + 2, hdr.length + 2 + payload.length, hdr.length + 2 + payload.length + tagLen⟩ := by
  obtain ⟨low, hl, rfl, _⟩ := writeLong_none h 2 cap hdr hwf hw
  have hlow : low = 1 := by
    unfold lowBits at hl
    cases hty : h.ty <;> simp [hty] at hl
    exact hl.symm
  subst hlow
  have hh : (encodeLong h 1 ++ pn).length = (encodeLong h 1).length + 2 := by simp [hp]
  have s := sealParts_ok (encodeLong h 1 ++ pn) payload tag extra _ 2 hh ht (by unfold sampleSkip; omega)
  have o := openParts_ok (encodeLong h 1 ++ pn) payload tag _ 2 hh ht
  rw [hh] at s o
  exact ⟨rfl, length_encodeLong h 1, s, o⟩

#audit_axioms Vinc.TransportHdr.writeLong_ok
#audit_axioms Vinc.TransportHdr.writeLong_refused_nothing
#audit_axioms Vinc.TransportHdr.late_writes
#audit_axioms Vinc.TransportHdr.parse_write
#audit_axioms Vinc.TransportHdr.parse_canonical
#audit_axioms Vinc.TransportHdr.parse_append
#audit_axioms Vinc.TransportHdr.parse_err_length
#audit_axioms Vinc.TransportHdr.parse_cut
#audit_axioms Vinc.TransportHdr.writeShort_refused_nothing
#audit_axioms Vinc.TransportHdr.short_roundtrip
#audit_axioms Vinc.TransportHdr.short_canonical
#audit_axioms Vinc.TransportHdr.aad_short
#audit_axioms Vinc.TransportHdr.aad_zero_rtt
#audit_axioms Vinc.TransportHdr.open_seal_parts

end Vinc.TransportHdr
