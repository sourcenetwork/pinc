import Vinc.Transcript

/-!
# The credit record

A model of `vinc-security/src/credit.rs`. A record is three `u16` values: the stream window in units of
`WINDOW_UNIT` (16 KiB), the concurrent-stream limit and the largest datagram frame in bytes. It is 6 bytes on the
wire, three big-endian `u16`s. Fields are `Nat`s at most `u16::MAX` (`Valid`); a byte string is a list of `Nat`s each
below 256 (`ValidBytes`).

* `new` is `CreditRecord::new`: the window is rounded down to whole units and saturates at `u16::MAX` units.
* `never_exceeds`: the record `new w s d` grants at most the requested window, streams and datagram bytes.
* `encode_decode` and `decode_encode`: every 6-byte string decodes to exactly one record that re-encodes to the
  same bytes (so `decode` is a bijection from 6-byte strings to records), hence `encode_injective`.
* `covers` is a partial order whose bottom is `NONE`; `NONE.covers(r)` holds only for `r = NONE`.
* The record is absorbed as its own 6-byte field of the transcript (`credit_field_injective`): a transcript that
  contains the field determines the record.
-/

namespace Vinc.Credit
open Vinc.Transcript

/-- `WINDOW_UNIT`: 16 KiB. -/
def windowUnit : Nat := 16 * 1024
/-- `CREDIT_RECORD_LEN`. -/
def recordLen : Nat := 6
/-- `u16::MAX`. -/
def u16max : Nat := 2 ^ 16 - 1

/-- `CreditRecord`. -/
structure Record where
  windowUnits : Nat
  maxStreams : Nat
  maxDatagram : Nat
  deriving DecidableEq

/-- Every field is a `u16`. -/
def Valid (r : Record) : Prop := r.windowUnits ≤ u16max ∧ r.maxStreams ≤ u16max ∧ r.maxDatagram ≤ u16max

/-- Every element of a byte string is a byte. -/
def ValidBytes (b : List Nat) : Prop := ∀ x ∈ b, x < 256

/-- `CreditRecord::NONE`. -/
def none : Record := ⟨0, 0, 0⟩

/-- `CreditRecord::new`: `window_bytes / WINDOW_UNIT`, clamped to `u16::MAX`. -/
def new (windowBytes maxStreams maxDatagram : Nat) : Record :=
  ⟨if windowBytes / windowUnit > u16max then u16max else windowBytes / windowUnit, maxStreams, maxDatagram⟩

/-- `CreditRecord::window_bytes`. -/
def windowBytes (r : Record) : Nat := r.windowUnits * windowUnit

/-- `CreditRecord::encode`: three big-endian `u16`s. -/
def encode (r : Record) : List Nat :=
  [r.windowUnits / 256, r.windowUnits % 256, r.maxStreams / 256, r.maxStreams % 256, r.maxDatagram / 256,
   r.maxDatagram % 256]

/-- `CreditRecord::decode` of a 6-byte string. -/
def decode (b : List Nat) : Record :=
  ⟨b.getD 0 0 * 256 + b.getD 1 0, b.getD 2 0 * 256 + b.getD 3 0, b.getD 4 0 * 256 + b.getD 5 0⟩

/-- `CreditRecord::covers`: every limit is at least `other`'s. -/
def covers (r o : Record) : Bool :=
  decide (r.windowUnits ≥ o.windowUnits) && decide (r.maxStreams ≥ o.maxStreams) &&
    decide (r.maxDatagram ≥ o.maxDatagram)

theorem encode_length (r : Record) : (encode r).length = recordLen := rfl

theorem encode_valid (r : Record) (h : Valid r) : ValidBytes (encode r) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold u16max at h1 h2 h3
  intro x hx
  simp only [encode, List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

/-- Decoding what was encoded gives the record back. -/
theorem decode_encode (r : Record) (h : Valid r) : decode (encode r) = r := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨w, s, d⟩ := r
  simp only [decode, encode, List.getD_cons_zero, List.getD_cons_succ]
  simp only [Record.mk.injEq]
  omega

/-- Every 6-byte string decodes to a record that re-encodes to the same bytes. -/
theorem encode_decode (b : List Nat) (hl : b.length = recordLen) (hb : ValidBytes b) : encode (decode b) = b := by
  match b, hl with
  | [a0, a1, a2, a3, a4, a5], _ =>
    have h0 := hb a0 (by simp)
    have h1 := hb a1 (by simp)
    have h2 := hb a2 (by simp)
    have h3 := hb a3 (by simp)
    have h4 := hb a4 (by simp)
    have h5 := hb a5 (by simp)
    simp only [decode, encode, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq, and_true]
    omega

/-- A decoded record is valid: every 6-byte string is a record of three `u16`s. -/
theorem decode_valid (b : List Nat) (hl : b.length = recordLen) (hb : ValidBytes b) : Valid (decode b) := by
  match b, hl with
  | [a0, a1, a2, a3, a4, a5], _ =>
    have h0 := hb a0 (by simp)
    have h1 := hb a1 (by simp)
    have h2 := hb a2 (by simp)
    have h3 := hb a3 (by simp)
    have h4 := hb a4 (by simp)
    have h5 := hb a5 (by simp)
    simp only [Valid, decode, u16max, List.getD_cons_zero, List.getD_cons_succ]
    omega

/-- The encoding is injective: two valid records with the same 6 bytes are equal. -/
theorem encode_injective (r s : Record) (hr : Valid r) (hs : Valid s) (h : encode r = encode s) : r = s := by
  rw [← decode_encode r hr, ← decode_encode s hs, h]

/-! ## `new` -/

/-- `new` rounds down to whole units: the window it grants is a multiple of the unit. -/
theorem new_window_multiple (w s d : Nat) : windowBytes (new w s d) % windowUnit = 0 := by
  simp [windowBytes, new, windowUnit]

/-- The units `new` stores: the quotient, clamped to `u16::MAX`. -/
theorem new_windowUnits (w s d : Nat) : (new w s d).windowUnits = min (w / windowUnit) u16max := by
  simp only [new]
  split <;> omega

/-- `new` never grants more than was asked, and the limits it grants are the ones asked for. -/
theorem never_exceeds (w s d : Nat) :
    windowBytes (new w s d) ≤ w ∧ (new w s d).maxStreams ≤ s ∧ (new w s d).maxDatagram ≤ d := by
  refine ⟨?_, Nat.le_refl _, Nat.le_refl _⟩
  unfold windowBytes
  rw [new_windowUnits]
  calc min (w / windowUnit) u16max * windowUnit ≤ w / windowUnit * windowUnit :=
        Nat.mul_le_mul_right _ (Nat.min_le_left _ _)
    _ ≤ w := Nat.div_mul_le_self _ _

/-- The window is rounded down by less than a unit, unless it saturated. -/
theorem new_rounds_down (w s d : Nat) :
    w < windowBytes (new w s d) + windowUnit ∨ (new w s d).windowUnits = u16max := by
  unfold windowBytes
  rw [new_windowUnits]
  unfold windowUnit u16max
  omega

/-- The window saturates at `u16::MAX` units. -/
theorem new_saturates (w s d : Nat) (h : u16max * windowUnit ≤ w) : (new w s d).windowUnits = u16max := by
  rw [new_windowUnits]
  unfold u16max windowUnit at *
  omega

/-- Below saturation the window is exactly `w / WINDOW_UNIT` units. -/
theorem new_units (w s d : Nat) (h : w < u16max * windowUnit) : (new w s d).windowUnits = w / windowUnit := by
  rw [new_windowUnits]
  unfold u16max windowUnit at *
  omega

/-- `new` always builds a valid record when the stream and datagram limits are `u16`s. -/
theorem new_valid (w s d : Nat) (hs : s ≤ u16max) (hd : d ≤ u16max) : Valid (new w s d) := by
  refine ⟨?_, hs, hd⟩
  rw [new_windowUnits]
  exact Nat.min_le_right _ _

/-- `window_bytes` of a valid record is its units times 16 KiB, below `2^30`. -/
theorem windowBytes_eq (r : Record) : windowBytes r = r.windowUnits * 16384 := rfl

theorem windowBytes_lt (r : Record) (h : Valid r) : windowBytes r < 2 ^ 30 := by
  obtain ⟨h1, _, _⟩ := h
  unfold windowBytes windowUnit u16max at *
  omega

/-! ## `covers` -/

theorem covers_refl (r : Record) : covers r r = true := by simp [covers]

theorem covers_trans (a b c : Record) (h1 : covers a b = true) (h2 : covers b c = true) : covers a c = true := by
  simp only [covers, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

/-- `covers` in both directions makes two records equal. -/
theorem covers_antisymm (a b : Record) (h1 : covers a b = true) (h2 : covers b a = true) : a = b := by
  obtain ⟨w, s, d⟩ := a
  obtain ⟨w', s', d'⟩ := b
  simp only [covers, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  obtain ⟨⟨a1, a2⟩, a3⟩ := h1
  obtain ⟨⟨b1, b2⟩, b3⟩ := h2
  simp only [Record.mk.injEq]
  omega

/-- Every record covers `NONE`. -/
theorem covers_none (r : Record) : covers r none = true := by simp [covers, none]

/-- `NONE` covers only itself. -/
theorem none_covers_only_none (r : Record) (h : covers none r = true) : r = none := by
  obtain ⟨w, s, d⟩ := r
  simp only [covers, none, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, Nat.le_zero] at h
  obtain ⟨⟨a1, a2⟩, a3⟩ := h
  simp only [none, Record.mk.injEq]
  omega

/-! ## The record in a transcript -/

/-- A record absorbed as its own 6-byte field is recovered from any transcript list that contains it at a known
position: the list determines the record. -/
theorem credit_field_injective (pre post : List Field) (r s : Record) (hr : Valid r) (hs : Valid s)
    (h : pre ++ encode r :: post = pre ++ encode s :: post) : r = s := by
  have := List.append_cancel_left h
  exact encode_injective r s hr hs (List.head_eq_of_cons_eq this)

/-- The field of an Initial that holds the credit record determines it: two Initials whose lists are equal carry
the same record. -/
theorem initial_credit_recovered (a b : Initial) (r s : Record) (hr : Valid r) (hs : Valid s)
    (ha : a.credit = encode r) (hb : b.credit = encode s) (h : initialFields a = initialFields b) : r = s := by
  have := (initialFields_injective a b h)
  rw [this] at ha
  exact encode_injective r s hr hs (ha.symm.trans hb)

/-- The same for a resume Hello. -/
theorem hello_credit_recovered (a b : Hello) (r s : Record) (hr : Valid r) (hs : Valid s)
    (ha : a.credit = encode r) (hb : b.credit = encode s) (h : helloFields a = helloFields b) : r = s := by
  have := (helloFields_injective a b h)
  rw [this] at ha
  exact encode_injective r s hr hs (ha.symm.trans hb)

/-- The record of the identity and credit absorb is recovered. -/
theorem identity_credit_recovered (alg alg' : Nat) (k k' : Field) (r s : Record) (hr : Valid r) (hs : Valid s)
    (h : identityCreditFields alg k (encode r) = identityCreditFields alg' k' (encode s)) :
    alg = alg' ∧ k = k' ∧ r = s := by
  obtain ⟨h1, h2, h3⟩ := identityCreditFields_injective _ _ _ _ _ _ h
  exact ⟨h1, h2, encode_injective r s hr hs h3⟩

/-- The ticket context `H(tid, credit.encode())` determines the credit record. -/
theorem ticketCtx_credit_recovered (t t' : Field) (r s : Record) (hr : Valid r) (hs : Valid s)
    (h : ticketCtxFields t (encode r) = ticketCtxFields t' (encode s)) : t = t' ∧ r = s := by
  obtain ⟨h1, h2⟩ := ticketCtxFields_injective _ _ _ _ h
  exact ⟨h1, encode_injective r s hr hs h2⟩

end Vinc.Credit

#audit_axioms Vinc.Credit.decode_encode
#audit_axioms Vinc.Credit.encode_decode
#audit_axioms Vinc.Credit.decode_valid
#audit_axioms Vinc.Credit.encode_injective
#audit_axioms Vinc.Credit.new_window_multiple
#audit_axioms Vinc.Credit.never_exceeds
#audit_axioms Vinc.Credit.new_rounds_down
#audit_axioms Vinc.Credit.new_saturates
#audit_axioms Vinc.Credit.new_units
#audit_axioms Vinc.Credit.new_valid
#audit_axioms Vinc.Credit.windowBytes_lt
#audit_axioms Vinc.Credit.covers_refl
#audit_axioms Vinc.Credit.covers_trans
#audit_axioms Vinc.Credit.covers_antisymm
#audit_axioms Vinc.Credit.covers_none
#audit_axioms Vinc.Credit.none_covers_only_none
#audit_axioms Vinc.Credit.credit_field_injective
#audit_axioms Vinc.Credit.initial_credit_recovered
#audit_axioms Vinc.Credit.hello_credit_recovered
#audit_axioms Vinc.Credit.identity_credit_recovered
#audit_axioms Vinc.Credit.ticketCtx_credit_recovered
