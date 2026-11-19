import Pinc.BroadcastWire

/-!
# The port-mapping codecs

A model of the PCP and NAT-PMP codecs of `crates/pinc-portmap/src/pcp.rs` (`encode_request`, `decode_request`,
`encode_response`, `decode_response`) and `crates/pinc-portmap/src/natpmp.rs` (the same four).

The story. A client and its home gateway trade small fixed messages over UDP. Each message is a row of fields in a
fixed order: some fields are constant bytes the format pins (a version, an opcode, reserved zeros), the others are
big-endian numbers of a fixed width (a port, a lifetime, an epoch, a 16-byte address, a 12-byte nonce). What must
never happen: a decoder that reads back something other than what was written, that accepts two different byte
strings for one message, that accepts a message of the wrong length, or one whose constant bytes (reserved zeros
included) are not the pinned ones.

The model. A message format is a `Layout`: a list of fields (`Fld.const bs` or `Fld.num w`). `enc` writes the
values of the number fields in order; `dec` cuts the input by the layout and refuses a constant byte that differs,
a short input or bytes left over. Three theorems hold for every layout: `dec_enc` (round trip), `enc_dec` (a decode
determines its input: the canonical form, so reserved bytes are zero and nothing else is accepted) and `dec_len` (a
decoded input has exactly the layout's length). Each message of the two protocols is then a layout, with its length
checked by `decide`.

Stated assumptions. Bytes are `Nat`s below 256 (`ValidBytes`); a value fits its field (`Fits`). An address is its 16
bytes as one number: the code decodes an IPv4-mapped address to IPv4 (`to_canonical`) and encodes IPv4 back to the
same mapped bytes, which this model does not separate from the bytes themselves; the property tests of
`tests/portmap_codec.rs` check that step on the real code. The result-code rules of a header (an error header is not
a success, an ANNOUNCE is opcode 0) are the code's own checks on top of the layout and are not modelled here.
-/

namespace Pinc.PortMapCodec

open Pinc.BroadcastWire

/-- A field: constant bytes the format pins, or a big-endian number `w` bytes wide. -/
inductive Fld where
  -- bytes that must be exactly these
  | const (bs : List Nat)
  -- a number of `w` bytes, most significant first
  | num (w : Nat)

/-- A message format: its fields in order. -/
abbrev Layout := List Fld

/-- The bytes of a message: each constant as is, each number as `w` big-endian bytes, in field order. -/
def enc : Layout → List Nat → List Nat
  -- no field left: nothing more to write
  | [], _ => []
  -- a constant: its bytes, then the rest
  | .const bs :: fs, vs => bs ++ enc fs vs
  -- a number: its bytes, then the rest with the next values
  | .num w :: fs, v :: vs => beBytes w v ++ enc fs vs
  -- a number with no value left: the caller broke the arity (`Fits` rules it out)
  | .num _ :: _, [] => []

/-- Read a message: cut the input by the fields, refuse a constant that differs, a short input or bytes left over. -/
def dec : Layout → List Nat → Option (List Nat)
  -- no field left: the input must be used up
  | [], b => if b = [] then some [] else none
  -- a constant: the next bytes must be exactly it
  | .const bs :: fs, b => if b.take bs.length = bs then dec fs (b.drop bs.length) else none
  -- a number: the next `w` bytes, read big-endian, if there are that many
  | .num w :: fs, b =>
    if w ≤ b.length then (dec fs (b.drop w)).map (fun r => beVal (b.take w) :: r) else none

/-- The values fit the layout: one per number field, each below `256 ^ w`. -/
def Fits : Layout → List Nat → Prop
  -- no field left: no value left
  | [], vs => vs = []
  -- a constant takes no value
  | .const _ :: fs, vs => Fits fs vs
  -- a number takes the next value, which must fit its width
  | .num w :: fs, v :: vs => v < 256 ^ w ∧ Fits fs vs
  -- a number with no value: does not fit
  | .num _ :: _, [] => False

/-- The length of every message of a layout. -/
def len : Layout → Nat
  -- nothing
  | [] => 0
  -- the constant's bytes and the rest
  | .const bs :: fs => bs.length + len fs
  -- the number's width and the rest
  | .num w :: fs => w + len fs

/-- Round trip: reading the bytes written for values that fit gives the values back. -/
theorem dec_enc : ∀ (fs : Layout) (vs : List Nat), Fits fs vs → dec fs (enc fs vs) = some vs
  -- no field: nothing written, the empty input reads as no values
  | [], vs, h => by simp only [Fits] at h; subst h; simp [enc, dec]
  -- a constant: its bytes match and the rest reads back by induction
  | .const bs :: fs, vs, h => by
    simp only [Fits] at h
    simp [enc, dec, dec_enc fs vs h]
  -- a number: its `w` bytes read back as the value (it fits), the rest by induction
  | .num w :: fs, v :: vs, h => by
    simp only [Fits] at h
    obtain ⟨hv, hr⟩ := h
    have hl := length_beBytes w v
    simp [enc, dec, hl, dec_enc fs vs hr, beVal_of_lt hv]
  -- a number with no value cannot fit
  | .num _ :: _, [], h => by simp [Fits] at h

/-- The bytes of a valid input stay valid in any piece cut from it. -/
theorem valid_take {b : List Nat} (n : Nat) (h : ValidBytes b) : ValidBytes (b.take n) :=
  -- every byte of the front piece is a byte of the input
  fun x hx => h x (List.mem_of_mem_take hx)

/-- The same for the back piece. -/
theorem valid_drop {b : List Nat} (n : Nat) (h : ValidBytes b) : ValidBytes (b.drop n) :=
  -- every byte of the back piece is a byte of the input
  fun x hx => h x (List.mem_of_mem_drop hx)

/-- Canonical form: an input that reads as some values is exactly the bytes written for them, so no second byte
string (other reserved bytes, a longer or shorter input) reads as the same message. -/
theorem enc_dec : ∀ (fs : Layout) (b vs : List Nat), ValidBytes b → dec fs b = some vs → enc fs vs = b
  -- no field: the input was empty and so is the output
  | [], b, vs, _, h => by
    simp only [dec] at h
    split at h
    · simp_all [enc]
    · simp at h
  -- a constant: the input starts with it, the rest is canonical by induction
  | .const bs :: fs, b, vs, hv, h => by
    simp only [dec] at h
    split at h
    · rename_i ht
      have ih := enc_dec fs _ vs (valid_drop _ hv) h
      simp only [enc, ih]
      -- the input is its front piece (the constant) and the rest
      have e := List.take_append_drop bs.length b
      rw [ht] at e
      exact e
    · simp at h
  -- a number: its bytes are the big-endian bytes of the value read, the rest canonical by induction
  | .num w :: fs, b, vs, hv, h => by
    simp only [dec] at h
    split at h
    · rename_i hw
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, rfl⟩ := h
      have ih := enc_dec fs _ r (valid_drop _ hv) hr
      have hl : (b.take w).length = w := by simp; omega
      simp only [enc, ih, beBytes_beVal w (b.take w) hl (valid_take _ hv)]
      exact List.take_append_drop _ _
    · simp at h

/-- Exact length: an input that reads at all has the layout's length, so a decoder refuses every other length. -/
theorem dec_len : ∀ (fs : Layout) (b vs : List Nat), dec fs b = some vs → b.length = len fs
  -- no field: only the empty input reads
  | [], b, vs, h => by
    simp only [dec] at h
    split at h
    · simp_all [len]
    · simp at h
  -- a constant: its bytes and the rest by induction
  | .const bs :: fs, b, vs, h => by
    simp only [dec] at h
    split at h
    · rename_i ht
      have ih := dec_len fs _ vs h
      have hb : (b.take bs.length).length = bs.length := by rw [ht]
      simp only [len]
      simp only [List.length_drop] at ih
      simp only [List.length_take] at hb
      omega
    · simp at h
  -- a number: its width and the rest by induction
  | .num w :: fs, b, vs, h => by
    simp only [dec] at h
    split at h
    · rename_i hw
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨r, hr, _⟩ := h
      have ih := dec_len fs _ r hr
      simp only [List.length_drop] at ih
      simp only [len]
      omega
    · simp at h

/-! ## PCP (RFC 6887): `pcp.rs` -/

/-- A MAP request: version 2, opcode 1 (R clear), reserved 0, lifetime, client address, nonce, protocol, three
reserved zeros, internal port, suggested external port, suggested external address. -/
def pcpMapRequest : Layout :=
  [.const [2, 1, 0, 0], .num 4, .num 16, .num 12, .num 1, .const [0, 0, 0], .num 2, .num 2, .num 16]

/-- A MAP response: version 2, opcode 0x81 (R set), reserved 0, result, lifetime, epoch, twelve reserved zeros, then
the MAP data as in the request with the assigned port and address. -/
def pcpMapResponse : Layout :=
  [.const [2, 0x81, 0], .num 1, .num 4, .num 4, .const (List.replicate 12 0), .num 12, .num 1, .const [0, 0, 0],
    .num 2, .num 2, .num 16]

/-- An ANNOUNCE: the header alone, opcode 0x80. -/
def pcpAnnounce : Layout :=
  [.const [2, 0x80, 0], .num 1, .num 4, .num 4, .const (List.replicate 12 0)]

/-- An error answer to a MAP request without its opcode data: the header alone, opcode 0x81. -/
def pcpMapHeader : Layout :=
  [.const [2, 0x81, 0], .num 1, .num 4, .num 4, .const (List.replicate 12 0)]

/-- A MAP message is 60 bytes. -/
theorem pcp_map_len : len pcpMapRequest = 60 ∧ len pcpMapResponse = 60 := by decide

/-- A header alone is 24 bytes. -/
theorem pcp_header_len : len pcpAnnounce = 24 ∧ len pcpMapHeader = 24 := by decide

/-! ## NAT-PMP (RFC 6886): `natpmp.rs` -/

/-- The external address request: version 0, opcode 0. -/
def natAddressRequest : Layout := [.const [0, 0]]

/-- The UDP mapping request: version 0, opcode 1, reserved 0, internal port, external port, lifetime. -/
def natMapRequest : Layout := [.const [0, 1, 0, 0], .num 2, .num 2, .num 4]

/-- The external address response: version 0, opcode 128, result, epoch, address. -/
def natAddressResponse : Layout := [.const [0, 128], .num 2, .num 4, .num 4]

/-- The UDP mapping response: version 0, opcode 129, result, epoch, internal port, external port, lifetime. -/
def natMapResponse : Layout := [.const [0, 129], .num 2, .num 4, .num 2, .num 2, .num 4]

/-- An error with no body: version 0, the opcode answered with its response bit, result, epoch. -/
def natError : Layout := [.const [0], .num 1, .num 2, .num 4]

/-- The NAT-PMP lengths: 2 and 12 for the requests, 12, 16 and 8 for the answers. -/
theorem nat_len :
    len natAddressRequest = 2 ∧ len natMapRequest = 12 ∧ len natAddressResponse = 12 ∧ len natMapResponse = 16 ∧
      len natError = 8 := by decide

/-- A PCP MAP request whose reserved bytes are not zero, or whose length is not 60, is refused (from `enc_dec` and
`dec_len`: what reads is the encoding, which has zeros there and 60 bytes). -/
theorem pcp_request_refuses (b : List Nat) (hv : ValidBytes b)
    (hbad : b.length ≠ 60 ∨ ∀ vs, enc pcpMapRequest vs ≠ b) : dec pcpMapRequest b = none := by
  -- suppose it read: then it had the layout's length and was the encoding of what it read
  cases h : dec pcpMapRequest b with
  | none => rfl
  | some vs =>
    exfalso
    rcases hbad with hl | he
    · exact hl (by rw [dec_len _ _ _ h]; exact pcp_map_len.1)
    · exact he vs (enc_dec _ _ _ hv h)

end Pinc.PortMapCodec
