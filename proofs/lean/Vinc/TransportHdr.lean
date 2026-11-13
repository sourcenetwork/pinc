import Vinc.Axioms
import Vinc.Varint

/-!
# Packet headers: the model

A model of `vinc-transport` `packet/header.rs` and `packet/datagram.rs`, and of the byte ranges `packet/protect.rs`
hands to the AEAD, as `proofs/tla/HdrOps.tla` has them, over lists of bytes and unbounded `Nat`:

* the long header `0b11TT_xxxx | version | dcid_len dcid | scid_len scid | length (varint)`: `writeLong` is
  `LongHeader::write` put by put on a writer of `cap` bytes, so what a refused write leaves behind is part of the
  result; `parseLong` is `LongHeader::parse` read by read;
* the short header `0b010K_00LL | dcid | pn`: `writeShort` is `ShortHeader::write`, `shortDcid` is `short_dcid`, and
  `readFirst` is what `unprotect_header` reads from the first byte once the mask is off (the reserved bits, the
  packet-number length, the key phase);
* `packets` is the iterator `Packets::next` run to its end, with the offset and length of every packet it lends;
* `sealParts` and `openParts` are the split of a packet into associated data, payload and tag that `seal` and `open`
  make (the record layer and the header protection mask are `Vinc.Record`).

The varint is `Vinc.Varint`. A connection id is a list of at most 20 bytes (`ConnId`); `usize` is not bounded here:
the one place the bound matters, a body length of `2^63` or more, is the varint's limit and is refused by `writeLong`
before anything is written. `Vinc.TraceHdr` replays the recorded calls of the real code through these functions; the
theorems are in `Vinc.TransportHdrThm` and `Vinc.TransportHdrSplit`.
-/

namespace Vinc.TransportHdr
open Vinc

/-- `VERSION`. -/
def version : Nat := 1
/-- `MAX_CID_LEN`. -/
def maxCid : Nat := 20
/-- `Aead::TAG_LEN`. -/
def tagLen : Nat := 16
/-- `SAMPLE_SKIP`. -/
def sampleSkip : Nat := 4

/-- `PacketError`, with the `WireError` variants a header operation can return. -/
inductive PErr where
  | truncated (needed : Nat)
  | bufferTooSmall (needed : Nat)
  | varintTooLong
  | varintOverflow
  | varintNonMinimal
  | form
  | longType
  | version (v : Nat)
  | connIdLength
  | reserved
  | pnLength
  | tooShort
  | length
  deriving DecidableEq, Repr

/-- `PacketError::Wire` of a varint error. -/
def ofVarint : Varint.Error → PErr
  | .tooLong => .varintTooLong
  | .truncated => .truncated 1
  | .nonMinimal => .varintNonMinimal
  | .overflow => .varintOverflow
  | .bufferTooSmall n => .bufferTooSmall n

inductive LongType where
  | handshake
  | zeroRtt
  deriving DecidableEq, Repr

/-- `ty as u8`. -/
def LongType.bits : LongType → Nat
  | .handshake => 0
  | .zeroRtt => 1

/-- `LongType::from_bits`. -/
def LongType.fromBits : Nat → Option LongType
  | 0 => some .handshake
  | 1 => some .zeroRtt
  | _ => none

structure LongHeader where
  ty : LongType
  dcid : List Nat
  scid : List Nat
  bodyLen : Nat
  deriving DecidableEq, Repr

/-- The ids are `ConnId`s: at most 20 bytes each. -/
def LongHeader.WF (h : LongHeader) : Prop := h.dcid.length ≤ maxCid ∧ h.scid.length ≤ maxCid

/-! ## The writer -/

/-- A writer after some puts: the error of the first put that failed, and the bytes written before it. -/
structure WRes where
  err : Option PErr
  out : List Nat
  deriving DecidableEq, Repr

/-- `Writer::put_slice` into a buffer of `cap` bytes that holds `out`. -/
def putSlice (cap : Nat) (bs out : List Nat) : Except PErr (List Nat) :=
  if bs.length ≤ cap - out.length then .ok (out ++ bs)
  else .error (.bufferTooSmall (bs.length - (cap - out.length)))

/-- `put_u8(u8::try_from(len).map_err(ConnIdLength)?)`. -/
def putLen (cap : Nat) (len : Nat) (out : List Nat) : Except PErr (List Nat) :=
  if len ≤ 255 then putSlice cap [len] out else .error .connIdLength

/-- `Writer::put_varint`. -/
def putVarint (cap : Nat) (v : Nat) (out : List Nat) : Except PErr (List Nat) :=
  match Varint.encodeInto (cap - out.length) v with
  | .ok bs => .ok (out ++ bs)
  | .error e => .error (ofVarint e)

/-- One more put, with `?`: after an error nothing more happens, and a put that fails writes nothing. -/
def WRes.andThen (r : WRes) (f : List Nat → Except PErr (List Nat)) : WRes :=
  match r.err with
  | some _ => r
  | none =>
    match f r.out with
    | .ok o => ⟨none, o⟩
    | .error e => ⟨some e, r.out⟩

/-! ## The long header -/

/-- `LongHeader::header_len`. -/
def headerLen (h : LongHeader) : Nat :=
  1 + 1 + 1 + h.dcid.length + 1 + h.scid.length + Varint.encodedLen h.bodyLen

/-- The low four bits `write` chooses, or `none` for a `pn_len` that does not fit the type. -/
def lowBits (ty : LongType) (pnLen : Nat) : Option Nat :=
  match ty with
  | .zeroRtt => if pnLen = 2 then some (pnLen - 1) else none
  | .handshake => if pnLen = 0 then some 0 else none

/-- `LONG_FORM | ((ty as u8) << 4) | low`. -/
def firstLong (ty : LongType) (low : Nat) : Nat := 0xC0 ||| (ty.bits <<< 4) ||| low

/-- The puts of `LongHeader::write`, after its checks. -/
def longPuts (h : LongHeader) (low cap : Nat) : WRes :=
  ((((((((WRes.mk none []).andThen (putSlice cap [firstLong h.ty low])).andThen (putSlice cap [version])).andThen
    (putLen cap h.dcid.length)).andThen (putSlice cap h.dcid)).andThen (putLen cap h.scid.length)).andThen
    (putSlice cap h.scid)).andThen (putVarint cap h.bodyLen))

/-- `LongHeader::write` into a writer with room for `cap` bytes. -/
def writeLong (h : LongHeader) (pnLen cap : Nat) : WRes :=
  match lowBits h.ty pnLen with
  | none => ⟨some .pnLength, []⟩
  | some low =>
    if h.bodyLen ≥ Varint.limit then ⟨some .varintOverflow, []⟩
    else if cap < headerLen h then ⟨some (.bufferTooSmall (headerLen h - cap)), []⟩
    else longPuts h low cap

/-- `LongHeader::write` as it was before the body length was checked first: the room check, then the puts. -/
def writeLongLate (h : LongHeader) (pnLen cap : Nat) : WRes :=
  match lowBits h.ty pnLen with
  | none => ⟨some .pnLength, []⟩
  | some low =>
    if cap < headerLen h then ⟨some (.bufferTooSmall (headerLen h - cap)), []⟩
    else longPuts h low cap

/-- The one encoding of a long header whose first byte has the low bits `low`. -/
def encodeLong (h : LongHeader) (low : Nat) : List Nat :=
  [firstLong h.ty low, version, h.dcid.length] ++ h.dcid ++ [h.scid.length] ++ h.scid ++ Varint.encodeBytes h.bodyLen

/-- `read_cid`: the id and the rest. -/
def readCid (r : List Nat) : Except PErr (List Nat × List Nat) :=
  match r with
  | [] => .error (.truncated 1)
  | len :: r' =>
    if len > maxCid then .error .connIdLength
    else if r'.length < len then .error (.truncated (len - r'.length))
    else .ok (r'.take len, r'.drop len)

/-- `LongHeader::parse`: the header and its encoded size. -/
def parseLong (p : List Nat) : Except PErr (LongHeader × Nat) :=
  match p with
  | [] => .error (.truncated 1)
  | first :: r1 =>
    if first &&& 0xC0 ≠ 0xC0 then .error .form
    else
      match LongType.fromBits ((first >>> 4) &&& 3) with
      | none => .error .longType
      | some ty =>
        if ty ≠ .zeroRtt ∧ first &&& 0x0f ≠ 0 then .error .reserved
        else
          match r1 with
          | [] => .error (.truncated 1)
          | v :: r2 =>
            if v ≠ version then .error (.version v)
            else
              match readCid r2 with
              | .error e => .error e
              | .ok (dcid, r3) =>
                match readCid r3 with
                | .error e => .error e
                | .ok (scid, r4) =>
                  match Varint.decode r4 with
                  | .error e => .error (ofVarint e)
                  | .ok (bl, n) =>
                    if bl > r4.length - n then .error .length
                    else .ok (⟨ty, dcid, scid, bl⟩, 1 + 1 + (1 + dcid.length) + (1 + scid.length) + n)

/-! ## The short header -/

structure ShortHeader where
  keyPhase : Bool
  dcid : List Nat
  deriving DecidableEq, Repr

/-- `short_header_len`. -/
def shortHeaderLen (dcidLen pnLen : Nat) : Nat := 1 + dcidLen + pnLen

/-- `SHORT_FORM | phase | (pn.len() - 1)`. -/
def firstShort (keyPhase : Bool) (pnLen : Nat) : Nat := 0x40 ||| (if keyPhase then 0x10 else 0) ||| (pnLen - 1)

/-- The one encoding of a short header with the truncated packet number `pn`. -/
def encodeShort (h : ShortHeader) (pn : List Nat) : List Nat := [firstShort h.keyPhase pn.length] ++ h.dcid ++ pn

/-- `ShortHeader::write` into a writer with room for `cap` bytes. -/
def writeShort (h : ShortHeader) (pn : List Nat) (cap : Nat) : WRes :=
  if ¬(2 ≤ pn.length ∧ pn.length ≤ 3) then ⟨some .pnLength, []⟩
  else if cap < shortHeaderLen h.dcid.length pn.length then
    ⟨some (.bufferTooSmall (shortHeaderLen h.dcid.length pn.length - cap)), []⟩
  else
    (((WRes.mk none []).andThen (putSlice cap [firstShort h.keyPhase pn.length])).andThen (putSlice cap h.dcid)).andThen
      (putSlice cap pn)

/-- `short_dcid`. -/
def shortDcid (p : List Nat) (dcidLen : Nat) : Except PErr (List Nat) :=
  if dcidLen > maxCid then .error .connIdLength
  else
    match p with
    | [] => .error .tooShort
    | first :: rest =>
      if first &&& 0xE0 ≠ 0x40 then .error .form
      else if rest.length < dcidLen then .error .tooShort
      else .ok (rest.take dcidLen)

/-- What `unprotect_header` reads from the first byte once the mask is off: `Reserved` for bit 3 or 2, else the
packet-number length the byte declares (1 to 4) and the key phase (bit 4). -/
def readFirst (first : Nat) : Except PErr (Nat × Bool) :=
  if first &&& 0x0C ≠ 0 then .error .reserved else .ok ((first &&& 0x03) + 1, first &&& 0x10 ≠ 0)

/-! ## Datagrams -/

/-- What the iterator yields: a packet with the offset and the length of the bytes it lends, or the error that ends
the iteration, with the offset it was found at. -/
inductive Item where
  | long (h : LongHeader) (hlen start len : Nat)
  | short (dcid : List Nat) (start len : Nat)
  | err (e : PErr) (start : Nat)
  deriving DecidableEq, Repr

/-- `Packets::next` until it returns `None`; `rest` starts at offset `off` of the datagram. A step that yields an
error or a short packet leaves nothing (`mem::take`), so it is the last. -/
def packetsFrom : Nat → Nat → List Nat → Nat → List Item
  | 0, _, _, _ => []
  | fuel + 1, off, rest, dl =>
    match rest with
    | [] => []
    | first :: _ =>
      if first = 0 then
        if rest.any (fun b => b != 0) then [.err .form off] else []
      else if first &&& 0x80 = 0 then
        match shortDcid rest dl with
        | .ok d => [.short d off rest.length]
        | .error e => [.err e off]
      else
        match parseLong rest with
        | .error e => [.err e off]
        | .ok (h, hl) =>
          -- `split_at_mut_checked`: `None` ends the iteration
          if rest.length < hl + h.bodyLen then []
          else .long h hl off (hl + h.bodyLen) :: packetsFrom fuel (off + (hl + h.bodyLen)) (rest.drop (hl + h.bodyLen)) dl

/-- `packets(datagram, dcid_len)` collected. Every long packet takes at least five bytes, so the fuel is never the
reason the list ends (`packetsFrom_split` in `Vinc.TransportHdrSplit`). -/
def packets (d : List Nat) (dl : Nat) : List Item := packetsFrom (d.length + 1) 0 d dl

/-- `Packet::pn_off`. -/
def Item.pnOff : Item → Nat
  | .long _ hl _ _ => hl
  | .short d _ _ => 1 + d.length
  | .err _ _ => 0

/-! ## The associated data -/

/-- The split of a packet: the associated data, the payload range and the packet's length. -/
structure Parts where
  aad : List Nat
  payloadStart : Nat
  payloadEnd : Nat
  total : Nat
  deriving DecidableEq, Repr

/-- The split `seal` makes of `packet` before it calls the record layer: the header up to and including the packet
number is the associated data. -/
def sealParts (packet : List Nat) (pnOff pnLen payloadLen : Nat) : Except PErr Parts :=
  if pnLen + payloadLen < sampleSkip then .error .tooShort
  else
    let headerLen := pnOff + pnLen
    let total := headerLen + payloadLen + tagLen
    if packet.length < total then .error (.bufferTooSmall (total - packet.length))
    else .ok ⟨packet.take headerLen, headerLen, headerLen + payloadLen, total⟩

/-- The split `open` makes of `packet` (after `unprotect_header`) before it calls the record layer. -/
def openParts (packet : List Nat) (pnOff pnLen : Nat) : Except PErr Parts :=
  let headerLen := pnOff + pnLen
  if packet.length < headerLen then .error .tooShort
  else if packet.length - headerLen < tagLen then .error .tooShort
  else .ok ⟨packet.take headerLen, headerLen, headerLen + (packet.length - headerLen - tagLen), packet.length⟩

end Vinc.TransportHdr
