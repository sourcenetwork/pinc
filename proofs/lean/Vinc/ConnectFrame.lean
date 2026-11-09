import Vinc.ConnectCodecCore

/-!
# The carrier frame codec

`Frame::decode` and `Frame::encode` of `vinc-connect/src/carrier/frame.rs`, over the field engine of
`ConnectCodecCore.lean`. A frame is its type byte and its fields (`Fr`): the type byte selects a layout (`layoutOf`),
the two frames with a variable shape are special: DNSR (the status byte selects the tail) and BATCH (a count, varint
lengths and the member frames, which the decoder checks one by one; the fields of a batch are the member frames as
raw bytes).

The numbers of the formats are the ones of the code: the packet is 1 to 1452 bytes, a record 1 to `maxRecordLen`, a
notice 1 to 8192, a batch 2 to 64 frames and 16384 bytes of frames, an alias is below 32.
-/

namespace Vinc.ConnCodec
open Vinc.MemCodec (Byte beBytes beN beBytes_length beBytes_byte beN_beBytes beBytes_beN beN_lt beN_append)

/-- `MAX_PACKET_LEN`. -/
def maxPacket : Nat := 1452
/-- `MAX_RECORD_LEN`: the longest record, for the longest identity algorithm. -/
def maxRecordLen : Nat := 8 + 2 * 33 + 8 + 2 + 8 * 19 + 1 + 64 + 1984 + 3373
/-- `MAX_NOTICE_LEN`. -/
def maxNotice : Nat := 8192
/-- `BATCH_MAX_FRAMES`. -/
def batchFrames : Nat := 64
/-- `BATCH_MAX_BYTES`. -/
def batchBytes : Nat := 16384
/-- `BATCH_HEAD_MAX`. -/
def batchHead : Nat := 2 + batchFrames * 3
/-- `MAX_FRAME_LEN`. -/
def maxFrame : Nat := batchBytes + batchHead

/-- The tail of a frame that carries a packet. -/
def packetTail : Option (Nat × CErr) := some (maxPacket, .packetSize)
/-- The tail of a frame that carries a record. -/
def recordTail : Option (Nat × CErr) := some (maxRecordLen, .bodySize)
/-- The tail of a frame that carries a sleep notice. -/
def noticeTail : Option (Nat × CErr) := some (maxNotice, .bodySize)

/-- A frame: the type byte and the fields after it. For a batch the fields are the member frames as raw bytes. -/
structure Fr where
  ty : Nat
  fs : List F
  deriving DecidableEq, Repr

/-- The layout of the frames of a fixed shape. DNSR (15) and BATCH (13) are read by their own steps. -/
def layoutOf : Nat → Option L
  | 2 | 3 => some ⟨[.node, .u8], packetTail⟩
  | 4 | 17 => some ⟨[], recordTail⟩
  | 5 | 6 => some ⟨[], none⟩
  | 7 | 8 => some ⟨[], packetTail⟩
  | 9 | 11 => some ⟨[.node, .alias, .u8], packetTail⟩
  | 10 | 12 => some ⟨[.alias, .u8], packetTail⟩
  | 14 => some ⟨[.node], none⟩
  | 16 => some ⟨[.node, .node, .u8], packetTail⟩
  | 18 => some ⟨[], noticeTail⟩
  | _ => none

/-- `finish`: nothing may follow a frame. -/
def finish (r : List Nat) : Except CErr Unit :=
  if r = [] then .ok () else .error .trailing

/-- The DNSR step, after its type byte: the peer, the status, and a record only for status 1. `lw` lifts the wire
errors, `sf` builds the error of an unknown status and `e` is the error of an empty or oversized record, so that
the frame (type 15) and the datagram (type 4) are the same step. -/
def decodeDnsrG (lw : W → CErr) (sf : Nat → CErr) (e : CErr) (ty : Nat) (r : List Nat) : Except CErr Fr := do
  let (fs, r) ← rdPre lw [.node, .u8] r
  match fs with
  | [_, F.u8 0] => do finish r; pure ⟨ty, fs⟩
  | [_, F.u8 1] => do
    let (tf, r) ← rdTail (some (maxRecordLen, e)) r
    finish r
    pure ⟨ty, fs ++ tf⟩
  | [_, F.u8 2] => do finish r; pure ⟨ty, fs⟩
  | [_, F.u8 s] => throw (sf s)
  | _ => throw (CErr.wire (.unexpected "dnsr"))

/-- The DNSR frame. -/
def decodeDnsr (r : List Nat) : Except CErr Fr := decodeDnsrG CErr.wire CErr.status CErr.bodySize 15 r

/-- The variable-length varint reads of `vinc-wire`'s `Reader::read_varint`. -/
def rdVar (r : List Nat) : Except W (Nat × List Nat) :=
  match Varint.decode r with
  | .ok (v, n) => .ok (v, r.drop n)
  | .error .tooLong => .error .vLong
  | .error .truncated => .error (.trunc 1)
  | .error .nonMinimal => .error .vNonMin
  | .error .overflow => .error .vOver
  | .error (.bufferTooSmall n) => .error (.small n)

/-- The lengths of a batch: `k` varints, none zero, whose running total does not overflow a `usize`. -/
def rdLens : Nat → Nat → List Nat → Except CErr (List Nat × List Nat)
  | 0, _, r => .ok ([], r)
  | k + 1, total, r => do
    let (len, r1) ← liftW CErr.wire (rdVar r)
    if len = 0 then throw (CErr.batch "empty frame")
    if 2 ^ 64 ≤ total + len then throw (CErr.batch "length")
    let (ls, r2) ← rdLens k (total + len) r1
    pure (len :: ls, r2)

/-- The members of a batch, each checked: not a batch, and a frame (`dec` is the decoder of a non-batch frame). -/
def rdMembers (dec : List Nat → Except CErr Fr) : List Nat → List Nat → Except CErr (List (List Nat))
  | [], _ => .ok []
  | l :: ls, body => do
    let head := body.take l
    if head.head? = some 13 then throw (CErr.batch "nested batch")
    let _ ← dec head
    let ps ← rdMembers dec ls (body.drop l)
    pure (head :: ps)

/-- The batch frame after its type byte (`decode_batch`). -/
def decodeBatch (dec : List Nat → Except CErr Fr) (r : List Nat) : Except CErr Fr := do
  let (c, rest) ← liftW CErr.wire (rdU8 r)
  if c < 2 ∨ batchFrames < c then throw (CErr.batch "frame count")
  let (ls, body) ← rdLens c 0 rest
  if ls.sum ≠ body.length ∨ batchBytes < ls.sum then throw (CErr.batch "size")
  let ps ← rdMembers dec ls body
  pure ⟨13, ps.map F.raw⟩

/-- `Frame::decode` with the decoder of a batch left open, so that the members (never batches) can use it. -/
def decodeWith (bat : List Nat → Except CErr Fr) (b : List Nat) : Except CErr Fr := do
  let (ty, r) ← liftW CErr.wire (rdU8 b)
  if ty = 13 then bat r
  else if ty = 15 then decodeDnsr r
  else
    match layoutOf ty with
    | none => throw (CErr.unknownType ty)
    | some l => do
      let (fs, r) ← rdLayout CErr.wire l r
      finish r
      pure ⟨ty, fs⟩

/-- A frame that is not a batch: the decoder the members of a batch use. -/
def decodeNB (b : List Nat) : Except CErr Fr :=
  decodeWith (fun _ => .error (.unknownType 13)) b

/-- `Frame::decode`: one frame from exactly `b`. -/
def decode (b : List Nat) : Except CErr Fr := decodeWith (decodeBatch decodeNB) b

/-! ## Encoding -/

/-- The parts of a batch frame. -/
def Fr.parts (f : Fr) : List (List Nat) := f.fs.map F.enc

/-- The lengths of the members as varints. -/
def lensBytes (ps : List (List Nat)) : List Nat := (ps.map fun p => Varint.encodeBytes p.length).flatten

/-- The steps of an encoder for the fields of a layout. -/
def opsK : K → F → List Op
  | .alias, .u8 a => [.chk (decide (a < aliasMax)) (.alias a), .put [a]]
  | _, f => [.put f.enc]

def opsPre : List K → List F → List Op
  | k :: ks, f :: fs => opsK k f ++ opsPre ks fs
  | _, _ => []

def opsTail : Option (Nat × CErr) → List F → List Op
  | some (m, e), [F.raw b] => [.chk (decide (1 ≤ b.length ∧ b.length ≤ m)) e, .put b]
  | _, tf => tf.map fun f => .put f.enc

/-- The steps for a layout instance. -/
def opsLayout (l : L) (fs : List F) : List Op :=
  opsPre l.pre (fs.take l.pre.length) ++ opsTail l.tail (fs.drop l.pre.length)

/-- The steps of `Frame::encode`: the type byte and the fields (a batch writes its count, lengths and body as
three writes; DNSR writes its status before the record). -/
def Fr.ops (f : Fr) : List Op :=
  .put [f.ty] ::
    if f.ty = 13 then [.put [f.fs.length], .put (lensBytes f.parts), .put f.parts.flatten]
    else if f.ty = 15 then opsLayout ⟨[.node, .u8], recordTail⟩ f.fs
    else match layoutOf f.ty with
      | some l => opsLayout l f.fs
      | none => []

/-- `Frame::encode` into a buffer of `cap` bytes. -/
def Fr.encode (cap : Nat) (f : Fr) : Except CErr (List Nat) := run CErr.wire cap f.ops []

/-- The bytes of a frame. -/
def Fr.bytes (f : Fr) : List Nat :=
  if f.ty = 13 then 13 :: f.fs.length :: (lensBytes f.parts ++ f.parts.flatten) else f.ty :: encFs f.fs

/-! ## Validity -/

/-- The members of a batch: 2 to 64 non-empty frames that are not batches, within 16384 bytes. -/
def BatchOk (fs : List F) : Prop :=
  ∃ ps : List (List Nat), fs = ps.map F.raw ∧ 2 ≤ ps.length ∧ ps.length ≤ batchFrames ∧
    (∀ p ∈ ps, p ≠ [] ∧ p.head? ≠ some 13 ∧ Byte p ∧ ∃ fr, decodeNB p = .ok fr) ∧
    (ps.map List.length).sum ≤ batchBytes

/-- The fields of a DNSR: a peer, the status, and a record exactly for status 1. -/
def DnsrOk (fs : List F) : Prop :=
  match fs with
  | [F.node p, F.u8 0] | [F.node p, F.u8 2] => NodeOk p ∧ Byte p
  | [F.node p, F.u8 1, F.raw b] => NodeOk p ∧ Byte p ∧ 1 ≤ b.length ∧ b.length ≤ maxRecordLen ∧ Byte b
  | _ => False

/-- A frame the code can hold. -/
def Fr.valid (f : Fr) : Prop :=
  if f.ty = 13 then BatchOk f.fs
  else if f.ty = 15 then DnsrOk f.fs
  else match layoutOf f.ty with
    | some l => LayoutOk l f.fs
    | none => False

end Vinc.ConnCodec
