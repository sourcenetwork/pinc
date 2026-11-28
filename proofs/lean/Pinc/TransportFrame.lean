import Pinc.Axioms
import Pinc.Varint

/-!
# The PINCER frame codecs: the model

The frames of `crates/pinc-transport/src/frame/` (`mod.rs`, `decode.rs`, `encode.rs`, `ack.rs`) as total functions
over byte lists, call for call:

* the reader of `pinc-wire` (`rdVarint` is `Reader::read_varint` over `Varint.decode`, `rdBytes` is `read_bytes` and
  `read_array`, with the shortfall in `Truncated`), `Frame::decode` (`decode`: the type as a varint, then
  `decodeBody`), `Ack::parse` (`parseAck`, `ackLoop`), `decode_stream`, `Rekey::read` (`rdRekey`),
  `TicketBatch::read` (`rdTicketBatch`), the iterator `FrameIter` (`frames`) and `Ack::ranges` (`ackRanges`);
* the writer (`put` is `put_varint` over `Varint.encodeInto` and `put_slice`, each against the room left),
  `Frame::write` (`Frame.write`: `validate`, `ensure(encoded_len)`, then the puts of the frame one by one),
  `Frame::encoded_len`, `stream_overhead`, `datagram_overhead`, `ack_len` and `write_ack`.

A frame value holds what the Rust value holds: byte strings are lists of bytes, an ACK is its three head fields and
the raw bytes of its further ranges (`Ack::tail`), a REKEY its five fields, a ticket batch its entries. A `usize` is
64 bits wide, so `usize::try_from` of a varint never fails (the targets of the crate; on a narrower target the code
answers `Truncated { needed: usize::MAX }` or `TooManyRanges`, which is not modelled).

The theorems are in `TransportFrameThm.lean` (the reader, the writer, the lengths), `TransportFrameCodec.lean` (round
trip and the accepted encodings) and `TransportFrameAck.lean` (the ranges of an ACK). The TLA+ counterpart is
`proofs/tla/FrameOps.tla` with `Frame.tla`; the trace is replayed by `Pinc/TraceFrame.lean`.
-/

namespace Pinc.TransportFrame
open Pinc

/-- `FrameError`, with `WireError` flattened into it. -/
inductive Err where
  | truncated (needed : Nat)
  | tooLong
  | nonMinimal
  | overflow
  | bufferTooSmall (needed : Nat)
  | unexpected (what : String)
  | unknownType (t : Nat)
  | ack
  | tooManyRanges
  | streamEnd
  | rekeyKind
  deriving DecidableEq, Repr

/-- The `WireError` of a varint operation as a frame error. -/
def ofVarint : Varint.Error → Err
  | .tooLong => .tooLong
  | .truncated => .truncated 1
  | .nonMinimal => .nonMinimal
  | .overflow => .overflow
  | .bufferTooSmall n => .bufferTooSmall n

/-- `MAX_PN`: 2^62 - 1. -/
def maxPn : Nat := 2 ^ 62 - 1
/-- `MAX_STREAM_END`: 2^62 - 1. -/
def maxEnd : Nat := 2 ^ 62 - 1
/-- `EXTENSION_BASE`. -/
def extBase : Nat := 0x40
/-- `MAX_ACK_RANGES`. -/
def maxAckRanges : Nat := 32
/-- `MAX_BATCH` of a ticket batch. -/
def maxBatch : Nat := 4

/-- `Frame`. -/
inductive Frame where
  | padding (len : Nat)
  | ping
  | ack (largest first extra : Nat) (tail : List Nat)
  | resetStream (id error finalSize : Nat)
  | stopSending (id error : Nat)
  | stream (id offset : Nat) (fin : Bool) (data : List Nat) (implicitLen : Bool)
  | maxStreamData (id max : Nat)
  | maxStreams (lim : Nat)
  | pathChallenge (d : List Nat)
  | pathResponse (d : List Nat)
  | close (error : Nat)
  | datagram (data : List Nat) (implicitLen : Bool)
  | mtuProbeEcho (mtu : Nat)
  | sleep
  | wake
  | rekey (answer : Bool) (share echo : List Nat) (switchPn roll : Nat)
  | ready
  | newTickets (entries : List (List Nat × Nat))
  | ext (ty : Nat) (body : List Nat)
  deriving DecidableEq, Repr

/-! ## The reader -/

/-- The result of a read: the value and the bytes left. -/
abbrev Rd (α : Type) := Except Err (α × List Nat)

/-- One read, then the next on what is left (the `?` of the code). -/
def andThen {α β : Type} (x : Rd α) (f : α → List Nat → Except Err β) : Except Err β :=
  match x with
  | .error e => .error e
  | .ok (a, r) => f a r

/-- `Reader::read_varint`. -/
def rdVarint (b : List Nat) : Rd Nat :=
  match Varint.decode b with
  | .ok (v, n) => .ok (v, b.drop n)
  | .error e => .error (ofVarint e)

/-- `Reader::read_bytes(n)` and `read_array::<n>`. -/
def rdBytes (n : Nat) (b : List Nat) : Rd (List Nat) :=
  if n ≤ b.length then .ok (b.take n, b.drop n) else .error (.truncated (n - b.length))

/-- `read_len_prefixed`: a varint length, then that many bytes. -/
def rdLenPrefixed (b : List Nat) : Rd (List Nat) :=
  andThen (rdVarint b) fun n r => rdBytes n r

/-- A big-endian number (`u16::from_be_bytes`, `u32::from_be_bytes`). -/
def be (bs : List Nat) : Nat := bs.foldl (fun a x => a * 256 + x) 0

/-- The length of the run of zero bytes at the front (`position(|b| *b != 0).unwrap_or(len)`). -/
def zeroRun : List Nat → Nat
  | [] => 0
  | b :: bs => if b = 0 then zeroRun bs + 1 else 0

/-- The loop of `Ack::parse` over the further ranges: `extra` pairs `(gap, length)`, each range below the previous
one and not below packet number 0. The start of the lowest range and the bytes left. -/
def ackLoop : Nat → Nat → List Nat → Rd Nat
  | 0, ps, b => .ok (ps, b)
  | k + 1, ps, b =>
    andThen (rdVarint b) fun gap r1 =>
    andThen (rdVarint r1) fun len r2 =>
    if ps < gap + 2 then .error .ack
    else if ps - gap - 2 < len then .error .ack
    else ackLoop k (ps - gap - 2 - len) r2

/-- `Ack::parse`: the fields after the type. -/
def parseAck (r : List Nat) : Rd Frame :=
  andThen (rdVarint r) fun largest r1 =>
  if largest > maxPn then .error .ack
  else
    andThen (rdVarint r1) fun extra r2 =>
    if extra ≥ maxAckRanges then .error .tooManyRanges
    else
      andThen (rdVarint r2) fun first r3 =>
      if largest < first then .error .ack
      else
        andThen (ackLoop extra (largest - first) r3) fun _ r4 =>
        .ok (.ack largest first extra (r3.take (r3.length - r4.length)), r3.drop (r3.length - r4.length))

/-- `decode_stream`: bit 4 of the type says an offset follows, bit 2 a length, bit 1 is FIN (`t` is 8 to 15, so
`t & m != 0` for a power of two `m` is `t / m % 2 = 1`). -/
def decodeStream (t : Nat) (r : List Nat) : Rd Frame :=
  andThen (rdVarint r) fun id r1 =>
  andThen (if t / 4 % 2 = 1 then rdVarint r1 else .ok (0, r1)) fun offset r2 =>
  andThen (if t / 2 % 2 = 0 then rdBytes r2.length r2 else rdLenPrefixed r2) fun data r3 =>
  if offset + data.length > maxEnd then .error .streamEnd
  else .ok (.stream id offset (t % 2 = 1) data (t / 2 % 2 = 0), r3)

/-- `Rekey::read` under `decode_rekey`: an unknown kind is `RekeyKind`; a request carries its sender's roll count,
an answer its echo and switch packet number. -/
def rdRekey (r : List Nat) : Rd Frame :=
  andThen (rdBytes 1 r) fun k r1 =>
  if k.headD 0 > 1 then .error .rekeyKind
  else
    andThen (rdBytes 32 r1) fun share r2 =>
    if k.headD 0 = 1 then
      andThen (rdBytes 8 r2) fun echo r3 =>
      andThen (rdVarint r3) fun spn r4 => .ok (.rekey true share echo spn 0, r4)
    else andThen (rdVarint r2) fun roll r3 => .ok (.rekey false share (List.replicate 8 0) 0 roll, r3)

/-- The loop of `TicketBatch::read`: `count` entries of a 16-byte id and a big-endian `u32`. -/
def rdTickets : Nat → List Nat → Rd (List (List Nat × Nat))
  | 0, r => .ok ([], r)
  | k + 1, r =>
    andThen (rdBytes 16 r) fun tid r1 =>
    andThen (rdBytes 4 r1) fun lt r2 =>
    andThen (rdTickets k r2) fun es r3 => .ok ((tid, be lt) :: es, r3)

/-- `TicketBatch::read`. -/
def rdTicketBatch (r : List Nat) : Rd Frame :=
  andThen (rdBytes 1 r) fun c r1 =>
  if c.headD 0 > maxBatch then .error (.unexpected "ticket count")
  else andThen (rdTickets (c.headD 0) r1) fun es r2 => .ok (.newTickets es, r2)

/-- The `match` of `Frame::decode` on the type `t`, over the bytes after it. -/
def decodeBody (t : Nat) (r : List Nat) : Rd Frame :=
  if t = 0x00 then .ok (.padding (zeroRun r + 1), r.drop (zeroRun r))
  else if t = 0x01 then .ok (.ping, r)
  else if t = 0x02 then parseAck r
  else if t = 0x04 then
    andThen (rdVarint r) fun id r1 => andThen (rdVarint r1) fun e r2 => andThen (rdVarint r2) fun fs r3 =>
      .ok (.resetStream id e fs, r3)
  else if t = 0x05 then
    andThen (rdVarint r) fun id r1 => andThen (rdVarint r1) fun e r2 => .ok (.stopSending id e, r2)
  else if 0x08 ≤ t ∧ t ≤ 0x0f then decodeStream t r
  else if t = 0x11 then
    andThen (rdVarint r) fun id r1 => andThen (rdVarint r1) fun m r2 => .ok (.maxStreamData id m, r2)
  else if t = 0x12 then andThen (rdVarint r) fun l r1 => .ok (.maxStreams l, r1)
  else if t = 0x1a then andThen (rdBytes 8 r) fun d r1 => .ok (.pathChallenge d, r1)
  else if t = 0x1b then andThen (rdBytes 8 r) fun d r1 => .ok (.pathResponse d, r1)
  else if t = 0x1c then andThen (rdVarint r) fun e r1 => .ok (.close e, r1)
  else if t = 0x30 then andThen (rdBytes r.length r) fun d r1 => .ok (.datagram d true, r1)
  else if t = 0x31 then andThen (rdLenPrefixed r) fun d r1 => .ok (.datagram d false, r1)
  else if t = 0x3a then andThen (rdBytes 2 r) fun d r1 => .ok (.mtuProbeEcho (be d), r1)
  else if t = 0x3b then .ok (.sleep, r)
  else if t = 0x3c then .ok (.wake, r)
  else if t = 0x3d then rdRekey r
  else if t = 0x3e then .ok (.ready, r)
  else if t = 0x3f then rdTicketBatch r
  else if t ≥ extBase then andThen (rdLenPrefixed r) fun body r1 => .ok (.ext t body, r1)
  else .error (.unknownType t)

/-- `Frame::decode`: the frame and the bytes left, or the error. -/
def decode (b : List Nat) : Rd Frame :=
  andThen (rdVarint b) decodeBody

/-- `FrameIter`: the frames in order, and the error it ends with if any. The fuel is the length of the payload: a
frame takes at least one byte (`decode_progress`), so it never runs out (`frames_fuel`). -/
def iterFuel : Nat → List Nat → List Frame × Option Err
  | 0, _ => ([], none)
  | n + 1, b =>
    if b = [] then ([], none)
    else match decode b with
      | .error e => ([], some e)
      | .ok (f, r) => ((f :: (iterFuel n r).1), (iterFuel n r).2)

/-- `FrameIter::new(payload).collect()`. -/
def frames (b : List Nat) : List Frame × Option Err := iterFuel b.length b

/-- The loop of `AckRanges::next` over the further ranges, up to the first `None`. A range is `(start, end)`. -/
def rangesLoop : Nat → Nat → List Nat → List (Nat × Nat)
  | 0, _, _ => []
  | k + 1, ps, b =>
    match rdVarint b with
    | .error _ => []
    | .ok (gap, r1) =>
      match rdVarint r1 with
      | .error _ => []
      | .ok (len, r2) =>
        if ps < gap + 2 then []
        else if ps - gap - 2 < len then []
        else (ps - gap - 2 - len, ps - gap - 2) :: rangesLoop k (ps - gap - 2 - len) r2

/-- `Ack::ranges().collect()`: the inclusive ranges, highest first. -/
def ackRanges (largest first extra : Nat) (tail : List Nat) : List (Nat × Nat) :=
  if largest < first then rangesLoop extra largest tail
  else (largest - first, largest) :: rangesLoop extra (largest - first) tail

/-! ## The writer -/

/-- One call of the writer: `put_varint` or `put_slice`. -/
inductive Put where
  | v (x : Nat)
  | s (bs : List Nat)
  deriving DecidableEq, Repr

/-- `Writer::put_varint` and `put_slice` on a writer that holds `w` in a buffer of `cap` bytes: the bytes it holds
afterwards, or the error, which leaves it as it was. -/
def put (cap : Nat) (w : List Nat) : Put → Except Err (List Nat)
  | .v x =>
    match Varint.encodeInto (cap - w.length) x with
    | .ok bs => .ok (w ++ bs)
    | .error e => .error (ofVarint e)
  | .s bs =>
    if bs.length ≤ cap - w.length then .ok (w ++ bs) else .error (.bufferTooSmall (bs.length - (cap - w.length)))

/-- The calls in order, stopping at the first error. -/
def runPuts (cap : Nat) : List Nat → List Put → Except Err (List Nat)
  | w, [] => .ok w
  | w, p :: ps =>
    match put cap w p with
    | .error e => .error e
    | .ok w' => runPuts cap w' ps

/-- `u16::to_be_bytes`. -/
def be16 (v : Nat) : List Nat := [v / 256 % 256, v % 256]
/-- `u32::to_be_bytes`. -/
def be32 (v : Nat) : List Nat := [v / 16777216 % 256, v / 65536 % 256, v / 256 % 256, v % 256]

/-- The loop of `Frame::write` for PADDING: zero bytes in pieces of at most 64. -/
def zeroChunks (len : Nat) : List Put :=
  if len = 0 then [] else .s (List.replicate (min len 64) 0) :: zeroChunks (len - min len 64)
termination_by len
decreasing_by omega

/-- The type of a STREAM frame: `STREAM | flags`, the OFF bit exactly when the offset is not 0. -/
def streamType (offset : Nat) (fin implicitLen : Bool) : Nat :=
  8 + (if offset = 0 then 0 else 4) + (if implicitLen then 0 else 2) + (if fin then 1 else 0)

/-- The calls `Frame::write` makes on the writer once the frame and the room were checked. -/
def Frame.puts : Frame → List Put
  | .padding len => zeroChunks len
  | .ping => [.v 0x01]
  | .ack l f x tail => [.v 0x02, .v l, .v x, .v f, .s tail]
  | .resetStream id e fs => [.v 0x04, .v id, .v e, .v fs]
  | .stopSending id e => [.v 0x05, .v id, .v e]
  | .stream id off fin data imp =>
    [.v (streamType off fin imp), .v id] ++ (if off = 0 then [] else [.v off])
      ++ (if imp then [.s data] else [.v data.length, .s data])
  | .maxStreamData id m => [.v 0x11, .v id, .v m]
  | .maxStreams l => [.v 0x12, .v l]
  | .pathChallenge d => [.v 0x1a, .s d]
  | .pathResponse d => [.v 0x1b, .s d]
  | .close e => [.v 0x1c, .v e]
  | .datagram d imp => if imp then [.v 0x30, .s d] else [.v 0x31, .v d.length, .s d]
  | .mtuProbeEcho m => [.v 0x3a, .s (be16 m)]
  | .sleep => [.v 0x3b]
  | .wake => [.v 0x3c]
  | .rekey a sh echo spn roll =>
    [.v 0x3d, .s [if a then 1 else 0], .s sh] ++ (if a then [.s echo, .v spn] else [.v roll])
  | .ready => [.v 0x3e]
  | .newTickets es => [.v 0x3f, .s [es.length]] ++ es.flatMap (fun e => [.s e.1, .s (be32 e.2)])
  | .ext ty body => [.v ty, .v body.length, .s body]

/-- `stream_overhead`. -/
def streamOverhead (id offset dataLen : Nat) (implicitLen : Bool) : Nat :=
  1 + Varint.encodedLen id + (if offset = 0 then 0 else Varint.encodedLen offset) + (if implicitLen then 0 else Varint.encodedLen dataLen)

/-- `datagram_overhead`. -/
def datagramOverhead (dataLen : Nat) (implicitLen : Bool) : Nat :=
  1 + (if implicitLen then 0 else Varint.encodedLen dataLen)

/-- `Frame::encoded_len`. -/
def Frame.encodedLen : Frame → Nat
  | .padding len => len
  | .ping | .sleep | .wake | .ready => 1
  | .ack l f x tail => 1 + (Varint.encodedLen l + Varint.encodedLen x + Varint.encodedLen f + tail.length)
  | .resetStream id e fs => 1 + Varint.encodedLen id + Varint.encodedLen e + Varint.encodedLen fs
  | .stream id off _ data imp => streamOverhead id off data.length imp + data.length
  | .maxStreamData id v | .stopSending id v => 1 + Varint.encodedLen id + Varint.encodedLen v
  | .pathChallenge _ | .pathResponse _ => 1 + 8
  | .close e => 1 + Varint.encodedLen e
  | .maxStreams l => 1 + Varint.encodedLen l
  | .datagram d imp => datagramOverhead d.length imp + d.length
  | .mtuProbeEcho _ => 1 + 2
  | .rekey a _ _ spn roll => 1 + 1 + 32 + (if a then 8 + Varint.encodedLen spn else Varint.encodedLen roll)
  | .newTickets es => 1 + 1 + es.length * 20
  | .ext ty body => Varint.encodedLen ty + (Varint.encodedLen body.length + body.length)

/-- `varint_fields`: the varint fields `validate` checks, zero if unused. -/
def Frame.varintFields : Frame → List Nat
  | .resetStream id e fs => [id, e, fs]
  | .maxStreamData id v | .stopSending id v => [id, v, 0]
  | .stream id off _ _ _ => [id, off, 0]
  | .close v | .ext v _ | .maxStreams v => [v, 0, 0]
  | .rekey _ _ _ spn roll => [spn, roll, 0]
  | _ => [0, 0, 0]

/-- `Frame::validate`. -/
def Frame.validate (f : Frame) : Except Err Unit :=
  if f.varintFields.any (fun v => decide (v ≥ Varint.limit)) then .error .overflow
  else match f with
    | .stream _ off _ data _ => if off + data.length > maxEnd then .error .streamEnd else .ok ()
    | .ext ty _ => if ty < extBase then .error (.unknownType ty) else .ok ()
    | _ => .ok ()

/-- `Frame::write` on a writer that holds `w` in a buffer of `cap` bytes. -/
def Frame.write (cap : Nat) (w : List Nat) (f : Frame) : Except Err (List Nat) :=
  match f.validate with
  | .error e => .error e
  | .ok () =>
    if f.encodedLen ≤ cap - w.length then runPuts cap w f.puts
    else .error (.bufferTooSmall (f.encodedLen - (cap - w.length)))

/-- The bytes of the calls when none fails. -/
def flat : List Put → List Nat
  | [] => []
  | .v x :: ps => Varint.encodeBytes x ++ flat ps
  | .s bs :: ps => bs ++ flat ps

/-- The encoding of a frame: the bytes `write` appends when it succeeds (`write_eq`). -/
def Frame.bytes (f : Frame) : List Nat := flat f.puts

/-! ## The ACK encoder -/

/-- One item of `wire_fields` for the range `s..=e`: `(largest, first_range)` for the first range, `(gap, length)`
for a later one, `prev` being the start of the range before it. -/
def wireItem (prev : Option Nat) (s e : Nat) : Except Err (Nat × Nat) :=
  if s > e ∨ e > maxPn then .error .ack
  else match prev with
    | none => .ok (e, e - s)
    | some p => if p < e + 2 then .error .ack else .ok (p - e - 2, e - s)

/-- `wire_fields` walked to its end or its first error (the ranges were already cut to `MAX_ACK_RANGES`). -/
def wireFields : Option Nat → List (Nat × Nat) → Except Err (List (Nat × Nat))
  | _, [] => .ok []
  | prev, r :: rs =>
    match wireItem prev r.1 r.2 with
    | .error e => .error e
    | .ok it =>
      match wireFields (some r.1) rs with
      | .error e => .error e
      | .ok its => .ok (it :: its)

/-- The bytes of the further ranges. -/
def pairBytes : List (Nat × Nat) → List Nat
  | [] => []
  | (a, b) :: its => Varint.encodeBytes a ++ Varint.encodeBytes b ++ pairBytes its

/-- The encoded size of the further ranges. -/
def pairLen : List (Nat × Nat) → Nat
  | [] => 0
  | (a, b) :: its => Varint.encodedLen a + Varint.encodedLen b + pairLen its

/-- `shape`: how many ranges will be written and the size after the type. -/
def ackShape (rs : List (Nat × Nat)) : Except Err (Nat × Nat) :=
  match wireFields none (rs.take maxAckRanges) with
  | .error e => .error e
  | .ok [] => .error .ack
  | .ok ((l, f) :: its) => .ok (its.length + 1, pairLen its + (Varint.encodedLen l + Varint.encodedLen its.length + Varint.encodedLen f))

/-- `ack_len`. -/
def ackLen (rs : List (Nat × Nat)) : Except Err Nat :=
  match ackShape rs with
  | .error e => .error e
  | .ok (_, body) => .ok (1 + body)

/-- The calls `write_ack` makes once the ranges and the room were checked. -/
def ackPuts (l f : Nat) (its : List (Nat × Nat)) : List Put :=
  [.v 0x02, .v l, .v its.length, .v f] ++ its.flatMap (fun p => [.v p.1, .v p.2])

/-- `write_ack` on a writer that holds `w` in a buffer of `cap` bytes. -/
def writeAck (cap : Nat) (w : List Nat) (rs : List (Nat × Nat)) : Except Err (List Nat) :=
  match ackShape rs with
  | .error e => .error e
  | .ok (_, body) =>
    if 1 + body ≤ cap - w.length then
      match wireFields none (rs.take maxAckRanges) with
      | .ok ((l, f) :: its) => runPuts cap w (ackPuts l f its)
      | _ => .error .ack
    else .error (.bufferTooSmall (1 + body - (cap - w.length)))

/-! ## The names of the errors in the trace -/

/-- The name and the number the trace records for an error. -/
def Err.tag : Err → String × Nat
  | .truncated n => ("Truncated", n)
  | .tooLong => ("VarintTooLong", 0)
  | .nonMinimal => ("VarintNonMinimal", 0)
  | .overflow => ("VarintOverflow", 0)
  | .bufferTooSmall n => ("BufferTooSmall", n)
  | .unexpected w => (w, 0)
  | .unknownType t => ("UnknownType", t)
  | .ack => ("Ack", 0)
  | .tooManyRanges => ("TooManyRanges", 0)
  | .streamEnd => ("StreamEnd", 0)
  | .rekeyKind => ("RekeyKind", 0)

end Pinc.TransportFrame
