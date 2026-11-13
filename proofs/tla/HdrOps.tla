------------------------------- MODULE HdrOps -------------------------------
(***************************************************************************)
(* The packet header codecs of vinc-transport, step for step:              *)
(* packet/header.rs (LongHeader::write and parse, ShortHeader::write,      *)
(* short_dcid), the first byte unprotect_header reads once the mask is     *)
(* off, packet/datagram.rs (the iterator Packets::next run to its end) and *)
(* the split of a packet into associated data, payload and tag that seal   *)
(* and open of packet/protect.rs make. Hdr.tla checks them; TraceHdr.tla   *)
(* replays the recorded calls of the real code.                            *)
(*                                                                         *)
(* Bytes are integers 0..255 and a buffer is a sequence. The masks of the  *)
(* code are written as arithmetic on the byte: `first & 0xC0 == 0xC0` is   *)
(* first \div 64 = 3, `(first >> 4) & 3` is (first \div 16) % 4,           *)
(* `first & 0x0f` is first % 16, `first & 0xE0 == 0x40` is                 *)
(* first \div 32 = 2, `first & 0x0C` is (first \div 4) % 4, `first & 3` is *)
(* first % 4, `first & 0x10` is (first \div 16) % 2 and `first & 0x80` is  *)
(* first \div 128. The body length is a u64 word of U64.tla, so the varint *)
(* is the Encode and Decode of Varint.tla and a length of 2^63 or more is  *)
(* in the model.                                                           *)
(*                                                                         *)
(* A write is modelled put by put on a writer of `cap` bytes: the result   *)
(* holds the error of the first put that failed and the bytes written      *)
(* before it, so "a refused write writes nothing" is a statement about the *)
(* result. Late = FALSE is the code. Late = TRUE is LongHeader::write as   *)
(* it was before the body length was checked first: header_len counts ten  *)
(* bytes for a length no varint holds, the room check passes and the       *)
(* length is refused after the bytes before it were written                *)
(* (Hdr_late.cfg must violate WriteAtomic).                                *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/TransportHdr.lean.                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Late

V == INSTANCE Varint WITH SmallMax <- 0, c <- 0
U == INSTANCE U64

VERSION == 1
MAXCID == 20
TAGLEN == 16
SAMPLESKIP == 4

Err(e, n) == [err |-> e, n |-> n]

(* ---- the writer: the error of the first failed put and the bytes written before it ---- *)
W0 == [err |-> "ok", n |-> 0, out |-> <<>>]
PutSlice(cap, w, bs) ==
    IF w.err # "ok" THEN w
    ELSE IF Len(bs) <= cap - Len(w.out) THEN [w EXCEPT !.out = w.out \o bs]
    ELSE [w EXCEPT !.err = "BufferTooSmall", !.n = Len(bs) - (cap - Len(w.out))]
(* put_u8(u8::try_from(len).map_err(ConnIdLength)?) *)
PutLen(cap, w, len) ==
    IF w.err # "ok" THEN w
    ELSE IF len <= 255 THEN PutSlice(cap, w, <<len>>) ELSE [w EXCEPT !.err = "ConnIdLength"]
PutVarint(cap, w, v) ==
    IF w.err # "ok" THEN w
    ELSE LET e == V!Encode(v, cap - Len(w.out))
         IN IF e.kind = "ok" THEN [w EXCEPT !.out = w.out \o e.bytes]
            ELSE IF e.kind = "overflow" THEN [w EXCEPT !.err = "VarintOverflow"]
            ELSE [w EXCEPT !.err = "BufferTooSmall", !.n = e.needed]

(* ---- the long header: h = [ty (0 Handshake, 1 ZeroRtt), dcid, scid, bl (a word)] ---- *)
HeaderLen(h) == 1 + 1 + 1 + Len(h.dcid) + 1 + Len(h.scid) + V!EncodedLen(h.bl)
(* the low four bits write chooses, -1 for a pn_len that does not fit the type *)
LowBits(ty, pnLen) ==
    IF ty = 1 THEN (IF pnLen = 2 THEN pnLen - 1 ELSE -1) ELSE (IF pnLen = 0 THEN 0 ELSE -1)
FirstLong(ty, low) == 192 + 16 * ty + low
LongPuts(h, low, cap) ==
    PutVarint(cap,
        PutSlice(cap,
            PutLen(cap,
                PutSlice(cap,
                    PutLen(cap, PutSlice(cap, PutSlice(cap, W0, <<FirstLong(h.ty, low)>>), <<VERSION>>), Len(h.dcid)),
                    h.dcid),
                Len(h.scid)),
            h.scid),
        h.bl)
LongWrite(h, pnLen, cap) ==
    LET low == LowBits(h.ty, pnLen)
    IN IF low < 0 THEN [err |-> "PnLength", n |-> 0, out |-> <<>>]
       ELSE IF ~Late /\ ~U!Lt(h.bl, V!Limit) THEN [err |-> "VarintOverflow", n |-> 0, out |-> <<>>]
       ELSE IF cap < HeaderLen(h) THEN [err |-> "BufferTooSmall", n |-> HeaderLen(h) - cap, out |-> <<>>]
       ELSE LongPuts(h, low, cap)

(* read_cid: the id and the rest *)
ReadCid(r) ==
    IF Len(r) = 0 THEN Err("Truncated", 1)
    ELSE LET len == r[1]
             rest == Tail(r)
         IN IF len > MAXCID THEN Err("ConnIdLength", 0)
            ELSE IF Len(rest) < len THEN Err("Truncated", len - Len(rest))
            ELSE [err |-> "ok", n |-> 0, id |-> SubSeq(rest, 1, len), rest |-> SubSeq(rest, len + 1, Len(rest))]

VarErr(kind) ==
    IF kind = "toolong" THEN Err("VarintTooLong", 0)
    ELSE IF kind = "nonminimal" THEN Err("VarintNonMinimal", 0)
    ELSE Err("Truncated", 1)

(* LongHeader::parse: the header and its encoded size hl *)
LongParse(p) ==
    IF Len(p) = 0 THEN Err("Truncated", 1)
    ELSE LET first == p[1]
         IN IF first \div 64 # 3 THEN Err("Form", 0)
            ELSE IF (first \div 16) % 4 > 1 THEN Err("LongType", 0)
            ELSE LET ty == (first \div 16) % 4
                 IN IF ty # 1 /\ first % 16 # 0 THEN Err("Reserved", 0)
                    ELSE IF Len(p) < 2 THEN Err("Truncated", 1)
                    ELSE IF p[2] # VERSION THEN Err("Version", p[2])
                    ELSE LET d == ReadCid(SubSeq(p, 3, Len(p)))
                         IN IF d.err # "ok" THEN Err(d.err, d.n)
                            ELSE LET s == ReadCid(d.rest)
                                 IN IF s.err # "ok" THEN Err(s.err, s.n)
                                    ELSE LET v == V!Decode(s.rest)
                                         IN IF v.kind # "ok" THEN VarErr(v.kind)
                                            ELSE IF U!Lt(U!W(Len(s.rest) - v.n), v.v) THEN Err("Length", 0)
                                            ELSE [err |-> "ok", n |-> 0, ty |-> ty, dcid |-> d.id, scid |-> s.id,
                                                  bl |-> v.v, hl |-> 1 + 1 + (1 + Len(d.id)) + (1 + Len(s.id)) + v.n]

(* ---- the short header: h = [kp, dcid] and the truncated packet number pn ---- *)
ShortHeaderLen(dl, pl) == 1 + dl + pl
FirstShort(kp, pl) == 64 + (IF kp THEN 16 ELSE 0) + (pl - 1)
ShortWrite(h, pn, cap) ==
    IF ~(2 <= Len(pn) /\ Len(pn) <= 3) THEN [err |-> "PnLength", n |-> 0, out |-> <<>>]
    ELSE IF cap < ShortHeaderLen(Len(h.dcid), Len(pn))
    THEN [err |-> "BufferTooSmall", n |-> ShortHeaderLen(Len(h.dcid), Len(pn)) - cap, out |-> <<>>]
    ELSE PutSlice(cap, PutSlice(cap, PutSlice(cap, W0, <<FirstShort(h.kp, Len(pn))>>), h.dcid), pn)

ShortDcid(p, dl) ==
    IF dl > MAXCID THEN Err("ConnIdLength", 0)
    ELSE IF Len(p) = 0 THEN Err("TooShort", 0)
    ELSE IF p[1] \div 32 # 2 THEN Err("Form", 0)
    ELSE IF Len(p) - 1 < dl THEN Err("TooShort", 0)
    ELSE [err |-> "ok", n |-> 0, id |-> SubSeq(p, 2, dl + 1)]

(* what unprotect_header reads from the first byte once the mask is off *)
ReadFirst(first) ==
    IF (first \div 4) % 4 # 0 THEN Err("Reserved", 0)
    ELSE [err |-> "ok", n |-> 0, pl |-> (first % 4) + 1, kp |-> (first \div 16) % 2 = 1]

(* ---- datagrams: Packets::next until None; the rest starts at offset off ---- *)
RECURSIVE PacketsFrom(_, _, _)
PacketsFrom(d, off, dl) ==
    LET rest == SubSeq(d, off + 1, Len(d))
    IN IF Len(rest) = 0 THEN <<>>
       ELSE IF rest[1] = 0
       THEN (IF \E k \in 1..Len(rest) : rest[k] # 0 THEN <<[k |-> "err", err |-> "Form", n |-> 0, s |-> off]>> ELSE <<>>)
       ELSE IF rest[1] \div 128 = 0
       THEN LET r == ShortDcid(rest, dl)
            IN IF r.err = "ok" THEN <<[k |-> "short", dcid |-> r.id, s |-> off, len |-> Len(rest)]>>
               ELSE <<[k |-> "err", err |-> r.err, n |-> r.n, s |-> off]>>
       ELSE LET r == LongParse(rest)
            IN IF r.err # "ok" THEN <<[k |-> "err", err |-> r.err, n |-> r.n, s |-> off]>>
               \* split_at_mut_checked: None ends the iteration
               ELSE IF U!Lt(U!W(Len(rest) - r.hl), r.bl) THEN <<>>
               ELSE <<[k |-> "long", ty |-> r.ty, dcid |-> r.dcid, scid |-> r.scid, bl |-> r.bl, hl |-> r.hl,
                       s |-> off, len |-> r.hl + U!Val(r.bl)]>>
                    \o PacketsFrom(d, off + r.hl + U!Val(r.bl), dl)
Packets(d, dl) == PacketsFrom(d, 0, dl)

(* Packet::pn_off *)
PnOff(it) == IF it.k = "long" THEN it.hl ELSE 1 + Len(it.dcid)

(* ---- the associated data: the split seal and open make before they call the record layer ---- *)
SealParts(packet, pnOff, pnLen, payloadLen) ==
    IF pnLen + payloadLen < SAMPLESKIP THEN Err("TooShort", 0)
    ELSE LET hl == pnOff + pnLen
             total == hl + payloadLen + TAGLEN
         IN IF Len(packet) < total THEN Err("BufferTooSmall", total - Len(packet))
            ELSE [err |-> "ok", n |-> 0, aad |-> SubSeq(packet, 1, hl), ps |-> hl, pe |-> hl + payloadLen, total |-> total]
OpenParts(packet, pnOff, pnLen) ==
    LET hl == pnOff + pnLen
    IN IF Len(packet) < hl THEN Err("TooShort", 0)
       ELSE IF Len(packet) - hl < TAGLEN THEN Err("TooShort", 0)
       ELSE [err |-> "ok", n |-> 0, aad |-> SubSeq(packet, 1, hl), ps |-> hl, pe |-> Len(packet) - TAGLEN,
             total |-> Len(packet)]

(***************************************************************************)
(* The body of a Handshake packet (conn/send.rs write_handshake, conn/     *)
(* handshake.rs on_fragment): varint(total) varint(off) fragment. total    *)
(* and off are u64 words of U64.tla; data is the fragment.                 *)
(***************************************************************************)
R == INSTANCE ReasmOps

HsEnc(v) == V!Encode(v, 16).bytes
HsBody(total, off, data) == HsEnc(total) \o HsEnc(off) \o data
HsBodyLen(total, off, n) == V!EncodedLen(total) + V!EncodedLen(off) + n
(* the header write_handshake writes: a Handshake long header whose body length counts the three parts *)
HsHeader(dcid, scid, total, off, n) == [ty |-> 0, dcid |-> dcid, scid |-> scid, bl |-> U!W(HsBodyLen(total, off, n))]
(* header.write(&mut w, 0).is_ok() && put_varint(total) && put_varint(off) && put_slice(bytes), on one writer of
   cap bytes (the window); the code returns 0 if one failed, so the result is a datagram only if err = "ok" *)
HsWrite(dcid, scid, total, off, data, cap) ==
    PutSlice(cap, PutVarint(cap, PutVarint(cap, LongWrite(HsHeader(dcid, scid, total, off, Len(data)), 0, cap), total), off), data)
(* what write_handshake needs of the window for the fragment: the whole header, both varints, the bytes *)
HsNeed(dcid, scid, total, off, n) == HeaderLen(HsHeader(dcid, scid, total, off, n)) + V!EncodedLen(total) + V!EncodedLen(off) + n
(* the room write_handshake leaves for the fragment: the window less the fixed part of the header, two bytes for
   the body length and both varints (fragment_overhead) at the size of the offset the fragment starts at *)
HsRoom(win, dl, sl, total, off) ==
    LET fixed == 1 + 1 + 1 + dl + 1 + sl + 2 + V!EncodedLen(total) + V!EncodedLen(off)
    IN IF win > fixed THEN win - fixed ELSE 0

(* on_fragment's parse: the two varints (usize::try_from is the identity on a u64 here) and the rest *)
HsRead(body) ==
    LET v1 == V!Decode(body)
    IN IF v1.kind # "ok" THEN [ok |-> FALSE]
       ELSE LET rest == SubSeq(body, v1.n + 1, Len(body))
                v2 == V!Decode(rest)
            IN IF v2.kind # "ok" THEN [ok |-> FALSE]
               ELSE [ok |-> TRUE, total |-> v1.v, off |-> v2.v, data |-> SubSeq(rest, v2.n + 1, Len(rest))]

(* on_fragment then Reassembly::add with the length of the fragment. The two words are clamped to the integers
   ReasmOps takes without changing what Add does: a total above mx is refused whatever it is, and an offset at or
   past the total gives the same result whatever it is (the stop is the total, which is not past the offset). *)
HsRecv(r, mx, nr, body) ==
    LET p == HsRead(body)
    IN IF ~p.ok THEN [out |-> -1, r |-> r]
       ELSE LET tI == IF U!Lt(p.total, U!W(mx + 1)) THEN U!Val(p.total) ELSE mx + 1
                oI == IF U!Lt(p.off, U!W(tI)) THEN U!Val(p.off) ELSE tI
            IN R!Add(r, mx, nr, tI, oI, Len(p.data))

(***************************************************************************)
(* pad_to (packet/datagram.rs): zero bytes appended in chunks of 64 until  *)
(* the writer, which holds out and has room for cap bytes, holds min_len;  *)
(* ensure(left) comes first, so a refusal writes nothing. PadToLate is     *)
(* the call without that check (chunk after chunk until one does not fit): *)
(* it leaves a part of the padding behind.                                 *)
(***************************************************************************)
Zeros(n) == [i \in 1..n |-> 0]
RECURSIVE PadLoop(_, _)
PadLoop(left, out) ==
    IF left = 0 THEN out
    ELSE LET n == IF left < 64 THEN left ELSE 64 IN PadLoop(left - n, out \o Zeros(n))
PadTo(cap, minLen, out) ==
    LET left == IF minLen > Len(out) THEN minLen - Len(out) ELSE 0
        room == cap - Len(out)
    IN IF left > room THEN [err |-> "BufferTooSmall", n |-> left - room, out |-> out]
       ELSE [err |-> "ok", n |-> 0, out |-> PadLoop(left, out)]
RECURSIVE PadLoopLate(_, _, _)
PadLoopLate(cap, left, out) ==
    IF left = 0 THEN [err |-> "ok", n |-> 0, out |-> out]
    ELSE LET n == IF left < 64 THEN left ELSE 64
         IN IF Len(out) + n > cap
            THEN [err |-> "BufferTooSmall", n |-> Len(out) + n - cap, out |-> out]
            ELSE PadLoopLate(cap, left - n, out \o Zeros(n))
PadToLate(cap, minLen, out) ==
    PadLoopLate(cap, IF minLen > Len(out) THEN minLen - Len(out) ELSE 0, out)

(***************************************************************************)
(* sample_at (packet/protect.rs): the 16 bytes from pn_off + SAMPLE_SKIP,  *)
(* or TooShort. SampleAtSkip takes the skip so that a skip that is not the *)
(* one of the code can be shown wrong (HdrBody_skip3.cfg).                 *)
(***************************************************************************)
SAMPLELEN == 16
SampleAtSkip(p, po, skip) ==
    IF po + skip + SAMPLELEN <= Len(p)
    THEN [err |-> "ok", n |-> 0, s |-> SubSeq(p, po + skip + 1, po + skip + SAMPLELEN)]
    ELSE Err("TooShort", 0)
SampleAt(p, po) == SampleAtSkip(p, po, SAMPLESKIP)
=============================================================================
