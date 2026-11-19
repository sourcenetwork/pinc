------------------------------ MODULE FrameOps ------------------------------
(***************************************************************************)
(* The PINCER frame codecs of pinc-transport (frame/mod.rs, decode.rs,     *)
(* encode.rs, ack.rs) as operators over byte sequences, call for call.     *)
(*                                                                         *)
(* The reader is the one of pinc-wire: RdVarint (Reader::read_varint over  *)
(* varint::decode: at most MAXLEN bytes, VarintTooLong, VarintNonMinimal,  *)
(* Truncated with 1), RdBytes (read_bytes and read_array: Truncated with   *)
(* the shortfall) and RdLenPrefixed. Decode is Frame::decode: the type as  *)
(* a varint, then DecodeBody, the match on the type, with ParseAck         *)
(* (Ack::parse), DecodeStream, RdRekey (Rekey::read under decode_rekey)    *)
(* and RdTicketBatch (TicketBatch::read). Iter is FrameIter, AckRanges is  *)
(* Ack::ranges.                                                            *)
(*                                                                         *)
(* The writer runs the calls of a frame in order against a buffer of cap   *)
(* bytes: Put is put_varint (VarintOverflow from LIMIT, BufferTooSmall     *)
(* with the shortfall) or put_slice. Write is Frame::write: Validate, the  *)
(* room check against EncodedLen, then the calls. AckLen and WriteAck are  *)
(* ack_len and write_ack over WireFields, the ranges cut to MAXRANGES.     *)
(*                                                                         *)
(* A result is [ok |-> TRUE, v, r] (the value and the bytes left) or       *)
(* [ok |-> FALSE, e, n]: the name of the error and its number (the         *)
(* shortfall of Truncated and BufferTooSmall, the type of UnknownType,     *)
(* else 0). A frame is a record whose field k names its kind; an ACK holds *)
(* its three head fields and the raw bytes of its further ranges, a ticket *)
(* its id and its lifetime as two 16-bit halves (TLC integers are 32 bits  *)
(* wide).                                                                  *)
(*                                                                         *)
(* The code's constants are MAXLEN = 9, LIMIT = 2^63, MAXPN = MAXEND =     *)
(* 2^62 - 1 and MAXRANGES = 32. The model check (Frame.tla) runs the same  *)
(* operators with a varint of at most 2 bytes and LIMIT = 2^14, so every   *)
(* bound is reached inside TLC's integers; the trace check runs them with  *)
(* MAXLEN = 9 on the recorded calls whose numbers stay below 2^28, and the *)
(* Lean replay takes every call at full width. MINIMAL is TRUE in the      *)
(* code: FALSE is the wrong rule of a witness (a varint with a redundant   *)
(* zero byte accepted).                                                    *)
(*                                                                         *)
(* Lean counterpart: Pinc/TransportFrame.lean (the same functions over     *)
(* unbounded naturals), with the theorems of TransportFrameThm.lean,       *)
(* TransportFrameCodec.lean and TransportFrameAck.lean.                    *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS MAXLEN, LIMIT, MAXPN, MAXEND, MAXRANGES, MINIMAL

Ok(v, r) == [ok |-> TRUE, v |-> v, r |-> r]
Er(e, n) == [ok |-> FALSE, e |-> e, n |-> n]
Take(b, n) == SubSeq(b, 1, n)
Drop(b, n) == SubSeq(b, n + 1, Len(b))
Min(a, b) == IF a < b THEN a ELSE b

(* ---- varints (pinc-wire varint.rs) ---- *)
RECURSIVE VLen(_)
VLen(v) == IF v < 128 THEN 1 ELSE 1 + VLen(v \div 128)
RECURSIVE VEnc(_)
VEnc(v) == IF v < 128 THEN <<v>> ELSE <<(v % 128) + 128>> \o VEnc(v \div 128)

\* the loop of decode over the first MAXLEN bytes: i is the byte, mult is 128^(i-1)
RECURSIVE VLoop(_, _, _, _)
VLoop(b, i, value, mult) ==
    IF i > Len(b) \/ i > MAXLEN
    THEN IF Len(b) >= MAXLEN THEN Er("VarintTooLong", 0) ELSE Er("Truncated", 1)
    ELSE LET v2 == value + (b[i] % 128) * mult IN
         IF b[i] < 128
         THEN IF MINIMAL /\ b[i] = 0 /\ i > 1 THEN Er("VarintNonMinimal", 0) ELSE Ok(v2, i)
         ELSE VLoop(b, i + 1, v2, mult * 128)

(* ---- the reader ---- *)
RdVarint(b) == LET d == VLoop(b, 1, 0, 1) IN IF d.ok THEN Ok(d.v, Drop(b, d.r)) ELSE d
RdBytes(n, b) == IF n <= Len(b) THEN Ok(Take(b, n), Drop(b, n)) ELSE Er("Truncated", n - Len(b))
RdLenPrefixed(b) == LET n == RdVarint(b) IN IF ~n.ok THEN n ELSE RdBytes(n.v, n.r)

RECURSIVE ZeroRun(_)
ZeroRun(b) == IF Len(b) = 0 \/ b[1] # 0 THEN 0 ELSE 1 + ZeroRun(Tail(b))

(* ---- ACK ---- *)
\* the loop of Ack::parse: k further ranges below the range that starts at ps
RECURSIVE AckLoop(_, _, _)
AckLoop(k, ps, b) ==
    IF k = 0 THEN Ok(ps, b)
    ELSE LET g == RdVarint(b) IN
         IF ~g.ok THEN g
         ELSE LET l == RdVarint(g.r) IN
              IF ~l.ok THEN l
              ELSE IF ps < g.v + 2 THEN Er("Ack", 0)
              ELSE IF ps - g.v - 2 < l.v THEN Er("Ack", 0)
              ELSE AckLoop(k - 1, ps - g.v - 2 - l.v, l.r)

ParseAck(r) ==
    LET a == RdVarint(r) IN
    IF ~a.ok THEN a
    ELSE IF a.v > MAXPN THEN Er("Ack", 0)
    ELSE LET x == RdVarint(a.r) IN
         IF ~x.ok THEN x
         ELSE IF x.v >= MAXRANGES THEN Er("TooManyRanges", 0)
         ELSE LET f == RdVarint(x.r) IN
              IF ~f.ok THEN f
              ELSE IF a.v < f.v THEN Er("Ack", 0)
              ELSE LET t == AckLoop(x.v, a.v - f.v, f.r) IN
                   IF ~t.ok THEN t
                   ELSE LET n == Len(f.r) - Len(t.r) IN
                        Ok([k |-> "Ack", largest |-> a.v, first |-> f.v, extra |-> x.v, tail |-> Take(f.r, n)],
                           Drop(f.r, n))

\* the loop of AckRanges::next, up to its first None; a range is <<start, end>>
RECURSIVE RangesLoop(_, _, _)
RangesLoop(k, ps, b) ==
    IF k = 0 THEN <<>>
    ELSE LET g == RdVarint(b) IN
         IF ~g.ok THEN <<>>
         ELSE LET l == RdVarint(g.r) IN
              IF ~l.ok THEN <<>>
              ELSE IF ps < g.v + 2 THEN <<>>
              ELSE IF ps - g.v - 2 < l.v THEN <<>>
              ELSE <<<<ps - g.v - 2 - l.v, ps - g.v - 2>>>> \o RangesLoop(k - 1, ps - g.v - 2 - l.v, l.r)

AckRanges(f) ==
    IF f.largest < f.first THEN RangesLoop(f.extra, f.largest, f.tail)
    ELSE <<<<f.largest - f.first, f.largest>>>> \o RangesLoop(f.extra, f.largest - f.first, f.tail)

(* ---- the other frames ---- *)
\* decode_stream: t is 8 to 15; bit 4 an offset follows, bit 2 a length follows, bit 1 FIN
DecodeStream(t, r) ==
    LET id == RdVarint(r) IN
    IF ~id.ok THEN id
    ELSE LET off == IF (t \div 4) % 2 = 1 THEN RdVarint(id.r) ELSE Ok(0, id.r) IN
         IF ~off.ok THEN off
         ELSE LET imp == (t \div 2) % 2 = 0
                  d == IF imp THEN RdBytes(Len(off.r), off.r) ELSE RdLenPrefixed(off.r) IN
              IF ~d.ok THEN d
              ELSE IF off.v + Len(d.v) > MAXEND THEN Er("StreamEnd", 0)
              ELSE Ok([k |-> "Stream", id |-> id.v, off |-> off.v, fin |-> (t % 2 = 1), data |-> d.v, imp |-> imp],
                      d.r)

Zeros(n) == [i \in 1..n |-> 0]

RdRekey(r) ==
    LET kb == RdBytes(1, r) IN
    IF ~kb.ok THEN kb
    ELSE IF kb.v[1] > 1 THEN Er("RekeyKind", 0)
    ELSE LET sh == RdBytes(32, kb.r) IN
         IF ~sh.ok THEN sh
         ELSE IF kb.v[1] = 1
              THEN LET echo == RdBytes(8, sh.r) IN
                   IF ~echo.ok THEN echo
                   ELSE LET spn == RdVarint(echo.r) IN
                        IF ~spn.ok THEN spn
                        ELSE Ok([k |-> "Rekey", ans |-> TRUE, sh |-> sh.v, echo |-> echo.v, spn |-> spn.v], spn.r)
              ELSE Ok([k |-> "Rekey", ans |-> FALSE, sh |-> sh.v, echo |-> Zeros(8), spn |-> 0], sh.r)

\* a ticket lifetime: the big-endian u32 as its two 16-bit halves
Halves(d) == <<d[1] * 256 + d[2], d[3] * 256 + d[4]>>
RECURSIVE RdTickets(_, _)
RdTickets(k, r) ==
    IF k = 0 THEN Ok(<<>>, r)
    ELSE LET tid == RdBytes(16, r) IN
         IF ~tid.ok THEN tid
         ELSE LET lt == RdBytes(4, tid.r) IN
              IF ~lt.ok THEN lt
              ELSE LET es == RdTickets(k - 1, lt.r) IN
                   IF ~es.ok THEN es ELSE Ok(<<[tid |-> tid.v, lt |-> Halves(lt.v)]>> \o es.v, es.r)

RdTicketBatch(r) ==
    LET c == RdBytes(1, r) IN
    IF ~c.ok THEN c
    ELSE IF c.v[1] > 4 THEN Er("ticket count", 0)
    ELSE LET es == RdTickets(c.v[1], c.r) IN
         IF ~es.ok THEN es ELSE Ok([k |-> "NewTickets", es |-> es.v], es.r)

DecodeBody(t, r) ==
    IF t = 0 THEN Ok([k |-> "Padding", len |-> ZeroRun(r) + 1], Drop(r, ZeroRun(r)))
    ELSE IF t = 1 THEN Ok([k |-> "Ping"], r)
    ELSE IF t = 2 THEN ParseAck(r)
    ELSE IF t = 4
    THEN LET a == RdVarint(r) IN
         IF ~a.ok THEN a
         ELSE LET b == RdVarint(a.r) IN
              IF ~b.ok THEN b
              ELSE LET c == RdVarint(b.r) IN
                   IF ~c.ok THEN c ELSE Ok([k |-> "ResetStream", id |-> a.v, error |-> b.v, fs |-> c.v], c.r)
    ELSE IF t = 5
    THEN LET a == RdVarint(r) IN
         IF ~a.ok THEN a
         ELSE LET b == RdVarint(a.r) IN
              IF ~b.ok THEN b ELSE Ok([k |-> "StopSending", id |-> a.v, error |-> b.v], b.r)
    ELSE IF 8 <= t /\ t <= 15 THEN DecodeStream(t, r)
    ELSE IF t = 17
    THEN LET a == RdVarint(r) IN
         IF ~a.ok THEN a
         ELSE LET b == RdVarint(a.r) IN
              IF ~b.ok THEN b ELSE Ok([k |-> "MaxStreamData", id |-> a.v, max |-> b.v], b.r)
    ELSE IF t = 18 THEN LET a == RdVarint(r) IN IF ~a.ok THEN a ELSE Ok([k |-> "MaxStreams", limit |-> a.v], a.r)
    ELSE IF t = 26 THEN LET d == RdBytes(8, r) IN IF ~d.ok THEN d ELSE Ok([k |-> "PathChallenge", d |-> d.v], d.r)
    ELSE IF t = 27 THEN LET d == RdBytes(8, r) IN IF ~d.ok THEN d ELSE Ok([k |-> "PathResponse", d |-> d.v], d.r)
    ELSE IF t = 28 THEN LET a == RdVarint(r) IN IF ~a.ok THEN a ELSE Ok([k |-> "Close", error |-> a.v], a.r)
    ELSE IF t = 48
    THEN LET d == RdBytes(Len(r), r) IN
         IF ~d.ok THEN d ELSE Ok([k |-> "Datagram", data |-> d.v, imp |-> TRUE], d.r)
    ELSE IF t = 49
    THEN LET d == RdLenPrefixed(r) IN
         IF ~d.ok THEN d ELSE Ok([k |-> "Datagram", data |-> d.v, imp |-> FALSE], d.r)
    ELSE IF t = 58
    THEN LET d == RdBytes(2, r) IN
         IF ~d.ok THEN d ELSE Ok([k |-> "MtuProbeEcho", mtu |-> d.v[1] * 256 + d.v[2]], d.r)
    ELSE IF t = 59 THEN Ok([k |-> "Sleep"], r)
    ELSE IF t = 60 THEN Ok([k |-> "Wake"], r)
    ELSE IF t = 61 THEN RdRekey(r)
    ELSE IF t = 62 THEN Ok([k |-> "Ready"], r)
    ELSE IF t = 63 THEN RdTicketBatch(r)
    ELSE IF t >= 64
    THEN LET d == RdLenPrefixed(r) IN
         IF ~d.ok THEN d ELSE Ok([k |-> "Extension", ty |-> t, body |-> d.v], d.r)
    ELSE Er("UnknownType", t)

Decode(b) == LET t == RdVarint(b) IN IF ~t.ok THEN t ELSE DecodeBody(t.v, t.r)

\* FrameIter: the frames in order and the error it ends with ("none" when the payload is used up)
RECURSIVE Iter(_)
Iter(b) ==
    IF Len(b) = 0 THEN [fs |-> <<>>, e |-> "none", n |-> 0]
    ELSE LET d == Decode(b) IN
         IF ~d.ok THEN [fs |-> <<>>, e |-> d.e, n |-> d.n]
         ELSE LET t == Iter(d.r) IN [fs |-> <<d.v>> \o t.fs, e |-> t.e, n |-> t.n]

(* ---- the writer ---- *)
PV(x) == <<"v", x>>
PS(bs) == <<"s", bs>>

Put(cap, w, p) ==
    IF p[1] = "v"
    THEN IF p[2] >= LIMIT THEN Er("VarintOverflow", 0)
         ELSE IF VLen(p[2]) > cap - Len(w) THEN Er("BufferTooSmall", VLen(p[2]) - (cap - Len(w)))
         ELSE Ok(w \o VEnc(p[2]), <<>>)
    ELSE IF Len(p[2]) <= cap - Len(w) THEN Ok(w \o p[2], <<>>)
         ELSE Er("BufferTooSmall", Len(p[2]) - (cap - Len(w)))

RECURSIVE RunPuts(_, _, _)
RunPuts(cap, w, ps) ==
    IF Len(ps) = 0 THEN Ok(w, <<>>)
    ELSE LET r == Put(cap, w, Head(ps)) IN IF ~r.ok THEN r ELSE RunPuts(cap, r.v, Tail(ps))

\* the PADDING loop: zero bytes in pieces of at most 64
RECURSIVE ZeroChunks(_)
ZeroChunks(len) == IF len = 0 THEN <<>> ELSE <<PS(Zeros(Min(len, 64)))>> \o ZeroChunks(len - Min(len, 64))

StreamType(off, fin, imp) ==
    8 + (IF off = 0 THEN 0 ELSE 4) + (IF imp THEN 0 ELSE 2) + (IF fin THEN 1 ELSE 0)

HalvesBytes(h) == <<h[1] \div 256, h[1] % 256, h[2] \div 256, h[2] % 256>>
RECURSIVE TicketPuts(_)
TicketPuts(es) ==
    IF Len(es) = 0 THEN <<>> ELSE <<PS(es[1].tid), PS(HalvesBytes(es[1].lt))>> \o TicketPuts(Tail(es))

Puts(f) ==
    CASE f.k = "Padding" -> ZeroChunks(f.len)
      [] f.k = "Ping" -> <<PV(1)>>
      [] f.k = "Ack" -> <<PV(2), PV(f.largest), PV(f.extra), PV(f.first), PS(f.tail)>>
      [] f.k = "ResetStream" -> <<PV(4), PV(f.id), PV(f.error), PV(f.fs)>>
      [] f.k = "StopSending" -> <<PV(5), PV(f.id), PV(f.error)>>
      [] f.k = "Stream" ->
           <<PV(StreamType(f.off, f.fin, f.imp)), PV(f.id)>> \o (IF f.off = 0 THEN <<>> ELSE <<PV(f.off)>>)
             \o (IF f.imp THEN <<PS(f.data)>> ELSE <<PV(Len(f.data)), PS(f.data)>>)
      [] f.k = "MaxStreamData" -> <<PV(17), PV(f.id), PV(f.max)>>
      [] f.k = "MaxStreams" -> <<PV(18), PV(f.limit)>>
      [] f.k = "PathChallenge" -> <<PV(26), PS(f.d)>>
      [] f.k = "PathResponse" -> <<PV(27), PS(f.d)>>
      [] f.k = "Close" -> <<PV(28), PV(f.error)>>
      [] f.k = "Datagram" -> IF f.imp THEN <<PV(48), PS(f.data)>> ELSE <<PV(49), PV(Len(f.data)), PS(f.data)>>
      [] f.k = "MtuProbeEcho" -> <<PV(58), PS(<<f.mtu \div 256, f.mtu % 256>>)>>
      [] f.k = "Sleep" -> <<PV(59)>>
      [] f.k = "Wake" -> <<PV(60)>>
      [] f.k = "Rekey" ->
           <<PV(61), PS(<<IF f.ans THEN 1 ELSE 0>>), PS(f.sh)>> \o (IF f.ans THEN <<PS(f.echo), PV(f.spn)>> ELSE <<>>)
      [] f.k = "Ready" -> <<PV(62)>>
      [] f.k = "NewTickets" -> <<PV(63), PS(<<Len(f.es)>>)>> \o TicketPuts(f.es)
      [] f.k = "Extension" -> <<PV(f.ty), PV(Len(f.body)), PS(f.body)>>

StreamOverhead(id, off, dlen, imp) ==
    1 + VLen(id) + (IF off = 0 THEN 0 ELSE VLen(off)) + (IF imp THEN 0 ELSE VLen(dlen))
DatagramOverhead(dlen, imp) == 1 + (IF imp THEN 0 ELSE VLen(dlen))

EncodedLen(f) ==
    CASE f.k = "Padding" -> f.len
      [] f.k \in {"Ping", "Sleep", "Wake", "Ready"} -> 1
      [] f.k = "Ack" -> 1 + (VLen(f.largest) + VLen(f.extra) + VLen(f.first) + Len(f.tail))
      [] f.k = "ResetStream" -> 1 + VLen(f.id) + VLen(f.error) + VLen(f.fs)
      [] f.k = "Stream" -> StreamOverhead(f.id, f.off, Len(f.data), f.imp) + Len(f.data)
      [] f.k = "MaxStreamData" -> 1 + VLen(f.id) + VLen(f.max)
      [] f.k = "StopSending" -> 1 + VLen(f.id) + VLen(f.error)
      [] f.k \in {"PathChallenge", "PathResponse"} -> 1 + 8
      [] f.k = "Close" -> 1 + VLen(f.error)
      [] f.k = "MaxStreams" -> 1 + VLen(f.limit)
      [] f.k = "Datagram" -> DatagramOverhead(Len(f.data), f.imp) + Len(f.data)
      [] f.k = "MtuProbeEcho" -> 1 + 2
      [] f.k = "Rekey" -> 1 + 1 + 32 + (IF f.ans THEN 8 + VLen(f.spn) ELSE 0)
      [] f.k = "NewTickets" -> 1 + 1 + Len(f.es) * 20
      [] f.k = "Extension" -> VLen(f.ty) + (VLen(Len(f.body)) + Len(f.body))

VarintFields(f) ==
    CASE f.k = "ResetStream" -> <<f.id, f.error, f.fs>>
      [] f.k = "MaxStreamData" -> <<f.id, f.max, 0>>
      [] f.k = "StopSending" -> <<f.id, f.error, 0>>
      [] f.k = "Stream" -> <<f.id, f.off, 0>>
      [] f.k = "Close" -> <<f.error, 0, 0>>
      [] f.k = "Extension" -> <<f.ty, 0, 0>>
      [] f.k = "MaxStreams" -> <<f.limit, 0, 0>>
      [] f.k = "Rekey" -> <<f.spn, 0, 0>>
      [] OTHER -> <<0, 0, 0>>

Validate(f) ==
    IF \E i \in 1..3 : VarintFields(f)[i] >= LIMIT THEN Er("VarintOverflow", 0)
    ELSE IF f.k = "Stream" /\ f.off + Len(f.data) > MAXEND THEN Er("StreamEnd", 0)
    ELSE IF f.k = "Extension" /\ f.ty < 64 THEN Er("UnknownType", f.ty)
    ELSE Ok(<<>>, <<>>)

\* Frame::write into an empty buffer of cap bytes: the bytes written, or the error (nothing is written)
Write(cap, f) ==
    LET v == Validate(f) IN
    IF ~v.ok THEN v
    ELSE IF EncodedLen(f) <= cap THEN RunPuts(cap, <<>>, Puts(f))
    ELSE Er("BufferTooSmall", EncodedLen(f) - cap)

(* ---- the ACK encoder ---- *)
\* one item of wire_fields for the range s..=e; prev is the start of the range before it, -1 for the first
WireItem(prev, s, e) ==
    IF s > e \/ e > MAXPN THEN Er("Ack", 0)
    ELSE IF prev = -1 THEN Ok(<<e, e - s>>, <<>>)
    ELSE IF prev < e + 2 THEN Er("Ack", 0)
    ELSE Ok(<<prev - e - 2, e - s>>, <<>>)

RECURSIVE WireFields(_, _)
WireFields(prev, rs) ==
    IF Len(rs) = 0 THEN Ok(<<>>, <<>>)
    ELSE LET it == WireItem(prev, rs[1][1], rs[1][2]) IN
         IF ~it.ok THEN it
         ELSE LET rest == WireFields(rs[1][1], Tail(rs)) IN
              IF ~rest.ok THEN rest ELSE Ok(<<it.v>> \o rest.v, <<>>)

RECURSIVE PairLen(_)
PairLen(its) == IF Len(its) = 0 THEN 0 ELSE VLen(its[1][1]) + VLen(its[1][2]) + PairLen(Tail(its))
RECURSIVE PairPuts(_)
PairPuts(its) == IF Len(its) = 0 THEN <<>> ELSE <<PV(its[1][1]), PV(its[1][2])>> \o PairPuts(Tail(its))

\* shape: the wire fields of the first MAXRANGES ranges and the size after the type
AckShape(rs) ==
    LET w == WireFields(-1, Take(rs, Min(MAXRANGES, Len(rs)))) IN
    IF ~w.ok THEN w
    ELSE IF Len(w.v) = 0 THEN Er("Ack", 0)
    ELSE Ok(w.v, PairLen(Tail(w.v)) + (VLen(w.v[1][1]) + VLen(Len(w.v) - 1) + VLen(w.v[1][2])))

AckLen(rs) == LET s == AckShape(rs) IN IF ~s.ok THEN s ELSE Ok(1 + s.r, <<>>)

WriteAck(cap, rs) ==
    LET s == AckShape(rs) IN
    IF ~s.ok THEN s
    ELSE IF 1 + s.r <= cap
         THEN RunPuts(cap, <<>>, <<PV(2), PV(s.v[1][1]), PV(Len(s.v) - 1), PV(s.v[1][2])>> \o PairPuts(Tail(s.v)))
         ELSE Er("BufferTooSmall", 1 + s.r - cap)
=============================================================================
