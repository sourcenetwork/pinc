-------------------------------- MODULE Hdr ---------------------------------
(***************************************************************************)
(* The packet header codecs of vinc-transport (packet/header.rs,           *)
(* packet/datagram.rs and the associated data of packet/protect.rs),       *)
(* checked over the operators of HdrOps.tla.                               *)
(*                                                                         *)
(* The cases are the states of one machine (as in Varint.tla):             *)
(*  - long headers: every type, five connection ids each side (0, 1, 2 and *)
(*    20 bytes), body lengths 0, 1, 3, 127, 128, 300 and 2^j - 1, 2^j,     *)
(*    2^j + 1 for j in 14, 31, 62, 63, 64, every pn_len 0..3 and every     *)
(*    room 0..header_len + 1;                                              *)
(*  - short headers: both key phases, the same ids, packet numbers of 0 to *)
(*    4 bytes, every room;                                                 *)
(*  - byte strings of 0 to 6 bytes over the bytes 0, 1, 2, 0x40, 0x80,     *)
(*    0xC0, 0xD1, as headers and as datagrams;                             *)
(*  - datagrams that are up to four pieces back to back: four long         *)
(*    packets, two short packets, padding, a long packet whose body is cut *)
(*    and a byte that is no packet.                                        *)
(*                                                                         *)
(* Checked:                                                                *)
(*   WriteAtomic   a refused write (long or short) writes nothing, for     *)
(*                 every error: the pn_len that does not fit, the body     *)
(*                 length of 2^63 or more, the room;                       *)
(*   WriteExact    the error is exactly PnLength, then VarintOverflow,     *)
(*                 then BufferTooSmall with the shortfall, and a write     *)
(*                 that succeeds wrote the encoding, header_len bytes;     *)
(*   RoundTrip     parsing what was written, with its body and anything    *)
(*                 after it, gives the fields and the header length; the   *)
(*                 low four bits of a 0-RTT first byte are not looked at;  *)
(*                 short_dcid and the first byte give the id, the key      *)
(*                 phase and the packet-number length back;                *)
(*   Strict        every cut of a header is Truncated with the missing     *)
(*                 bytes, a body one byte short or a length past the end   *)
(*                 is Length, another version is Version with the byte, an *)
(*                 id length above 20 is ConnIdLength, a first byte        *)
(*                 without both top bits is Form, type bits 2 and 3 are    *)
(*                 LongType, a low bit on a handshake is Reserved; for the *)
(*                 short header Form, TooShort, ConnIdLength, Reserved;    *)
(*   Canonical     an accepted long header is the encoding of the fields   *)
(*                 it yields (up to the low four bits of a 0-RTT first     *)
(*                 byte), its body fits; an accepted short header is the   *)
(*                 encoding of its fields;                                 *)
(*   Split         the packets of a datagram are long packets then at most *)
(*                 one short packet or one error; the ranges start at 0,   *)
(*                 are back to back, not empty and inside the datagram; a  *)
(*                 short packet runs to the end; each packet is what the   *)
(*                 parser finds at its offset; after the last long packet  *)
(*                 only zero bytes remain; an error is the parser's at the *)
(*                 offset it is reported; the split of a parsed long       *)
(*                 packet never fails;                                     *)
(*   Aad           the associated data seal and open take is the header as *)
(*                 written, packet number included, and both find the same *)
(*                 payload; the length errors are TooShort and             *)
(*                 BufferTooSmall with the shortfall.                      *)
(* Hdr_late.cfg (Late = TRUE, the rule before the fix) must violate        *)
(* WriteAtomic; Hdr_coalesced.cfg must violate NotCoalesced (a datagram of *)
(* two long packets and a short one is reached).                           *)
(*                                                                         *)
(* Lean counterparts (proofs/lean/Vinc/TransportHdrThm.lean and            *)
(* TransportHdrSplit.lean): writeLong_refused_nothing, writeLong_ok, the   *)
(* writeLong_err theorems, late_writes, parse_write, parse_canonical,      *)
(* parse_cut, the parse_err theorems, writeShort_refused_nothing,          *)
(* writeShort_ok, short_roundtrip, short_canonical,                        *)
(* packets_shape, packets_ranges, packets_items, packets_end, aad_short,   *)
(* aad_zero_rtt, open_seal_parts.                                          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT Late
INSTANCE HdrOps

VARIABLE c
Init == c = [t |-> "root"]

Cids == {<<>>, <<5>>, <<255, 0>>, [i \in 1..20 |-> i], [i \in 1..20 |-> 0]}
SmallBl == {0, 1, 3, 127, 128, 300}
Edges == UNION {{V!EdgeVal(j, d) : d \in {x \in -1..1 : V!EdgeOK(j, x)}} : j \in {14, 31, 62, 63, 64}}
Bls == {U!W(k) : k \in SmallBl} \cup Edges
Pns == {<<>>, <<7>>, <<1, 2>>, <<0, 0>>, <<255, 254, 253>>, <<1, 2, 3, 4>>}
Alpha == {0, 1, 2, 64, 128, 192, 209}
Pieces == <<
    <<192, 1, 0, 0, 0>>,                      \* the smallest handshake packet
    <<192, 1, 1, 9, 1, 8, 2, 5, 6>>,          \* a handshake packet with ids and a body of 2
    <<209, 1, 0, 1, 7, 3, 1, 2, 3>>,          \* a 0-RTT packet with a body of 3
    <<64, 9, 1, 2, 3>>,                       \* a short packet
    <<80, 9>>,                                \* a short packet, key phase 1
    <<0, 0>>,                                 \* padding
    <<192, 1, 0, 0, 2, 1>>,                   \* a long packet whose body is cut
    <<1>>,                                    \* no packet
    <<209, 1, 0, 0, 20>> \o [i \in 1..20 |-> i] >>  \* a 0-RTT packet long enough to open
Dls == {0, 1, 2, 21}

Next ==
    \/ c.t = "root" /\ \E f \in {"long", "short", "bytes", "cat"} : c' = [t |-> "seed", f |-> f]
    \/ c.t = "seed" /\ c.f = "long" /\ \E ty \in 0..2, d \in Cids, s \in Cids, bl \in Bls :
           c' = [t |-> "long", h |-> [ty |-> ty, dcid |-> d, scid |-> s, bl |-> bl]]
    \/ c.t = "seed" /\ c.f = "short" /\ \E kp \in BOOLEAN, d \in Cids, pn \in Pns :
           c' = [t |-> "short", h |-> [kp |-> kp, dcid |-> d], pn |-> pn]
    \/ c.t = "seed" /\ c.f = "bytes" /\ c' = [t |-> "bytes", in |-> <<>>]
    \/ c.t = "seed" /\ c.f = "cat" /\ c' = [t |-> "cat", in |-> <<>>, k |-> 0]
    \/ c.t = "bytes" /\ Len(c.in) < 6 /\ \E b \in Alpha : c' = [c EXCEPT !.in = Append(c.in, b)]
    \/ c.t = "cat" /\ c.k < 4 /\ \E p \in 1..Len(Pieces) : c' = [c EXCEPT !.in = c.in \o Pieces[p], !.k = c.k + 1]

Spec == Init /\ [][Next]_c

Prefix(s, n) == SubSeq(s, 1, n)
Rest(s, n) == SubSeq(s, n + 1, Len(s))
Fill(n, b) == [i \in 1..n |-> b]
Big(h) == ~U!Lt(h.bl, V!Limit)
Small(h) == U!Lt(h.bl, U!W(400))
PnOf(h) == IF h.ty = 1 THEN 2 ELSE 0
(* the specification of the encoding, apart from the writer *)
EncodeLong(h, low) ==
    <<FirstLong(h.ty, low), VERSION, Len(h.dcid)>> \o h.dcid \o <<Len(h.scid)>> \o h.scid \o V!Encode(h.bl, 16).bytes
EncodeShort(h, pn) == <<FirstShort(h.kp, Len(pn))>> \o h.dcid \o pn
OkLong(h, hl) == [err |-> "ok", n |-> 0, ty |-> h.ty, dcid |-> h.dcid, scid |-> h.scid, bl |-> h.bl, hl |-> hl]
SetAt(s, k, b) == [s EXCEPT ![k] = b]

(* ---- writes ---- *)
LongWriteAtomic(h) ==
    \A pn \in 0..3, cap \in 0..(HeaderLen(h) + 1) :
        LET r == LongWrite(h, pn, cap) IN r.err # "ok" => r.out = <<>>
ShortWriteAtomic(h, pn) ==
    \A cap \in 0..(ShortHeaderLen(Len(h.dcid), Len(pn)) + 1) :
        LET r == ShortWrite(h, pn, cap) IN r.err # "ok" => r.out = <<>>
WriteAtomic ==
    /\ c.t = "long" => LongWriteAtomic(c.h)
    /\ c.t = "short" => ShortWriteAtomic(c.h, c.pn)

LongWriteExact(h) ==
    LET hl == HeaderLen(h)
    IN \A pn \in 0..3, cap \in 0..(hl + 1) :
        LET r == LongWrite(h, pn, cap)
        IN /\ r.err = (IF pn # PnOf(h) THEN "PnLength" ELSE IF Big(h) THEN "VarintOverflow"
                       ELSE IF cap < hl THEN "BufferTooSmall" ELSE "ok")
           /\ r.err = "BufferTooSmall" => r.n = hl - cap
           /\ r.err = "ok" => r.out = EncodeLong(h, IF h.ty = 1 THEN 1 ELSE 0) /\ Len(r.out) = hl
ShortWriteExact(h, pn) ==
    LET hl == ShortHeaderLen(Len(h.dcid), Len(pn))
    IN \A cap \in 0..(hl + 1) :
        LET r == ShortWrite(h, pn, cap)
        IN /\ r.err = (IF Len(pn) \notin {2, 3} THEN "PnLength" ELSE IF cap < hl THEN "BufferTooSmall" ELSE "ok")
           /\ r.err = "BufferTooSmall" => r.n = hl - cap
           /\ r.err = "ok" => r.out = EncodeShort(h, pn) /\ Len(r.out) = hl
WriteExact ==
    /\ c.t = "long" => LongWriteExact(c.h)
    /\ c.t = "short" => ShortWriteExact(c.h, c.pn)

(* ---- the long header read back ---- *)
Lows(h) == IF h.ty = 1 THEN 0..15 ELSE {0}
LongRoundTrip(h) ==
    ~Big(h) =>
        \A low \in Lows(h) :
            LET e == EncodeLong(h, low)
            IN IF Small(h)
               THEN \A trail \in {<<>>, <<0>>, <<192>>} :
                        LongParse(e \o Fill(U!Val(h.bl), 7) \o trail) = OkLong(h, HeaderLen(h))
               ELSE TRUE
(* the bytes a cut at m leaves the parser short of *)
CutNeeds(h, m) ==
    LET dl == Len(h.dcid)
        sl == Len(h.scid)
    IN IF m < 3 THEN 1
       ELSE IF m - 3 < dl THEN dl - (m - 3)
       ELSE IF m = 3 + dl THEN 1
       ELSE IF m - 4 - dl < sl THEN sl - (m - 4 - dl)
       ELSE 1
LongStrict(h) ==
    ~Big(h) =>
        LET e == EncodeLong(h, IF h.ty = 1 THEN 1 ELSE 0)
            hl == HeaderLen(h)
            body == IF Small(h) THEN Fill(U!Val(h.bl), 7) ELSE <<1, 2, 3>>
            whole == e \o body
        IN /\ Len(e) = hl
           /\ \A m \in 0..(hl - 1) : LongParse(Prefix(e, m)) = Err("Truncated", CutNeeds(h, m))
           /\ (~Small(h) \/ U!Val(h.bl) > 0) => LongParse(Prefix(whole, Len(whole) - 1)) = Err("Length", 0)
           /\ ~Small(h) => LongParse(whole) = Err("Length", 0)
           /\ \A v \in {0, 2, 255} : LongParse(SetAt(whole, 2, v)) = Err("Version", v)
           /\ \A l \in {21, 255} :
                /\ LongParse(SetAt(whole, 3, l)) = Err("ConnIdLength", 0)
                /\ LongParse(SetAt(whole, 4 + Len(h.dcid), l)) = Err("ConnIdLength", 0)
           /\ \A f \in 0..191 : LongParse(SetAt(whole, 1, f)) = Err("Form", 0)
           /\ \A f \in 240..255 : LongParse(SetAt(whole, 1, f)) = Err("LongType", 0)
           /\ \A f \in (193..207) \cup (225..239) : LongParse(SetAt(whole, 1, f)) = Err("Reserved", 0)

(* ---- the short header read back ---- *)
ShortRoundTrip(h, pn) ==
    Len(pn) \in {2, 3} =>
        LET e == EncodeShort(h, pn)
            f == ReadFirst(e[1])
        IN /\ \A trail \in {<<>>, <<0>>, <<9, 9>>} : ShortDcid(e \o trail, Len(h.dcid)) = [err |-> "ok", n |-> 0, id |-> h.dcid]
           /\ f = [err |-> "ok", n |-> 0, pl |-> Len(pn), kp |-> h.kp]
ShortStrict(h, pn) ==
    Len(pn) \in {2, 3} =>
        LET e == EncodeShort(h, pn)
        IN /\ ShortDcid(e, 21) = Err("ConnIdLength", 0)
           /\ ShortDcid(<<>>, Len(h.dcid)) = Err("TooShort", 0)
           /\ \A m \in 1..Len(h.dcid) : ShortDcid(Prefix(e, m), Len(h.dcid)) = Err("TooShort", 0)
           /\ \A f \in (0..63) \cup (96..255) : ShortDcid(SetAt(e, 1, f), Len(h.dcid)) = Err("Form", 0)
           /\ \A f \in 64..95 : (f \div 4) % 4 # 0 => ReadFirst(f) = Err("Reserved", 0)

RoundTrip ==
    /\ c.t = "long" => LongRoundTrip(c.h)
    /\ c.t = "short" => ShortRoundTrip(c.h, c.pn)
Strict ==
    /\ c.t = "long" => LongStrict(c.h)
    /\ c.t = "short" => ShortStrict(c.h, c.pn)

(* ---- an accepted header is the encoding of its fields ---- *)
LongCanonical(s) ==
    LET r == LongParse(s)
    IN r.err = "ok" =>
        LET h == [ty |-> r.ty, dcid |-> r.dcid, scid |-> r.scid, bl |-> r.bl]
        IN /\ Len(h.dcid) <= MAXCID /\ Len(h.scid) <= MAXCID /\ ~Big(h)
           /\ r.hl = HeaderLen(h) /\ r.hl + U!Val(h.bl) <= Len(s)
           /\ Prefix(s, r.hl) = EncodeLong(h, s[1] % 16)
           /\ h.ty # 1 => Prefix(s, r.hl) = LongWrite(h, 0, r.hl).out
           /\ h.ty = 1 => Rest(Prefix(s, r.hl), 1) = Rest(LongWrite(h, 2, r.hl).out, 1) /\ s[1] \div 16 = 13
ShortCanonical(s) ==
    \A dl \in {0, 1, 2} :
        LET r == ShortDcid(s, dl)
            f == IF Len(s) > 0 THEN ReadFirst(s[1]) ELSE Err("TooShort", 0)
        IN (r.err = "ok" /\ f.err = "ok" /\ f.pl \in {2, 3} /\ Len(s) >= 1 + dl + f.pl) =>
              Prefix(s, 1 + dl + f.pl) = ShortWrite([kp |-> f.kp, dcid |-> r.id], SubSeq(s, 2 + dl, 1 + dl + f.pl), 99).out
Canonical == c.t \in {"bytes", "cat"} => LongCanonical(c.in) /\ ShortCanonical(c.in)

(* ---- datagrams ---- *)
SplitOK(d, dl) ==
    LET R == Packets(d, dl)
        n == Len(R)
        end == IF n = 0 THEN 0 ELSE IF R[n].k = "err" THEN R[n].s ELSE R[n].s + R[n].len
        tail == Rest(d, end)
    IN /\ \A i \in 1..(n - 1) : R[i].k = "long"
       /\ n > 0 => R[1].s = 0
       /\ \A i \in 1..(n - 1) : R[i + 1].s = R[i].s + R[i].len
       /\ \A i \in 1..n : R[i].k # "err" => R[i].len > 0 /\ R[i].s + R[i].len <= Len(d)
       /\ \A i \in 1..n : R[i].k = "short" => R[i].s + R[i].len = Len(d)
       /\ \A i \in 1..n :
            LET rest == Rest(d, R[i].s)
            IN /\ R[i].k = "long" =>
                    /\ LongParse(rest) = [err |-> "ok", n |-> 0, ty |-> R[i].ty, dcid |-> R[i].dcid, scid |-> R[i].scid,
                                          bl |-> R[i].bl, hl |-> R[i].hl]
                    /\ R[i].len = R[i].hl + U!Val(R[i].bl)
                    /\ rest[1] >= 128
               /\ R[i].k = "short" => ShortDcid(rest, dl) = [err |-> "ok", n |-> 0, id |-> R[i].dcid] /\ rest[1] \in 1..127
       /\ (n = 0 \/ R[n].k = "long") => \A k \in 1..Len(tail) : tail[k] = 0
       /\ (n > 0 /\ R[n].k = "err") =>
            /\ Len(tail) > 0
            /\ tail[1] = 0 => R[n].err = "Form" /\ \E k \in 1..Len(tail) : tail[k] # 0
            /\ tail[1] \in 1..127 => ShortDcid(tail, dl) = Err(R[n].err, R[n].n)
            /\ tail[1] >= 128 => LongParse(tail) = Err(R[n].err, R[n].n)
(* the split of a long packet the parser accepted never fails: the body fits *)
SplitNeverFails(d) ==
    \A off \in 0..Len(d) :
        LET r == LongParse(Rest(d, off)) IN r.err = "ok" => ~U!Lt(U!W(Len(d) - off - r.hl), r.bl)
Split == c.t \in {"bytes", "cat"} => SplitNeverFails(c.in) /\ \A dl \in Dls : SplitOK(c.in, dl)

(* ---- the associated data ---- *)
Tag == Fill(TAGLEN, 170)
AadOK(e, pnOff, pnLen) ==
    \A pl \in 0..5 :
        LET packet == e \o Fill(pl, 33) \o Tag
            s == SealParts(packet, pnOff, pnLen, pl)
            o == OpenParts(packet, pnOff, pnLen)
        IN /\ IF pnLen + pl < SAMPLESKIP THEN s = Err("TooShort", 0)
              ELSE /\ s = [err |-> "ok", n |-> 0, aad |-> e, ps |-> Len(e), pe |-> Len(e) + pl, total |-> Len(packet)]
                   /\ SealParts(packet \o <<1, 2>>, pnOff, pnLen, pl) = s
                   /\ SealParts(Prefix(packet, Len(packet) - 1), pnOff, pnLen, pl) = Err("BufferTooSmall", 1)
           /\ o = [err |-> "ok", n |-> 0, aad |-> e, ps |-> Len(e), pe |-> Len(e) + pl, total |-> Len(packet)]
           /\ OpenParts(Prefix(packet, Len(e) + TAGLEN - 1), pnOff, pnLen) = Err("TooShort", 0)
           /\ OpenParts(Prefix(packet, Len(e) - 1), pnOff, pnLen) = Err("TooShort", 0)
Aad ==
    /\ (c.t = "short" /\ Len(c.pn) \in {2, 3}) =>
          LET w == ShortWrite(c.h, c.pn, 99) IN AadOK(w.out, 1 + Len(c.h.dcid), Len(c.pn))
    /\ (c.t = "long" /\ c.h.ty = 1 /\ ~Big(c.h)) =>
          LET w == LongWrite(c.h, 2, 99) IN \A pn \in {<<0, 0>>, <<255, 1>>} : AadOK(w.out \o pn, Len(w.out), 2)
    \* a packet found in a datagram: the associated data is its first pn_off + pn_len bytes as they are
    /\ c.t = "cat" =>
          \A dl \in {0, 1} :
              LET R == Packets(c.in, dl)
              IN \A i \in 1..Len(R) :
                    (R[i].k # "err" /\ PnOff(R[i]) + 2 + TAGLEN <= R[i].len) =>
                        OpenParts(SubSeq(c.in, R[i].s + 1, R[i].s + R[i].len), PnOff(R[i]), 2).aad
                            = SubSeq(c.in, R[i].s + 1, R[i].s + PnOff(R[i]) + 2)

(* ---- witnesses ---- *)
NotCoalesced ==
    ~(c.t = "cat" /\ LET R == Packets(c.in, 1) IN Len(R) = 3 /\ R[1].k = "long" /\ R[2].k = "long" /\ R[3].k = "short")
=============================================================================
