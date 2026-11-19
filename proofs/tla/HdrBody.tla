------------------------------- MODULE HdrBody -------------------------------
(***************************************************************************)
(* The three places a datagram is put together or taken apart besides the  *)
(* headers of Hdr.tla, over the operators of HdrOps.tla:                   *)
(*  - the body of a Handshake packet, varint(total) varint(offset)         *)
(*    fragment: conn/send.rs write_handshake and conn/handshake.rs         *)
(*    on_fragment, which hands the fragment to Reassembly::add             *)
(*    (ReasmOps.tla);                                                      *)
(*  - pad_to of packet/datagram.rs;                                        *)
(*  - sample_at of packet/protect.rs, tied to the header protection of     *)
(*    HeaderProt.tla.                                                      *)
(*                                                                         *)
(* The cases are the states of one machine (as in Hdr.tla):                *)
(*  - "hs": a Handshake packet written: ids of 0, 1 and 20 bytes, message  *)
(*    lengths and offsets 0, 1, 5, 63, 64, 127, 128 and 2^j - 1, 2^j,      *)
(*    2^j + 1 for j in 14, 31, 62, 63, fragments of 0, 1, 3 and 130        *)
(*    bytes, windows around the size of the datagram;                      *)
(*  - "recv": a body handed to on_fragment over four reassembly states     *)
(*    (largest message 6, two runs): message lengths 0, 1, 5, 6, 7, 300,   *)
(*    2^62, offsets 0 to 7 and 2^62, fragments of 0 to 10 bytes;           *)
(*  - "bytes": every string of 0 to 6 bytes over 0, 1, 128, 129, 255 as a  *)
(*    body;                                                                *)
(*  - "pad": every window of 0 to 140 bytes holding 0, 1, 5 or 70 bytes,   *)
(*    every minimum length;                                                *)
(*  - "smp": packets of 0 to 40 bytes, every offset, every packet-number   *)
(*    length of 1 to 4 bytes, both header forms, masks.                    *)
(*                                                                         *)
(* Checked:                                                                *)
(*   WriteOK       the writer succeeds exactly when both numbers are below *)
(*                 2^63 and the window holds the header, both varints and  *)
(*                 the fragment; what it wrote is the header (whose body   *)
(*                 length counts the three parts) and the three parts;     *)
(*   WriteRead     the datagram parses back to the same header and the     *)
(*                 body after it reads back as the message length, the     *)
(*                 offset and the fragment, whatever follows;              *)
(*   RoomOK        a fragment of at most the room the code computes always *)
(*                 fits, as long as the body length takes two bytes of     *)
(*                 varint at most (below 2^14), which the code sets aside; *)
(*   Canon         a body that parses is the one encoding of what it       *)
(*                 yields, and a body that does not leaves the             *)
(*                 reassembly alone;                                       *)
(*   RecvOK        what reaches the reassembly: a message length of 0 or   *)
(*                 above the largest is refused and changes nothing, an    *)
(*                 offset at or past the length is refused (a message of   *)
(*                 another length starts the count over), a fragment that  *)
(*                 runs past the length is cut at it, and a body written   *)
(*                 by the writer is added as the fragment it carries;      *)
(*   PadOK         pad_to appends exactly the zeros that bring the writer  *)
(*                 to min_len, leaves what was written, and refuses with   *)
(*                 the shortfall and writes nothing when min_len does not  *)
(*                 fit; a writer that holds min_len is left alone;         *)
(*   SampleExact   sample_at is the 16 bytes at pn_off + 4, TooShort when  *)
(*                 fewer than 16 follow;                                   *)
(*   SampleStable  header protection (HeaderProt.tla Apply: the first byte *)
(*                 and a packet number of 1 to 4 bytes) leaves the sample  *)
(*                 as it was: the offset 4 is the longest packet number;   *)
(*   SealSample    seal refuses a packet for being too short exactly when  *)
(*                 no sample can be taken from the packet it would make.   *)
(*                                                                         *)
(* Witnesses, each of which TLC must violate:                              *)
(*   HdrBody_room.cfg     RoomAny: the room without the bound on the body  *)
(*                        length, with a fragment of 16384 bytes (the body *)
(*                        length then takes four bytes, not the two the    *)
(*                        code reserves);                                  *)
(*   HdrBody_trim.cfg     PastRefused: a fragment that runs past the       *)
(*                        message length is refused (it is cut and kept);  *)
(*   HdrBody_done.cfg     NotDone: no body completes a message;            *)
(*   HdrBody_padlate.cfg  PadAtomicLate: pad_to without the room check up  *)
(*                        front writes part of the padding;                *)
(*   HdrBody_skip3.cfg    SampleStable3: a sample offset of 3 (not 4)      *)
(*                        overlaps a packet number of 4 bytes.             *)
(*                                                                         *)
(* Lean counterparts (proofs/lean/Pinc/TransportHdrBody.lean):             *)
(* hsWrite_ok, hsWrite_err, hsWrite_room, write_read, hsRead_hsBody,       *)
(* hsRead_canonical, hsRecv_unparsed, hsRecv_bad_total, hsRecv_past,       *)
(* add_trim, hsRecv_write, padTo_ok, padTo_err, padTo_noop, sampleAt_ok,   *)
(* sampleAt_err, sampleAt_unmasked, sealParts_sample,                      *)
(* sealParts_tooShort_iff.                                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Late, Big
INSTANCE HdrOps
HP == INSTANCE HeaderProt WITH FirstSet <- {0}, M0Set <- {0}, Smp <- {0}, long <- TRUE, first <- 0, m0 <- 0,
                               rest <- <<>>, pn <- <<>>, tail <- <<>>

VARIABLE c
Init == c = [t |-> "root"]

MX == 6
NR == 2

Cids2 == IF Big THEN {<<>>} ELSE {<<>>, <<5>>, [i \in 1..20 |-> i]}
SmallW == {U!W(k) : k \in {0, 1, 5, 63, 64, 127, 128}}
EdgeW == UNION {{V!EdgeVal(j, d) : d \in {x \in -1..1 : V!EdgeOK(j, x)}} : j \in {14, 31, 62, 63}}
Words == IF Big THEN {U!W(1)} ELSE SmallW \cup EdgeW
OffWords == IF Big THEN {U!W(0)} ELSE Words
Dlens == IF Big THEN {16384} ELSE {0, 1, 3, 130}
RStates == {R!Reasm0,
            [runs |-> <<<<0, 2>>>>, total |-> 5],
            [runs |-> <<<<0, 1>>, <<3, 4>>>>, total |-> 5],
            [runs |-> <<<<0, 1>>, <<3, 4>>>>, total |-> 6]}
RTotals == {U!W(k) : k \in {0, 1, 5, 6, 7, 300}} \cup {U!Pw(62)}
ROffs == {U!W(k) : k \in 0..7} \cup {U!Pw(62)}
RDlens == {0, 1, 2, 4, 10}
Alpha == {0, 1, 128, 129, 255}
PadPre == {0, 1, 5, 70}
Masks == {<<255, 255, 255, 255, 255>>, <<90, 165, 1, 2, 3>>, <<15, 0, 0, 0, 0>>}

Next ==
    \/ c.t = "root" /\ \E f \in {"hs", "recv", "bytes", "pad", "smp"} : c' = [t |-> "seed", f |-> f]
    \/ c.t = "seed" /\ c.f = "hs" /\ \E d \in Cids2, s \in Cids2, tw \in Words, ow \in OffWords, dl \in Dlens :
           c' = [t |-> "hs", d |-> d, s |-> s, tw |-> tw, ow |-> ow, dl |-> dl]
    \/ c.t = "seed" /\ c.f = "recv" /\ \E r \in RStates, tw \in RTotals, ow \in ROffs, dl \in RDlens :
           c' = [t |-> "recv", r |-> r, tw |-> tw, ow |-> ow, dl |-> dl]
    \/ c.t = "seed" /\ c.f = "bytes" /\ c' = [t |-> "bytes", in |-> <<>>]
    \/ c.t = "bytes" /\ Len(c.in) < 6 /\ \E b \in Alpha : c' = [c EXCEPT !.in = Append(c.in, b)]
    \/ c.t = "seed" /\ c.f = "pad" /\ c' = [t |-> "pad"]
    \/ c.t = "seed" /\ c.f = "smp" /\ c' = [t |-> "smp"]

Spec == Init /\ [][Next]_c

(* The quick profile (quick/HdrBody.cfg substitutes NextQuick for Next): the same cases over fewer values, keeping  *)
(* the varint edges (one to two bytes, two to four, the largest accepted and the first refused) of the total and of *)
(* the offset, each against a one-byte other and both equal; the ids empty, one byte and 20 bytes, each against an  *)
(* empty other and both equal; a body length of two varint bytes; a total over MX; byte strings of up to 3 bytes.   *)
WordsQuick == IF Big THEN {U!W(1)}
              ELSE {U!W(k) : k \in {0, 5, 63, 64}} \cup {V!EdgeVal(j, d) : j \in {14, 62}, d \in {-1, 0}}
HsWordsQuick == IF Big THEN {<<U!W(1), U!W(0)>>}
                ELSE {<<w, U!W(5)>> : w \in WordsQuick} \cup {<<U!W(5), w>> : w \in WordsQuick} \cup {<<w, w>> : w \in WordsQuick}
HsCidsQuick == {<<d, <<>>>> : d \in Cids2} \cup {<<<<>>, s>> : s \in Cids2} \cup {<<d, d>> : d \in Cids2}
DlensQuick == IF Big THEN {16384} ELSE {0, 3, 130}
RTotalsQuick == {U!W(k) : k \in {0, 1, 5, 6, 7}} \cup {U!Pw(62)}
ROffsQuick == {U!W(k) : k \in {0, 1, 3, 4, 5, 6}} \cup {U!Pw(62)}
RDlensQuick == {0, 1, 2, 10}
NextQuick ==
    \/ c.t = "root" /\ \E f \in {"hs", "recv", "bytes", "pad", "smp"} : c' = [t |-> "seed", f |-> f]
    \/ c.t = "seed" /\ c.f = "hs" /\ \E ds \in HsCidsQuick, wo \in HsWordsQuick, dl \in DlensQuick :
           c' = [t |-> "hs", d |-> ds[1], s |-> ds[2], tw |-> wo[1], ow |-> wo[2], dl |-> dl]
    \/ c.t = "seed" /\ c.f = "recv" /\ \E r \in RStates, tw \in RTotalsQuick, ow \in ROffsQuick, dl \in RDlensQuick :
           c' = [t |-> "recv", r |-> r, tw |-> tw, ow |-> ow, dl |-> dl]
    \/ c.t = "seed" /\ c.f = "bytes" /\ c' = [t |-> "bytes", in |-> <<>>]
    \/ c.t = "bytes" /\ Len(c.in) < 3 /\ \E b \in Alpha : c' = [c EXCEPT !.in = Append(c.in, b)]
    \/ c.t = "seed" /\ c.f = "pad" /\ c' = [t |-> "pad"]
    \/ c.t = "seed" /\ c.f = "smp" /\ c' = [t |-> "smp"]

Fill(n, b) == [i \in 1..n |-> b]
Prefix(s, n) == SubSeq(s, 1, n)
Rest(s, n) == SubSeq(s, n + 1, Len(s))
Big63(w) == ~U!Lt(w, V!Limit)
EncodeH(h) ==
    <<FirstLong(h.ty, 0), VERSION, Len(h.dcid)>> \o h.dcid \o <<Len(h.scid)>> \o h.scid \o V!Encode(h.bl, 16).bytes
OkLong(h, hl) == [err |-> "ok", n |-> 0, ty |-> h.ty, dcid |-> h.dcid, scid |-> h.scid, bl |-> h.bl, hl |-> hl]

(* ---- a Handshake packet written ---- *)
(* the windows that matter: none, around the header, around the whole datagram *)
HsCaps(hl, need) == {0, hl - 1, hl, hl + 1, need - 1, need, need + 1}
WriteOK ==
    c.t = "hs" =>
        LET data == Fill(c.dl, 7)
            h == HsHeader(c.d, c.s, c.tw, c.ow, c.dl)
            need == HsNeed(c.d, c.s, c.tw, c.ow, c.dl)
            refused == Big63(c.tw) \/ Big63(c.ow)
        IN \A cap \in HsCaps(HeaderLen(h), need) :
              LET r == HsWrite(c.d, c.s, c.tw, c.ow, data, cap)
              IN /\ (r.err = "ok") = (~refused /\ cap >= need)
                 /\ r.err = "ok" => /\ r.out = EncodeH(h) \o HsBody(c.tw, c.ow, data)
                                    /\ Len(r.out) = need
                                    /\ Len(r.out) = HeaderLen(h) + U!Val(h.bl)
WriteRead ==
    c.t = "hs" =>
        LET data == Fill(c.dl, 7)
            h == HsHeader(c.d, c.s, c.tw, c.ow, c.dl)
            need == HsNeed(c.d, c.s, c.tw, c.ow, c.dl)
            r == HsWrite(c.d, c.s, c.tw, c.ow, data, need)
        IN r.err = "ok" =>
              /\ \A tail \in {<<>>, <<0>>, <<192>>} : LongParse(r.out \o tail) = OkLong(h, HeaderLen(h))
              /\ HsRead(Rest(r.out, HeaderLen(h))) = [ok |-> TRUE, total |-> c.tw, off |-> c.ow, data |-> data]
(* the room write_handshake leaves always holds the fragment, up to a body length of two varint bytes *)
RoomFits(win) ==
    LET data == Fill(c.dl, 7)
        dl == Len(c.d)
        sl == Len(c.s)
        fixed == 1 + 1 + 1 + dl + 1 + sl + 2 + V!EncodedLen(c.tw) + V!EncodedLen(c.ow)
    IN (win >= fixed /\ c.dl <= HsRoom(win, dl, sl, c.tw, c.ow)) => HsWrite(c.d, c.s, c.tw, c.ow, data, win).err = "ok"
RoomWins ==
    LET fixed == 1 + 1 + 1 + Len(c.d) + 1 + Len(c.s) + 2 + V!EncodedLen(c.tw) + V!EncodedLen(c.ow)
    IN {fixed + c.dl - 1, fixed + c.dl, fixed + c.dl + 1, fixed + c.dl + 9}
RoomOK ==
    (c.t = "hs" /\ ~Big63(c.tw) /\ ~Big63(c.ow) /\ HsBodyLen(c.tw, c.ow, c.dl) < 16384) =>
        \A win \in RoomWins : RoomFits(win)
RoomAny == (c.t = "hs" /\ ~Big63(c.tw) /\ ~Big63(c.ow)) => \A win \in RoomWins : RoomFits(win)

(* ---- a body that parses is the one encoding, a body that does not parse changes nothing ---- *)
Canon ==
    c.t = "bytes" =>
        LET p == HsRead(c.in)
        IN IF p.ok
           THEN /\ ~Big63(p.total) /\ ~Big63(p.off)
                /\ c.in = HsBody(p.total, p.off, p.data)
           ELSE \A r \in RStates : HsRecv(r, MX, NR, c.in) = [out |-> -1, r |-> r]

(* ---- what reaches the reassembly ---- *)
ValidTotal(tw) == ~U!Lt(U!W(MX), tw) /\ tw # U!Zero
RecvX == HsRecv(c.r, MX, NR, HsBody(c.tw, c.ow, Fill(c.dl, 7)))
RecvOK ==
    c.t = "recv" =>
        LET data == Fill(c.dl, 7)
            body == HsBody(c.tw, c.ow, data)
            x == HsRecv(c.r, MX, NR, body)
            tI == U!Val(c.tw)
            oI == U!Val(c.ow)
        IN /\ HsRead(body) = [ok |-> TRUE, total |-> c.tw, off |-> c.ow, data |-> data]
           /\ ~ValidTotal(c.tw) => x = [out |-> -1, r |-> c.r]
           /\ (ValidTotal(c.tw) /\ ~U!Lt(c.ow, c.tw)) =>
                 x = [out |-> -1, r |-> IF tI # c.r.total THEN [runs |-> <<>>, total |-> tI] ELSE c.r]
           /\ (ValidTotal(c.tw) /\ U!Lt(c.ow, c.tw)) =>
                 /\ x = R!Add(c.r, MX, NR, tI, oI, c.dl)
                 /\ x = R!Add(c.r, MX, NR, tI, oI, IF c.dl < tI - oI THEN c.dl ELSE tI - oI)
PastRefused ==
    (c.t = "recv" /\ ValidTotal(c.tw) /\ U!Lt(c.ow, c.tw) /\ U!Val(c.ow) + c.dl > U!Val(c.tw)) =>
        RecvX = [out |-> -1, r |-> c.r]
NotDone == ~(c.t = "recv" /\ RecvX.out >= 0)

(* ---- pad_to ---- *)
PadOK ==
    c.t = "pad" =>
        \A cap \in 0..140, pre \in PadPre, minLen \in 0..145 :
            pre <= cap =>
                LET out == Fill(pre, 7)
                    r == PadTo(cap, minLen, out)
                IN IF minLen <= cap
                   THEN /\ r.err = "ok"
                        /\ Len(r.out) = (IF minLen > pre THEN minLen ELSE pre)
                        /\ Prefix(r.out, pre) = out
                        /\ r.out = out \o Zeros(IF minLen > pre THEN minLen - pre ELSE 0)
                   ELSE /\ r = [err |-> "BufferTooSmall", n |-> minLen - cap, out |-> out]
                        /\ r.out = out
PadAtomicLate ==
    c.t = "pad" =>
        \A cap \in 0..140, pre \in PadPre, minLen \in 0..145 :
            pre <= cap => (PadToLate(cap, minLen, Fill(pre, 7)).err # "ok" => PadToLate(cap, minLen, Fill(pre, 7)).out = Fill(pre, 7))

(* ---- sample_at and the header protection ---- *)
Pkt(n) == [i \in 1..n |-> (i * 7 + 3) % 256]
(* apply header protection to the packet: the first byte and the packet number, as HeaderProt.tla's Apply *)
Prot(p, po, pl, mask, long) ==
    LET a == HP!Apply(mask, p[1], SubSeq(p, po + 1, po + pl), long)
    IN [i \in 1..Len(p) |-> IF i = 1 THEN a.first ELSE IF i > po /\ i <= po + pl THEN a.pn[i - po] ELSE p[i]]
SampleExact ==
    c.t = "smp" =>
        \A n \in 0..40, po \in 0..30 :
            LET r == SampleAt(Pkt(n), po)
            IN IF n >= po + 20
               THEN r = [err |-> "ok", n |-> 0, s |-> SubSeq(Pkt(n), po + 5, po + 20)] /\ Len(r.s) = SAMPLELEN
               ELSE r = Err("TooShort", 0)
StableFor(skip) ==
    \A n \in {25, 30, 40}, po \in 1..8, pl \in 1..4, long \in BOOLEAN, mask \in Masks :
        po + pl <= n =>
            LET p == Pkt(n)
                q == Prot(p, po, pl, mask, long)
            IN SampleAtSkip(q, po, skip) = SampleAtSkip(p, po, skip)
SampleStable == c.t = "smp" => StableFor(SAMPLESKIP)
SampleStable3 == c.t = "smp" => StableFor(3)
SealSample ==
    c.t = "smp" =>
        \A po \in {1, 2, 5, 25}, pl \in 1..4, pay \in 0..6 :
            LET q == Fill(po + pl + pay + TAGLEN, 9)
                s == SealParts(q, po, pl, pay)
                r == SampleAt(q, po)
            IN /\ (s.err = "TooShort") = (r.err = "TooShort")
               /\ s.err = "ok" => r.err = "ok"
=============================================================================
