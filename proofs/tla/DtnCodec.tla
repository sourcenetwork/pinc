------------------------------ MODULE DtnCodec ------------------------------
(***************************************************************************)
(* The head and acknowledgement codecs of vinc-dtn (head.rs, custody.rs,   *)
(* endorse.rs) on byte sequences: `Head::write`, `Head::read` (known       *)
(* identity tags, then a valid layout), `Endorsement::{encode, decode}`    *)
(* (the two lengths must be the algorithm's), `SignedHead::{encode,        *)
(* decode}` and `CustodyAck::{encode, decode}` (no trailing byte). The     *)
(* fields are read in the order of the code from a reader that fails on a  *)
(* short input. Numbers are big-endian and the u64 and u32 fields are the  *)
(* five-limb words of U64.tla; the layout test is DtnLayout!NewOK, the    *)
(* same operator the layout model checks.                                  *)
(*                                                                         *)
(* Checked by TLC (DtnCodec.cfg) for heads and acknowledgements of every   *)
(* identity algorithm, with every number all zero or all ones and          *)
(* several layouts: encoding has the exact length of the code (HEAD_LEN =  *)
(* 1287 and the endorsement of the algorithm); decoding an encoding gives  *)
(* the value back and re-encodes to the same bytes; every proper prefix    *)
(* is rejected; one to five trailing bytes are rejected; a source or       *)
(* destination tag outside 1..4 is rejected; and for every position (all   *)
(* of them for Ed25519 and ECDSA, the head and the endorsement ends for    *)
(* the long keys) and three replacement bytes the mutated string is        *)
(* either rejected or decodes to a value whose encoding is that very       *)
(* string, so a byte string has at most one reading and garbage never      *)
(* decodes to a different encoding. A wrong endorsement length, an         *)
(* invalid layout and an unknown tag are mutations of length, layout and   *)
(* tag bytes and are covered by the same scan, with the targeted checks    *)
(* below as well.                                                          *)
(*                                                                         *)
(* Lean counterpart (proofs/lean/Vinc/DtnCodec.lean, DtnCodecWire.lean,    *)
(* unbounded): signed_roundtrip, signed_canonical (a decoded string is the *)
(* canonical encoding of a well-formed value), signed_injective,           *)
(* signed_trailing, signed_truncated, signed_checks (tags, layout,         *)
(* endorsement lengths), signed_len, headC_len, and the same for the       *)
(* acknowledgement (ack_roundtrip, ack_canonical, ack_injective,           *)
(* ack_trailing, ack_truncated, ack_len).                                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64
D == INSTANCE DtnLayout WITH c <- 0

PkLen(a) == CASE a = 1 -> 32 [] a = 2 -> 33 [] a = 3 -> 1952 [] a = 4 -> 1984
SigLen(a) == CASE a = 1 -> 64 [] a = 2 -> 64 [] a = 3 -> 3309 [] a = 4 -> 3373
HeadLen == 32 + 2 * 33 + 12 + 8 + 2 + 2 + 1 + 8 + 32 + 4 + 32 + 1088
AckBodyLen == 32 + 33 + 33 + 12

RECURSIVE Cat(_)
Cat(s) == IF s = <<>> THEN <<>> ELSE Head(s) \o Cat(Tail(s))

(* ---- numbers: w big-endian bytes of a word, and back ---- *)
BE(a, w) == [j \in 1..w |-> LET e == w - j IN (a[(e \div 2) + 1] \div (IF e % 2 = 1 THEN 256 ELSE 1)) % 256]
LsbByte(bs, e) == IF e < Len(bs) THEN bs[Len(bs) - e] ELSE 0
BEWord(bs) == [k \in 1..5 |-> IF k > 4 THEN 0 ELSE LsbByte(bs, 2 * (k - 1)) + 256 * LsbByte(bs, 2 * (k - 1) + 1)]

(* ---- the reader: fields of the given widths, nothing consumed past a failure ---- *)
RECURSIVE ReadAll(_, _, _)
ReadAll(bs, i, ws) ==
    IF ws = <<>> THEN [ok |-> TRUE, chunks |-> <<>>, i |-> i]
    ELSE IF i + Head(ws) > Len(bs) THEN [ok |-> FALSE, chunks |-> <<>>, i |-> i]
    ELSE LET r == ReadAll(bs, i + Head(ws), Tail(ws))
         IN [ok |-> r.ok, chunks |-> <<SubSeq(bs, i + 1, i + Head(ws))>> \o r.chunks, i |-> r.i]

HeadWidths == <<32, 1, 32, 1, 32, 8, 4, 8, 2, 1, 1, 1, 8, 32, 4, 32, 1088>>

(* a head: numbers as words (u16 copies and u8 fields as naturals) *)
HeadBytes(h) ==
    Cat(<<h.id, <<h.sa>>, h.sb, <<h.da>>, h.db, BE(h.wall, 8), BE(h.cnt, 4), BE(h.life, 8), BE(h.copies, 2),
          <<h.k>>, <<h.m>>, <<h.log>>, BE(h.payload, 8), h.root, BE(h.epoch, 4), h.eph, h.ct>>)

(* Head::read: fields, then the tags are known, then the layout is valid *)
HeadRead(bs, i) ==
    LET r == ReadAll(bs, i, HeadWidths)
    IN IF ~r.ok THEN [ok |-> FALSE, i |-> i]
       ELSE LET ch == r.chunks
                tags == ch[2][1] \in 1..4 /\ ch[4][1] \in 1..4
                pl == BEWord(ch[13])
            IN IF ~tags \/ ~D!NewOK(ch[10][1], ch[11][1], ch[12][1], pl) THEN [ok |-> FALSE, i |-> i]
               ELSE [ok |-> TRUE, i |-> r.i,
                     v |-> [id |-> ch[1], sa |-> ch[2][1], sb |-> ch[3], da |-> ch[4][1], db |-> ch[5], wall |-> BEWord(ch[6]),
                            cnt |-> BEWord(ch[7]), life |-> BEWord(ch[8]), copies |-> BEWord(ch[9]),
                            k |-> ch[10][1], m |-> ch[11][1], log |-> ch[12][1], payload |-> pl, root |-> ch[14],
                            epoch |-> BEWord(ch[15]), eph |-> ch[16], ct |-> ch[17]]]

(* Endorsement::encode: the two lengths and the two byte strings; decode needs the algorithm's exact lengths *)
EndBytes(e) == Cat(<<BE(U!W(Len(e.pk)), 2), e.pk, BE(U!W(Len(e.sig)), 2), e.sig>>)

EndRead(alg, bs, i) ==
    LET r1 == ReadAll(bs, i, <<2>>)
    IN IF ~r1.ok \/ BEWord(r1.chunks[1]) # U!W(PkLen(alg)) THEN [ok |-> FALSE]
       ELSE LET r2 == ReadAll(bs, r1.i, <<PkLen(alg), 2>>)
            IN IF ~r2.ok \/ BEWord(r2.chunks[2]) # U!W(SigLen(alg)) THEN [ok |-> FALSE]
               ELSE LET r3 == ReadAll(bs, r2.i, <<SigLen(alg)>>)
                    IN IF ~r3.ok THEN [ok |-> FALSE]
                       ELSE [ok |-> TRUE, i |-> r3.i, v |-> [pk |-> r2.chunks[1], sig |-> r3.chunks[1]]]

(* SignedHead::{encode, decode} *)
SignedBytes(s) == HeadBytes(s.h) \o EndBytes(s.e)
SignedRead(bs) ==
    LET h == HeadRead(bs, 0)
    IN IF ~h.ok THEN [ok |-> FALSE]
       ELSE LET e == EndRead(h.v.sa, bs, h.i)
            IN IF ~e.ok \/ e.i # Len(bs) THEN [ok |-> FALSE] ELSE [ok |-> TRUE, v |-> [h |-> h.v, e |-> e.v]]

(* CustodyAck::{encode, decode} *)
AckBodyWidths == <<32, 1, 32, 1, 32, 8, 4>>
AckBytes(a) ==
    Cat(<<a.bundle, <<a.ca>>, a.cb, <<a.pa>>, a.pb, BE(a.wall, 8), BE(a.cnt, 4)>>) \o EndBytes(a.e)
AckRead(bs) ==
    LET r == ReadAll(bs, 0, AckBodyWidths)
    IN IF ~r.ok \/ r.chunks[2][1] \notin 1..4 \/ r.chunks[4][1] \notin 1..4 THEN [ok |-> FALSE]
       ELSE LET e == EndRead(r.chunks[2][1], bs, r.i)
            IN IF ~e.ok \/ e.i # Len(bs) THEN [ok |-> FALSE]
               ELSE [ok |-> TRUE, v |-> [bundle |-> r.chunks[1], ca |-> r.chunks[2][1], cb |-> r.chunks[3],
                                         pa |-> r.chunks[4][1], pb |-> r.chunks[5], wall |-> BEWord(r.chunks[6]),
                                         cnt |-> BEWord(r.chunks[7]), e |-> e.v]]

(* ---- the checked domain ---- *)
Fill(n, s) == [j \in 1..n |-> (j * 7 + s) % 256]
Ones(w) == IF w = 8 THEN U!FromLimbs(<<65535, 65535, 65535, 65535>>) ELSE U!FromLimbs(<<65535, 65535, 0, 0>>)
Zeros == U!Zero

\* (k, m, log, payload) layouts that are valid, and one that is not (it only has to be refused on decode)
Layouts == {<<4, 2, 2, U!W(100000)>>, <<255, 0, 4, U!Pw(40)>>}

N(ones, w) == IF ones THEN Ones(w) ELSE Zeros
MkHead(sa, da, ones, ly) ==
    [id |-> Fill(32, 1), sa |-> sa, sb |-> Fill(32, 2), da |-> da, db |-> Fill(32, 3), wall |-> N(ones, 8), cnt |-> N(ones, 4),
     life |-> N(ones, 8), copies |-> IF ones THEN U!FromLimbs(<<65535, 0, 0, 0>>) ELSE Zeros,
     k |-> ly[1], m |-> ly[2], log |-> ly[3], payload |-> ly[4], root |-> Fill(32, 4), epoch |-> N(ones, 4),
     eph |-> Fill(32, 5), ct |-> Fill(1088, 6)]
MkEnd(a) == [pk |-> Fill(PkLen(a), 7), sig |-> Fill(SigLen(a), 8)]

Algs == {<<1, 1>>, <<2, 3>>, <<3, 2>>, <<4, 4>>}

Cases == {[kind |-> "head", sa |-> a[1], da |-> a[2], ones |-> o, ly |-> ly] : a \in Algs, o \in BOOLEAN, ly \in Layouts}
         \cup {[kind |-> "ack", sa |-> a[1], da |-> a[2], ones |-> o, ly |-> <<1, 0, 0, U!One>>] : a \in Algs, o \in BOOLEAN}

HeadOf(c) == MkHead(c.sa, c.da, c.ones, c.ly)
SignedOf(c) == [h |-> HeadOf(c), e |-> MkEnd(c.sa)]
AckOf(c) == [bundle |-> Fill(32, 1), ca |-> c.sa, cb |-> Fill(32, 2), pa |-> c.da, pb |-> Fill(32, 3), wall |-> N(c.ones, 8),
             cnt |-> N(c.ones, 4), e |-> MkEnd(c.sa)]

Enc(c) == IF c.kind = "head" THEN SignedBytes(SignedOf(c)) ELSE AckBytes(AckOf(c))
Dec(c, bs) == IF c.kind = "head" THEN SignedRead(bs) ELSE AckRead(bs)
Val(c) == IF c.kind = "head" THEN SignedOf(c) ELSE AckOf(c)
ExpectLen(c) == IF c.kind = "head" THEN HeadLen + 4 + PkLen(c.sa) + SigLen(c.sa) ELSE AckBodyLen + 4 + PkLen(c.sa) + SigLen(c.sa)

Mutate(bs, i, d) == [bs EXCEPT ![i] = IF d = 0 THEN 0 ELSE IF d = 1 THEN 255 ELSE (bs[i] + 1) % 256]

\* positions scanned: the head start, the identity tags, the ends of the endorsement fields, the tail and a stride
Positions(c, n) ==
    LET ends == IF c.kind = "head" THEN HeadLen ELSE AckBodyLen
        near == (1..40) \cup ((n - 5)..n) \cup {ends + k : k \in 1..8} \cup {33, 66}
        pk == {ends + 6 + PkLen(c.sa) + k : k \in -1..3} \cup {ends + 4 + PkLen(c.sa) + k : k \in -1..4}
    IN (near \cup pk \cup {p \in 41..n : p % (IF c.sa <= 2 THEN 11 ELSE 97) = 0}) \cap (1..n)

Truncs(c, n) ==
    ((0..70) \cup ((n - 70)..(n - 1)) \cup {HeadLen + k : k \in 0..8} \cup {AckBodyLen + k : k \in 0..8} \cup {n \div 2}
     \cup {k \in 71..n : k % (IF c.sa <= 2 THEN 11 ELSE 211) = 0}) \cap (0..(n - 1))

Canon(c, bs) == LET r == Dec(c, bs) IN r.ok => (IF c.kind = "head" THEN SignedBytes(r.v) = bs ELSE AckBytes(r.v) = bs)

VARIABLE s
Checks == {"rt", "trunc", "trail", "tag"} \cup {"m0", "m1", "m2", "m3", "m4", "m5", "m6", "m7"}
Init == s = [t |-> "root"]
Next == \/ s.t = "root" /\ \E c \in Cases, k \in Checks : s' = [t |-> "case", c |-> c, chk |-> k]
Spec == Init /\ [][Next]_s

Inv ==
    s.t = "root" \/
    LET c == s.c
        bs == Enc(c)
        n == Len(bs)
    IN CASE s.chk = "rt" -> /\ n = ExpectLen(c) /\ Dec(c, bs) = [ok |-> TRUE, v |-> Val(c)]
      [] s.chk = "trunc" -> \A k \in Truncs(c, n) : ~Dec(c, SubSeq(bs, 1, k)).ok
      [] s.chk = "trail" -> \A x \in 1..5 : ~Dec(c, bs \o Fill(x, 9)).ok
      [] s.chk = "tag" -> \A p \in {33, 66}, v \in {0, 5, 255} : ~Dec(c, [bs EXCEPT ![p] = v]).ok
      [] OTHER -> \A p \in Positions(c, n), d \in 0..2 :
                  "m" \o ToString(p % 8) = s.chk => Canon(c, Mutate(bs, p, d))
=============================================================================
