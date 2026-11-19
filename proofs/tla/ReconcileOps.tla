---------------------------- MODULE ReconcileOps ----------------------------
(***************************************************************************)
(* The byte-level building blocks of pinc-reconcile (wire.rs, the index    *)
(* queries of index.rs/mem.rs and the Out buffer of core.rs), written step *)
(* for step as the Lean model Pinc/ReconcileWire.lean and                  *)
(* Pinc/ReconcileMachine.lean. ReconcileCore.tla builds the part rules and *)
(* the handlers on it; Reconcile.tla is the system.                        *)
(*                                                                         *)
(* Conventions. Bytes are ints below 256; an item, a bound and a message   *)
(* are sequences of bytes. A step that can fail returns Ok(v) or Er(name)  *)
(* (a record with the field ok), and Bind(r, LAMBDA x : ...) is the monad  *)
(* of the Rust `?`, so the order of reads, checks and writes is the code's *)
(* and the error a message gets is the code's. An option is <<>> (none) or *)
(* <<x>> (some x).                                                         *)
(*                                                                         *)
(* Varints. TLC integers are 32 bits and a varint carries 63. A decoded    *)
(* value saturates at BIG = 2^23, and its parity (the `more` bit) is kept  *)
(* exactly. Every comparison the code makes on a decoded value is against  *)
(* a length, a count or a limit that the checked configurations keep below *)
(* BIG / 2, so every value at or above BIG behaves as BIG does (a count    *)
(* too large, a length past the buffer, a cold item count that dwarfs the  *)
(* responder's). The encoder is exact for every value below BIG.           *)
(*                                                                         *)
(* The hashes are an oracle `o`: o.H[x] is the 16 byte fingerprint of an   *)
(* item and o.idb[x] its id (8 bytes). The XOR           *)
(* independence of the item hashes is an assumption of the properties, not *)
(* of the model; the one-hot oracle of Reconcile.tla states it exactly.    *)
(*                                                                         *)
(* Lean: Pinc/ReconcileWire.lean (Reconcile.readBound, putBound, ...),     *)
(* ReconcileWireProofs (round trip and canonical form).                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS SPLIT, ALEAF, BLEAF, COLD_RATIO, MAX_NEST, CPL_MAX, FRAME_MAX

BIG == 8388608
VARMAX == 9
FPLEN == 16
IDLEN == 8
SeenBytes == (ALEAF + 7) \div 8

Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

Take(s, n) == IF n >= Len(s) THEN s ELSE SubSeq(s, 1, n)
Drop(s, n) == IF n >= Len(s) THEN <<>> ELSE SubSeq(s, n + 1, Len(s))
Last(s) == s[Len(s)]

RECURSIVE Flat(_)
Flat(ss) == IF ss = <<>> THEN <<>> ELSE Head(ss) \o Flat(Tail(ss))

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN 0 ELSE Head(s) + SumSeq(Tail(s))

None == <<>>
Some(x) == <<x>>

Ok(v) == [ok |-> TRUE, v |-> v]
Er(e) == [ok |-> FALSE, err |-> e]
Bind(r, F(_)) == LET x == r IN IF x.ok THEN F(x.v) ELSE x

(* The LET evaluates the first argument once: TLC passes operator arguments by name, so a plain `r.ok ... r.v` would
   evaluate the whole chain below it three times at every level. *)

(* ---- bytes ---- *)

RECURSIVE Pow2(_)
Pow2(i) == IF i = 0 THEN 1 ELSE 2 * Pow2(i - 1)

BitOf(x, i) == (x \div Pow2(i)) % 2
SetBitByte(x, i) == IF BitOf(x, i) = 1 THEN x ELSE x + Pow2(i)

XorBit(a, b, i) == (BitOf(a, i) + BitOf(b, i)) % 2
Xor8Slow(a, b) ==
    XorBit(a, b, 0) + 2 * XorBit(a, b, 1) + 4 * XorBit(a, b, 2) + 8 * XorBit(a, b, 3)
    + 16 * XorBit(a, b, 4) + 32 * XorBit(a, b, 5) + 64 * XorBit(a, b, 6) + 128 * XorBit(a, b, 7)
(* the byte XOR as a table, computed once *)
XorTab == [a \in 0..255 |-> [b \in 0..255 |-> Xor8Slow(a, b)]]
Xor8(a, b) == XorTab[a][b]

Zero16 == [i \in 1..FPLEN |-> 0]
XorFp(f, g) == [i \in 1..FPLEN |-> Xor8(f[i], g[i])]

RECURSIVE BeBytes(_, _)
BeBytes(w, v) == IF w = 0 THEN <<>> ELSE BeBytes(w - 1, v \div 256) \o <<v % 256>>

(* lexicographic order of byte strings; a prefix sorts first *)
RECURSIVE LexLt(_, _)
LexLt(a, b) ==
    IF b = <<>> THEN FALSE
    ELSE IF a = <<>> THEN TRUE
    ELSE Head(a) < Head(b) \/ (Head(a) = Head(b) /\ LexLt(Tail(a), Tail(b)))

RECURSIVE Cpl(_, _)
Cpl(a, b) == IF a = <<>> \/ b = <<>> THEN 0 ELSE IF Head(a) = Head(b) THEN Cpl(Tail(a), Tail(b)) + 1 ELSE 0

(* ---- varints ---- *)

RECURSIVE Venc(_)
Venc(v) == IF v < 128 THEN <<v>> ELSE <<(v % 128) + 128>> \o Venc(v \div 128)

RECURSIVE PowSat(_)
PowSat(i) == IF i = 0 THEN 1 ELSE Min(BIG, 128 * PowSat(i - 1))

(* The loop of Varint.decode over the first 9 bytes: Ok(<<value, odd, used>>) with the value saturated, or an error
   (all of which `count` maps to Truncated) *)
RECURSIVE DecLoop(_, _, _)
DecLoop(i, acc, bs) ==
    IF bs = <<>> \/ i >= 9 THEN Er("truncated")
    ELSE LET b == Head(bs)
             acc2 == Min(BIG, acc + Min(BIG, (b % 128) * PowSat(i)))
         IN IF b < 128
            THEN IF b = 0 /\ i > 0 THEN Er("truncated") ELSE Ok(<<acc2, i + 1>>)
            ELSE DecLoop(i + 1, acc2, Tail(bs))

(* count: a varint, as <<value, odd, rest>> *)
CountP(r) ==
    Bind(DecLoop(0, 0, r), LAMBDA d : Ok(<<d[1], r[1] % 2, Drop(r, d[2])>>))

Count(r) == Bind(CountP(r), LAMBDA d : Ok(<<d[1], d[3]>>))

(* ---- the reader ---- *)

ReadU8(r) == IF r = <<>> THEN Er("truncated") ELSE Ok(<<Head(r), Tail(r)>>)
ReadBytes(n, r) == IF n <= Len(r) THEN Ok(<<Take(r, n), Drop(r, n)>>) ELSE Er("truncated")

(* ---- bounds ---- *)

PutBound(last, b) ==
    LET c == Min(Cpl(last, b), CPL_MAX)
    IN <<<<c>> \o Venc(Len(b) - c) \o Drop(b, c), b>>

(* read_bound with the canonical check *)
ReadBound(last, r, mx) ==
    Bind(ReadU8(r), LAMBDA a :
    Bind(Count(a[2]), LAMBDA n :
        IF a[1] > Len(last) \/ a[1] + n[1] > mx THEN Er("bound")
        ELSE Bind(ReadBytes(n[1], n[2]), LAMBDA s :
            LET c == a[1]
                rest == Drop(last, c)
                noncanon == c < CPL_MAX /\ rest # <<>> /\ s[1] # <<>> /\ Head(rest) = Head(s[1])
            IN IF noncanon THEN Er("bound") ELSE Ok(<<Take(last, c) \o s[1], s[2]>>))))

PutHead(last, kind, lo, hi) ==
    LET b1 == PutBound(last, lo)
    IN IF hi = None THEN <<<<kind + 128>> \o b1[1], b1[2]>>
       ELSE LET b2 == PutBound(b1[2], hi[1]) IN <<<<kind>> \o b1[1] \o b2[1], b2[2]>>

(* ---- framing and the count field ---- *)

FrameBody(msg) ==
    IF Len(msg) < 3 THEN Er("truncated")
    ELSE IF (msg[1] * 256 + msg[2]) * 256 + msg[3] = Len(msg) - 3 THEN Ok(Drop(msg, 3)) ELSE Er("frame")

FrameHeader(len) == IF len > FRAME_MAX THEN None ELSE Some(BeBytes(3, len))

PutParts(cnt, more) == Venc(cnt * 2 + IF more THEN 1 ELSE 0)

ReadParts(r) ==
    Bind(CountP(r), LAMBDA d :
        IF d[1] \div 2 = 0 /\ d[2] = 1 THEN Er("count")
        ELSE Ok(<<<<d[1] \div 2, d[2] = 1>>, d[3]>>))

(* ---- the index (a strictly ascending sequence S of items; positions are 0-based as in the code) ---- *)

(* the number of items below b: the binary search of MemIndex::rank over the ascending sequence *)
RECURSIVE RankBin(_, _, _, _)
RankBin(S, lo, hi, b) ==
    IF lo >= hi THEN lo
    ELSE LET mid == lo + (hi - lo) \div 2
         IN IF LexLt(S[mid + 1], b) THEN RankBin(S, mid + 1, hi, b) ELSE RankBin(S, lo, mid, b)
Rank(S, b) == RankBin(S, 0, Len(S), b)

ReadItem(lim, S, i) ==
    IF i >= Len(S) THEN Er("index")
    ELSE IF Len(S[i + 1]) <= lim.maxItem THEN Ok(S[i + 1]) ELSE Er("index")

(* The hash oracle holds sorted tables of <<item, value>> pairs, looked up by binary search: o.H the 16 byte
   fingerprints, o.idb the 8 byte ids. A missing item stops TLC with an error. *)
RECURSIVE BinGet(_, _, _, _)
BinGet(tab, lo, hi, x) ==
    IF lo > hi THEN tab[0][2]
    ELSE LET mid == (lo + hi) \div 2
             k == tab[mid][1]
         IN IF k = x THEN tab[mid][2] ELSE IF LexLt(x, k) THEN BinGet(tab, lo, mid - 1, x) ELSE BinGet(tab, mid + 1, hi, x)
HOf(o, x) == BinGet(o.H, 1, Len(o.H), x)
IdOf(o, x) == BinGet(o.idb, 1, Len(o.idb), x)

RECURSIVE XorH(_, _)
XorH(o, xs) == IF xs = <<>> THEN Zero16 ELSE XorFp(HOf(o, Head(xs)), XorH(o, Tail(xs)))

(* the XOR over the positions a..b-1 (0-based) of S *)
RECURSIVE XorRange(_, _, _, _)
XorRange(o, S, a, b) == IF a >= b THEN Zero16 ELSE XorFp(HOf(o, S[a + 1]), XorRange(o, S, a + 1, b))

Slice(S, a, b) == IF b <= a THEN <<>> ELSE SubSeq(S, a + 1, b)
FpRange(o, S, a, b) == XorRange(o, S, a, b)

RECURSIVE DataLen(_)
DataLen(xs) == IF xs = <<>> THEN 0 ELSE Len(Venc(Len(Head(xs)))) + Len(Head(xs)) + DataLen(Tail(xs))

(* ---- the message under construction ---- *)

OutEmpty == [body |-> <<>>, stage |-> <<>>, last |-> <<>>, snap |-> <<>>]
OutReset(o) == [o EXCEPT !.body = <<>>, !.stage = <<>>, !.last = <<>>]
OutMark(o) == <<Len(o.body), [o EXCEPT !.snap = o.last]>>
OutRollback(o, mark) == [o EXCEPT !.body = Take(o.body, mark), !.stage = <<>>, !.last = o.snap]
OutHead(o, kind, lo, hi) ==
    LET ph == PutHead(o.last, kind, lo, hi)
    IN [o EXCEPT !.body = o.body \o ph[1], !.last = ph[2]]
OutStageItem(o, x) == [o EXCEPT !.stage = o.stage \o Venc(Len(x)) \o x]

=============================================================================
