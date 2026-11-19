---------------------------- MODULE DagCborLen ----------------------------
(***************************************************************************)
(* The encoded sizes of pinc-dag cbor_len.rs (head_len, text_len,          *)
(* cid_len) against the bytes the canonical DAG-CBOR encoder of pinc-wire  *)
(* (cbor/encode.rs: head_shape, Encoder::head, string, header, tag_cid)    *)
(* writes for the same piece, on the machine integers of U64.tla.          *)
(*                                                                         *)
(* Module invariant of cbor_len.rs: each function returns exactly the byte *)
(* count the encoder writes for the same piece. Checked by TLC             *)
(* (DagCborLen.cfg) for every argument below SmallMax and, for every j in  *)
(* 0..64, 2^j - 1, 2^j and 2^j + 1 (both ends of every header width,       *)
(* u64::MAX among them):                                                   *)
(*   HeadSize  head_len(a) is the length of the header Encoder::head       *)
(*             writes for a, under every major type 0..6;                  *)
(*   TextSize  text_len(n) is what Encoder::text and Encoder::bytes write  *)
(*             for n payload bytes; its saturating_add never saturates;    *)
(*   CidSize   cid_len(n) is what Encoder::tag_cid writes for a CID of n   *)
(*             bytes, its `n as u64 + 1` never overflows (U64 Add64 stops  *)
(*             TLC if it did) and it never saturates.                      *)
(* A length n is below 2^63: no slice is longer than isize::MAX bytes (the *)
(* semantics of Rust's core library, an assumption). head_len is constant  *)
(* between the powers of two 2^8, 2^16, 2^32, so the boundary set reaches  *)
(* each piece at both of its ends; the property needs no Lean theorem.     *)
(*                                                                         *)
(* The item operators at the end give the bytes and the written length of  *)
(* one DAG-CBOR item as the encoder writes it (an item is what the pull    *)
(* decoder of pinc-wire yields, Item in cbor/mod.rs); DagItems.tla,        *)
(* DagBlock.tla and DagCar.tla use them.                                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

U == INSTANCE U64

(* ---- the code: crates/pinc-dag/src/cbor_len.rs ---- *)

(* head_len: 0..=23 -> 1, 24..=0xff -> 2, 0x100..=0xffff -> 3, 0x1_0000..=0xffff_ffff -> 5, else 9 *)
HeadLen(a) ==
    IF U!Lt(a, U!W(24)) THEN 1
    ELSE IF U!Lt(a, U!W(256)) THEN 2
    ELSE IF U!Lt(a, U!Pw(16)) THEN 3
    ELSE IF U!Lt(a, U!Pw(32)) THEN 5
    ELSE 9

(* usize::saturating_add on 64-bit words *)
SatAdd(a, b) == LET s == U!Add(a, b) IN IF U!Lt(s, U!Pw(64)) THEN s ELSE U!Max64

(* text_len: head_len(n as u64).saturating_add(n) *)
TextLen(n) == SatAdd(U!W(HeadLen(n)), n)

(* cid_len: 2usize.saturating_add(head_len(n as u64 + 1)).saturating_add(1).saturating_add(n) *)
CidLen(n) == SatAdd(SatAdd(SatAdd(U!W(2), U!W(HeadLen(U!Add64(n, U!One)))), U!One), n)

(* ---- the encoder: crates/pinc-wire/src/cbor/encode.rs ---- *)

(* head_shape: (initial-byte info, trailing argument bytes) *)
HeadShape(a) ==
    IF U!Lt(a, U!W(24)) THEN <<U!Val(a), 0>>
    ELSE IF U!Lt(a, U!W(256)) THEN <<24, 1>>
    ELSE IF U!Lt(a, U!Pw(16)) THEN <<25, 2>>
    ELSE IF U!Lt(a, U!Pw(32)) THEN <<26, 4>>
    ELSE <<27, 8>>

(* the big-endian bytes of a word (arg.to_be_bytes()) *)
Be8(w) == <<w[4] \div 256, w[4] % 256, w[3] \div 256, w[3] % 256, w[2] \div 256, w[2] % 256, w[1] \div 256, w[1] % 256>>

(* Encoder::head: put_u8(major << 5 | info), then the last `tail` bytes of to_be_bytes *)
EncHead(major, a) == LET sh == HeadShape(a) IN <<major * 32 + sh[1]>> \o SubSeq(Be8(a), 9 - sh[2], 8)

(* the bytes Encoder::text / Encoder::bytes write for n payload bytes, and Encoder::tag_cid for a CID of n bytes *)
WrittenString(major, n) == U!Add(U!W(Len(EncHead(major, n))), n)
WrittenCid(n) == U!Add(U!W(Len(EncHead(6, U!W(42))) + Len(EncHead(2, U!Add(n, U!One))) + 1), n)

(* ---- items: one DAG-CBOR item as the encoder writes it ---- *)
(* An item is a record with a kind k: "uint", "nint", "tag" (field v), "array", "map" (field n, the count),        *)
(* "bytes", "text" (field b, the payload bytes), "null", "bool", "float". Counts and integers are naturals below    *)
(* 2^30 here (DagItems.tla says how a trace bounds them).                                                           *)

Major(it) ==
    CASE it.k = "uint" -> 0 [] it.k = "nint" -> 1 [] it.k = "bytes" -> 2 [] it.k = "text" -> 3
      [] it.k = "array" -> 4 [] it.k = "map" -> 5 [] it.k = "tag" -> 6

ItemArg(it) ==
    CASE it.k \in {"uint", "nint", "tag"} -> U!W(it.v)
      [] it.k \in {"array", "map"} -> U!W(it.n)
      [] it.k \in {"bytes", "text"} -> U!W(Len(it.b))

(* the bytes of the items the model writes (no bool or float: no writer of pinc-dag emits one) *)
ItemBytes(it) ==
    CASE it.k \in {"bytes", "text"} -> EncHead(Major(it), ItemArg(it)) \o it.b
      [] it.k \in {"uint", "nint", "tag", "array", "map"} -> EncHead(Major(it), ItemArg(it))
      [] it.k = "null" -> <<246>>

RECURSIVE ItemsBytes(_)
ItemsBytes(s) == IF s = <<>> THEN <<>> ELSE ItemBytes(Head(s)) \o ItemsBytes(Tail(s))

(* the length of an item as the encoder writes it: Encoder::bool and null write 1 byte, float 9 *)
ItemWritten(it) ==
    CASE it.k \in {"bytes", "text"} -> Len(EncHead(Major(it), ItemArg(it))) + Len(it.b)
      [] it.k \in {"uint", "nint", "tag", "array", "map"} -> Len(EncHead(Major(it), ItemArg(it)))
      [] it.k \in {"null", "bool"} -> 1
      [] it.k = "float" -> 9

RECURSIVE ItemsWritten(_)
ItemsWritten(s) == IF s = <<>> THEN 0 ELSE ItemWritten(Head(s)) + ItemsWritten(Tail(s))

(* the sizes of cbor_len.rs on native lengths below 2^30, as the callers in block/encode.rs and car/writer.rs use them *)
HL(n) == HeadLen(U!W(n))
TL(n) == U!Val(TextLen(U!W(n)))
CL(n) == U!Val(CidLen(U!W(n)))

(***************************************************************************)
(* The checked domain                                                      *)
(***************************************************************************)
CONSTANT SmallMax

EdgeVal(j, d) ==
    IF d = -1 THEN U!Sub(U!Pw(j), U!One) ELSE IF d = 0 THEN U!Pw(j) ELSE U!Add(U!Pw(j), U!One)
EdgeOK(j, d) == (j >= 1 \/ d >= 0) /\ (j < 64 \/ d = -1)

(* the root has one successor per seed (a block of 64 small values or one boundary value), a seed one per value *)
VARIABLE c
Init == c = [t |-> "root"]

Seeds ==
    {[f |-> "blk", b |-> b] : b \in 0..((SmallMax - 1) \div 64)}
    \cup {[f |-> "edge", j |-> j, d |-> d] : j \in 0..64, d \in -1..1}

Expand(sd) ==
    CASE sd.f = "blk" -> {[t |-> "v", v |-> U!W(k)] : k \in (64 * sd.b)..(IF 64 * sd.b + 63 < SmallMax THEN 64 * sd.b + 63 ELSE SmallMax - 1)}
      [] sd.f = "edge" -> IF EdgeOK(sd.j, sd.d) THEN {[t |-> "v", v |-> EdgeVal(sd.j, sd.d)]} ELSE {}

Next ==
    \/ c.t = "root" /\ \E sd \in Seeds : c' = [t |-> "seed", sd |-> sd]
    \/ c.t = "seed" /\ \E x \in Expand(c.sd) : c' = x

Spec == Init /\ [][Next]_c

(***************************************************************************)
(* The properties                                                          *)
(***************************************************************************)
HeadSize(a) == \A m \in 0..6 : Len(EncHead(m, a)) = HeadLen(a)

TextSize(n) ==
    U!Lt(n, U!Pw(63)) =>
        /\ TextLen(n) = WrittenString(3, n)
        /\ TextLen(n) = WrittenString(2, n)
        /\ U!Lt(TextLen(n), U!Max64)

CidSize(n) ==
    U!Lt(n, U!Pw(63)) =>
        /\ CidLen(n) = WrittenCid(n)
        /\ U!Lt(CidLen(n), U!Max64)

Inv == c.t = "v" => HeadSize(c.v) /\ TextSize(c.v) /\ CidSize(c.v)
=============================================================================
