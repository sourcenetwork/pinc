---------------------------- MODULE ValuesWire ----------------------------
(***************************************************************************)
(* The wire codecs of vinc-values (wire.rs), written step for step on the  *)
(* Reader and Writer of vinc-wire and the machine integers of U64.tla:     *)
(*   REQ        Req::parse, Req::total_len, Req::encode                    *)
(*   GROUP      GroupHeader::parse, GroupHeader::encode                    *)
(*   PROOF      ProofFrame::parse, ProofFrame::write_head                  *)
(*   PROOF_REQ  ProofReq::parse, ProofReq::encode (sid is a varint, see    *)
(*              Varint.tla, which this module instantiates)                *)
(* A byte string is a sequence of integers 0..255. A parse returns         *)
(* [ok |-> TRUE, fields, n] or [ok |-> FALSE, err, msg, needed], with err  *)
(* one of "truncated" (WireError::Truncated, needed bytes), "unexpected"   *)
(* (WireError::Unexpected, msg the reason), "toolong", "nonminimal"        *)
(* (varint errors), "overflow" and "small" (an encode: VarintOverflow,     *)
(* BufferTooSmall). An encode into a buffer out returns [ok, n, after]:    *)
(* the bytes written and the buffer afterwards, so the properties can say  *)
(* that a failed encode leaves the buffer as it was. u64 and u32 fields    *)
(* are words of U64.tla, u8 and u16 fields are plain integers.             *)
(*                                                                         *)
(* The properties are stated apart from the code (the Spec* operators work *)
(* on the byte positions and on the exact sum of the bytes times powers of *)
(* 256, never on the code's operators):                                    *)
(*  - an input is accepted exactly when the conditions of the format hold  *)
(*    (type byte, count at most 255, flag 0 or 1, length not 0, proof a     *)
(*    whole number of pairs and at most 1100 bytes, no trailing byte after *)
(*    a PROOF_REQ, a canonical varint); the fields equal the big-endian    *)
(*    values of their bytes; the error kind and msg of a refusal are the   *)
(*    first condition that fails, and the Truncated shortfall is the end   *)
(*    of the first field that does not fit, less the length;               *)
(*  - canonical: an accepted input re-encodes to exactly the bytes the     *)
(*    parse consumed (the whole input for a PROOF_REQ, the prefix of n     *)
(*    bytes for the others);                                               *)
(*  - round trip: parse of an encode is the value, with any rest after it; *)
(*  - an encode refuses more than 255 ranges and a short buffer with the    *)
(*    exact error and writes nothing then; on success it writes exactly    *)
(*    the bytes and leaves the rest of the buffer alone;                   *)
(*  - every strict prefix of a valid input is refused as truncated;        *)
(*  - total_len agrees with parse.                                         *)
(*                                                                         *)
(* Checked by TLC (ValuesWire.cfg) over a machine whose root has one       *)
(* successor per seed, each seed standing for a family of cases (172303    *)
(* distinct states in all):                                                *)
(*  REQ    - every type byte 0..255 (count 2) at the cut lengths           *)
(*           0,1,2,33,34,66,67; every count byte 0..255 (type 1) at every  *)
(*           cut length from 0 to 1 past the full string for counts up to  *)
(*           33, and at the cuts 0 1 2 32 33 34 35 49 50 and around the     *)
(*           full size for the larger counts; each full string has 32 root *)
(*           bytes and 16*count range bytes that are all different, so a   *)
(*           wrong byte order or field offset shows;                       *)
(*  GROUP  - every combination of 5 type bytes {0,1,2,3,255}, 4 offset     *)
(*           words, 6 length words, 10 proof-length words and 5 flag bytes *)
(*           {0,1,2,128,255}; every type byte, every flag byte and every   *)
(*           one of the 65536 proof lengths with the other fields valid;   *)
(*           every cut length 0..17 of two valid headers;                  *)
(*  PROOF  - 14 id forms (the canonical encodings of 0, 1, 127, 128,       *)
(*           16383, 2^62 and 2^63-1 and 7 broken ones: empty, cut, non-    *)
(*           minimal, too long, 2^63) with 4 fixed tails and 18 proof      *)
(*           lengths (0, 1, 63, 64, 65, 127, 128, 1087, 1088, 1089, 1100,  *)
(*           1101, 1151, 1152, 1153, 1216, 1300, 1400); every cut length of*)
(*           the frame for proof lengths 0 and 64;                         *)
(*  PROOF_REQ - the 14 id forms with 4 pairs of offsets and the trailers   *)
(*           {}, {0}, {255,255}, and every cut length;                     *)
(*  every byte string of 0 to 2 bytes over all 256 values, parsed by all   *)
(*  four codecs; every string of 0 to 4 bytes over the class alphabet      *)
(*  {0,1,2,64,127,128,129,192,255} followed by a valid tail, as the id of  *)
(*  a PROOF and of a PROOF_REQ (every non-canonical varint form in place);  *)
(*  the encoders: REQ with 0 1 2 3 31 32 33 34 255 256 ranges at every     *)
(*  buffer size up to 3 ranges and at the sizes 0 1 33 34 35 and around    *)
(*  the full size for the others; GROUP with 5 offset words, 5 length      *)
(*  words (zero among them), 7 proof lengths and both flags (valid and     *)
(*  invalid); PROOF and PROOF_REQ heads with the ids 2^j-1, 2^j, 2^j+1 for *)
(*  j in {0,6,7,13,14,20,21,27,28,34,35,41,42,48,49,55,56,62,63,64} (the   *)
(*  edges of every byte length, 2^63 and u64::MAX among them) and buffers  *)
(*  of 0, 1, n-1, n and n+1 bytes (n the head size).                       *)
(* Not covered by enumeration here and covered unboundedly by Lean: longer *)
(* byte strings of other shapes, ids and offsets outside the classes.      *)
(*                                                                         *)
(* Lean counterparts (proofs/lean/Vinc/ValuesWire*.lean, namespace         *)
(* Vinc.ValuesWire):                                                       *)
(*   REQ        reqParse_eq, req_accept_iff, req_canonical, req_injective, *)
(*              req_roundtrip, reqEncode_ok, reqEncode_short,              *)
(*              reqEncode_too_many, req_reject_type, req_reject_count,     *)
(*              req_reject_short, req_prefix_truncated, totalLen_of_parse, *)
(*              totalLen_agrees, totalLen_reject_parse_reject              *)
(*   GROUP      ghBody_eq, ghParse_eq, gh_accept_iff, gh_canonical,        *)
(*              gh_injective, gh_roundtrip, gh_prefix_truncated,           *)
(*              gh_reject_type, gh_reject_follows, gh_reject_empty,        *)
(*              gh_reject_pairs                                            *)
(*   PROOF      pfTail_eq, pf_shape, pf_canonical, pf_injective,           *)
(*              pf_roundtrip, pf_reject_varint, pf_reject_proof,           *)
(*              pf_prefix_truncated, pfWriteHead_ok, pfWriteHead_short,    *)
(*              pfWriteHead_overflow                                       *)
(*   PROOF_REQ  prTail_eq, pr_shape, pr_canonical, pr_injective,           *)
(*              pr_roundtrip, pr_reject_trailing, pr_reject_varint,        *)
(*              pr_prefix_truncated, prEncode_ok, prEncode_short,          *)
(*              prEncode_overflow                                          *)
(*   ids        decode_nonminimal_run, decode_truncated_run,               *)
(*              decode_too_long_run, decode_cut_truncated, and Varint.lean  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64
V == INSTANCE Varint WITH SmallMax <- 0, c <- 0

VARIABLE c

ReqFixed == 34
GroupHdr == 16
MaxReq == 255
ParentLen == 64
WtPmax == 1100
TReq == 1
TGroup == 2
ProofFixed == 21

(* ---- results ---- *)

Unexp(msg) == [ok |-> FALSE, err |-> "unexpected", msg |-> msg, needed |-> 0]
Trunc(n) == [ok |-> FALSE, err |-> "truncated", msg |-> "", needed |-> n]
Fail(kind) == [ok |-> FALSE, err |-> kind, msg |-> "", needed |-> 0]

(* ---- big-endian fields ---- *)

(* byte at little-endian position p of a big-endian byte string (0 past its length) *)
BeByte(bs, p) == IF p < Len(bs) THEN bs[Len(bs) - p] ELSE 0

(* u64::from_be_bytes, u32::from_be_bytes: the word of at most 8 bytes *)
BeWord(bs) == <<BeByte(bs, 0) + 256 * BeByte(bs, 1), BeByte(bs, 2) + 256 * BeByte(bs, 3),
                BeByte(bs, 4) + 256 * BeByte(bs, 5), BeByte(bs, 6) + 256 * BeByte(bs, 7), 0>>

(* v.to_be_bytes() of n bytes *)
BeBytes(w, n) == [i \in 1..n |-> U!Val(U!Low(U!Shr(w, 8 * (n - i)), 8))]

(* ---- the Reader (vinc-wire reader.rs) over the bytes not yet consumed ---- *)

RdBytes(rest, n) ==
    IF n <= Len(rest)
    THEN [ok |-> TRUE, v |-> SubSeq(rest, 1, n), rest |-> SubSeq(rest, n + 1, Len(rest))]
    ELSE Trunc(n - Len(rest))
RdU8(rest) == LET r == RdBytes(rest, 1) IN IF r.ok THEN [r EXCEPT !.v = r.v[1]] ELSE r
RdU16(rest) == LET r == RdBytes(rest, 2) IN IF r.ok THEN [r EXCEPT !.v = r.v[1] * 256 + r.v[2]] ELSE r
RdW(rest, n) == LET r == RdBytes(rest, n) IN IF r.ok THEN [r EXCEPT !.v = BeWord(r.v)] ELSE r
RdVar(rest) ==
    LET d == V!Decode(rest)
    IN IF d.kind = "ok" THEN [RdBytes(rest, d.n) EXCEPT !.v = d.v]
       ELSE IF d.kind = "truncated" THEN Trunc(1) ELSE Fail(d.kind)

(* ---- the Writer: a write that does not fit changes nothing ---- *)

WriteOk(bytes, out) ==
    IF Len(bytes) <= Len(out)
    THEN [ok |-> TRUE, n |-> Len(bytes), after |-> bytes \o SubSeq(out, Len(bytes) + 1, Len(out))]
    ELSE [ok |-> FALSE, err |-> "small", msg |-> "", needed |-> Len(bytes) - Len(out), after |-> out]

(* ---- REQ ---- *)

ReqParse(buf) ==
    LET t == RdU8(buf)
        root == RdBytes(t.rest, 32)
        cnt == RdU8(root.rest)
        rng == RdBytes(cnt.rest, 16 * cnt.v)
    IN IF ~t.ok THEN t
       ELSE IF t.v # TReq THEN Unexp("not a request")
       ELSE IF ~root.ok THEN root
       ELSE IF ~cnt.ok THEN cnt
       ELSE IF cnt.v > MaxReq THEN Unexp("too many ranges")
       ELSE IF ~rng.ok THEN rng
       ELSE [ok |-> TRUE, root |-> root.v, ranges |-> rng.v, n |-> ReqFixed + 16 * cnt.v]

ReqTotalLen(head) ==
    IF Len(head) < ReqFixed THEN Trunc(ReqFixed - Len(head))
    ELSE IF head[1] # TReq \/ head[ReqFixed] > MaxReq THEN Unexp("bad request header")
    ELSE [ok |-> TRUE, n |-> ReqFixed + 16 * head[ReqFixed]]

(* Req::ranges: the spans of the 16-byte chunks *)
SpansOf(rb) == [i \in 1..(Len(rb) \div 16) |->
                   [off |-> BeWord(SubSeq(rb, 16 * (i - 1) + 1, 16 * (i - 1) + 8)),
                    len |-> BeWord(SubSeq(rb, 16 * (i - 1) + 9, 16 * i))]]

RECURSIVE SpanBytes(_)
SpanBytes(spans) ==
    IF spans = <<>> THEN <<>>
    ELSE BeBytes(Head(spans).off, 8) \o BeBytes(Head(spans).len, 8) \o SpanBytes(Tail(spans))

(* Req::encode: refuses over 255 ranges (a count past 255 does not fit the u8), checks the room, then writes *)
ReqEncode(root, spans, out) ==
    IF Len(spans) > MaxReq
    THEN [ok |-> FALSE, err |-> "unexpected", msg |-> "too many ranges", needed |-> 0, after |-> out]
    ELSE WriteOk(<<TReq>> \o root \o <<Len(spans)>> \o SpanBytes(spans), out)

(* ---- GROUP ---- *)

GhParse(buf) ==
    IF Len(buf) < GroupHdr THEN Trunc(GroupHdr - Len(buf))
    ELSE LET h == SubSeq(buf, 1, GroupHdr)
             t == RdU8(h)
             off == RdW(t.rest, 8)
             len == RdW(off.rest, 4)
             plen == RdU16(len.rest)
             fl == RdU8(plen.rest)
         IN IF t.v # TGroup THEN Unexp("not a group")
            ELSE IF fl.v > 1 THEN Unexp("bad follows flag")
            ELSE IF len.v = U!Zero \/ plen.v % ParentLen # 0 THEN Unexp("bad group lengths")
            ELSE [ok |-> TRUE, off |-> off.v, len |-> len.v, plen |-> plen.v, follows |-> (fl.v = 1)]

GhEncode(h) ==
    <<TGroup>> \o BeBytes(h.off, 8) \o BeBytes(h.len, 4) \o BeBytes(U!W(h.plen), 2) \o <<IF h.follows THEN 1 ELSE 0>>

(* ---- PROOF ---- *)

PfParse(body) ==
    LET sid == RdVar(body)
        glog == RdU8(sid.rest)
        start == RdW(glog.rest, 8)
        wn == RdW(start.rest, 4)
        ln == RdW(wn.rest, 8)
        proof == RdBytes(ln.rest, Len(ln.rest))
    IN IF ~sid.ok THEN sid
       ELSE IF ~glog.ok THEN glog
       ELSE IF ~start.ok THEN start
       ELSE IF ~wn.ok THEN wn
       ELSE IF ~ln.ok THEN ln
       ELSE IF Len(proof.v) % ParentLen # 0 \/ Len(proof.v) > WtPmax THEN Unexp("bad proof length")
       ELSE [ok |-> TRUE, sid |-> sid.v, glog |-> glog.v, start |-> start.v, wn |-> wn.v, ln |-> ln.v, proof |-> proof.v]

(* ProofFrame::write_head: the head is built whole, then copied whole *)
PfHead(sid, glog, start, wn, ln, out) ==
    LET e == V!Encode(sid, 9)
    IN IF e.kind = "overflow" THEN [ok |-> FALSE, err |-> "overflow", msg |-> "", needed |-> 0, after |-> out]
       ELSE WriteOk(e.bytes \o <<glog>> \o BeBytes(start, 8) \o BeBytes(wn, 4) \o BeBytes(ln, 8), out)

(* ---- PROOF_REQ ---- *)

PrParse(body) ==
    LET sid == RdVar(body)
        from == RdW(sid.rest, 8)
        upto == RdW(from.rest, 8)
    IN IF ~sid.ok THEN sid
       ELSE IF ~from.ok THEN from
       ELSE IF ~upto.ok THEN upto
       ELSE IF upto.rest # <<>> THEN Unexp("trailing bytes")
       ELSE [ok |-> TRUE, sid |-> sid.v, from |-> from.v, upto |-> upto.v]

PrEncode(r, out) ==
    LET e == V!Encode(r.sid, 9)
    IN IF e.kind = "overflow" THEN [ok |-> FALSE, err |-> "overflow", msg |-> "", needed |-> 0, after |-> out]
       ELSE WriteOk(e.bytes \o BeBytes(r.from, 8) \o BeBytes(r.upto, 8), out)

(* ---- the specification, apart from the code ---- *)

Prefix(s, n) == SubSeq(s, 1, n)

(* the exact value of a big-endian byte string: the sum of byte * 2^(8 * (n - i)) *)
RECURSIVE BeSpecFrom(_, _)
BeSpecFrom(bs, i) == IF i > Len(bs) THEN U!Zero ELSE U!Add(U!Shl(U!W(bs[i]), 8 * (Len(bs) - i)), BeSpecFrom(bs, i + 1))
BeSpec(bs) == BeSpecFrom(bs, 1)

(* the end of the first field that does not fit in a string of length L, less L *)
NeededSpec(ends, L) ==
    LET e == CHOOSE e \in ends : e > L /\ \A e2 \in ends : e2 > L => e <= e2
    IN e - L

(* a refusal: the error kind, the reason and the shortfall are as the format says *)
RefusedAs(r, kind, msg, needed) ==
    /\ ~r.ok /\ r.err = kind /\ r.msg = msg /\ r.needed = needed

(* -- REQ -- *)
ReqSpecOK(s) == Len(s) >= ReqFixed /\ s[1] = TReq /\ s[ReqFixed] <= MaxReq /\ Len(s) >= ReqFixed + 16 * s[ReqFixed]

ReqRefusal(s, r) ==
    IF Len(s) = 0 THEN RefusedAs(r, "truncated", "", 1)
    ELSE IF s[1] # TReq THEN RefusedAs(r, "unexpected", "not a request", 0)
    ELSE IF Len(s) < ReqFixed THEN RefusedAs(r, "truncated", "", NeededSpec({33, 34}, Len(s)))
    ELSE IF s[ReqFixed] > MaxReq THEN RefusedAs(r, "unexpected", "too many ranges", 0)
    ELSE RefusedAs(r, "truncated", "", ReqFixed + 16 * s[ReqFixed] - Len(s))

SpecSpans(s) == [i \in 1..s[ReqFixed] |->
                    [off |-> BeSpec(SubSeq(s, 35 + 16 * (i - 1), 42 + 16 * (i - 1))),
                     len |-> BeSpec(SubSeq(s, 43 + 16 * (i - 1), 50 + 16 * (i - 1)))]]

Sent(n) == [i \in 1..n |-> 170]

(* full >= 0 says the string is a cut of a valid input of that length *)
ReqCase(s, full) ==
    LET r == ReqParse(s)
        t == ReqTotalLen(s)
    IN /\ r.ok = ReqSpecOK(s)
       /\ ~r.ok => ReqRefusal(s, r)
       /\ r.ok =>
            /\ r.n = ReqFixed + 16 * s[ReqFixed] /\ r.n <= Len(s)
            /\ r.root = SubSeq(s, 2, 33)
            /\ SpansOf(r.ranges) = SpecSpans(s)                                        \* fields
            /\ LET e == ReqEncode(r.root, SpansOf(r.ranges), Sent(Len(s) + 1))          \* canonical
               IN e.ok /\ e.n = r.n /\ SubSeq(e.after, 1, r.n) = Prefix(s, r.n)
                  /\ SubSeq(e.after, r.n + 1, Len(s) + 1) = Sent(Len(s) + 1 - r.n)
       /\ (full >= 0 /\ Len(s) < full) => (~r.ok /\ r.err = "truncated")               \* every cut
       /\ IF Len(s) >= ReqFixed                                                         \* total_len
          THEN /\ t.ok = (s[1] = TReq /\ s[ReqFixed] <= MaxReq)
               /\ ~t.ok => (RefusedAs(t, "unexpected", "bad request header", 0)
                            /\ ~r.ok /\ r.err = "unexpected")
               /\ t.ok => (r.ok = (Len(s) >= t.n)) /\ (r.ok => r.n = t.n)
          ELSE RefusedAs(t, "truncated", "", ReqFixed - Len(s))

(* -- GROUP -- *)
GhSpecOK(s) ==
    /\ Len(s) >= GroupHdr /\ s[1] = TGroup /\ s[16] <= 1
    /\ BeSpec(SubSeq(s, 10, 13)) # U!Zero /\ (s[14] * 256 + s[15]) % ParentLen = 0

GhRefusal(s, r) ==
    IF Len(s) < GroupHdr THEN RefusedAs(r, "truncated", "", GroupHdr - Len(s))
    ELSE IF s[1] # TGroup THEN RefusedAs(r, "unexpected", "not a group", 0)
    ELSE IF s[16] > 1 THEN RefusedAs(r, "unexpected", "bad follows flag", 0)
    ELSE RefusedAs(r, "unexpected", "bad group lengths", 0)

GhCase(s, full) ==
    LET r == GhParse(s)
    IN /\ r.ok = GhSpecOK(s)
       /\ ~r.ok => GhRefusal(s, r)
       /\ r.ok =>
            /\ r.off = BeSpec(SubSeq(s, 2, 9)) /\ r.len = BeSpec(SubSeq(s, 10, 13))
            /\ r.plen = U!Val(BeSpec(SubSeq(s, 14, 15))) /\ r.follows = (s[16] = 1)
            /\ GhEncode(r) = Prefix(s, GroupHdr)                                        \* canonical
       /\ (full >= 0 /\ Len(s) < full) => (~r.ok /\ r.err = "truncated")

(* -- PROOF and PROOF_REQ: the id is a varint, the spec of Varint.tla -- *)
SidN(s) == IF \E n \in 1..(IF Len(s) < 9 THEN Len(s) ELSE 9) : V!IsEnc(Prefix(s, n))
           THEN CHOOSE n \in 1..(IF Len(s) < 9 THEN Len(s) ELSE 9) : V!IsEnc(Prefix(s, n))
           ELSE 0

(* the refusal of a bad id: the error kind of Varint.tla, a cut id is Truncated of 1 *)
SidRefusal(s, r) ==
    LET d == V!Decode(s)
    IN IF d.kind = "truncated" THEN RefusedAs(r, "truncated", "", 1) ELSE RefusedAs(r, d.kind, "", 0)

PfCase(s, full) ==
    LET r == PfParse(s)
        n == SidN(s)
        pl == Len(s) - n - ProofFixed
        ends == {n + 1, n + 9, n + 13, n + 21}
    IN /\ r.ok = (n > 0 /\ pl >= 0 /\ pl % ParentLen = 0 /\ pl <= WtPmax)
       /\ (~r.ok /\ n = 0) => SidRefusal(s, r)
       /\ (~r.ok /\ n > 0) =>
            IF pl < 0 THEN RefusedAs(r, "truncated", "", NeededSpec(ends, Len(s)))
            ELSE RefusedAs(r, "unexpected", "bad proof length", 0)
       /\ r.ok =>
            /\ r.sid = V!ValueOf(Prefix(s, n), 1) /\ r.glog = s[n + 1]
            /\ r.start = BeSpec(SubSeq(s, n + 2, n + 9)) /\ r.wn = BeSpec(SubSeq(s, n + 10, n + 13))
            /\ r.ln = BeSpec(SubSeq(s, n + 14, n + 21)) /\ r.proof = SubSeq(s, n + 22, Len(s))
            /\ Len(r.proof) <= 17 * ParentLen                                           \* 1100 rounds down to 17 pairs
            /\ LET e == PfHead(r.sid, r.glog, r.start, r.wn, r.ln, Sent(Len(s) + 1))    \* canonical
               IN e.ok /\ e.n = n + ProofFixed /\ SubSeq(e.after, 1, e.n) = Prefix(s, e.n)
                  /\ SubSeq(e.after, e.n + 1, Len(s) + 1) = Sent(Len(s) + 1 - e.n)
       /\ (full >= 0 /\ Len(s) < full) => (~r.ok /\ r.err = "truncated")

PrCase(s, full) ==
    LET r == PrParse(s)
        n == SidN(s)
        ends == {n + 8, n + 16}
    IN /\ r.ok = (n > 0 /\ Len(s) = n + 16)
       /\ (~r.ok /\ n = 0) => SidRefusal(s, r)
       /\ (~r.ok /\ n > 0) =>
            IF Len(s) < n + 16 THEN RefusedAs(r, "truncated", "", NeededSpec(ends, Len(s)))
            ELSE RefusedAs(r, "unexpected", "trailing bytes", 0)
       /\ r.ok =>
            /\ r.sid = V!ValueOf(Prefix(s, n), 1)
            /\ r.from = BeSpec(SubSeq(s, n + 1, n + 8)) /\ r.upto = BeSpec(SubSeq(s, n + 9, n + 16))
            /\ LET e == PrEncode(r, Sent(Len(s) + 1))                                   \* canonical: the whole input
               IN e.ok /\ e.n = Len(s) /\ SubSeq(e.after, 1, e.n) = s
       /\ (full >= 0 /\ Len(s) < full) => (~r.ok /\ r.err = "truncated")

(* every codec, on a string of any shape: used for the short strings *)
AllCodecs(s) == ReqCase(s, -1) /\ GhCase(s, -1) /\ PfCase(s, -1) /\ PrCase(s, -1)

(* ---- the encoders ---- *)

(* an encode into a buffer of cap sentinel bytes: refusals leave the buffer as it was, a success writes exactly *)
ReqEncCase(root, spans, cap) ==
    LET e == ReqEncode(root, spans, Sent(cap))
        tot == ReqFixed + 16 * Len(spans)
    IN IF Len(spans) > MaxReq
       THEN RefusedAs(e, "unexpected", "too many ranges", 0) /\ e.after = Sent(cap)
       ELSE IF cap < tot
       THEN RefusedAs(e, "small", "", tot - cap) /\ e.after = Sent(cap)
       ELSE /\ e.ok /\ e.n = tot
            /\ e.after[1] = TReq /\ SubSeq(e.after, 2, 33) = root /\ e.after[ReqFixed] = Len(spans)
            /\ \A i \in 1..Len(spans) :
                 /\ BeSpec(SubSeq(e.after, 35 + 16 * (i - 1), 42 + 16 * (i - 1))) = spans[i].off
                 /\ BeSpec(SubSeq(e.after, 43 + 16 * (i - 1), 50 + 16 * (i - 1))) = spans[i].len
            /\ SubSeq(e.after, tot + 1, cap) = Sent(cap - tot)
            /\ LET r == ReqParse(e.after)                                                 \* round trip
               IN r.ok /\ r.n = tot /\ r.root = root /\ SpansOf(r.ranges) = spans
                  /\ ReqTotalLen(SubSeq(e.after, 1, ReqFixed)) = [ok |-> TRUE, n |-> tot]

GhEncCase(h) ==
    LET b == GhEncode(h)
        r == GhParse(b \o <<9>>)
        valid == h.len # U!Zero /\ h.plen % ParentLen = 0
    IN /\ Len(b) = GroupHdr /\ b[1] = TGroup
       /\ BeSpec(SubSeq(b, 2, 9)) = h.off /\ BeSpec(SubSeq(b, 10, 13)) = h.len
       /\ b[14] * 256 + b[15] = h.plen /\ b[16] = (IF h.follows THEN 1 ELSE 0)
       /\ r.ok = valid
       /\ valid => (r.off = h.off /\ r.len = h.len /\ r.plen = h.plen /\ r.follows = h.follows)   \* round trip
       /\ ~valid => RefusedAs(r, "unexpected", "bad group lengths", 0)

PfEncCase(sid, glog, start, wn, ln, cap, pp) ==
    LET e == PfHead(sid, glog, start, wn, ln, Sent(cap))
        v == V!Encode(sid, 9)
        proof == [i \in 1..(ParentLen * pp) |-> (i * 5 + 1) % 256]
    IN IF ~U!Lt(sid, U!Pw(63))
       THEN RefusedAs(e, "overflow", "", 0) /\ e.after = Sent(cap)
       ELSE LET hn == Len(v.bytes) + ProofFixed
            IN IF cap < hn
               THEN RefusedAs(e, "small", "", hn - cap) /\ e.after = Sent(cap)
               ELSE /\ e.ok /\ e.n = hn /\ SubSeq(e.after, hn + 1, cap) = Sent(cap - hn)
                    /\ LET r == PfParse(SubSeq(e.after, 1, hn) \o proof)                  \* round trip
                       IN IF ParentLen * pp > WtPmax
                          THEN RefusedAs(r, "unexpected", "bad proof length", 0)
                          ELSE /\ r.ok /\ r.sid = sid /\ r.glog = glog /\ r.start = start /\ r.wn = wn
                               /\ r.ln = ln /\ r.proof = proof

PrEncCase(sid, from, upto, cap) ==
    LET e == PrEncode([sid |-> sid, from |-> from, upto |-> upto], Sent(cap))
        v == V!Encode(sid, 9)
    IN IF ~U!Lt(sid, U!Pw(63))
       THEN RefusedAs(e, "overflow", "", 0) /\ e.after = Sent(cap)
       ELSE LET n == Len(v.bytes) + 16
            IN IF cap < n
               THEN RefusedAs(e, "small", "", n - cap) /\ e.after = Sent(cap)
               ELSE /\ e.ok /\ e.n = n /\ SubSeq(e.after, n + 1, cap) = Sent(cap - n)
                    /\ LET r == PrParse(SubSeq(e.after, 1, n))                            \* round trip
                       IN r.ok /\ r.sid = sid /\ r.from = from /\ r.upto = upto
                    /\ cap > n => LET r2 == PrParse(SubSeq(e.after, 1, n + 1))            \* a trailing byte
                                  IN RefusedAs(r2, "unexpected", "trailing bytes", 0)

(* ---- the bounded domain ---- *)

Fill(k, salt) == [i \in 1..k |-> (i * 7 + salt) % 256]

Words == <<U!Zero, U!One, U!Max64, U!FromLimbs(<<770, 1284, 1798, 2312>>), U!Pw(63)>>

(* the u64 values of the edge sets: 2^j - 1, 2^j, 2^j + 1 for j in a spread of bit widths *)
EdgeJs == {0, 6, 7, 13, 14, 20, 21, 27, 28, 34, 35, 41, 42, 48, 49, 55, 56, 62, 63, 64}
EdgeW(j, d) == IF d = -1 THEN U!Sub(U!Pw(j), U!One) ELSE IF d = 0 THEN U!Pw(j) ELSE U!Add(U!Pw(j), U!One)
EdgeOK(j, d) == (j >= 1 \/ d >= 0) /\ (j < 64 \/ d = -1)
EdgeWords == {EdgeW(q[1], q[2]) : q \in {r \in EdgeJs \X (-1..1) : EdgeOK(r[1], r[2])}}

(* the PROOF / PROOF_REQ id forms: seven canonical encodings and seven broken strings *)
CanonSid(v) == V!Encode(v, 9).bytes
SidForms == <<CanonSid(U!Zero), CanonSid(U!One), CanonSid(U!W(127)), CanonSid(U!W(128)), CanonSid(U!W(16383)),
              CanonSid(U!Pw(62)), CanonSid(U!Sub(U!Pw(63), U!One)),
              <<>>, <<128>>, <<128, 0>>, <<255, 255, 255, 255, 255, 255, 255, 255, 255>>,
              <<128, 128, 128, 128, 128, 128, 128, 128, 0>>, <<129, 128, 0>>,
              <<128, 128, 128, 128, 128, 128, 128, 128, 128>>>>

FixedTails == <<Fill(21, 1), Fill(21, 100), [i \in 1..21 |-> 255], [i \in 1..21 |-> 0]>>
FUPairs == <<Fill(16, 3), Fill(16, 200), [i \in 1..16 |-> 255], [i \in 1..16 |-> 0]>>
ProofLens == {0, 1, 63, 64, 65, 127, 128, 1087, 1088, 1089, 1100, 1101, 1151, 1152, 1153, 1216, 1300, 1400}
Trailers == <<<<>>, <<0>>, <<255, 255>>>>

Alpha == {0, 1, 2, 64, 127, 128, 129, 192, 255}

ReqStr(t, cnt, salt) ==
    <<t>> \o Fill(32, salt) \o <<cnt>> \o Fill(IF cnt <= MaxReq THEN 16 * cnt ELSE 17, salt + 1)

(* the cut lengths of a request string for count n: every one for a small count, the edges for a large one *)
ReqCuts(n) == IF n <= 33 THEN 0..(Len(ReqStr(1, n, 5)) + 1)
              ELSE {0, 1, 2, 32, 33, 34, 35, 49, 50, 34 + 16 * n - 17, 34 + 16 * n - 16, 34 + 16 * n - 1, 34 + 16 * n, 34 + 16 * n + 1}

(* a case: the codec, the input and, for a cut of a valid input, the length of the valid input (else -1) *)
Cs(k, s, full) == [t |-> "case", k |-> k, s |-> s, full |-> full]

(* the cuts of a string B: the prefixes of lengths in ms, and B with a byte after it *)
Cuts(k, B, full, ms) == {Cs(k, IF m <= Len(B) THEN Prefix(B, m) ELSE B \o <<7>>, full) : m \in ms}

ValidGh == <<2>> \o Fill(8, 9) \o <<0, 0, 1, 0>> \o <<0, 64>> \o <<1>>
GhPieces(a, b, ty, plenB, fl) ==
    <<ty>> \o (CASE a = 1 -> <<0, 0, 0, 0, 0, 0, 0, 0>> [] a = 2 -> Fill(8, 9) [] a = 3 -> <<255, 255, 255, 255, 255, 255, 255, 255>>
                [] OTHER -> <<128, 0, 0, 0, 0, 0, 0, 1>>)
          \o (CASE b = 1 -> <<0, 0, 0, 0>> [] b = 2 -> <<0, 0, 0, 1>> [] b = 3 -> <<1, 0, 0, 0>> [] b = 4 -> <<255, 255, 255, 255>>
                [] b = 5 -> <<0, 1, 2, 3>> [] OTHER -> <<128, 0, 0, 0>>)
          \o plenB \o <<fl>>
GhPlens == {<<0, 0>>, <<0, 63>>, <<0, 64>>, <<0, 65>>, <<0, 128>>, <<1, 0>>, <<255, 192>>, <<255, 255>>, <<192, 0>>, <<0, 192>>}

Seeds ==
    {[f |-> "reqtype", t |-> t] : t \in 0..255}
    \cup {[f |-> "reqcnt", n |-> n] : n \in 0..255}
    \cup {[f |-> "gh", a |-> a, b |-> b] : a \in 1..4, b \in 1..6}
    \cup {[f |-> "ghplen", hi |-> hi] : hi \in 0..255}
    \cup {[f |-> "ghbyte", x |-> x] : x \in 0..255}
    \cup {[f |-> "ghcut"]}
    \cup {[f |-> "pf", i |-> i] : i \in 1..Len(SidForms)}
    \cup {[f |-> "pfcut", i |-> i] : i \in 1..Len(SidForms)}
    \cup {[f |-> "pr", i |-> i] : i \in 1..Len(SidForms)}
    \cup {[f |-> "short"], [f |-> "alpha"]}
    \cup {[f |-> "reqenc", k |-> k] : k \in {0, 1, 2, 3, 31, 32, 33, 34, 255, 256}}
    \cup {[f |-> "ghenc", a |-> a] : a \in 1..5}
    \cup {[f |-> "pfenc", w |-> w] : w \in EdgeWords}
    \cup {[f |-> "prenc", w |-> w] : w \in EdgeWords}

IsValidSid(i) == i <= 7

ReqSpans(k, a) == [i \in 1..k |-> [off |-> Words[((i + a) % 5) + 1], len |-> Words[((i + a + 2) % 5) + 1]]]
ReqCaps(k) == IF k <= 3 THEN 0..(ReqFixed + 16 * k + 2)
              ELSE {0, 1, 33, 34, 35, ReqFixed + 16 * k - 1, ReqFixed + 16 * k, ReqFixed + 16 * k + 1, 600}

Expand(sd) ==
    CASE sd.f = "reqtype" ->
           Cuts("REQ", ReqStr(sd.t, 2, 11), IF sd.t = TReq THEN 66 ELSE -1, {0, 1, 2, 33, 34, 66, 67})
      [] sd.f = "reqcnt" ->
           Cuts("REQ", ReqStr(1, sd.n, 5), IF sd.n <= MaxReq THEN 34 + 16 * sd.n ELSE -1, ReqCuts(sd.n))
      [] sd.f = "gh" ->
           {Cs("GH", GhPieces(sd.a, sd.b, ty, p, fl), -1) : ty \in {0, 1, 2, 3, 255}, p \in GhPlens, fl \in {0, 1, 2, 128, 255}}
      [] sd.f = "ghplen" ->
           {Cs("GH", <<2>> \o Fill(8, 9) \o <<0, 0, 1, 0, sd.hi, lo, 1>>, -1) : lo \in 0..255}
      [] sd.f = "ghbyte" ->
           {Cs("GH", <<sd.x>> \o Fill(8, 9) \o <<0, 0, 1, 0, 0, 64, 1>>, -1),
            Cs("GH", <<2>> \o Fill(8, 9) \o <<0, 0, 1, 0, 0, 64, sd.x>>, -1),
            Cs("GH", <<2>> \o Fill(8, 9) \o <<0, 0, 1, 0, 0, 64, sd.x, 9, 9>>, -1)}
      [] sd.f = "ghcut" -> Cuts("GH", ValidGh, 16, 0..17) \cup Cuts("GH", <<2>> \o Fill(8, 9) \o <<0, 0, 1, 0, 0, 0, 0>>, 16, 0..17)
      [] sd.f = "pf" ->
           LET sid == SidForms[sd.i]
           IN {Cs("PF", sid \o FixedTails[j] \o Fill(L, j), -1) : j \in 1..4, L \in ProofLens}
      [] sd.f = "pfcut" ->
           LET sid == SidForms[sd.i]
               hl == Len(sid) + ProofFixed
           IN UNION {Cuts("PF", sid \o FixedTails[j] \o Fill(L, j), IF IsValidSid(sd.i) THEN hl ELSE -1, 0..(hl + L + 1)) : j \in 1..4, L \in {0, 64}}
      [] sd.f = "pr" ->
           LET sid == SidForms[sd.i]
               hl == Len(sid) + 16
           IN {Cs("PR", sid \o FUPairs[j] \o Trailers[t], -1) : j \in 1..4, t \in 1..3}
              \cup UNION {Cuts("PR", sid \o FUPairs[j], IF IsValidSid(sd.i) THEN hl ELSE -1, 0..(hl + 1)) : j \in 1..4}

(* the encoders are cases of their own, a seed standing for a family *)
EncCases(sd) ==
    CASE sd.f = "reqenc" ->
           {[t |-> "enc", k |-> "REQ", spans |-> ReqSpans(sd.k, a), cap |-> cap] : a \in 0..1, cap \in ReqCaps(sd.k)}
      [] sd.f = "ghenc" ->
           {[t |-> "enc", k |-> "GH", h |-> [off |-> Words[sd.a], len |-> ln, plen |-> pl, follows |-> fl]] :
                ln \in {U!Zero, U!One, U!W(65536), U!FromLimbs(<<65535, 65535, 0, 0>>), U!FromLimbs(<<770, 1284, 0, 0>>)},
                pl \in {0, 1, 64, 65, 4096, 65472, 65535}, fl \in {FALSE, TRUE}}
      [] sd.f = "pfenc" ->
           LET sn == IF U!Lt(sd.w, U!Pw(63)) THEN Len(CanonSid(sd.w)) + ProofFixed ELSE 30
           IN {[t |-> "enc", k |-> "PF", sid |-> sd.w, cap |-> cap, pp |-> pp] :
                  cap \in {0, 1, sn - 1, sn, sn + 1, 30}, pp \in {0, 1, 17, 18}}
      [] sd.f = "prenc" ->
           LET sn == IF U!Lt(sd.w, U!Pw(63)) THEN Len(CanonSid(sd.w)) + 16 ELSE 25
           IN {[t |-> "enc", k |-> "PR", sid |-> sd.w, a |-> a, cap |-> cap] :
                  a \in 1..5, cap \in {0, 1, sn - 1, sn, sn + 1, 25}}

IsEncSeed(sd) == sd.f \in {"reqenc", "ghenc", "pfenc", "prenc"}

Init == c = [t |-> "root"]

(* the root has one successor per seed; a seed one per case; the short and alpha machines grow a string *)
Next ==
    \/ c.t = "root" /\ \E sd \in Seeds : c' = [t |-> "seed", sd |-> sd]
    \/ c.t = "seed" /\ ~IsEncSeed(c.sd) /\ c.sd.f \notin {"short", "alpha"} /\ \E x \in Expand(c.sd) : c' = x
    \/ c.t = "seed" /\ IsEncSeed(c.sd) /\ \E x \in EncCases(c.sd) : c' = x
    \/ c.t = "seed" /\ c.sd.f = "short" /\ c' = [t |-> "short", s |-> <<>>]
    \/ c.t = "seed" /\ c.sd.f = "alpha" /\ c' = [t |-> "alpha", s |-> <<>>]
    \/ c.t = "short" /\ Len(c.s) < 2 /\ \E b \in 0..255 : c' = [c EXCEPT !.s = Append(c.s, b)]
    \/ c.t = "alpha" /\ Len(c.s) < 4 /\ \E b \in Alpha : c' = [c EXCEPT !.s = Append(c.s, b)]

Spec == Init /\ [][Next]_c

(* ---- the properties ---- *)

EncOK(x) ==
    CASE x.k = "REQ" -> ReqEncCase(<<>> \o Fill(32, 3), x.spans, x.cap)
      [] x.k = "GH" -> GhEncCase(x.h)
      [] x.k = "PF" -> PfEncCase(x.sid, 77, Words[2], U!FromLimbs(<<770, 1284, 0, 0>>), Words[4], x.cap, x.pp)
      [] x.k = "PR" -> PrEncCase(x.sid, Words[x.a], Words[((x.a + 1) % 5) + 1], x.cap)

CaseOK(x) ==
    CASE x.k = "REQ" -> ReqCase(x.s, x.full)
      [] x.k = "GH" -> GhCase(x.s, x.full)
      [] x.k = "PF" -> PfCase(x.s, x.full)
      [] x.k = "PR" -> PrCase(x.s, x.full)

Inv ==
    CASE c.t \in {"root", "seed"} -> TRUE
      [] c.t = "case" -> CaseOK(c)
      [] c.t = "enc" -> EncOK(c)
      [] c.t = "short" -> AllCodecs(c.s)
      [] c.t = "alpha" -> PrCase(c.s \o FUPairs[1], -1) /\ PfCase(c.s \o FixedTails[1], -1) /\ PrCase(c.s, -1)
=============================================================================
