--------------------------- MODULE BroadcastStatement ---------------------------
(***************************************************************************)
(* The signed statement of a version 2 topic message: pinc-broadcast       *)
(* statement.rs `encode` (with `write`, `cid`, `body_cid`,                 *)
(* `strictly_ascending`) over the CBOR heads of pinc-wire cbor/encode.rs   *)
(* (`head_shape`, `string`, `tag_cid`, `ordered_map`).                     *)
(*                                                                         *)
(* Encode is the code's byte layout: a map of 9 entries whose keys are in  *)
(* DAG-CBOR order (shorter first, then bytewise; an ASSUME checks the      *)
(* order), each integer under its shortest head, the body and the parents  *)
(* as tag-42 CID links, the origin as its algorithm tag followed by the    *)
(* node id. The refusals come in the code's order: TopicTooLong,           *)
(* TooManyParents, ParentsNotAscending, ReservedFlags (BufferTooSmall is   *)
(* unreachable: the buffer is STATEMENT_MAX bytes and Bound shows it is    *)
(* enough). Integers are fixed-width big-endian byte lists (8 bytes for a  *)
(* u64, 4 for the counter) because TLC integers are 32 bits wide.          *)
(*                                                                         *)
(* The code never parses a statement (signer and verifier both build it    *)
(* from head fields). Decode is a strict reader written for the model: it  *)
(* accepts only the shortest head of every integer and length, the fixed  *)
(* keys in their order and definite lengths. RoundTrip (Decode of Encode   *)
(* gives back every field) therefore shows that the encoding is canonical  *)
(* DAG-CBOR and injective: two sets of fields never share a statement, so  *)
(* (with an ideal hash) never share a content id, and the content id       *)
(* covers every field (the signature and the public key are not fields).   *)
(*                                                                         *)
(* Widths are parameters: IdW (node id), DigW (content id and body hash),  *)
(* MaxParents, MaxTopic. Wide = TRUE is the code's shape (32, 32, 8, 255), *)
(* where Bound checks the code's STATEMENT_MAX formula: no statement is    *)
(* longer, and the widest one is exactly that long.                        *)
(*                                                                         *)
(* Checked: RoundTrip, Bound. Witness: BroadcastStatement_refused.cfg      *)
(* (NoRefusal is violated: the refusal branches are reached).              *)
(* TraceBroadcastStatement.tla checks the real encode against Encode.      *)
(* Ideal hash assumed (collision free), not modelled.                      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS IdW, DigW, MaxParents, MaxTopic, Wide

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Fill(n, x) == [i \in 1..n |-> x]
Zeros(n) == Fill(n, 0)
Pad(s, k) == Zeros(k - Len(s)) \o s
\* k <= 4 only (256^3 is the largest power taken)
BE(n, k) == [i \in 1..k |-> (n \div (256 ^ (k - i))) % 256]
RECURSIVE Cat(_)
Cat(s) == IF s = <<>> THEN <<>> ELSE Head(s) \o Cat(Tail(s))
\* a < b bytewise, for byte lists of one length (content ids and keys of one length)
LexLt(a, b) == \E k \in 1..Len(a) : a[k] < b[k] /\ \A j \in 1..(k - 1) : a[j] = b[j]

\* ---- CBOR heads (cbor/encode.rs head_shape) ----
Sig(v) == LET nz == {i \in 1..Len(v) : v[i] # 0} IN IF nz = {} THEN <<>> ELSE SubSeq(v, Min(nz), Len(v))
HeadB(mj, v) ==
    LET s == Sig(v)
        ib == mj * 32
    IN CASE Len(s) = 0 -> <<ib>>
         [] Len(s) = 1 /\ s[1] <= 23 -> <<ib + s[1]>>
         [] Len(s) = 1 /\ s[1] > 23 -> <<ib + 24>> \o s
         [] Len(s) = 2 -> <<ib + 25>> \o s
         [] Len(s) \in 3..4 -> <<ib + 26>> \o Pad(s, 4)
         [] Len(s) > 4 -> <<ib + 27>> \o Pad(s, 8)
HeadN(mj, n) == HeadB(mj, BE(n, 4))
Uint(v) == HeadB(0, v)
Bytes(s) == HeadN(2, Len(s)) \o s
Text(s) == HeadN(3, Len(s)) \o s
TagCid(c) == HeadN(6, 42) \o HeadN(2, Len(c) + 1) \o <<0>> \o c

\* ---- statement.rs ----
StmtPrefix == <<1, 113, 30, 32>>     \* 01 71 1e 20
BodyPrefix == <<1, 85, 30, 32>>      \* 01 55 1e 20
Cid(d) == StmtPrefix \o d
BodyCid(d) == BodyPrefix \o d
KSeq == <<115, 101, 113>>
KBody == <<98, 111, 100, 121>>
KKind == <<107, 105, 110, 100>>
KTime == <<116, 105, 109, 101>>
KFlags == <<102, 108, 97, 103, 115>>
KTopic == <<116, 111, 112, 105, 99>>
KOrigin == <<111, 114, 105, 103, 105, 110>>
KParents == <<112, 97, 114, 101, 110, 116, 115>>
KInc == <<105, 110, 99, 97, 114, 110, 97, 116, 105, 111, 110>>
Keys == <<KSeq, KBody, KKind, KTime, KFlags, KTopic, KOrigin, KParents, KInc>>
\* "pinc/broadcast/2"
Kind == <<112, 105, 110, 99, 47, 98, 114, 111, 97, 100, 99, 97, 115, 116, 47, 50>>

KeyLess(a, b) == Len(a) < Len(b) \/ (Len(a) = Len(b) /\ LexLt(a, b))
\* MapKeys::key would refuse keys out of DAG-CBOR order: the code's order is that order
ASSUME \A i \in 1..8 : KeyLess(Keys[i], Keys[i + 1])

Ascending(ps) == \A i \in 1..(Len(ps) - 1) : LexLt(ps[i], ps[i + 1])
Ok(b) == [ok |-> TRUE, b |-> b]
Err(e) == [ok |-> FALSE, err |-> e]

\* encode: the checks in the code's order, then write
Encode(g) ==
    IF Len(g.topic) > MaxTopic THEN Err("TopicTooLong")
    ELSE IF Len(g.parents) > MaxParents THEN Err("TooManyParents")
    ELSE IF ~Ascending(g.parents) THEN Err("ParentsNotAscending")
    ELSE IF g.flags \div 2 # 0 THEN Err("ReservedFlags")
    ELSE Ok(HeadN(5, 9)
            \o Text(KSeq) \o Uint(g.seq)
            \o Text(KBody) \o TagCid(BodyCid(g.body))
            \o Text(KKind) \o Text(Kind)
            \o Text(KTime) \o HeadN(4, 2) \o Uint(g.wall) \o Uint(g.ctr)
            \o Text(KFlags) \o HeadN(0, g.flags)
            \o Text(KTopic) \o Bytes(g.topic)
            \o Text(KOrigin) \o Bytes(<<g.alg>> \o g.origin)
            \o Text(KParents) \o HeadN(4, Len(g.parents)) \o Cat([i \in 1..Len(g.parents) |-> TagCid(Cid(g.parents[i]))])
            \o Text(KInc) \o Uint(g.inc))

\* ---- the model's strict reader ----
Bad == [ok |-> FALSE]
Small(v) == \A i \in 1..5 : v[i] = 0
ToInt(v) == v[6] * 65536 + v[7] * 256 + v[8]

\* a head at p: its major type, its value as 8 bytes, the next position; only the shortest head of a value is read
RdHead(b, p) ==
    IF p > Len(b) THEN Bad
    ELSE LET mj == b[p] \div 32
             info == b[p] % 32
             w == CASE info <= 23 -> 0 [] info = 24 -> 1 [] info = 25 -> 2 [] info = 26 -> 4 [] info = 27 -> 8
                    [] info > 27 -> -1
         IN IF w < 0 \/ p + w > Len(b) THEN Bad
            ELSE LET v == IF w = 0 THEN Pad(<<info>>, 8) ELSE Pad(SubSeq(b, p + 1, p + w), 8)
                 IN IF HeadB(mj, v) # SubSeq(b, p, p + w) THEN Bad
                    ELSE [ok |-> TRUE, mj |-> mj, v |-> v, p |-> p + w + 1]
RdStr(b, p, mj) ==
    LET h == RdHead(b, p)
    IN IF ~h.ok THEN Bad
       ELSE IF h.mj # mj \/ ~Small(h.v) THEN Bad
       ELSE IF h.p + ToInt(h.v) - 1 > Len(b) THEN Bad
       ELSE [ok |-> TRUE, s |-> SubSeq(b, h.p, h.p + ToInt(h.v) - 1), p |-> h.p + ToInt(h.v)]
RdKey(b, p, k) == LET r == RdStr(b, p, 3) IN IF r.ok /\ r.s = k THEN [ok |-> TRUE, p |-> r.p] ELSE Bad
RdUint(b, p) == LET h == RdHead(b, p) IN IF h.ok /\ h.mj = 0 THEN h ELSE Bad
RdCid(b, p, pre) ==
    LET t == RdHead(b, p)
    IN IF ~t.ok THEN Bad
       ELSE IF t.mj # 6 \/ t.v # Pad(<<42>>, 8) THEN Bad
       ELSE LET s == RdStr(b, t.p, 2)
            IN IF ~s.ok THEN Bad
               ELSE IF Len(s.s) # 5 + DigW THEN Bad
               ELSE IF s.s[1] # 0 \/ SubSeq(s.s, 2, 5) # pre THEN Bad
               ELSE [ok |-> TRUE, d |-> SubSeq(s.s, 6, Len(s.s)), p |-> s.p]
RECURSIVE RdCids(_, _, _)
RdCids(b, p, n) ==
    IF n = 0 THEN [ok |-> TRUE, l |-> <<>>, p |-> p]
    ELSE LET c == RdCid(b, p, StmtPrefix)
         IN IF ~c.ok THEN Bad
            ELSE LET r == RdCids(b, c.p, n - 1)
                 IN IF ~r.ok THEN Bad ELSE [ok |-> TRUE, l |-> <<c.d>> \o r.l, p |-> r.p]

Decode(b) ==
    LET m == RdHead(b, 1) IN
    IF ~m.ok THEN Bad ELSE IF m.mj # 5 \/ m.v # Pad(<<9>>, 8) THEN Bad ELSE
    LET k1 == RdKey(b, m.p, KSeq) IN IF ~k1.ok THEN Bad ELSE
    LET seq == RdUint(b, k1.p) IN IF ~seq.ok THEN Bad ELSE
    LET k2 == RdKey(b, seq.p, KBody) IN IF ~k2.ok THEN Bad ELSE
    LET body == RdCid(b, k2.p, BodyPrefix) IN IF ~body.ok THEN Bad ELSE
    LET k3 == RdKey(b, body.p, KKind) IN IF ~k3.ok THEN Bad ELSE
    LET kind == RdStr(b, k3.p, 3) IN IF ~kind.ok THEN Bad ELSE IF kind.s # Kind THEN Bad ELSE
    LET k4 == RdKey(b, kind.p, KTime) IN IF ~k4.ok THEN Bad ELSE
    LET ta == RdHead(b, k4.p) IN IF ~ta.ok THEN Bad ELSE IF ta.mj # 4 \/ ta.v # Pad(<<2>>, 8) THEN Bad ELSE
    LET wall == RdUint(b, ta.p) IN IF ~wall.ok THEN Bad ELSE
    LET ctr == RdUint(b, wall.p) IN IF ~ctr.ok THEN Bad ELSE IF (\E i \in 1..4 : ctr.v[i] # 0) THEN Bad ELSE
    LET k5 == RdKey(b, ctr.p, KFlags) IN IF ~k5.ok THEN Bad ELSE
    LET fl == RdUint(b, k5.p) IN IF ~fl.ok THEN Bad ELSE IF ~Small(fl.v) \/ ToInt(fl.v) > 255 THEN Bad ELSE
    LET k6 == RdKey(b, fl.p, KTopic) IN IF ~k6.ok THEN Bad ELSE
    LET tp == RdStr(b, k6.p, 2) IN IF ~tp.ok THEN Bad ELSE
    LET k7 == RdKey(b, tp.p, KOrigin) IN IF ~k7.ok THEN Bad ELSE
    LET og == RdStr(b, k7.p, 2) IN IF ~og.ok THEN Bad ELSE IF Len(og.s) # 1 + IdW THEN Bad ELSE
    LET k8 == RdKey(b, og.p, KParents) IN IF ~k8.ok THEN Bad ELSE
    LET pa == RdHead(b, k8.p) IN IF ~pa.ok THEN Bad ELSE IF pa.mj # 4 \/ ~Small(pa.v) THEN Bad ELSE
    LET ps == RdCids(b, pa.p, ToInt(pa.v)) IN IF ~ps.ok THEN Bad ELSE
    LET k9 == RdKey(b, ps.p, KInc) IN IF ~k9.ok THEN Bad ELSE
    LET inc == RdUint(b, k9.p) IN IF ~inc.ok THEN Bad ELSE IF inc.p # Len(b) + 1 THEN Bad ELSE
    [ok |-> TRUE,
     f |-> [alg |-> og.s[1], origin |-> Tail(og.s), inc |-> inc.v, seq |-> seq.v, topic |-> tp.s, wall |-> wall.v,
            ctr |-> SubSeq(ctr.v, 5, 8), flags |-> ToInt(fl.v), parents |-> ps.l, body |-> body.d]]

\* ---- the fields checked ----
Id(x) == Fill(IdW, x)
Dig(x) == Fill(DigW, x)
U64Edges == {Pad(<<>>, 8), Pad(<<23>>, 8), Pad(<<24>>, 8), Pad(<<255>>, 8), Pad(<<1, 0>>, 8), Pad(<<255, 255>>, 8),
             Pad(<<1, 0, 0>>, 8), Pad(<<255, 255, 255, 255>>, 8), Pad(<<1, 0, 0, 0, 0>>, 8), Fill(8, 255)}
U32Edges == {Pad(<<>>, 4), Pad(<<23>>, 4), Pad(<<24>>, 4), Pad(<<255>>, 4), Pad(<<1, 0>>, 4), Pad(<<255, 255>>, 4),
             Pad(<<1, 0, 0>>, 4), Fill(4, 255)}
F0 == [alg |-> 1, origin |-> Id(7), inc |-> Pad(<<1>>, 8), seq |-> Pad(<<2>>, 8), topic |-> <<1>>,
       wall |-> Pad(<<3>>, 8), ctr |-> Pad(<<>>, 4), flags |-> 0, parents |-> <<>>, body |-> Dig(5)]
TopicSet == {<<>>, <<1>>, Fill(MaxTopic, 0), Fill(MaxTopic + 1, 0)}
ParentSet == UNION {[1..n -> {Dig(0), Dig(1)}] : n \in 0..(MaxParents + 1)}
\* every refusal crossed with every other (the order), every integer at every head boundary, every algorithm tag
SmallSet ==
    {[F0 EXCEPT !.topic = t, !.parents = p, !.flags = g] : t \in TopicSet, p \in ParentSet, g \in {0, 1, 2, 255}}
    \union {[F0 EXCEPT !.inc = v] : v \in U64Edges} \union {[F0 EXCEPT !.seq = v] : v \in U64Edges}
    \union {[F0 EXCEPT !.wall = v] : v \in U64Edges} \union {[F0 EXCEPT !.ctr = v] : v \in U32Edges}
    \union {[F0 EXCEPT !.alg = a, !.origin = o, !.body = d] : a \in 1..4, o \in {Id(0), Id(255)}, d \in {Dig(0), Dig(255)}}
Widest == [alg |-> 4, origin |-> Id(255), inc |-> Fill(8, 255), seq |-> Fill(8, 255), topic |-> Fill(MaxTopic, 255),
           wall |-> Fill(8, 255), ctr |-> Fill(4, 255), flags |-> 1, parents |-> [i \in 1..MaxParents |-> Dig(i)],
           body |-> Dig(255)]
WideSet == {Widest, F0, [Widest EXCEPT !.topic = Fill(MaxTopic + 1, 255)],
            [Widest EXCEPT !.parents = [i \in 1..(MaxParents + 1) |-> Dig(i)]],
            [Widest EXCEPT !.parents = <<Dig(2), Dig(1)>>], [Widest EXCEPT !.parents = <<Dig(1), Dig(1)>>],
            [Widest EXCEPT !.flags = 2]}

VARIABLE f
Init == f \in (IF Wide THEN WideSet ELSE SmallSet)
Next == UNCHANGED f
Spec == Init /\ [][Next]_f

\* statement.rs STATEMENT_MAX, as the code writes it (LINK_LEN = 2 + 2 + 1 + CID_LEN, CID_LEN = 36): Wide only
LinkLen == 2 + 2 + 1 + 36
StatementMax == 1 + (3 + 1 + 9) + (4 + 1 + LinkLen) + (4 + 1 + 1 + 16) + (4 + 1 + 1 + 9 + 5) + (5 + 1 + 1)
                + (5 + 1 + 2 + MaxTopic) + (6 + 1 + 2 + 1 + 32) + (7 + 1 + 1 + MaxParents * LinkLen) + (11 + 1 + 9)

\* the strict reader gives every field back: canonical DAG-CBOR, and no two field sets share a statement
RoundTrip == Encode(f).ok => (Decode(Encode(f).b).ok /\ Decode(Encode(f).b).f = f)

\* no statement is longer than STATEMENT_MAX, and the widest one is exactly that long
Bound == Wide => /\ LinkLen = Len(TagCid(Cid(Dig(0))))
                 /\ Encode(f).ok => Len(Encode(f).b) <= StatementMax
                 /\ f = Widest => (Encode(f).ok /\ Len(Encode(f).b) = StatementMax)

\* witness (must be violated): some fields are refused
NoRefusal == Encode(f).ok
=============================================================================
