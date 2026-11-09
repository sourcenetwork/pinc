--------------------------- MODULE ValuesPlanOps ---------------------------
(***************************************************************************)
(* The operators of the response geometry of vinc-values (plan.rs), step   *)
(* for step on TLC integers: left_groups, parents_in, parents_in_suffix,   *)
(* parents_before, path, Plan::new, frame_start, frame, locate, the binary *)
(* search of locate, frame_of_group, proof_pair, range_pairs; and the      *)
(* reference they must equal: the steps of the range encoder of vinc-dag   *)
(* (the pre-order walk of the nodes that meet the group range, Encoder.tla *)
(* SpecWalk), cut into frames (a header, the pairs the previous group      *)
(* leaves open, the group).                                                *)
(*                                                                         *)
(* The group size G, the header size HDR, the pair size PAR, the machine   *)
(* word MaxU (the largest u64 of the code: every checked_add and           *)
(* checked_mul is checked against it), the response limit MaxS (2^62 - 1   *)
(* of the code) and the request limit MaxR are constants: the code has     *)
(* G = 16384, HDR = 16, PAR = 64, MaxU = 2^64 - 1, MaxS = 2^62 - 1,        *)
(* MaxR = 32, and TLC integers are 32 bits, so the model checks run the    *)
(* same arithmetic at a small G and word (every overflow branch of the     *)
(* code is reached: the Lean proofs cover the 64-bit word, ValuesPlan*.lean).*)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/ValuesPlanCount.lean (parents_in,    *)
(* the suffix loop, parents_before), ValuesPlanModel.lean (Plan::new),     *)
(* ValuesPlanGeom.lean (frame), ValuesPlanLocate.lean (locate),            *)
(* ValuesPlanPairs.lean (proof_pair, frame_of_group).                      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS G, HDR, PAR, MaxU, MaxS, MaxR

Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

(* the largest power of two strictly below count, for count >= 2 (0 otherwise): left_groups *)
RECURSIVE Below(_, _)
Below(c, p) == IF 2 * p < c THEN Below(c, 2 * p) ELSE p
LeftGroups(c) == IF c < 2 THEN 0 ELSE Below(c, 1)

(* the checked operations of u64 *)
CAdd(x, y) == IF x + y <= MaxU THEN [ok |-> TRUE, v |-> x + y] ELSE [ok |-> FALSE, v |-> 0]
CMul(x, y) == IF x * y <= MaxU THEN [ok |-> TRUE, v |-> x * y] ELSE [ok |-> FALSE, v |-> 0]
SatMul(x, y) == Min(x * y, MaxU)

(* Layout::groups and group_size *)
Groups(len) == (len + G - 1) \div G
GroupSize(len, x) == IF x * G >= len THEN 0 ELSE IF len - x * G < G THEN len - x * G ELSE G

(* ---- parents_in(lo, hi, a, b) ---- *)
RECURSIVE ParentsIn(_, _, _, _)
ParentsIn(lo, hi, a, b) ==
    IF hi - lo < 2 \/ b <= lo \/ hi <= a THEN 0
    ELSE IF a <= lo /\ hi <= b THEN hi - lo - 1
    ELSE LET mid == lo + LeftGroups(hi - lo)
         IN 1 + ParentsIn(lo, mid, a, b) + ParentsIn(mid, hi, a, b)

(* ---- parents_in_suffix: the loop with its running sum ---- *)
RECURSIVE SufGo(_, _, _, _)
SufGo(lo, hi, s, sum) ==
    IF hi - lo >= 2 /\ s < hi
    THEN IF s <= lo THEN sum + hi - lo - 1
         ELSE LET mid == lo + LeftGroups(hi - lo)
              IN IF s < mid THEN SufGo(lo, mid, s, sum + 1 + (hi - mid - 1))
                 ELSE SufGo(mid, hi, s, sum + 1)
    ELSE sum
ParentsInSuffix(lo, hi, s) == SufGo(lo, hi, s, 0)

(* ---- parents_before(n, a, x) ---- *)
RECURSIVE PbGo(_, _, _, _, _)
PbGo(a, x, lo, hi, sum) ==
    IF hi - lo >= 2
    THEN LET mid == lo + LeftGroups(hi - lo)
         IN IF x < mid THEN PbGo(a, x, lo, mid, sum + 1)
            ELSE PbGo(a, x, mid, hi, sum + 1 + ParentsInSuffix(lo, mid, a))
    ELSE sum
ParentsBefore(n, a, x) == PbGo(a, x, 0, n, 0)

(* ---- path(n, x): the parents above group x, root first, in an array of 64 (a node past the 64th is dropped) ---- *)
RECURSIVE PathGo(_, _, _, _, _)
PathGo(x, lo, hi, idx, acc) ==
    IF hi - lo >= 2
    THEN LET left == LeftGroups(hi - lo)
             mid == lo + left
             acc2 == IF Len(acc) < 64 THEN Append(acc, <<lo, idx>>) ELSE acc
         IN IF x < mid THEN PathGo(x, lo, mid, idx + 1, acc2) ELSE PathGo(x, mid, hi, idx + left, acc2)
    ELSE acc
Path(n, x) == PathGo(x, 0, n, 0, <<>>)

RangePairs(n, a, b) == ParentsIn(0, n, a, b)

(* ---- the reference: the encoder's walk and its frames ---- *)

(* the steps of the groups [a, b) in the node [lo, hi) of a tree of n groups with pre-order index idx: the node's
   pair, the steps of the left child, those of the right child, a child only when it meets [a, b) *)
RECURSIVE RefWalk(_, _, _, _, _, _)
RefWalk(len, lo, hi, idx, a, b) ==
    IF hi - lo < 2
    THEN <<[k |-> "g", off |-> lo * G, len |-> GroupSize(len, lo)]>>
    ELSE LET left == LeftGroups(hi - lo)
             mid == lo + left
         IN <<[k |-> "p", off |-> idx * PAR]>>
            \o (IF a < mid THEN RefWalk(len, lo, mid, idx + 1, a, b) ELSE <<>>)
            \o (IF mid < b THEN RefWalk(len, mid, hi, idx + left, a, b) ELSE <<>>)

RefSteps(len, a, b) == RefWalk(len, 0, Groups(len), 0, a, b)

(* the frames of a step list: the pairs opened since the previous group, then the group *)
RECURSIVE RefCut(_, _)
RefCut(steps, pend) ==
    IF steps = <<>> THEN <<>>
    ELSE IF Head(steps).k = "p" THEN RefCut(Tail(steps), Append(pend, Head(steps).off))
    ELSE <<[pend |-> pend, off |-> Head(steps).off, len |-> Head(steps).len]>> \o RefCut(Tail(steps), <<>>)

RefFrames(len, a, b) == RefCut(RefSteps(len, a, b), <<>>)

FrameBytes(f) == HDR + Len(f.pend) * PAR + f.len

RECURSIVE RefSizeSum(_)
RefSizeSum(fs) == IF fs = <<>> THEN 0 ELSE FrameBytes(Head(fs)) + RefSizeSum(Tail(fs))
RefSize(len, a, b) == RefSizeSum(RefFrames(len, a, b))

(* ---- Plan::new ---- *)

(* the specification: exact sizes of the reference frames, the same refusals *)
RECURSIVE SpecGo(_, _, _, _)
SpecGo(len, spans, total, rs) ==
    IF spans = <<>> THEN [total |-> total, rs |-> rs]
    ELSE LET s == Head(spans)
         IN IF s[2] = 0 THEN SpecGo(len, Tail(spans), total, rs)
            ELSE IF s[1] + s[2] > len THEN [err |-> "oob"]
            ELSE LET a == s[1] \div G
                     b == (s[1] + s[2] + G - 1) \div G
                     sz == RefSize(len, a, b)
                 IN IF total + sz > MaxS THEN [err |-> "long"]
                    ELSE SpecGo(len, Tail(spans), total + sz, Append(rs, [first |-> a, last |-> b, start |-> total]))
SpecNew(len, spans) == IF Len(spans) > MaxR THEN [err |-> "many"] ELSE SpecGo(len, spans, 0, <<>>)

(* the code: u64 arithmetic with its checks *)
RECURSIVE NewGo(_, _, _, _, _)
NewGo(len, n, spans, total, rs) ==
    IF spans = <<>> THEN [total |-> total, rs |-> rs]
    ELSE LET s == Head(spans)
         IN IF s[2] = 0 THEN NewGo(len, n, Tail(spans), total, rs)
            ELSE LET e == CAdd(s[1], s[2])
                 IN IF ~e.ok \/ e.v > len THEN [err |-> "oob"]
                    ELSE LET first == s[1] \div G
                             last == (e.v + G - 1) \div G
                             data == Min(SatMul(last, G), len) - first * G
                             h == CMul(last - first, HDR)
                             d == CAdd(h.v, data)
                             p == CMul(ParentsIn(0, n, first, last), PAR)
                             sz == CAdd(d.v, p.v)
                             t == CAdd(total, sz.v)
                         IN IF ~(h.ok /\ d.ok /\ p.ok /\ sz.ok) THEN [err |-> "long"]
                            ELSE IF ~t.ok \/ t.v > MaxS THEN [err |-> "long"]
                            ELSE NewGo(len, n, Tail(spans), t.v, Append(rs, [first |-> first, last |-> last, start |-> total]))
PlanNew(len, spans) ==
    IF Len(spans) > MaxR THEN [err |-> "many"] ELSE NewGo(len, Groups(len), spans, 0, <<>>)

(* ---- frames ---- *)
FrameStart(len, r, k) ==
    IF k = 0 THEN r.start
    ELSE r.start + k * HDR + (Min((r.first + k) * G, len) - r.first * G)
         + PAR * ParentsBefore(Groups(len), r.first, r.first + k - 1)

(* Plan::frame(i, k): none (an empty record) for a range or group the plan lacks *)
Frame(len, rs, i, k) ==
    IF i < 1 \/ i > Len(rs) THEN [none |-> TRUE]
    ELSE LET r == rs[i]
             x == r.first + k
         IN IF x >= r.last THEN [none |-> TRUE]
            ELSE LET n == Groups(len)
                     before == ParentsBefore(n, r.first, x)
                     prev == IF k = 0 THEN 0 ELSE ParentsBefore(n, r.first, x - 1)
                 IN [range |-> i, k |-> k, start |-> FrameStart(len, r, k), off |-> x * G,
                     dlen |-> GroupSize(len, x), plen |-> (before - prev) * PAR, follows |-> k > 0]

FrameEnd(f) == f.start + HDR + f.plen + f.dlen

(* the binary search of locate: lo, hi, mid = lo + (hi - lo).div_ceil(2) *)
RECURSIVE BsGo(_, _, _, _, _, _)
BsGo(len, r, at, lo, hi, dummy) ==
    IF lo < hi
    THEN LET mid == lo + (hi - lo + 1) \div 2
         IN IF FrameStart(len, r, mid) <= at THEN BsGo(len, r, at, mid, hi, dummy)
            ELSE BsGo(len, r, at, lo, mid - 1, dummy)
    ELSE lo

(* partition_point(|r| r.start <= at) on the ranges: the first index where the predicate fails (0-based count) *)
RECURSIVE PartPoint(_, _, _)
PartPoint(rs, at, i) == IF i > Len(rs) THEN Len(rs) ELSE IF rs[i].start <= at THEN PartPoint(rs, at, i + 1) ELSE i - 1

Locate(len, rs, total, at) ==
    IF at >= total THEN [none |-> TRUE]
    ELSE LET p == PartPoint(rs, at, 1)
         IN IF p < 1 THEN [none |-> TRUE]
            ELSE LET r == rs[p]
                     k == BsGo(len, r, at, 0, r.last - r.first - 1, 0)
                     f == Frame(len, rs, p, k)
                 IN IF "none" \in DOMAIN f THEN f ELSE IF at < FrameEnd(f) THEN f ELSE [none |-> TRUE]

(* frame_of_group: the frame of the group at value offset off in the first range that holds it *)
RECURSIVE FirstHolding(_, _, _)
FirstHolding(rs, g, i) == IF i > Len(rs) THEN 0 ELSE IF rs[i].first <= g /\ g < rs[i].last THEN i ELSE FirstHolding(rs, g, i + 1)
FrameOfGroup(len, rs, off) ==
    IF off % G # 0 THEN [none |-> TRUE]
    ELSE LET g == off \div G
             i == FirstHolding(rs, g, 1)
         IN IF i = 0 THEN [none |-> TRUE] ELSE Frame(len, rs, i, g - rs[i].first)

(* proof_pair(frame, j): the outboard offset of the j-th pair of the proof (j from 0), none past the pairs *)
RECURSIVE Starting(_, _)
Starting(live, x) == IF live = <<>> THEN <<>>
                     ELSE (IF Head(live)[1] = x THEN <<Head(live)>> ELSE <<>>) \o Starting(Tail(live), x)
ProofPair(len, rs, f, j) ==
    LET r == rs[f.range]
        x == r.first + f.k
        live == Path(Groups(len), x)
        cands == IF f.follows THEN Starting(live, x) ELSE live
    IN IF j + 1 > Len(cands) THEN [none |-> TRUE]
       ELSE LET m == CMul(cands[j + 1][2], PAR) IN IF m.ok THEN [off |-> m.v] ELSE [none |-> TRUE]
=============================================================================
