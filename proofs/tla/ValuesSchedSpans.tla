---------------------------- MODULE ValuesSchedSpans ----------------------------
(***************************************************************************)
(* The operators of pinc-values span.rs on lists of spans [off, len],       *)
(* shared by the list model (ValuesSchedList.tla) and the schedule model    *)
(* (ValuesSched.tla): Span::end, RangeList push / push_front / extend /     *)
(* push_new / total with the capacity as an argument, and the holes loop    *)
(* against any `verified_from` (an operator argument). The saturating add   *)
(* of Span::end is Sat, MAXU standing for u64::MAX.                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, ValuesSchedOps

CONSTANT MAXU

Sat(x) == IF x > MAXU THEN MAXU ELSE x
End(s) == Sat(s.off + s.len)
Seg(s) == s.off .. (End(s) - 1)

(* RangeList<c>::push: merge with the last span when s starts inside or right after it; a full list widens its last span *)
PushC(c, l, s) ==
    IF s.len = 0 THEN l
    ELSE IF l = <<>> THEN (IF c > 0 THEN <<s>> ELSE l)
    ELSE LET last == l[Len(l)]
         IN IF (s.off >= last.off /\ s.off <= End(last)) \/ Len(l) = c
            THEN LET off == Min(last.off, s.off)
                 IN SubSeq(l, 1, Len(l) - 1) \o <<[off |-> off, len |-> Max(End(last), End(s)) - off]>>
            ELSE IF Len(l) < c THEN Append(l, s) ELSE l

(* RangeList<c>::push_front: a full list widens its first span back over s *)
PushFrontC(c, l, s) ==
    IF s.len = 0 THEN l
    ELSE IF Len(l) = c
         THEN (IF l = <<>> THEN l
               ELSE LET f == l[1]
                        off == Min(f.off, s.off)
                    IN <<[off |-> off, len |-> Max(End(f), End(s)) - off]>> \o Tail(l))
         ELSE <<s>> \o l

(* RangeList::extend: push every span of o in order *)
RECURSIVE ExtendC(_, _, _)
ExtendC(c, l, o) == IF o = <<>> THEN l ELSE ExtendC(c, PushC(c, l, Head(o)), Tail(o))

(* RangeList::total, with the saturating add of the fold *)
TotalL(l) == LET RECURSIVE T(_, _)
                 T(i, acc) == IF i > Len(l) THEN acc ELSE T(i + 1, Sat(acc + l[i].len))
             IN T(1, 0)

(* RangeList::push_new: the parts of s that no span of the list covers, appended in order *)
RECURSIVE PushNewLoop(_, _, _, _)
PushNewLoop(c, l, cur, e) ==
    IF cur >= e THEN l
    ELSE LET covering == {End(l[k]) : k \in {j \in 1 .. Len(l) : l[j].off <= cur /\ cur < End(l[j])}}
             starts == {l[k].off : k \in {j \in 1 .. Len(l) : l[j].off > cur /\ l[j].off < e}}
         IN IF covering # {}
            THEN PushNewLoop(c, l, CHOOSE m \in covering : \A y \in covering : y <= m, e)
            ELSE LET nxt == IF starts = {} THEN e ELSE CHOOSE m \in starts : \A y \in starts : y >= m
                 IN PushNewLoop(c, PushC(c, l, [off |-> cur, len |-> nxt - cur]), nxt, e)
PushNewC(c, l, s) == PushNewLoop(c, l, s.off, End(s))

NONE == [none |-> TRUE]

(* span.rs holes: the parts of [cur, e) the store has not verified. VFop(c) is the first verified interval that ends
   after c, [start, end] (it may start before c), or NONE. *)
RECURSIVE HolesLoop(_, _, _)
HolesLoop(VFop(_), e, cur) ==
    IF cur >= e THEN <<>>
    ELSE LET v == VFop(cur)
         IN IF v = NONE THEN <<[off |-> cur, len |-> e - cur]>>
            ELSE IF v.start <= cur THEN HolesLoop(VFop, e, v.end)
            ELSE IF v.start < e THEN <<[off |-> cur, len |-> v.start - cur]>> \o HolesLoop(VFop, e, v.end)
            ELSE <<[off |-> cur, len |-> e - cur]>>
HolesOf(VFop(_), s) == HolesLoop(VFop, End(s), s.off)

(* fetch retain_missing: the unverified parts of every span, pushed in order into a list of capacity c *)
RECURSIVE RetainLoop(_, _, _, _)
RetainLoop(c, VFop(_), l, out) ==
    IF l = <<>> THEN out
    ELSE RetainLoop(c, VFop, Tail(l), ExtendC(c, out, HolesOf(VFop, Head(l))))
Retain(c, VFop(_), l) == RetainLoop(c, VFop, l, <<>>)

(* span.rs align: round a non-empty span out to whole groups of gg bytes, clamped to a value of `total` bytes *)
CeilDiv(x, d) == (x + d - 1) \div d
AlignG(gg, s, total) ==
    LET a == (s.off \div gg) * gg
        b == Min(Sat(CeilDiv(End(s), gg) * gg), total)
    IN IF s.len > 0 /\ b > a THEN [off |-> a, len |-> b - a] ELSE NONE

(* RangeList::split into S shares of capacity c, k wanted: contiguous shares of whole groups of gg bytes *)
RECURSIVE SplitSpan(_, _, _, _, _, _, _, _)
\* SplitSpan(c, k, share, e, cur, idx, acc, out) -> [idx, acc, out]
SplitSpan(c, k, share, e, cur, idx, acc, out) ==
    IF cur >= e THEN [idx |-> idx, acc |-> acc, out |-> out]
    ELSE LET last == idx + 1 >= k
             room == IF last THEN e - cur ELSE Max(share - acc, 1)
             take == Min(room, e - cur)
             out2 == [out EXCEPT ![idx] = PushC(c, out[idx], [off |-> cur, len |-> take])]
         IN IF acc + take >= share /\ ~last
            THEN SplitSpan(c, k, share, e, cur + take, idx + 1, 0, out2)
            ELSE SplitSpan(c, k, share, e, cur + take, idx, acc + take, out2)

RECURSIVE SplitList(_, _, _, _, _, _)
SplitList(c, k, share, l, i, st) ==
    IF i > Len(l) THEN st
    ELSE SplitList(c, k, share, l, i + 1, SplitSpan(c, k, share, End(l[i]), l[i].off, st.idx, st.acc, st.out))

SplitG(gg, c, l, S, kk) ==
    LET k == Max(1, Min(kk, Max(S, 1)))
        share == Max((((TotalL(l) \div k) \div gg)) * gg, gg)
    IN SplitList(c, k, share, l, 1, [idx |-> 0, acc |-> 0, out |-> [i \in 0 .. (S - 1) |-> <<>>]]).out

(* the bytes of a list, for the small domains of the list model, and the multiplicity of a byte *)
Bytes(l) == UNION {Seg(l[k]) : k \in 1 .. Len(l)}
Mult(l, x) == Cardinality({k \in 1 .. Len(l) : x \in Seg(l[k])})
=================================================================================
