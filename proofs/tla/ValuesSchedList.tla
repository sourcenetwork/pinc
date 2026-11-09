---------------------------- MODULE ValuesSchedList ----------------------------
(***************************************************************************)
(* Model of vinc-values span.rs: Span, the bounded RangeList<N> (push,      *)
(* push_front, pop_front, push_new, total), holes, align and split. Every   *)
(* operator is the code step for step, with the saturating arithmetic of    *)
(* Span::end: End(s) = min(off + len, MAXU), MAXU standing for u64::MAX     *)
(* (TLC integers are 32 bits, so the word is a small one; the Lean theorems *)
(* of ValuesSchedList / ValuesSchedHoles / ValuesSchedSplit are for the     *)
(* real 2^64 and every length).                                              *)
(*                                                                         *)
(* TLC explores every list reachable by any sequence of the operations and  *)
(* checks, after each one:                                                  *)
(*  - the list never outgrows N and holds non-empty spans inside the word;  *)
(*  - coverage never shrinks: a push or push_front onto a full list widens, *)
(*    it may ask twice, it never skips (CoverNeverShrinks);                 *)
(*  - below capacity, and for a span that touches the last one, the covered *)
(*    set is exactly the union (PushExact), and a byte beyond the union is  *)
(*    in the hull of the last span and the new one (WidenInHull);           *)
(*  - disjoint pushes below capacity keep every byte once (NoDoubleBelow);  *)
(*  - an in-order push keeps the list sorted (SortedKept);                  *)
(*  - push_new adds exactly the uncovered bytes (PushNewExact);             *)
(*  - pop_front returns the first span and the rest.                        *)
(* StaticChecks, over every verified set, span, group count and share      *)
(* count of the bounded domain: holes returns exactly the unverified part   *)
(* of the span, in order, strictly separated; align rounds a non-empty span *)
(* out to whole groups clamped to the value; split gives shares that cover  *)
(* the list, stay in order, and cut only at group boundaries.               *)
(***************************************************************************)
EXTENDS ValuesSchedSpans, TLC

CONSTANTS N, GG, SPLITS

Spans == [off : 0 .. MAXU, len : 0 .. MAXU]
Valid(s) == s.off + s.len <= MAXU

Push(l, s) == PushC(N, l, s)
PushFront(l, s) == PushFrontC(N, l, s)
PushNew(l, s) == PushNewC(N, l, s)
Total(l) == TotalL(l)
Extend(l, o) == ExtendC(N, l, o)

(* ---- holes against the contract of ValueStore::verified_from ---- *)
(* the maximal runs of verified bytes: [a, b) *)
Runs(V) == {<<a, b>> \in (0 .. MAXU) \X (0 .. (MAXU + 1)) :
              a \in V /\ (a - 1) \notin V /\ b > a /\ (\A y \in a .. (b - 1) : y \in V) /\ b \notin V}
(* the first verified interval that ends after c (it may start before c) *)
VF(V, c) ==
    LET cand == {r \in Runs(V) : r[2] > c}
    IN IF cand = {} THEN NONE
       ELSE LET r == CHOOSE r \in cand : \A q \in cand : r[2] <= q[2] IN [start |-> r[1], end |-> r[2]]

Holes(V, s) == HolesOf(LAMBDA c : VF(V, c), s)

Align(s, total) == AlignG(GG, s, total)
Split(l, S, kk) == SplitG(GG, N, l, S, kk)

(* ---- the state machine of the list operations ---- *)
(* The state is the list and a flag that records whether any step broke a postcondition, so that the state space is the
   set of reachable lists and not their histories. *)
VARIABLES l, bad
vars == <<l, bad>>

Init == l = <<>> /\ bad = FALSE

Touches(p, s) == p # <<>> /\ s.off >= p[Len(p)].off /\ s.off <= End(p[Len(p)])

SortedL(m) == \A a, b \in 1 .. Len(m) : a < b => End(m[a]) <= m[b].off

(* coverage never shrinks, and the new span is covered *)
CoverNeverShrinks(pre, s, new) == Bytes(pre) \cup Seg(s) \subseteq Bytes(new)

(* below capacity, or touching the last span (push), the covered set is exactly the union *)
PushExact(pre, s, new) == (Len(pre) < N \/ Touches(pre, s)) => Bytes(new) = Bytes(pre) \cup Seg(s)
PushFrontExact(pre, s, new) == Len(pre) < N => Bytes(new) = Bytes(pre) \cup Seg(s)

(* a widened byte lies between the last (first) span and the new one *)
WidenInHull(pre, s, new) ==
    pre # <<>> =>
        Bytes(new) \ (Bytes(pre) \cup Seg(s)) \subseteq Min(pre[Len(pre)].off, s.off) .. (Max(End(pre[Len(pre)]), End(s)) - 1)
WidenFrontInHull(pre, s, new) ==
    pre # <<>> =>
        Bytes(new) \ (Bytes(pre) \cup Seg(s)) \subseteq Min(pre[1].off, s.off) .. (Max(End(pre[1]), End(s)) - 1)

(* below capacity, a span disjoint from the list adds its bytes once and no others *)
NoDoubleBelow(pre, s, new) ==
    (Len(pre) < N /\ Bytes(pre) \cap Seg(s) = {}) =>
        \A x \in 0 .. MAXU : Mult(new, x) = Mult(pre, x) + (IF x \in Seg(s) THEN 1 ELSE 0)

(* an in-order push (not before the last span) keeps the list sorted *)
SortedKept(pre, s, new) == (SortedL(pre) /\ (pre = <<>> \/ pre[Len(pre)].off <= s.off)) => SortedL(new)

(* push_new adds exactly the bytes nothing covered, each once *)
PushNewExact(pre, s, new) ==
    (Len(pre) + Cardinality(Seg(s)) <= N) =>
        /\ Bytes(new) = Bytes(pre) \cup Seg(s)
        /\ (TotalL(pre) + Cardinality(Seg(s) \ Bytes(pre)) <= MAXU =>
              TotalL(new) - TotalL(pre) = Cardinality(Seg(s) \ Bytes(pre)))

PushOk(pre, s, new) ==
    /\ CoverNeverShrinks(pre, s, new) /\ PushExact(pre, s, new) /\ WidenInHull(pre, s, new)
    /\ NoDoubleBelow(pre, s, new) /\ SortedKept(pre, s, new) /\ Len(new) <= Len(pre) + 1 /\ Len(new) <= N
PushFrontOk(pre, s, new) ==
    /\ CoverNeverShrinks(pre, s, new) /\ PushFrontExact(pre, s, new) /\ WidenFrontInHull(pre, s, new)
    /\ Len(new) <= Len(pre) + 1 /\ Len(new) <= N
PushNewOk(pre, s, new) == PushNewExact(pre, s, new) /\ Len(new) <= N

DoPush(s) == /\ l' = Push(l, s) /\ bad' = (bad \/ ~PushOk(l, s, Push(l, s)))
DoPushFront(s) == /\ l' = PushFront(l, s) /\ bad' = (bad \/ ~PushFrontOk(l, s, PushFront(l, s)))
DoPushNew(s) == /\ l' = PushNew(l, s) /\ bad' = (bad \/ ~PushNewOk(l, s, PushNew(l, s)))
DoPop == /\ l # <<>> /\ l' = Tail(l) /\ bad' = bad

Next == \/ \E s \in Spans : Valid(s) /\ (DoPush(s) \/ DoPushFront(s) \/ DoPushNew(s))
        \/ DoPop

Spec == Init /\ [][Next]_vars

TypeOK == /\ Len(l) <= N /\ \A k \in 1 .. Len(l) : l[k].len > 0 /\ Valid(l[k]) /\ End(l[k]) = l[k].off + l[k].len

Inv == TypeOK /\ ~bad

(* ---- the static checks ---- *)
Subsets(S) == SUBSET S
RunsOf(l1) == l1

\* holes: exactly the unverified part of the span, in order, strictly separated, each non-empty
HolesOk ==
    \A V \in SUBSET (0 .. (MAXU - 1)) : \A s \in Spans :
        Valid(s) =>
            LET h == Holes(V, s)
            IN /\ Bytes(h) = Seg(s) \ V
               /\ \A a \in 1 .. Len(h) : h[a].len > 0
               /\ \A a, b \in 1 .. Len(h) : a < b => End(h[a]) < h[b].off
               /\ Total(h) = Cardinality(Seg(s) \ V)

\* align: a non-empty span inside the value rounds out to the whole groups around it
AlignOk ==
    \A total \in 0 .. MAXU : \A s \in Spans :
        (Valid(s) /\ s.off + s.len <= total) =>
            LET a == Align(s, total)
            IN IF s.len = 0 THEN a = NONE
               ELSE /\ a # NONE
                    /\ a.off % GG = 0 /\ a.off <= s.off /\ s.off < a.off + GG
                    /\ s.off + s.len <= a.off + a.len /\ a.off + a.len <= total
                    /\ ((a.off + a.len) % GG = 0 \/ a.off + a.len = total)

\* an empty or out-of-value span asks for nothing, never panics
AlignEmpty == \A total \in 0 .. MAXU : \A s \in Spans : s.len = 0 => Align(s, total) = NONE

AlignedL(m) == \A k \in 1 .. Len(m) : m[k].off % GG = 0 /\ m[k].len % GG = 0

\* split: the shares cover the list exactly, in order, and cut only at group boundaries (a list of whole groups)
SplitOk ==
    \A m \in {m \in UNION {[1 .. n -> Spans] : n \in 0 .. 2} :
                 AlignedL(m) /\ (\A k \in 1 .. Len(m) : m[k].len > 0 /\ Valid(m[k])) /\ SortedL(m) /\ Len(m) + 3 <= N} :
        \A S \in SPLITS : \A kk \in 0 .. (S + 1) :
            LET out == Split(m, S, kk)
                kc == Max(1, Min(kk, Max(S, 1)))
                all == [i \in 1 .. 0 |-> 0]
            IN /\ \A i \in 0 .. (S - 1) : AlignedL(out[i]) /\ (i >= kc => out[i] = <<>>)
               /\ UNION {Bytes(out[i]) : i \in 0 .. (S - 1)} = Bytes(m)
               /\ \A x \in Bytes(m) : (Cardinality({i \in 0 .. (S - 1) : x \in Bytes(out[i])}) = 1)
               /\ \A i, j \in 0 .. (S - 1) : i < j => \A x \in Bytes(out[i]), y \in Bytes(out[j]) : x < y

StaticChecks == HolesOk /\ AlignOk /\ AlignEmpty /\ SplitOk

(* checked once, at startup, over the whole bounded domain *)
ASSUME StaticChecks

=================================================================================
