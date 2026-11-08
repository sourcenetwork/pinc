--------------------------------- MODULE RangeOps ---------------------------------
(***************************************************************************)
(* The pure operations of a verified-range set (vinc-dag/src/ranges.rs).   *)
(* A set is a sequence of <<start, end>> pairs, half-open, sorted. Shared  *)
(* by the model (VerifiedRanges.tla) and by the trace check, so both use  *)
(* one definition of insert.                                               *)
(***************************************************************************)
EXTENDS Integers, Sequences

Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

(* x lies in one of the intervals *)
Covers(items, x) == \E i \in 1..Len(items) : items[i][1] <= x /\ x < items[i][2]

(* every offset of [s, e) is covered; true for an empty range *)
CoversRange(items, s, e) == \A x \in s..(e - 1) : Covers(items, x)

(* Each start is below its end and neighbours are strictly separated. *)
Canonical(items) ==
    /\ \A i \in 1..Len(items) : items[i][1] < items[i][2]
    /\ \A i \in 1..(Len(items) - 1) : items[i][2] < items[i + 1][1]

(* slice::partition_point for a partitioned sequence: the index of the first element where Pred fails *)
PP(Pred(_), sq) ==
    CHOOSE k \in 0..Len(sq) :
        /\ \A i \in 1..k : Pred(sq[i])
        /\ k < Len(sq) => ~Pred(sq[k + 1])

(* plan: two partition points and the merged interval (indices are the Rust 0-based counts) *)
Plan(items, r) ==
    LET from == PP(LAMBDA iv : iv[2] < r[1], items)
        to == PP(LAMBDA iv : iv[1] <= r[2], items)
        start == IF from < Len(items) THEN Min(items[from + 1][1], r[1]) ELSE r[1]
        stop == IF to >= 1 THEN Max(items[to][2], r[2]) ELSE r[2]
    IN [from |-> from, to |-> to, merged |-> IF from < to THEN <<start, stop>> ELSE r]

(* insert into a set of capacity cap: the new items and whether it succeeded (a failure changes nothing) *)
InsertResult(items, r, cap) ==
    IF r[1] >= r[2]
    THEN [items |-> items, ok |-> TRUE]
    ELSE LET p == Plan(items, r)
             newLen == Len(items) - (p.to - p.from) + 1
         IN IF newLen > cap
            THEN [items |-> items, ok |-> FALSE]
            ELSE [items |-> SubSeq(items, 1, p.from) \o <<p.merged>> \o SubSeq(items, p.to + 1, Len(items)),
                  ok |-> TRUE]

(* covered_len: the sum of the interval lengths *)
CoveredLen(items) ==
    LET RECURSIVE Sum(_)
        Sum(i) == IF i = 0 THEN 0 ELSE Sum(i - 1) + items[i][2] - items[i][1]
    IN Sum(Len(items))
=================================================================================
