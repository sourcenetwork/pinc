--------------------------------- MODULE RangeOps ---------------------------------
(***************************************************************************)
(* The pure operations of a verified-range set (pinc-dag/src/ranges.rs).   *)
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

(* the specification of slice::partition_point for a partitioned sequence: the index of the first element where
   Pred fails *)
PP(Pred(_), sq) ==
    CHOOSE k \in 0..Len(sq) :
        /\ \A i \in 1..k : Pred(sq[i])
        /\ k < Len(sq) => ~Pred(sq[k + 1])

(* slice::partition_point as the standard library computes it: the branchless binary search over `size` candidates
   from `base` (the loop of core::slice::binary_search_by in the pinned toolchain, 0-based as in Rust; the sequence
   is 1-based). Lean: PP.ppGo, PP.partitionPoint_eq. *)
RECURSIVE PPGo(_, _, _)
PPGo(bs, base, size) ==
    IF size > 1
    THEN LET half == size \div 2
             mid == base + half
         IN PPGo(bs, IF bs[mid + 1] THEN mid ELSE base, size - half)
    ELSE IF bs[base + 1] THEN base + 1 ELSE base

(* the predicate is pure, so its value at each element is computed up front and the loop reads the probed ones *)
PPLoop(Pred(_), sq) ==
    LET bs == [i \in 1..Len(sq) |-> Pred(sq[i])]
    IN IF Len(sq) = 0 THEN 0 ELSE PPGo(bs, 0, Len(sq))

(* plan: two partition points and the merged interval (indices are the Rust 0-based counts) *)
Plan(items, r) ==
    LET from == PPLoop(LAMBDA iv : iv[2] < r[1], items)
        to == PPLoop(LAMBDA iv : iv[1] <= r[2], items)
        start == IF from < Len(items) THEN Min(items[from + 1][1], r[1]) ELSE r[1]
        stop == IF to >= 1 THEN Max(items[to][2], r[2]) ELSE r[2]
    IN [from |-> from, to |-> to, merged |-> IF from < to THEN <<start, stop>> ELSE r]

(* find: the interval that holds offset x, if any: the partition point of `end <= x`, then the interval there
   when it starts at or before x (contains and contains_range use it) *)
FindAt(items, x) == PPLoop(LAMBDA iv : iv[2] <= x, items)
Find(items, x) == FindAt(items, x) < Len(items) /\ items[FindAt(items, x) + 1][1] <= x

(* contains_range: an empty range, or the interval found at its start reaches its end *)
ContainsRange(items, s, e) == s >= e \/ (Find(items, s) /\ items[FindAt(items, s) + 1][2] >= e)

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
