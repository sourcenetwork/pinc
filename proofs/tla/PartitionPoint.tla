---------------------------- MODULE PartitionPoint ----------------------------
(***************************************************************************)
(* slice::partition_point, which plan and find of pinc-dag use             *)
(* (ranges.rs), as the standard library computes it: the branchless        *)
(* binary search of RangeOps.PPGo, run on every partitioned slice of up to *)
(* MaxLen elements (a prefix where the predicate holds, then the rest), so *)
(* every length, every number of leading true elements and every branch of *)
(* the halving loop is exercised, including the power-of-two lengths. The  *)
(* result must be the specification, the first index where the predicate  *)
(* fails (RangeOps.PP), and every probe must lie inside the slice (an      *)
(* out-of-range read of the sequence stops TLC with an error; the standard *)
(* library reads unchecked).                                               *)
(*                                                                         *)
(* The predicates of plan and find over the sets the insert reaches are    *)
(* checked in VerifiedRanges.tla (Inv) and, on the recorded sets of the    *)
(* Rust code, in TraceVerifiedRanges.tla.                                  *)
(*                                                                         *)
(* Lean counterpart: PP.partitionPoint_eq (proofs/lean/Pinc/PartitionPoint.lean), *)
(* whose loop ppGo is PPGo; Ranges.part_end_lt, part_start_le, part_end_le *)
(* for the partition of canonical sets.                                    *)
(***************************************************************************)
EXTENDS RangeOps

CONSTANT MaxLen

(* a slice of n elements whose first k satisfy the predicate *)
Slice(n, k) == [i \in 1..n |-> IF i <= k THEN 1 ELSE 0]
IsOne(x) == x = 1

VARIABLE c
Init == \E n \in 0..MaxLen : \E k \in 0..n : c = [n |-> n, k |-> k]
Next == UNCHANGED c
Spec == Init /\ [][Next]_c

Inv ==
    LET sq == Slice(c.n, c.k)
        r == PPLoop(IsOne, sq)
    IN /\ r = c.k
       /\ r = PP(IsOne, sq)
       /\ r <= c.n
=============================================================================
