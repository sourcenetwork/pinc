------------------------------ MODULE VerifiedRanges ------------------------------
(***************************************************************************)
(* Model of vinc-dag VerifiedRanges<N>: a sorted list of disjoint          *)
(* half-open intervals with fixed capacity N. Insert mirrors the Rust      *)
(* insert, including the capacity failure that changes nothing.            *)
(*                                                                         *)
(* Checked by TLC over offsets 0..MaxOff: the Canonical invariant, a       *)
(* monotone coverage, and that an insert covers its range exactly on       *)
(* success and fails exactly when the merged set needs more than N         *)
(* intervals (counted independently as maximal runs of covered offsets).   *)
(***************************************************************************)
EXTENDS RangeOps, FiniteSets

CONSTANTS N, MaxOff

Offsets == 0..MaxOff

VARIABLES items, req, res
vars == <<items, req, res>>

Init == items = <<>> /\ req = <<0, 0>> /\ res = "ok"

(* One insert of r into a set of capacity cap. *)
Insert(r, cap) ==
    LET out == InsertResult(items, r, cap)
    IN /\ items' = out.items
       /\ req' = r
       /\ res' = IF out.ok THEN "ok" ELSE "full"

Next == \E s \in Offsets, e \in Offsets : Insert(<<s, e>>, N)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ items \in Seq(Offsets \X Offsets)
    /\ req \in Offsets \X Offsets
    /\ res \in {"ok", "full"}

(* the canonical invariant, within capacity; and the binary search loop of partition_point, run with each
   predicate that plan and find use, returns the first index where it fails (PP, the specification) and finds
   exactly the covered offsets (Lean: PP.partitionPoint_eq, with Ranges.part_end_lt, part_start_le, part_end_le
   for the partition of canonical sets) *)
Inv ==
    /\ Canonical(items) /\ Len(items) <= N
    /\ CoveredLen(items) = Cardinality({x \in Offsets : Covers(items, x)})
    /\ \A x \in 0..(MaxOff + 1) :
          /\ PPLoop(LAMBDA iv : iv[2] < x, items) = PP(LAMBDA iv : iv[2] < x, items)
          /\ PPLoop(LAMBDA iv : iv[1] <= x, items) = PP(LAMBDA iv : iv[1] <= x, items)
          /\ PPLoop(LAMBDA iv : iv[2] <= x, items) = PP(LAMBDA iv : iv[2] <= x, items)
          /\ Find(items, x) = Covers(items, x)
          /\ \A y \in 0..(MaxOff + 1) : ContainsRange(items, x, y) = CoversRange(items, x, y)

(* a covered offset stays covered, also across a capacity failure *)
MonotoneCoverage == [][\A x \in Offsets : Covers(items, x) => Covers(items', x)]_vars

(* on success the range is covered *)
InsertCovers == res = "ok" => \A x \in Offsets : (req[1] <= x /\ x < req[2]) => Covers(items, x)

(* on success the new coverage is the old one plus the range, nothing else *)
InsertExact ==
    [][res' = "ok" => \A x \in Offsets :
          Covers(items', x) <=> (Covers(items, x) \/ (req'[1] <= x /\ x < req'[2]))]_vars

(* a failed insert changes nothing *)
FailureUnchanged == [][res' = "full" => items' = items]_vars

(* the number of maximal runs of consecutive offsets in a set of offsets *)
Runs(S) == Cardinality({x \in S : (x - 1) \notin S})

(* failure happens iff the merged set needs more than N intervals *)
FailIff ==
    [][LET merged == {x \in Offsets : Covers(items, x) \/ (req'[1] <= x /\ x < req'[2])}
       IN res' = "full" <=> (req'[1] < req'[2] /\ Runs(merged) > N)]_vars
=================================================================================
