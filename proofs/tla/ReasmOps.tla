------------------------------ MODULE ReasmOps ------------------------------
(***************************************************************************)
(* The operations of vinc-transport conn/reasm.rs (Reassembly), step for   *)
(* step: one handshake message put together from fragments that arrive in  *)
(* any order and any number of times, kept as at most nr disjoint sorted   *)
(* runs [start, end). Reasm.tla checks them over every interleaving at     *)
(* small sizes; TraceReasm.tla replays the recorded calls of the real      *)
(* code.                                                                   *)
(*                                                                         *)
(* The state r: runs (the runs, lowest first) and total (the length of the *)
(* message being assembled, 0 for none). mx is the largest message and nr  *)
(* the most runs; Add returns out, the length of the message when it is    *)
(* complete and -1 otherwise, and the new state. The bytes themselves are  *)
(* not in the model: the code copies a fragment into the buffer at its     *)
(* offset when it keeps it, and the Rust test checks the buffer against    *)
(* the fragments it sent.                                                  *)
(***************************************************************************)
EXTENDS Integers, Sequences

Mn(a, b) == IF a < b THEN a ELSE b
Mx(a, b) == IF a > b THEN a ELSE b

Reasm0 == [runs |-> <<>>, total |-> 0]

\* the runs that do not touch the new one are kept; the ones that do are folded into it
RECURSIVE MergeRuns(_, _, _, _)
MergeRuns(rs, lo, hi, keep) ==
    IF rs = <<>> THEN [keep |-> keep, lo |-> lo, hi |-> hi]
    ELSE IF rs[1][2] < lo \/ rs[1][1] > hi THEN MergeRuns(Tail(rs), lo, hi, Append(keep, rs[1]))
    ELSE MergeRuns(Tail(rs), Mn(lo, rs[1][1]), Mx(hi, rs[1][2]), keep)

RECURSIVE Below(_, _)
Below(keep, s) == IF keep = <<>> \/ keep[1][1] >= s THEN 0 ELSE 1 + Below(Tail(keep), s)
InsertRun(keep, iv) == LET p == Below(keep, iv[1]) IN SubSeq(keep, 1, p) \o <<iv>> \o SubSeq(keep, p + 1, Len(keep))

Add(r, mx, nr, total, off, dlen) ==
    IF total = 0 \/ total > mx THEN [out |-> -1, r |-> r]
    ELSE LET r1 == IF total # r.total THEN [runs |-> <<>>, total |-> total] ELSE r
             stop == Mn(off + dlen, total)
         IN IF stop <= off THEN [out |-> -1, r |-> r1]
            ELSE LET m == MergeRuns(r1.runs, off, stop, <<>>)
                 IN IF Len(m.keep) = nr THEN [out |-> -1, r |-> r1]
                    ELSE LET runs2 == InsertRun(m.keep, <<m.lo, m.hi>>)
                         IN IF Len(runs2) = 1 /\ m.lo = 0 /\ m.hi = total
                            THEN [out |-> total, r |-> Reasm0]
                            ELSE [out |-> -1, r |-> [runs |-> runs2, total |-> r1.total]]
=============================================================================
