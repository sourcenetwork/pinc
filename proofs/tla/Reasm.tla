-------------------------------- MODULE Reasm --------------------------------
(***************************************************************************)
(* Handshake fragment reassembly of pinc-transport conn/reasm.rs over      *)
(* every interleaving of fragments (any order, any number of times, of     *)
(* messages of different lengths), at small sizes (ReasmOps.tla has the    *)
(* operators).                                                             *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the runs are sorted, disjoint, non-adjacent and non-empty, inside   *)
(*    [0, total), at most NR of them (Shape);                              *)
(*  - reassembly is exact: the bytes the runs cover are exactly the bytes *)
(*    of the fragments the reassembly kept, none that was dropped or      *)
(*    cut off at the end of the message, none twice (Exact);              *)
(*  - a message is handed over only when its bytes 0 .. total - 1 are all *)
(*    in, and then the next message starts from nothing (NoFalseComplete, *)
(*    CompleteIsExact);                                                    *)
(*  - the table is bounded: a fragment that needs a run past NR is        *)
(*    dropped and changes nothing but the message length (Bounded);        *)
(*  - the state never holds more than MX bytes (Total).                    *)
(* Lean counterpart: proofs/lean/Pinc/TransportReasm*.lean.                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS MX, NR, KMAX
VARIABLES r, acc, k, comp
vars == <<r, acc, k, comp>>

INSTANCE ReasmOps

Init == r = Reasm0 /\ acc = {} /\ k = 0 /\ comp = TRUE

Frag == \E total \in {0, 3, 4, MX + 1}, off \in 0..4, dlen \in 0..4 :
          LET x == Add(r, MX, NR, total, off, dlen)
              stop == Mn(off + dlen, total)
              rejected == total = 0 \/ total > MX
              base == IF total # r.total THEN {} ELSE acc
              r1 == IF total # r.total THEN [runs |-> <<>>, total |-> total] ELSE r
              fits == stop > off /\ Len(MergeRuns(r1.runs, off, stop, <<>>).keep) < NR
              got == base \cup {p \in off..(stop - 1) : TRUE}
          IN /\ r' = x.r /\ k' = k + 1
             /\ acc' = IF rejected THEN acc ELSE IF fits THEN (IF x.out >= 0 THEN {} ELSE got) ELSE base
             /\ comp' = (x.out >= 0 => got = {p \in 0..(total - 1) : TRUE})

Next == Frag
Spec == Init /\ [][Next]_vars
Bound == k <= KMAX

Cover(rs) == UNION {{p \in rs[i][1]..(rs[i][2] - 1) : TRUE} : i \in DOMAIN rs}
Shape == /\ Len(r.runs) <= NR
         /\ \A i \in DOMAIN r.runs : r.runs[i][1] < r.runs[i][2] /\ r.runs[i][2] <= r.total
         /\ \A i \in 1..(Len(r.runs) - 1) : r.runs[i][2] < r.runs[i + 1][1]
Exact == Cover(r.runs) = acc
NoFalseComplete == comp
Total == r.total <= MX
Inv == Shape /\ Exact /\ NoFalseComplete /\ Total
=============================================================================
