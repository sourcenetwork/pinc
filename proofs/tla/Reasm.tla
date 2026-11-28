-------------------------------- MODULE Reasm --------------------------------
(***************************************************************************)
(* Handshake fragment reassembly of pinc-transport conn/reasm.rs over      *)
(* every interleaving of fragments (any order, any number of times, of     *)
(* messages of different lengths, with bytes of NV senders), at small      *)
(* sizes (ReasmOps.tla has the operators).                                 *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the runs are sorted, disjoint, non-adjacent and non-empty, inside   *)
(*    [0, total), at most NR of them (Shape);                              *)
(*  - reassembly is exact: the bytes the runs cover are exactly the bytes *)
(*    of the fragments the reassembly kept, none that was dropped, refused *)
(*    or cut off at the end of the message, none twice (Exact);           *)
(*  - a message is handed over only when its bytes 0 .. total - 1 are all *)
(*    in, and then the next message starts from nothing (NoFalseComplete, *)
(*    CompleteIsExact);                                                    *)
(*  - the table is bounded: a fragment that needs a run past NR is        *)
(*    dropped and changes nothing but the message length (Bounded);        *)
(*  - the state never holds more than MX bytes (Total);                    *)
(*  - what is held stays (Agrees): until a message is handed over, every   *)
(*    byte the runs cover keeps the value it arrived with, so a fragment   *)
(*    that disagrees with it (another value at an offset it holds, or      *)
(*    another message length while one is under way) changes nothing and   *)
(*    is refused, for the caller to give it to another holder.            *)
(* Witness Reasm_last: the rule before the handshake fix (AGREE = FALSE),  *)
(* the last bytes written to an offset win and a fragment of another       *)
(* length starts over; a forged fragment erases or overwrites the honest   *)
(* message, and Agrees fails.                                              *)
(* Lean counterpart: proofs/lean/Pinc/TransportReasm*.lean (the shape and  *)
(* cover; the agreement rule is not in it yet).                            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS MX, NR, KMAX, NV, AGREE
VARIABLES r, vs, acc, k, comp, keeps
vars == <<r, vs, acc, k, comp, keeps>>

INSTANCE ReasmOps

Init == r = Reasm0 /\ vs = V0(MX) /\ acc = {} /\ k = 0 /\ comp = TRUE /\ keeps = TRUE

Cover(rs) == UNION {{p \in rs[i][1]..(rs[i][2] - 1) : TRUE} : i \in DOMAIN rs}

Frag == \E total \in {0, 3, 4, MX + 1}, off \in 0..4, dlen \in 0..4, v \in 1..NV :
          LET y == AddV([r |-> r, vs |-> vs], MX, NR, total, off, dlen, v, AGREE)
              stop == Mn(off + dlen, total)
              rejected == total = 0 \/ total > MX
              base == IF total # r.total THEN {} ELSE acc
              r1 == IF total # r.total THEN [runs |-> <<>>, total |-> total] ELSE r
              fits == stop > off /\ Len(MergeRuns(r1.runs, off, stop, <<>>).keep) < NR
              got == base \cup {p \in off..(stop - 1) : TRUE}
          IN /\ k' = k + 1
             /\ IF y.out = -2
                THEN UNCHANGED <<r, vs, acc, comp, keeps>>
                ELSE /\ r' = y.rv.r /\ vs' = y.rv.vs
                     /\ acc' = IF rejected THEN acc ELSE IF fits THEN (IF y.out >= 0 THEN {} ELSE got) ELSE base
                     /\ comp' = (y.out >= 0 => got = {p \in 0..(total - 1) : TRUE})
                     /\ keeps' = (keeps /\ (y.out < 0 => \A p \in Cover(r.runs) : p \in Cover(r'.runs) /\ vs'[p] = vs[p]))

Next == Frag
Spec == Init /\ [][Next]_vars
Bound == k <= KMAX

Shape == /\ Len(r.runs) <= NR
         /\ \A i \in DOMAIN r.runs : r.runs[i][1] < r.runs[i][2] /\ r.runs[i][2] <= r.total
         /\ \A i \in 1..(Len(r.runs) - 1) : r.runs[i][2] < r.runs[i + 1][1]
Exact == Cover(r.runs) = acc
NoFalseComplete == comp
Total == r.total <= MX
Agrees == keeps
Inv == Shape /\ Exact /\ NoFalseComplete /\ Total /\ Agrees
=============================================================================
