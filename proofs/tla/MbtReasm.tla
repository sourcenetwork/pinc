------------------------------ MODULE MbtReasm ------------------------------
(***************************************************************************)
(* Model-based tests of the handshake fragment reassembly (vinc-transport  *)
(* conn/reasm.rs, Reassembly::add): the state graph of the operators of    *)
(* ReasmOps.tla at the size of the real table, for a Rust test to walk.    *)
(*                                                                         *)
(* TLC enumerates every state reachable by the call below and writes the   *)
(* graph (-dump dot,actionlabels,constrained): a node is the reassembly    *)
(* (ReasmOps' r: the runs and the message length being assembled) and an   *)
(* edge is one call with what it returns, as the label TLC gives it:       *)
(*   CallAdd(total, off, len, out)   add of a fragment of len bytes at off *)
(*                                   of a message of total bytes; out is   *)
(*                                   the length of the message when it is  *)
(*                                   complete and -1 otherwise.            *)
(* The result is an argument so that the graph has one node per            *)
(* reassembly: TLC makes one action per value of every bounded \E of Next, *)
(* and only the calls whose result is the model's are enabled.             *)
(*                                                                         *)
(* tests/mbt_reasm.rs drives a real reassembly along each path, comparing  *)
(* the result and the whole state (runs, total) after every call, and the  *)
(* bytes of the buffer inside the runs against the fragments sent.         *)
(*                                                                         *)
(* The sizes are the code's: NR is its 8 runs and MX its largest message   *)
(* (MAX_MESSAGE_LEN); neither is a parameter of the code, so the table is  *)
(* filled with calls, not with a smaller table. The calls are a fixed set, *)
(* Calls: a message of T1 = 17 bytes (the least that holds 9 disjoint      *)
(* runs, so the table fills and a ninth is dropped) in one-byte fragments  *)
(* at each even offset, a fragment across all the gaps (1, 15), one for    *)
(* the whole message, overlapping ones (1, 2), (3, 1) and (5, 3), one     *)
(* that runs past the end and is cut (15, 4), an empty one and one past    *)
(* the end; a message of                                                   *)
(* T2 = 3 bytes and one of MX bytes (the other length that starts the      *)
(* count over, and the largest one, with a fragment at its last byte, cut  *)
(* at its end, and the whole of it); and the lengths that are refused, 0   *)
(* and MX + 1. The graph is every state those calls reach; a call repeated *)
(* is a duplicate.                                                         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS MX, NR, T1, T2
VARIABLES r
vars == <<r>>

INSTANCE ReasmOps

Init == r = Reasm0

Calls == {<<T1, o, 1>> : o \in {0, 2, 4, 6, 8, 10, 12, 14, 16}}
         \cup {<<T1, 0, 0>>, <<T1, 1, 2>>, <<T1, 1, 15>>, <<T1, 0, 17>>, <<T1, 15, 4>>, <<T1, 17, 1>>,
               <<T1, 3, 1>>, <<T1, 5, 3>>,
               <<T2, 0, 1>>, <<T2, 1, 1>>, <<T2, 2, 5>>, <<T2, 0, 3>>,
               <<MX, 0, 1>>, <<MX, MX - 1, 1>>, <<MX, MX - 1, 5>>, <<MX, 0, MX>>,
               <<0, 0, 1>>, <<MX + 1, 0, 1>>}
Totals == {0, T2, T1, MX, MX + 1}
Offs == (0..17) \cup {MX - 1}
Lens == {0, 1, 2, 3, 4, 5, 15, 17, MX}
Outs == {-1, T2, T1, MX}

CallAdd(total, off, len, out) ==
    /\ <<total, off, len>> \in Calls
    /\ LET x == Add(r, MX, NR, total, off, len) IN out = x.out /\ r' = x.r

Next == \E t \in Totals, o \in Offs, l \in Lens, out \in Outs : CallAdd(t, o, l, out)
Spec == Init /\ [][Next]_vars

\* every call of a state in the graph has its result in the set Next ranges over, so no call is lost; the runs
\* are the shape the code states
Complete ==
    /\ \A c \in Calls : c[1] \in Totals /\ c[2] \in Offs /\ c[3] \in Lens
                        /\ Add(r, MX, NR, c[1], c[2], c[3]).out \in Outs
    /\ Len(r.runs) <= NR
    /\ \A i \in DOMAIN r.runs : r.runs[i][1] < r.runs[i][2] /\ r.runs[i][2] <= r.total
    /\ \A i \in 1..(Len(r.runs) - 1) : r.runs[i][2] < r.runs[i + 1][1]
=============================================================================
