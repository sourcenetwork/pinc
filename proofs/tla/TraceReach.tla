------------------------------ MODULE TraceReach ------------------------------
(***************************************************************************)
(* Trace validation of the ring of REACH_OUT bodies: vinc-core reach.rs    *)
(* (ReachRing).                                                            *)
(*                                                                         *)
(* The Rust test tests/trace_reach.rs drives real rings (built with the    *)
(* cargo feature `trace`) with seeded calls: puts of bodies for more       *)
(* sessions than the ring has places, with lengths of every kind that      *)
(* matters (empty, the limit of 153 bytes, one over it, far over it), and  *)
(* gets. Every call must be the step the operators of ReachOps.tla         *)
(* compute, with the body the get returned (its length and first byte);    *)
(* the pointer `next` and the four places (session, body length and first  *)
(* byte, or nothing) recorded after every call must be the model's. The    *)
(* model's body carries the first byte in the slot of its place in the     *)
(* order of puts.                                                          *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds reach.ndjson.         *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLES i, r, n, mx
vars == <<i, r, n, mx>>
INSTANCE ReachOps

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/reach.ndjson")
Ev0 == Trace[i]

\* a place as the test records it: [] for empty, else [session, length, first byte]
Rec(c) == IF c = None THEN <<>> ELSE <<c[1], c[2][2], c[2][1]>>

Same(x, m) ==
    /\ x.next = Ev0.v.next
    /\ [k \in 1..m |-> Rec(x.cells[k - 1])] = Ev0.v.cells

InitEv == /\ Ev0.op = "init" /\ n' = Ev0.n /\ mx' = Ev0.mx /\ r' = Reach0(Ev0.n) /\ Same(r', Ev0.n)
PutEv == LET c == Ev0.c
         IN /\ Ev0.op = "put"
            /\ r' = RPut(r, n, mx, c[1], <<c[3], c[2]>>, FALSE, FALSE)
            /\ Same(r', n) /\ UNCHANGED <<n, mx>>
GetEv == LET b == RGet(r, n, Ev0.s)
         IN /\ Ev0.op = "get"
            /\ (IF b = None THEN <<>> ELSE <<b[2], b[1]>>) = Ev0.out
            /\ r' = r /\ Same(r', n) /\ UNCHANGED <<n, mx>>

Init == i = 1 /\ r = Reach0(1) /\ n = 1 /\ mx = 0
Step == /\ i <= Len(Trace) /\ Ev0.t = "cor"
        /\ (InitEv \/ PutEv \/ GetEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the ring never grows, holds no body over the limit, and no session twice
Inv == /\ r.next \in 0..n - 1
       /\ \A k \in Occ(r.cells, n) : r.cells[k][2][2] <= mx
       /\ \A k, l \in Occ(r.cells, n) : r.cells[k][1] = r.cells[l][1] => k = l
=============================================================================
