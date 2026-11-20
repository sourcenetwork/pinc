------------------------------ MODULE TraceReach ------------------------------
(***************************************************************************)
(* Trace validation of the ring of REACH_OUT bodies: pinc-core reach.rs    *)
(* (ReachRing).                                                            *)
(*                                                                         *)
(* The Rust test tests/trace_reach.rs drives real rings (built with the    *)
(* cargo feature `trace`) with seeded calls: puts of bodies for more       *)
(* sessions than the ring has places, with lengths of every kind that      *)
(* matters (empty, the limit of 153 bytes, one over it, far over it), and  *)
(* gets. Every call must be the step the operators of ReachOps.tla         *)
(* compute: the number of bodies a put returned as lost, the body a get    *)
(* returned (its length and first byte), and the four places (session,     *)
(* body length and first byte, or nothing) recorded after every call. The  *)
(* stamps and the put counter are not recorded: the replay carries them,   *)
(* from the empty ring at the start of each run, so which place a full     *)
(* ring gives up is checked through the places recorded. The model's body  *)
(* carries the first byte in the slot of its place in the order of puts.   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds reach.ndjson.         *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd
VARIABLES i, r, n, mx
vars == <<i, r, n, mx>>
INSTANCE ReachOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/reach.ndjson")
Ev0 == Trace[i]

\* a place as the test records it: [] for empty, else [session, length, first byte]
Rec(c) == IF c = None THEN <<>> ELSE <<c[1], c[2][2], c[2][1]>>

Same(x, m) == [k \in 1..m |-> Rec(x.cells[k - 1])] = Ev0.v.cells

InitEv == /\ Ev0.op = "init" /\ n' = Ev0.n /\ mx' = Ev0.mx /\ r' = Reach0(Ev0.n) /\ Same(r', Ev0.n)
PutEv == LET c == Ev0.c
             b == <<c[3], c[2]>>
         IN /\ Ev0.op = "put"
            /\ RLost(r, n, mx, c[1], b, FALSE, FALSE) = Ev0.lost
            /\ r' = RPut(r, n, mx, c[1], b, FALSE, FALSE)
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

\* the ring never grows, holds no body over the limit, no session twice, and no stamp past its counter
Inv == /\ DOMAIN r.cells = 0..n - 1
       /\ \A k \in Occ(r.cells, n) : r.cells[k][2][2] <= mx /\ r.cells[k][3] <= r.clock
       /\ \A k, l \in Occ(r.cells, n) : r.cells[k][1] = r.cells[l][1] => k = l
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
