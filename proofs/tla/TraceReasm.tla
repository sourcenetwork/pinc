----------------------------- MODULE TraceReasm ------------------------------
(***************************************************************************)
(* Trace validation of the handshake fragment reassembly: pinc-transport   *)
(* conn/reasm.rs.                                                          *)
(*                                                                         *)
(* The Rust test tests/trace_reasm.rs drives real reassemblies (built with *)
(* the cargo feature `trace`) with seeded fragments: in order, reversed,   *)
(* shuffled, repeated, overlapping, cut off at the end of the message, with *)
(* a message of another length in between, past the largest message, and   *)
(* enough disjoint runs to fill the table. Every call must be the step the *)
(* operators of ReasmOps.tla compute, with the result the code returned,   *)
(* and the runs recorded must be the model's.                              *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds reasm.ndjson.         *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd
VARIABLES i, r, mx, nr
vars == <<i, r, mx, nr>>
INSTANCE ReasmOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/reasm.ndjson")
Ev0 == Trace[i]
RunsOf(l) == [k \in 1..Len(l) |-> <<l[k][1], l[k][2]>>]
Same(y, v) == y.runs = RunsOf(v.runs) /\ y.total = v.total

InitEv == /\ Ev0.op = "init" /\ mx' = Ev0.max /\ nr' = Ev0.nr /\ r' = Reasm0 /\ Same(r', Ev0.v)
AddEv == LET x == Add(r, mx, nr, Ev0.total, Ev0.off, Ev0.len)
         IN /\ Ev0.op = "add" /\ x.out = Ev0.out /\ r' = x.r /\ Same(r', Ev0.v) /\ UNCHANGED <<mx, nr>>

Init == i = 1 /\ r = Reasm0 /\ mx = 0 /\ nr = 0
Step == /\ i <= Len(Trace) /\ Ev0.t = "txrs" /\ (InitEv \/ AddEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == Len(r.runs) <= nr \/ nr = 0
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
