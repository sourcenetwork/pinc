------------------------- MODULE TraceFacadeMachines -------------------------
(***************************************************************************)
(* Trace validation of the facade's rule for handshake machine pools:      *)
(* crates/pinc/src/node.rs `machines()` and `AnyEp::new` (which hands the  *)
(* pool to the endpoint with `share_machines`), FacadeMachines.tla's Home: *)
(* with `std` every endpoint of a thread takes the thread's pool, without  *)
(* it every endpoint has its own.                                          *)
(*                                                                         *)
(* The unit test `node::tests::trace_facade_machines` runs in both builds  *)
(* of the crate `pinc` (facade_machines_std.ndjson, facade_machines_nostd. *)
(* ndjson). On each of two threads it takes the thread's handle           *)
(* `machines()` first, then builds endpoints with `AnyEp::new` at several  *)
(* rungs of the ladder and reads each endpoint's pool through the probes   *)
(* `Endpoint::machines` (pinc-core) and `Machines::shares`                 *)
(* (pinc-transport). An event names the endpoint (ep, numbered from 1 in   *)
(* the file), its thread, the first endpoint of the file whose pool it     *)
(* shares (pool; itself when none), and whether it shares the handle taken *)
(* first on its thread (thr). The pool behind the rule (take, put,         *)
(* allocate, free) is TraceMachines'.                                      *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds both files.           *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd
VARIABLE i

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/facade_machines_std.ndjson")
         \o ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/facade_machines_nostd.ndjson")

\* the first endpoint of the same file and thread as event k (endpoints of a file are numbered 1, 2, ... in order)
FirstOf(k) == LET ev == Trace[k]
              IN CHOOSE m \in 1..k : /\ Trace[m].std = ev.std /\ Trace[m].thread = ev.thread
                                     /\ \A n \in 1..(m - 1) : ~(Trace[n].std = ev.std /\ Trace[n].thread = ev.thread)

\* FacadeMachines' Home: the thread's one pool with std, the endpoint's own without
EvOK(k) ==
    LET ev == Trace[k]
    IN /\ ev.t = "machines"
       /\ ev.has = TRUE
       /\ IF ev.std THEN ev.pool = Trace[FirstOf(k)].ep /\ ev.thr = TRUE
          ELSE ev.pool = ev.ep /\ ev.thr = FALSE

Init == i = 1
Step == i <= Len(Trace) /\ EvOK(i) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED i
TraceSpec == Init /\ [][Step \/ Finished]_i

\* the trace holds endpoints of both builds and, with std, two endpoints of a thread
Inv == i > Len(Trace) =>
    /\ \E k \in DOMAIN Trace : ~Trace[k].std
    /\ \E k, m \in DOMAIN Trace : k # m /\ Trace[k].std /\ Trace[m].std /\ Trace[k].thread = Trace[m].thread
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
