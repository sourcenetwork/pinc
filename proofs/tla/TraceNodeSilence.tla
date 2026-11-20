--------------------------- MODULE TraceNodeSilence ---------------------------
(***************************************************************************)
(* Trace validation of the silence bound of pinc-node bound.rs.            *)
(*                                                                         *)
(* The Rust test tests/trace_node_silence.rs calls the real `give_up` and  *)
(* `heal_after` on every boundary value NodeSilence.tla enumerates and on  *)
(* seeded random round trips and keepalives, and records one event per     *)
(* call: the arguments and the result. Each result must equal GiveUp or    *)
(* HealAfter of NodeSilenceOps.tla, whose properties TLC checks in         *)
(* NodeSilence.cfg. Times are four 16-bit limbs (TLC integers are 32 bits  *)
(* wide).                                                                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds silence.ndjson.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, Nanos, TraceEnd

VARIABLE c

INSTANCE NodeSilenceOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/silence.ndjson")
L(x) == U!FromLimbs(x)

Init == c = [t |-> "root"]

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK ==
    c.t = "event" =>
        LET ev == Trace[c.i]
        IN /\ ev.t = "sil"
           /\ IF ev.op = "give" THEN L(ev.r) = GiveUp(L(ev.srtt), ev.thin)
              ELSE ev.op = "heal" /\ L(ev.r) = HealAfter(L(ev.keep), L(ev.srtt), ev.thin)
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
