-------------------------- MODULE TraceFacadeEvents --------------------------
(***************************************************************************)
(* Trace validation of the facade's topic event queue: crates/pinc/src/    *)
(* engine/topics.rs `push_event` (through `on_node_event` of a             *)
(* `NodeEvent::Message`), `on_node_event` of `NodeEvent::Lost`,            *)
(* `poll_event`, and a stop (`Core::stopped` set), against the operators   *)
(* of FacadeEventsOps.tla at the real bounds (EVENTS = 1024, the count a   *)
(* u32 saturating at 2^32 - 1).                                            *)
(*                                                                         *)
(* The unit test `engine::event_tests::trace_events` (both builds of the   *)
(* crate `pinc`, file facade_events.ndjson) drives real cores from         *)
(* `adjacent_tests::core()`. A message's payload is its id (a u32, big     *)
(* endian), so a polled event names the push it came from. An event       *)
(* records the call, its answer and the queue after it: its length, first *)
(* and last id, the count as two 16-bit limbs, and every 50th event the    *)
(* whole queue. Every call must be the model's step and every recorded     *)
(* field the model's state; an "init" event starts a new core.             *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds facade_events.ndjson. *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd
VARIABLES i, s
vars == <<i, s>>

O == INSTANCE FacadeEventsOps WITH CAP <- 1024, TOPW <- <<65535, 65535, 0, 0, 0>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/facade_events.ndjson")
Ev0 == Trace[i]

\* a u32 from two 16-bit limbs
W2(l) == <<l[1], l[2], 0, 0, 0>>

\* the recorded queue is the model's
Same(y, v) ==
    /\ Len(y.q) = v.qn
    /\ v.first = (IF y.q = <<>> THEN 0 ELSE Head(y.q))
    /\ v.last = (IF y.q = <<>> THEN 0 ELSE y.q[Len(y.q)])
    /\ y.lost = W2(v.lost)
    /\ y.stopped = v.stopped
    /\ "q" \in DOMAIN v => y.q = v.q

InitEv == /\ Ev0.op = "init" /\ s' = O!Empty
PushEv == /\ Ev0.op = "push" /\ s' = O!Enq(s, Ev0.id)
NodeLostEv == /\ Ev0.op = "nodelost" /\ s' = O!NodeLost(s, W2(Ev0.c))
PollEv == LET p == O!PollOf(s)
          IN /\ Ev0.op = "poll"
             /\ Ev0.r = p.r /\ W2(Ev0.n) = p.n /\ Ev0.e = p.e
             /\ s' = p.s
StopEv == /\ Ev0.op = "stop" /\ s' = O!Stop(s)

Init == i = 1 /\ s = O!Empty
Step == /\ i <= Len(Trace) /\ Ev0.t = "events"
        /\ (InitEv \/ PushEv \/ NodeLostEv \/ PollEv \/ StopEv)
        /\ Same(s', Ev0)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* along the trace: at most EVENTS queued, in the order pushed
Inv == /\ Len(s.q) <= 1024
       /\ \A k \in 2..Len(s.q) : s.q[k] > s.q[k - 1]
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
