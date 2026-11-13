----------------------------- MODULE TraceQueue -----------------------------
(***************************************************************************)
(* Trace validation of the endpoint's event queue: vinc-core queue.rs.     *)
(*                                                                         *)
(* The Rust test tests/trace_queue.rs drives real rings (built with the    *)
(* cargo feature `trace`) with seeded calls: pushes of recoverable and     *)
(* unrecoverable events for a few sessions and for none, a session's       *)
(* Closed, pops, purges of a session, and bursts of at most the headroom   *)
(* of unrecoverable events from a ring that is not stalled, in mixes that  *)
(* keep the ring short, fill it, push on into the full ring (drops and     *)
(* evictions of the oldest recoverable event, deep in the queue too, and   *)
(* of the oldest event when none is recoverable) and take the head round   *)
(* it. Every call must be the step the operators of QueueOps.tla compute,  *)
(* with the result the code returned; the head, length, recoverable count, *)
(* counters and stall flag recorded must be the model's, and so must the   *)
(* queued events whenever the record carries them (at most 24 queued, and  *)
(* then every 307th call and the end of the run).                          *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds queue.ndjson.         *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLES i, r, cap, h
vars == <<i, r, cap, h>>
INSTANCE QueueOps

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/queue.ndjson")
Ev0 == Trace[i]

Same(x, v, c, hh) ==
    /\ x.head = v.head /\ x.len = v.len /\ x.ll = v.ll /\ x.dropped = v.dropped /\ x.lost = v.lost
    /\ Stalled(x, c, hh) = v.stalled
    /\ v.full => Window(x, c) = v.q

RECURSIVE PushAll(_, _, _)
PushAll(x, c, evs) == IF evs = <<>> THEN x ELSE PushAll(Push(x, c, Head(evs), FALSE), c, Tail(evs))
RECURSIVE UnrecIn(_)
UnrecIn(evs) == IF evs = <<>> THEN 0 ELSE (IF Head(evs)[2] THEN 0 ELSE 1) + UnrecIn(Tail(evs))

InitEv == /\ Ev0.op = "init" /\ cap' = Ev0.cap /\ h' = Ev0.h /\ r' = Ring0(Ev0.cap)
          /\ Same(r', Ev0.v, Ev0.cap, Ev0.h)
PushEv == /\ Ev0.op = "push" /\ r' = Push(r, cap, Ev0.ev, FALSE) /\ Same(r', Ev0.v, cap, h)
          /\ UNCHANGED <<cap, h>>
\* a burst from a ring that is not stalled, of at most h unrecoverable events, loses none
BurstEv == /\ Ev0.op = "burst"
           /\ ~Stalled(r, cap, h) /\ UnrecIn(Ev0.evs) <= h
           /\ r' = PushAll(r, cap, Ev0.evs) /\ r'.lost = r.lost /\ Same(r', Ev0.v, cap, h)
           /\ UNCHANGED <<cap, h>>
PopEv == LET x == Pop(r, cap)
         IN /\ Ev0.op = "pop" /\ x.out = Ev0.out /\ r' = x.r /\ Same(r', Ev0.v, cap, h)
            /\ UNCHANGED <<cap, h>>
PurgeEv == /\ Ev0.op = "purge" /\ r' = Purge(r, cap, Ev0.s) /\ Same(r', Ev0.v, cap, h)
           /\ UNCHANGED <<cap, h>>
EndEv == /\ Ev0.op = "end" /\ r' = r /\ Same(r', Ev0.v, cap, h) /\ UNCHANGED <<cap, h>>

Init == i = 1 /\ r = Ring0(1) /\ cap = 1 /\ h = 0
Step == /\ i <= Len(Trace) /\ Ev0.t = "coq"
        /\ (InitEv \/ PushEv \/ BurstEv \/ PopEv \/ PurgeEv \/ EndEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the ring never grows, the counters are consistent
Inv == /\ r.len \in 0..cap /\ r.ll <= r.len /\ r.lost <= r.dropped
=============================================================================
