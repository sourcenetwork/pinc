---------------------------- MODULE TraceEvQueue ----------------------------
(***************************************************************************)
(* Trace validation of the connection's event queue: pinc-transport        *)
(* conn/event.rs (EvQueue over Lazy, with `alloc`: 640 places).            *)
(*                                                                         *)
(* The Rust test tests/trace_evqueue.rs drives real queues through         *)
(* EvQueueProbe (cargo feature `trace`) with seeded pushes of every kind   *)
(* of event and pops: repeats of queued events, mixes that keep the queue  *)
(* short, a queue filled with unrecoverable events and pushed on (drops    *)
(* of recoverable notifications, losses), a queue filled with recoverable  *)
(* ones and then unrecoverable ones (each gives way the oldest recoverable *)
(* one, deep in the queue too), the head taken round the ring, and pops of *)
(* the last event (the head goes back to place 0). Every call must be the  *)
(* step the operators of EvQueueOps.tla compute, with the event `pop`      *)
(* returned; after every call the head, length, lost count and written     *)
(* prefix length must be the model's, and so must the queued events        *)
(* whenever the record carries them (at most 24 queued, every 101st call   *)
(* and the end of a run).                                                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds evqueue.ndjson.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLES i, q, cap
vars == <<i, q, cap>>
INSTANCE EvQueueOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/evqueue.ndjson")
Ev0 == Trace[i]

Same(x, c, v) == /\ x.head = v.head /\ x.len = v.len /\ x.lost = v.lost /\ Len(x.w) = v.wlen
                 /\ ("q" \in DOMAIN v => Window(x, c) = v.q)

InitEv == /\ Ev0.op = "init" /\ cap' = Ev0.cap /\ q' = Q0 /\ Same(q', Ev0.cap, Ev0.v)
PushEv == /\ Ev0.op = "push" /\ q' = Push(q, cap, Ev0.ev) /\ UNCHANGED cap /\ Same(q', cap, Ev0.v)
PopEv == LET p == Pop(q, cap)
         IN /\ Ev0.op = "pop" /\ p.out = Ev0.out /\ q' = p.q /\ UNCHANGED cap /\ Same(q', cap, Ev0.v)

Init == i = 1 /\ q = Q0 /\ cap = 1
Step == /\ i <= Len(Trace) /\ Ev0.t = "evq" /\ (InitEv \/ PushEv \/ PopEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the queue never holds more than its places, and the written prefix never passes them
Inv == q.len <= cap /\ Len(q.w) <= cap
=============================================================================
