------------------------- MODULE TraceNodeEventQueue -------------------------
(***************************************************************************)
(* Trace validation of the node's queue of application events, pinc-node  *)
(* io.rs `EventQueue`.                                                     *)
(*                                                                         *)
(* The Rust test tests/trace_node_event_queue.rs drives a real queue       *)
(* (through the probe `EventQueueProbe`, built with the cargo feature      *)
(* `trace`) with seeded runs: recoverable and unrecoverable endpoint       *)
(* events pushed one by one and in batches, reads, and the checks of the   *)
(* node loop, filling the queue to EVENT_CAP (8192) and past it, through   *)
(* the stop at EVENT_HIGH and the resume at EVENT_LOW. Every call must be  *)
(* the step of Push, Pop, CanTake, Resumable and IsEmpty of                *)
(* NodeEventQueueOps.tla, whose properties TLC checks in                   *)
(* NodeEventQueue.cfg, with the length and the lost count the code         *)
(* reports after it. A batch (extend) never crosses EVENT_CAP and a drain  *)
(* reads only events (no count pending): the test checks both, so a batch  *)
(* is the plain append and a drain the plain removal of the head.          *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds event_queue.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd
CONSTANTS CAP, HIGH, LOW, LMAX
VARIABLES i, s
vars == <<i, s>>
INSTANCE NodeEventQueueOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/event_queue.ndjson")
Ev0 == Trace[i]

Evs(ids, ls) == [j \in 1..Len(ids) |-> [id |-> ids[j], lossy |-> ls[j]]]
\* the length and the lost count the code reported after the call
After == Len(s'.q) = Ev0.len /\ s'.lost = Ev0.lost

InitEv == /\ Ev0.op = "init" /\ Ev0.cap = CAP /\ Ev0.high = HIGH /\ Ev0.low = LOW
          /\ s' = Q0 /\ Ev0.len = 0 /\ Ev0.lost = 0
PushEv == /\ Ev0.op = "push" /\ s' = Push(s, [id |-> Ev0.id, lossy |-> Ev0.lossy]) /\ After
ExtendEv == /\ Ev0.op = "extend" /\ Len(Ev0.ids) = Len(Ev0.lossy) /\ Len(s.q) + Len(Ev0.ids) <= CAP
            /\ s' = [s EXCEPT !.q = @ \o Evs(Ev0.ids, Ev0.lossy)] /\ After
PopEv == LET r == Pop(s)
         IN /\ Ev0.op = "pop" /\ s' = r.s /\ r.ev.k = Ev0.r /\ r.ev.count = Ev0.count
            /\ r.ev.e = [id |-> Ev0.id, lossy |-> Ev0.lossy] /\ After
DrainEv == /\ Ev0.op = "drain" /\ s.lost = 0 /\ Len(Ev0.ids) = Len(Ev0.lossy) /\ Len(Ev0.ids) <= Len(s.q)
           /\ SubSeq(s.q, 1, Len(Ev0.ids)) = Evs(Ev0.ids, Ev0.lossy)
           /\ s' = [s EXCEPT !.q = SubSeq(@, Len(Ev0.ids) + 1, Len(@))] /\ After
TakeEv == LET c == CanTake(s) IN /\ Ev0.op = "take" /\ c.ok = Ev0.ok /\ s' = c.s /\ After
ResumableEv == /\ Ev0.op = "resumable" /\ Resumable(s) = Ev0.r /\ s' = s /\ After
EmptyEv == /\ Ev0.op = "empty" /\ IsEmpty(s) = Ev0.r /\ s' = s /\ After

Init == i = 1 /\ s = Q0
Step == /\ i <= Len(Trace) /\ Ev0.t = "evq"
        /\ (InitEv \/ PushEv \/ ExtendEv \/ PopEv \/ DrainEv \/ TakeEv \/ ResumableEv \/ EmptyEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == Len(s.q) <= CAP /\ s.lost <= LMAX
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
