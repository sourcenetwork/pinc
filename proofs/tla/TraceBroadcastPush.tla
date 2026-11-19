--------------------------- MODULE TraceBroadcastPush ---------------------------
(***************************************************************************)
(* Trace validation of a hub pushing a topic over streams that fill up:    *)
(* pinc-broadcast msg.rs `hub_store`, behind.rs `fall_behind`,             *)
(* `room_to_store` and `peer_writable`, log.rs `HubLog::push`.             *)
(*                                                                         *)
(* The Rust test tests/trace_broadcast_push.rs drives one hub (built with  *)
(* the cargo feature `trace`, whose probes read the log's bounds and a     *)
(* subscriber's place) with subscribers 1 and 2 and a publisher. The test  *)
(* holds every frame between the hub and the others: a subscriber's stream *)
(* is a queue of StreamCap frames (the host's room), drained one frame at  *)
(* a time; a publish is handed to the hub when the test chooses, again    *)
(* after a refusal. The log holds LogCap messages (its bytes are set to    *)
(* LogCap messages of one size). Events: `store` (the hub stored message m *)
(* and acknowledged it), `refused` (it did not store m and sent no         *)
(* acknowledgement), `dup` (m again after it was stored), `drain` (one     *)
(* frame of subscriber s's stream delivered), `writable` (the host woke    *)
(* the hub for s after draining a full stream, and the hub sent n frames). *)
(* After each: the log's positions (top, base), each subscriber's place    *)
(* (behind, 0 for none) and the messages in each stream.                   *)
(*                                                                         *)
(* Each event must be the step of BroadcastPush.tla it names (Store,       *)
(* Store not enabled, a duplicate, Drain, n Writable steps), with the      *)
(* recorded log, places and streams, and the model's invariants hold on    *)
(* every state. Not driven here: a subscriber let go (the trace stays      *)
(* under PUSH_STALL_MS), a new session, an end of session and the GET of a *)
(* returning subscriber (Swap, End, Sub, Get); BroadcastPush_*.cfg check   *)
(* those.                                                                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds bcast/push.ndjson.                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

CONSTANTS Subs, N, LogCap, StreamCap, Swaps, Cursor, Guard, Tell, Resume, Ends, Owe, Notice

VARIABLES i, j, msgAt, base, acked, stream, got, behind, held, missed, told, wake, subq, swaps, ask, ends, gone, left
mvars == <<msgAt, base, acked, stream, got, behind, held, missed, told, wake, subq, swaps, ask, ends, gone, left>>
vars == <<i, j, mvars>>

M == INSTANCE BroadcastPush

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/bcast/push.ndjson")
Ev == Trace[i]

\* the recorded log, places and streams are the model's after the step
Proj == /\ Len(msgAt') = Ev.top /\ base' = Ev.base
        /\ \A s \in Subs : behind'[s] = Ev.behind[s] /\ stream'[s] = Ev.stream[s]
Next1 == i' = i + 1 /\ j' = 0

StoreEv == /\ Ev.op = "store" /\ Ev.pack /\ M!Store(Ev.m) /\ Proj /\ Next1
RefusedEv == /\ Ev.op = "refused" /\ ~Ev.pack /\ Ev.m \notin acked /\ ~ENABLED M!Store(Ev.m)
             /\ UNCHANGED mvars /\ Proj /\ Next1
DupEv == /\ Ev.op = "dup" /\ Ev.m \in acked /\ UNCHANGED mvars /\ Proj /\ Next1
DrainEv == /\ Ev.op = "drain" /\ M!Drain(Ev.s) /\ Proj /\ Next1
\* peer_writable sends until the stream is full or the subscriber caught up: n Writable steps, one per frame
WritableEv == /\ Ev.op = "writable"
              /\ IF Ev.n = 0
                 THEN /\ ~ENABLED M!Writable(Ev.s) /\ UNCHANGED mvars /\ Proj /\ Next1
                 ELSE /\ M!Writable(Ev.s)
                      /\ IF j + 1 = Ev.n THEN Proj /\ Next1 ELSE i' = i /\ j' = j + 1

Init == i = 1 /\ j = 0 /\ M!Init
Step == /\ i <= Len(Trace) /\ Ev.t = "push"
        /\ (StoreEv \/ RefusedEv \/ DupEv \/ DrainEv \/ WritableEv)
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == /\ M!AckedReachesLive /\ M!MissedOnlyHeld /\ M!OwedInLog /\ M!Bounds /\ M!WakeOrPending
=============================================================================
