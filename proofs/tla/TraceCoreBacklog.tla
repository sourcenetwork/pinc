--------------------------- MODULE TraceCoreBacklog ---------------------------
(***************************************************************************)
(* Trace validation of the accept room (pinc#436): pinc-core rx.rs        *)
(* (`set_backlog_room`, the room check of a first flight, `session_taken`, *)
(* `Taken`), endpoint.rs (`free_slot`, `Endpoint::owed`) and slot.rs       *)
(* (`Meta::owed`), against the backlog part of HalfOpen.tla (QCAP > 0).    *)
(*                                                                         *)
(* HalfOpen.tla keeps the backlog in the variables ow (the sessions the    *)
(* endpoint owes the host), pend (those whose Incoming the host has yet to *)
(* read; OwedExact makes it ow), q (the host's queue) and the room QCAP -  *)
(* q, beside the half-open table; its actions are Arrive (a first flight   *)
(* makes an owed session only while Cardinality(ow) < QCAP - q, Open),     *)
(* the expiries and closes (EndOwed: an ended session is owed no more),    *)
(* Take (the host reads an owed session's Incoming: Reserved, it waits in  *)
(* the queue), SubUp (a session not owed: it waits only in a place no      *)
(* owed session holds) and Accept (the application takes one). HalfOpen    *)
(* cannot be instanced here (its state is the whole half-open table), so   *)
(* this module states those updates on the recorded state, each next to    *)
(* the action it is, and checks HalfOpen's backlog invariants OwedExact,   *)
(* Placed and NoBusy on every state.                                       *)
(*                                                                         *)
(* The Rust test tests/trace_core_backlog.rs runs a real hub endpoint that *)
(* members dial (sessions that finish, first flights that never finish,    *)
(* sessions that end before the host reads them) while the test plays the *)
(* host as the facade does (engine.rs on_event, sync_backlog; ops.rs       *)
(* accept_route): a queue of QCAP places, the room set to its free places  *)
(* at every change, `session_taken` for every Incoming, the application    *)
(* taking sessions at random. Events: "init" (QCAP); "call" after every    *)
(* step the pump hands the hub (the slots in use, the slots owed by the    *)
(* `trace` view, the endpoint's owed counter, the slots made and freed in  *)
(* the step, the first flights refused for want of room); "take" (the      *)
(* host read an Incoming: the slot, whether that session is still live,    *)
(* the answer, the place it got, the room set after); "accept".            *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds core_backlog.ndjson.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd

VARIABLES i, qcap, q, room, ow, live
vars == <<i, qcap, q, room, ow, live>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/core_backlog.ndjson")
Ev == Trace[i]

Set(s) == {s[j] : j \in 1..Len(s)}

Init == /\ i = 1 /\ qcap = 0 /\ q = 0 /\ room = 0 /\ ow = {} /\ live = {}

\* A hub starts: an empty queue, the room the whole queue.
Start == /\ Ev.t = "init"
         /\ Ev.qcap > 0
         /\ qcap' = Ev.qcap /\ q' = 0 /\ room' = Ev.qcap /\ ow' = {} /\ live' = {}
         /\ i' = i + 1

\* One step of the endpoint (a datagram, a timer, a command). EndOwed: a freed slot is owed no more. Arrive: a
\* session a first flight made is owed from its creation, and is made only while the owed sessions are below the room
\* (Open); a first flight refused for want of room comes with the owed sessions at the room. Nothing else changes
\* what is owed. One step may free and make several slots in an order the record does not keep, so each check is the
\* weakest the code's rule implies in every order: when the last session was made the owed ones were at least the
\* ones that stayed plus the ones made, and below the room; when a flight was refused they were at most the ones
\* owed before plus the ones made, and at the room.
Call == /\ Ev.t = "call"
        /\ LET L1 == Set(Ev.live)
               O1 == Set(Ev.ow)
               made == Set(Ev.made)
               freed == Set(Ev.freed)
           IN /\ made \subseteq L1
              /\ freed \subseteq live
              /\ (freed \cap L1) \subseteq made
              /\ O1 = (ow \ freed) \cup made
              /\ (made # {} => Cardinality(O1) <= room)
              /\ (Ev.refused > 0 => Cardinality(ow \cup made) >= room)
              /\ Ev.owed = Cardinality(O1)
              /\ ow' = O1 /\ live' = L1
        /\ UNCHANGED <<qcap, q, room>>
        /\ i' = i + 1

\* The host reads the Incoming of the session in slot s. session_taken answers Gone for a session that ended, Reserved
\* for an owed one (Take: it is owed no more and waits in the queue, which always has a place for it: NoBusy) and
\* Unreserved with the owed count for one that is not owed (SubUp: it waits only in a place no owed session holds).
\* The host then sets the room to the queue's free places.
Take == /\ Ev.t = "take"
        /\ LET s == Ev.slot IN
           CASE Ev.res = "gone" ->
                    /\ Ev.alive = 0 /\ Ev.placed = 0
                    /\ UNCHANGED <<ow, q>>
             [] Ev.res = "reserved" ->
                    /\ Ev.alive = 1 /\ s \in ow
                    /\ q < qcap /\ Ev.placed = 1
                    /\ ow' = ow \ {s} /\ q' = q + 1
             [] Ev.res = "unreserved" ->
                    /\ Ev.alive = 1 /\ s \in live /\ s \notin ow
                    /\ Ev.owed = Cardinality(ow)
                    /\ Ev.placed = (IF q + Cardinality(ow) < qcap THEN 1 ELSE 0)
                    /\ q' = q + Ev.placed
                    /\ UNCHANGED ow
        /\ room' = qcap - q' /\ Ev.room = room'
        /\ UNCHANGED <<qcap, live>>
        /\ i' = i + 1

\* Accept: the application takes the oldest waiting session; the host sets the room again.
Accept == /\ Ev.t = "accept"
          /\ q > 0 /\ q' = q - 1
          /\ room' = qcap - q' /\ Ev.room = room'
          /\ UNCHANGED <<qcap, ow, live>>
          /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (Start \/ Call \/ Take \/ Accept)) \/ Done
TraceSpec == Init /\ [][TNext]_vars

\* HalfOpen's OwedExact (the owed sessions are live) and Placed (waiting plus owed never pass the queue); NoBusy is
\* the q < qcap of every Reserved take, a step condition above.
Inv == /\ ow \subseteq live
       /\ q + Cardinality(ow) <= qcap \/ qcap = 0
       /\ room = qcap - q
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
