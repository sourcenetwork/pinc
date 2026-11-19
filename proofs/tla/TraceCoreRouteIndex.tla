------------------------- MODULE TraceCoreRouteIndex -------------------------
(***************************************************************************)
(* Trace validation of the endpoint's table of sessions by address         *)
(* (pinc-core endpoint.rs by_route, sync_route, free_slot, session_from;   *)
(* Meta::route) against CoreRouteIndex.tla.                                *)
(*                                                                         *)
(* The Rust test tests/trace_core_route_index.rs runs a hub through dials  *)
(* (one member twice from one address), a member that changes its         *)
(* address, a NAT in front of a member that rebinds, sessions that close   *)
(* and slots taken again, and seeded runs of the same steps. After every   *)
(* step the pump hands any node (a datagram, a timer, a command: between   *)
(* the hub's calls, so no settle is pending) it records the hub's table as *)
(* the `trace` feature shows it: for each of the 8 slots whether it holds  *)
(* a session, the address of its validated direct path (None when there    *)
(* is none) and the address its entry is under (Meta::route), the table's  *)
(* entries oldest first, and for every address the slots session_from     *)
(* answers with (each found slot excluded in turn until none is left).     *)
(* Addresses are numbered by the test from 1 in the order it first sees    *)
(* them; 0 is None.                                                        *)
(*                                                                         *)
(* Each event is one state of the model between calls (pending empty): it *)
(* must satisfy TypeOK, Agree and Exact, and the answers of session_from   *)
(* must be the model's Lookup, which Agree makes the Walk.                 *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds                       *)
(* core_route_index.ndjson.                                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLE c

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/core_route_index.ndjson")

\* The hub's slots (the harness's K = 8) and the addresses the test may number (it asserts it saw at most 16).
NSlots == 8
NAddrs == 16

Ev == Trace[c.i]
\* The event's arrays are lists indexed from 1 for slot 0; the model's functions are on 0..7.
Live == [s \in 0..(NSlots - 1) |-> Ev.live[s + 1] = 1]
Cur == [s \in 0..(NSlots - 1) |-> Ev.cur[s + 1]]
Route == [s \in 0..(NSlots - 1) |-> Ev.route[s + 1]]
Idx == [j \in 1..Len(Ev.idx) |-> <<Ev.idx[j][1], Ev.idx[j][2]>>]

M == INSTANCE CoreRouteIndex WITH Slots <- 0..(NSlots - 1), Addrs <- 1..NAddrs, None <- 0, SYNC <- TRUE,
                                  FREE <- TRUE, VERIFY <- TRUE, REMOVE_OLD <- TRUE,
                                  live <- Live, cur <- Cur, route <- Route, idx <- Idx, pending <- {}

Init == c = [t |-> "root"]

\* What session_from answered at each address, as a set of slots.
Found(a) == {Ev.found[a][j] : j \in 1..Len(Ev.found[a])}

EvOK == /\ Ev.t = "route"
        /\ Len(Ev.live) = NSlots /\ Len(Ev.cur) = NSlots /\ Len(Ev.route) = NSlots /\ Len(Ev.found) = NAddrs
        /\ M!TypeOK /\ M!Agree /\ M!Exact
        /\ \A a \in 1..NAddrs : Found(a) = M!Lookup(a)

(* Every event is an independent state between calls, so the events are the states of one machine: the root state has
   one successor per block of 32 events and a block one per event. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

\* every recorded table is a state of the model between calls
EventsOK == c.t = "event" => EvOK
=============================================================================
