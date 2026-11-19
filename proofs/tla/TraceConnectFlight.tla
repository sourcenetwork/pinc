------------------------- MODULE TraceConnectFlight -------------------------
(***************************************************************************)
(* Trace validation of the candidate paths of a flight: pinc-connect       *)
(* client/flight.rs, Connectivity::candidates_for.                         *)
(*                                                                         *)
(* The Rust test tests/trace_connect_flight.rs builds a real Connectivity  *)
(* with three relays, takes it from no home relay to one, gives it local   *)
(* beacons and found records (fresh and stale, homed on a relay it knows   *)
(* and on one it does not) through its public API, and calls the probe     *)
(* Connectivity::trace_candidates (cargo feature `trace`) for peers with   *)
(* and without them, with hint lists from none to 20 addresses that repeat *)
(* each other and the beacon's and the record's, fresh_at none, at the    *)
(* record's last fresh moment and past it, and fwd either way. The probe   *)
(* returns the list candidates_for built and the tables it read; each      *)
(* event is one call: the inputs (`v`, the fields of ConnectFlightOps.tla) *)
(* and the list (`out`), addresses as their text. Each list must equal     *)
(* CandidatesFor of the inputs, whose properties ConnectFlight.cfg checks. *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds connect_flight.ndjson.*)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, ConnectFlightOps

VARIABLE c

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_flight.ndjson")

Init == c = [t |-> "root"]

(* Every event is an independent call, so the events are the states of one machine: the root state has one successor
   per block of 32 events and a block one per event. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

(* every recorded list is the specification's *)
EventsOK == c.t = "event" => (Trace[c.i].t = "fl" /\ CandidatesFor(Trace[c.i].v) = Trace[c.i].out)
=============================================================================
