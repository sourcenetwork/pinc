------------------------- MODULE TraceConnectNodeId -------------------------
(***************************************************************************)
(* Trace validation of the wire form of a node id: pinc-connect            *)
(* carrier/node.rs.                                                        *)
(*                                                                         *)
(* The Rust test tests/trace_connect_node.rs runs the real `node::read`    *)
(* and `node::write` on every tag byte 0..255 with fixed and random        *)
(* bodies, every cut of 0 to 33 bytes, bytes after the id, readers that    *)
(* already consumed a prefix, and writers with every room from 0 to 40     *)
(* bytes, and records one event per call: the input, the result (the tag   *)
(* and the 32 bytes, or the error with its shortfall), and how far the     *)
(* reader advanced or what the writer wrote. Each event must equal the     *)
(* NodeRead or NodeWrite operator of ConnectNodeIdOps.tla, whose           *)
(* properties ConnectNodeId.cfg checks.                                    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds connect_node.ndjson.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, ConnectNodeIdOps

VARIABLE c

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_node.ndjson")

Init == c = [t |-> "root"]

RdEv(ev) ==
    LET r == NodeRead(ev.in)
    IN /\ r.kind = ev.kind
       /\ r.used = ev.used
       /\ ev.kind = "ok" => (r.alg = ev.alg /\ r.bytes = ev.bytes)
       /\ ev.kind = "trunc" => r.needed = ev.needed

WrEv(ev) ==
    LET w == NodeWrite(ev.alg, ev.bytes, ev.room)
    IN /\ w.kind = ev.kind
       /\ w.out = ev.out
       /\ ev.kind = "small" => w.needed = ev.needed

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

(* every recorded event equals the specification *)
EventsOK == c.t = "event" => IF Trace[c.i].t = "nrd" THEN RdEv(Trace[c.i]) ELSE /\ Trace[c.i].t = "nwr"
                                                                             /\ WrEv(Trace[c.i])
=============================================================================
