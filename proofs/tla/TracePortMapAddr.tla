--------------------------- MODULE TracePortMapAddr ---------------------------
(***************************************************************************)
(* Trace validation of pinc-portmap addr.rs.                               *)
(*                                                                         *)
(* The Rust test tests/trace_portmap_addr.rs runs the real `is_shared`,    *)
(* `is_private`, `usable_host` and `external_ok` on the boundary sets of   *)
(* PortMapAddr.tla (every IPv4 address of O1 x O2 x O3 x O4, each also as  *)
(* an IPv4-mapped IPv6 address, the IPv6 first segments with every tail)   *)
(* and on seeded random addresses, and records one event per address: the *)
(* address and what each function returned (the IPv4 functions only for   *)
(* an IPv4 address). Each answer must equal the documented prefix rule of  *)
(* PortMapAddr.tla (RuleShared, RulePrivate, RuleHost, RuleExternal) and   *)
(* the model of the code (IsShared, IsPrivate, UsableHost, ExternalOk).    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds portmap/addr.ndjson.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

A == INSTANCE PortMapAddr WITH c <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/portmap/addr.ndjson")

Init == c = [t |-> "root"]

AddrOf(ev) == IF ev.v = 4 THEN A!V4(ev.o) ELSE A!V6(ev.s)

AddrEv(ev) ==
    LET a == AddrOf(ev)
    IN /\ ev.ex = A!RuleExternal(a) /\ ev.ex = A!ExternalOk(a)
       /\ ev.v = 4 =>
            /\ ev.sh = A!RuleShared(ev.o) /\ ev.sh = A!IsShared(ev.o)
            /\ ev.pr = A!RulePrivate(ev.o) /\ ev.pr = A!IsPrivate(ev.o)
            /\ ev.uh = A!RuleHost(ev.o) /\ ev.uh = A!UsableHost(ev.o)

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK == c.t = "event" => AddrEv(Trace[c.i])
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
