------------------------- MODULE TraceConnectMapped -------------------------
(***************************************************************************)
(* Trace validation of the port mappings the connectivity layer holds:     *)
(* pinc-connect client/mapped.rs.                                          *)
(*                                                                         *)
(* The Rust test tests/trace_connect_mapped.rs drives a real Connectivity  *)
(* with one relay (the rig of tests/connect_rig.rs, one local address)     *)
(* through its public API: set_mapped with 0 to 3 addresses (the same set  *)
(* again, a reorder, a repeat), address discovery rounds in which the      *)
(* relay reports the node at the mapping's IP, at another public IP, at a  *)
(* shared-range IP and at its local address, and link_changed, in seeded   *)
(* random orders and in fixed sequences. After every call it records the   *)
(* candidates the node offers and its class. Every event must be the step  *)
(* of ConnectMappedOps.tla (SetMapped, Answer, Restart) with the same      *)
(* candidates and class after it. All calls happen within the address      *)
(* discovery watchdog of the first probe or after UDP was heard, so the    *)
(* UdpBlocked branch is never taken (quiet is FALSE).                      *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds connect_mapped.ndjson.*)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, ConnectMappedOps

VARIABLES i, S
vars == <<i, S>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_mapped.ndjson")
Ev0 == Trace[i]

\* a recorded address {"ip": [a, b, c, d], "port": p}
Ad(o) == <<o.ip, o.port>>
Ads(s) == [k \in 1..Len(s) |-> Ad(s[k])]

NewEv == Ev0.op = "new" /\ S' = New(Ads(Ev0.local), Ev0.relays)
SetEv == Ev0.op = "set" /\ S' = SetMapped(S, Ads(Ev0.addrs), FALSE).s
ReportEv == Ev0.op = "report" /\ S' = Answer(S, Ev0.relay + 1, Ad(Ev0.a)).s
LinkEv == Ev0.op = "link" /\ S' = Restart(S).s

Init == i = 1 /\ S = New(<<>>, 1)
Step == /\ i <= Len(Trace)
        /\ Ev0.t = "map"
        /\ (NewEv \/ SetEv \/ ReportEv \/ LinkEv)
        /\ Cands(S') = Ads(Ev0.cands)
        /\ S'.cls = Ev0.cls
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the documented invariants hold on every recorded state
Inv == /\ S.cls = 2 => AnyLive(LiveOf(S, ReflList(S)))
       /\ S.live = LiveOf(S, ReflList(S))
=============================================================================
