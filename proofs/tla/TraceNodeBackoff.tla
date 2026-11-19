---------------------------- MODULE TraceNodeBackoff ---------------------------
(***************************************************************************)
(* Trace validation of the node's table of failed dials: pinc-node io.rs   *)
(* (`backoff`, `deny_back`, `set_failed`) and the window check of the      *)
(* frame hand-off.                                                         *)
(*                                                                         *)
(* The Rust test tests/trace_node_backoff.rs drives real tables (a node's  *)
(* `Io` over an endpoint that does nothing, built with the cargo feature   *)
(* `trace`) with seeded calls: failed dials and refusals of hubs and of    *)
(* other nodes, and the guard of a frame for a peer with no session, at    *)
(* times that step forward, stand still, step back, land on the edge of an *)
(* entry's window and sit at the top of the u64 range; one run fills the   *)
(* table (4096 entries) and goes on. Every call must be the step the       *)
(* operators of NodeBackoffOps.tla compute, with the entry of the peer and *)
(* the size of the table the code recorded; a dump of the whole table must *)
(* be the model's. Times and waits are four 16-bit limbs.                  *)
(*                                                                         *)
(* One run drives a real node instead (`Node` over a scripted endpoint)    *)
(* whose session table is full: each dial of a hub comes up and the table  *)
(* sheds the session (events.rs `hub_connected`), which is `Backoff`. The  *)
(* node's table is not readable, so the record of a shed has no entry; the *)
(* duty passes that follow (duties.rs `duties`: `dial_peer` of each hub,   *)
(* then the prune) record whether the node dialed the hub, which must be   *)
(* exactly outside the window the model's entry makes.                     *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds nobo.ndjson.          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, Nanos
CONSTANT MAXT
VARIABLES i, F, hubs
vars == <<i, F, hubs>>
INSTANCE NodeBackoffOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/nobo.ndjson")
Ev0 == Trace[i]
L(x) == U!FromLimbs(x)
\* the recorded entry of the peer: [] for none, else [until, wait]
Rec(p, e) == IF e = <<>> THEN F'[p] = None ELSE F'[p] = <<L(e[1]), L(e[2])>>

InitEv == /\ Ev0.op = "init" /\ Ev0.max = MAXT
          /\ L(Ev0.first) = FIRST /\ L(Ev0.hubcap) = HUBCAP /\ L(Ev0.cap) = CAP
          /\ L(Ev0.dfirst) = DFIRST /\ L(Ev0.dcap) = DCAP
          /\ F' = Tab0(1..Ev0.peers) /\ hubs' = {Ev0.hubs[k] : k \in DOMAIN Ev0.hubs}
BackoffEv == LET x == Backoff(F, L(Ev0.now), Ev0.peer, Ev0.peer \in hubs)
             IN /\ Ev0.op = "backoff" /\ F' = x.f /\ Rec(Ev0.peer, Ev0.e) /\ Size(F') = Ev0.len
                /\ UNCHANGED hubs
DenyEv == LET x == DenyBack(F, L(Ev0.now), Ev0.peer)
          IN /\ Ev0.op = "deny" /\ F' = x.f /\ Rec(Ev0.peer, Ev0.e) /\ Size(F') = Ev0.len /\ UNCHANGED hubs
\* the frame hand-off takes a frame for a peer with no session and nothing queued exactly outside the window
GateEv == /\ Ev0.op = "gate" /\ (~Window(F, L(Ev0.now), Ev0.peer)) = Ev0.ok
          /\ F' = F /\ Rec(Ev0.peer, Ev0.e) /\ Size(F) = Ev0.len /\ UNCHANGED hubs
\* our dial of the peer came up and the full session table shed the session: a failed dial
ShedEv == /\ Ev0.op = "shed" /\ F' = Backoff(F, L(Ev0.now), Ev0.peer, Ev0.peer \in hubs).f /\ UNCHANGED hubs
\* a duty pass of the node; the peer has no session, no dial in progress and is not revoked, so the node dials it
\* exactly outside its window; the pass ends with the prune
DutyEv == /\ Ev0.op = "duty" /\ (~Window(F, L(Ev0.now), Ev0.peer)) = Ev0.dialed
          /\ F' = Prune(F, L(Ev0.now)) /\ UNCHANGED hubs
DumpEv == /\ Ev0.op = "dump" /\ F' = F /\ UNCHANGED hubs
          /\ Used(F) = {Ev0.entries[k][1] : k \in DOMAIN Ev0.entries}
          /\ \A k \in DOMAIN Ev0.entries :
                F[Ev0.entries[k][1]] = <<L(Ev0.entries[k][2]), L(Ev0.entries[k][3])>>

Init == i = 1 /\ F = Tab0(1..1) /\ hubs = {}
Step == /\ i <= Len(Trace) /\ Ev0.t = "nobo"
        /\ (InitEv \/ BackoffEv \/ DenyEv \/ GateEv \/ ShedEv \/ DutyEv \/ DumpEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the table never grows past its bound, and every wait is within its bounds
Inv == /\ Size(F) <= MAXT
       /\ \A p \in Used(F) : Le(Sec(2), F[p][2]) /\ Le(F[p][2], Sec(900)) /\ Le(F[p][2], F[p][1])
=============================================================================
