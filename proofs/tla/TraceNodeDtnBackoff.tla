------------------------- MODULE TraceNodeDtnBackoff -------------------------
(***************************************************************************)
(* Trace validation of the backoff of the node's delay-tolerant dials:     *)
(* pinc-node io.rs `lfailed` and dtn.rs `redial_at`.                       *)
(*                                                                         *)
(* The Rust test tests/trace_node_dtn_backoff.rs drives a real table (a    *)
(* node's `Io` over an endpoint that does nothing, through the probe       *)
(* `DtnBackoffProbe`, built with the cargo feature `trace`) with seeded    *)
(* calls: failed dials (`dtn_failed`, the table step of `layer_failed`),   *)
(* the window check of `dial_layer` (`dtn_waits`), the removal of an entry *)
(* (`dtn_forget`), and the redial time of the delay-tolerant layer         *)
(* (`sooner` after each failure, `redial_due` at each timer), at times     *)
(* that step forward, stand still, land on the edge of an entry's window   *)
(* and sit at the top of the u64 range; one run fills the table (4096      *)
(* entries) and goes on. Every call must be the step of DtnFailed, Sooner, *)
(* RedialDue, Window and Forget of NodeDtnBackoffOps.tla, with the entry   *)
(* of the peer, the size of the table and the redial time the code         *)
(* recorded; a dump of the whole table must be the model's. Times and      *)
(* waits are four 16-bit limbs; an absent time or entry is [].             *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds dtn_backoff.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, Nanos
CONSTANT MAXT
VARIABLES i, F, redial
vars == <<i, F, redial>>
INSTANCE NodeDtnBackoffOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dtn_backoff.ndjson")
Ev0 == Trace[i]
L(x) == U!FromLimbs(x)
O(x) == IF x = <<>> THEN None ELSE <<L(x)>>
\* the recorded entry of the peer: [] for none, else [until, wait]
Rec(p, e) == IF e = <<>> THEN F'[p] = None ELSE F'[p] = <<L(e[1]), L(e[2])>>

InitEv == /\ Ev0.op = "init" /\ Ev0.max = MAXT /\ L(Ev0.first) = FIRST /\ L(Ev0.cap) = CAP
          /\ F' = Tab0(1..Ev0.peers) /\ redial' = None
FailEv == LET x == DtnFailed(F, L(Ev0.now), Ev0.peer)
          IN /\ Ev0.op = "fail" /\ F' = x.f /\ L(Ev0.at) = x.at /\ Rec(Ev0.peer, Ev0.e) /\ Size(F') = Ev0.len
             /\ redial' = Sooner(redial, x.at) /\ O(Ev0.redial) = redial'
WaitsEv == /\ Ev0.op = "waits" /\ Window(F, L(Ev0.now), Ev0.peer) = Ev0.r
           /\ Rec(Ev0.peer, Ev0.e) /\ F' = F /\ redial' = redial
ForgetEv == /\ Ev0.op = "forget" /\ F' = Forget(F, Ev0.peer) /\ Size(F') = Ev0.len /\ redial' = redial
FireEv == /\ Ev0.op = "fire" /\ RedialDue(redial, L(Ev0.now)) = Ev0.r
          /\ redial' = IF Ev0.r THEN None ELSE redial /\ O(Ev0.redial) = redial'
          /\ F' = F
DumpEv == /\ Ev0.op = "dump" /\ F' = F /\ redial' = redial
          /\ Used(F) = {Ev0.entries[k][1] : k \in DOMAIN Ev0.entries}
          /\ \A k \in DOMAIN Ev0.entries :
                F[Ev0.entries[k][1]] = <<L(Ev0.entries[k][2]), L(Ev0.entries[k][3])>>

Init == i = 1 /\ F = Tab0(1..1) /\ redial = None
Step == /\ i <= Len(Trace) /\ Ev0.t = "dtnb"
        /\ (InitEv \/ FailEv \/ WaitsEv \/ ForgetEv \/ FireEv \/ DumpEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the table never grows past its bound, and every wait is within its bounds
Inv == /\ Size(F) <= MAXT
       /\ \A p \in Used(F) : Le(Sec(2), F[p][2]) /\ Le(F[p][2], Sec(60)) /\ Le(F[p][2], F[p][1])
=============================================================================
