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
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, Nanos, TraceEnd
CONSTANT MAXT
VARIABLES i, F, redial, n
vars == <<i, F, redial, n>>
INSTANCE NodeDtnBackoffOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dtn_backoff.ndjson")
Ev0 == Trace[i]
L(x) == U!FromLimbs(x)
O(x) == IF x = <<>> THEN None ELSE <<L(x)>>
\* the recorded entry of the peer: [] for none, else [until, wait]
Rec(p, e) == IF e = <<>> THEN F'[p] = None ELSE F'[p] = <<L(e[1]), L(e[2])>>

InitEv == /\ Ev0.op = "init" /\ Ev0.max = MAXT /\ L(Ev0.first) = FIRST /\ L(Ev0.cap) = CAP
          /\ F' = Tab0(1..Ev0.peers) /\ redial' = None /\ n' = 0
FailEv == LET x == DtnFailedN(F, n, L(Ev0.now), Ev0.peer)
          IN /\ Ev0.op = "fail" /\ F' = x.f /\ L(Ev0.at) = x.at /\ Rec(Ev0.peer, Ev0.e)
             /\ n' = n + (IF F[Ev0.peer] = None /\ F'[Ev0.peer] # None THEN 1 ELSE 0) /\ n' = Ev0.len
             /\ redial' = Sooner(redial, x.at) /\ O(Ev0.redial) = redial'
WaitsEv == /\ Ev0.op = "waits" /\ Window(F, L(Ev0.now), Ev0.peer) = Ev0.r
           /\ F' = F /\ redial' = redial /\ n' = n /\ Rec(Ev0.peer, Ev0.e)
ForgetEv == /\ Ev0.op = "forget" /\ F' = Forget(F, Ev0.peer) /\ redial' = redial
            /\ n' = n - (IF F[Ev0.peer] # None THEN 1 ELSE 0) /\ n' = Ev0.len
FireEv == /\ Ev0.op = "fire" /\ RedialDue(redial, L(Ev0.now)) = Ev0.r
          /\ redial' = (IF Ev0.r THEN None ELSE redial) /\ O(Ev0.redial) = redial'
          /\ F' = F /\ n' = n
DumpEv == /\ Ev0.op = "dump" /\ F' = F /\ redial' = redial /\ n' = n
          /\ Used(F) = {Ev0.entries[k][1] : k \in DOMAIN Ev0.entries}
          /\ \A k \in DOMAIN Ev0.entries :
                F[Ev0.entries[k][1]] = <<L(Ev0.entries[k][2]), L(Ev0.entries[k][3])>>

\* n is the size of the table, Size(F), kept by the steps: Init and InitEv leave the table empty, a fail adds one when
\* it writes the entry of a peer that had none (only its peer's entry changes), a forget takes one away when the peer
\* had an entry, and every other event keeps F. So n = Size(F) in every state, and a fail or a forget checks the code's
\* len against n' exactly where it checked Size(F'), and a fail passes n as the size set_failed tests (DtnFailedN, the
\* same as DtnFailed when n = Size(F)), without scanning the 4096 entries of a full table at each event.
Init == i = 1 /\ F = Tab0(1..1) /\ redial = None /\ n = 0
Step == /\ i <= Len(Trace) /\ Ev0.t = "dtnb"
        /\ (InitEv \/ FailEv \/ WaitsEv \/ ForgetEv \/ FireEv \/ DumpEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* an entry within its bounds: the wait between BACKOFF_FIRST (FIRST, Sec(2)) and BACKOFF_CAP (CAP, Sec(60)), and not
\* past the end of the window
InBounds(e) == Le(FIRST, e[2]) /\ Le(e[2], CAP) /\ Le(e[2], e[1])

\* The table never grows past its bound, and every wait is within its bounds:
\*   Size(F) <= MAXT /\ \A p \in Used(F) : InBounds(F[p])
\* in every state. Only a fail writes an entry, that of its peer (FailEv, which also requires the size it leaves to be
\* the code's len); the table starts empty (Init, InitEv), a forget empties one entry and every other event keeps F.
\* So, by induction over the steps, that holds in every state of a behaviour exactly when the entry and the size each
\* fail leaves are within the bounds, which is what Inv checks on the state after the last event: the same traces
\* fail, at the same state, and nothing is checked less. It reads one entry per step instead of scanning up to 4096
\* entries with limb arithmetic at every step, which held the trace check past a minute.
\* The states seen are told apart by the event index alone (VIEW in the config): every event is the step of exactly
\* one of InitEv .. DumpEv (each requires its op) and each sets F', redial' and n' as functions of the state, so a
\* behaviour has one state per index and the view merges none. TLC then does not fingerprint the 4097 entries of a full
\* table at every state; the same traces are accepted, and Inv is still checked in every state.
View == i

Inv == (i > 1 /\ Trace[i - 1].op = "fail") =>
           LET e == Trace[i - 1] IN /\ e.len <= MAXT
                                    /\ F[e.peer] # None => InBounds(F[e.peer])
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
