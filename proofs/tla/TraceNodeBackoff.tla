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
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, Nanos, TraceEnd
CONSTANT MAXT
VARIABLES i, F, hubs, n
vars == <<i, F, hubs, n>>
INSTANCE NodeBackoffOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/nobo.ndjson")
Ev0 == Trace[i]
L(x) == U!FromLimbs(x)
\* the recorded entry of the peer: [] for none, else [until, wait]
Rec(p, e) == IF e = <<>> THEN F'[p] = None ELSE F'[p] = <<L(e[1]), L(e[2])>>

InitEv == /\ Ev0.op = "init" /\ Ev0.max = MAXT
          /\ L(Ev0.first) = FIRST /\ L(Ev0.hubcap) = HUBCAP /\ L(Ev0.cap) = CAP
          /\ L(Ev0.dfirst) = DFIRST /\ L(Ev0.dcap) = DCAP
          /\ F' = Tab0(1..Ev0.peers) /\ hubs' = {Ev0.hubs[k] : k \in DOMAIN Ev0.hubs} /\ n' = 0
\* the size after a step that writes at most the entry of p: one more when p had none and has one now
Grown(p) == n + (IF F[p] = None /\ F'[p] # None THEN 1 ELSE 0)
BackoffEv == LET x == BackoffN(F, n, L(Ev0.now), Ev0.peer, Ev0.peer \in hubs)
             IN /\ Ev0.op = "backoff" /\ F' = x.f /\ Rec(Ev0.peer, Ev0.e) /\ n' = Grown(Ev0.peer) /\ n' = Ev0.len
                /\ UNCHANGED hubs
DenyEv == LET x == DenyBackN(F, n, L(Ev0.now), Ev0.peer)
          IN /\ Ev0.op = "deny" /\ F' = x.f /\ Rec(Ev0.peer, Ev0.e) /\ n' = Grown(Ev0.peer) /\ n' = Ev0.len
             /\ UNCHANGED hubs
\* the frame hand-off takes a frame for a peer with no session and nothing queued exactly outside the window
GateEv == /\ Ev0.op = "gate" /\ (~Window(F, L(Ev0.now), Ev0.peer)) = Ev0.ok
          /\ F' = F /\ Rec(Ev0.peer, Ev0.e) /\ n = Ev0.len /\ UNCHANGED <<hubs, n>>
\* our dial of the peer came up and the full session table shed the session: a failed dial
ShedEv == /\ Ev0.op = "shed" /\ F' = BackoffN(F, n, L(Ev0.now), Ev0.peer, Ev0.peer \in hubs).f /\ n' = Grown(Ev0.peer)
          /\ UNCHANGED hubs
\* a duty pass of the node; the peer has no session, no dial in progress and is not revoked, so the node dials it
\* exactly outside its window; the pass ends with the prune (which builds the whole table, so the size is counted)
DutyEv == /\ Ev0.op = "duty" /\ (~Window(F, L(Ev0.now), Ev0.peer)) = Ev0.dialed
          /\ F' = Prune(F, L(Ev0.now)) /\ n' = Size(F') /\ UNCHANGED hubs
DumpEv == /\ Ev0.op = "dump" /\ F' = F /\ UNCHANGED <<hubs, n>>
          /\ Used(F) = {Ev0.entries[k][1] : k \in DOMAIN Ev0.entries}
          /\ \A k \in DOMAIN Ev0.entries :
                F[Ev0.entries[k][1]] = <<L(Ev0.entries[k][2]), L(Ev0.entries[k][3])>>

\* n is the size of the table, Size(F), kept by the steps: Init and InitEv leave the table empty, a backoff, a deny
\* and a shed write at most the entry of their peer and add one when it had none (Grown), a duty pass prunes and
\* counts what is left, and a gate and a dump keep F. So n = Size(F) in every state, a backoff or deny checks the
\* code's len against n' exactly where it checked Size(F'), a gate checks it against n where it checked Size(F), and
\* each passes n as the size set_failed tests (BackoffN, DenyBackN: the same as Backoff, DenyBack when n = Size(F)),
\* without counting the 4096 entries of a full table at each event.
Init == i = 1 /\ F = Tab0(1..1) /\ hubs = {} /\ n = 0
Step == /\ i <= Len(Trace) /\ Ev0.t = "nobo"
        /\ (InitEv \/ BackoffEv \/ DenyEv \/ GateEv \/ ShedEv \/ DutyEv \/ DumpEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* an entry within its bounds: the wait between BACKOFF_FIRST (Sec(2)) and DENY_CAP (Sec(900)), and not past the end
\* of the window
InBounds(e) == Le(Sec(2), e[2]) /\ Le(e[2], Sec(900)) /\ Le(e[2], e[1])

\* The table never grows past its bound, and every wait is within its bounds:
\*   Size(F) <= MAXT /\ \A p \in Used(F) : InBounds(F[p])
\* in every state. Only a backoff, a deny and a shed write an entry, that of their peer, and only they make the table
\* grow; the table starts empty (Init, InitEv), a duty pass only empties entries (Prune) and a gate and a dump keep F.
\* So, by induction over the steps, that holds in every state of a behaviour exactly when the entry and the size each
\* backoff, deny and shed leaves are within the bounds, which is what Inv checks on the state after the last event:
\* the same traces fail, at the same state, and nothing is checked less. It reads one entry per step instead of
\* scanning up to 4096 entries with limb arithmetic at every step.
\* The states seen are told apart by the event index alone (VIEW in the config): every event is the step of exactly
\* one of InitEv .. DumpEv (each requires its op) and each sets F', hubs' and n' as functions of the state, so a
\* behaviour has one state per index and the view merges none. TLC then does not fingerprint the entries of a full
\* table at every state; the same traces are accepted, and Inv is still checked in every state.
View == i

Inv == (i > 1 /\ Trace[i - 1].op \in {"backoff", "deny", "shed"}) =>
           LET e == Trace[i - 1] IN /\ n <= MAXT
                                    /\ F[e.peer] # None => InBounds(F[e.peer])
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
