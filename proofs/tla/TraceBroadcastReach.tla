--------------------------- MODULE TraceBroadcastReach ---------------------------
(***************************************************************************)
(* Trace validation of a hub's adjacency table: pinc-broadcast reach.rs    *)
(* `set_adjacent`, `on_adj`, `reach_timer`, reach/table.rs `Reach::take`,  *)
(* `expire`, `leave`, `drop_gone`, `reopen`, `class`, and the scope        *)
(* `Topics::hub_store` applies to a push.                                  *)
(*                                                                         *)
(* The Rust test tests/trace_broadcast_reach.rs runs one hub (node 0, the  *)
(* model's hub 101) and members 1..4 with Ed25519 keys (built with the     *)
(* cargo feature `trace`, whose probes read the hub's record of a member   *)
(* and run the hub's reach sweep alone). A record is charged in units of   *)
(* 32 bytes: 10 for a live record (256 + 64 of signature) and one per peer *)
(* it names, so RecBase is 10 and the hub's table holds TableBytes units.  *)
(* Events: `toggle` (a session between u and v opens or closes), `endturn`,*)
(* `report` (member n signs its record), `nextturn`, `recv` (the hub took *)
(* or refused member n's newest record; whether it reported a refusal and *)
(* a closing), `sub`, `hand` (o published; whether subscriber s got it),   *)
(* `leave` (the hub released n), and a sweep at a time past RECORD_TTL     *)
(* with no refresh: `expire` (n), `drain` (the log holds nothing of n),    *)
(* `reopen`. The last event of each call carries the hub's records         *)
(* (sequence, live, peers per member) and whether its table is closed.     *)
(*                                                                         *)
(* Each event must be the step of BroadcastReach.tla it names with that    *)
(* table, a hand-over must be one the model allows and a missed one one it *)
(* forbids, and the model's invariants hold on every state. The code       *)
(* charges a tombstone 256 bytes (8 units) where the model charges        *)
(* RecBase: the test makes no record decision while a tombstone is held    *)
(* (at most three members are held, at most three peers each, so a held   *)
(* member's record always fits and only a newcomer is refused), and the   *)
(* sweep ends the run. Not driven: liars, lost frames, the refresh, the   *)
(* drop of a tombstone, mirrors between hubs (BroadcastReach_*.cfg).      *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds bcast/reach.ndjson.                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

CONSTANTS N, HubCount, Liars, MaxChanges, MaxLoss, MaxExpire, MaxLeave, TableBytes, RecBase,
          Mutual, Rebuild, Tomb, ScopedRepair, Closed, EvictAny, Batch, Told, Waits, Charge

VARIABLES i, sess, changes, cur, tab, lab, net, lost, expired, subd, bad, closed, refd, left, logged, phase, sent, said,
          heard, bytes
mvars == <<sess, changes, cur, tab, lab, net, lost, expired, subd, bad, closed, refd, left, logged, phase, sent, said,
           heard, bytes>>
vars == <<i, mvars>>

M == INSTANCE BroadcastReach

\* the one hub
H == 101

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/bcast/reach.ndjson")
Ev == Trace[i]
Range(s) == {s[k] : k \in 1..Len(s)}

\* the hub's records and whether its table is closed, after the call (on its last event only); an expired record names
\* no peer in the code and keeps its last peers in the model, so peers are compared while live
Proj == "tab" \in DOMAIN Ev =>
          /\ closed'[H] = Ev.shut
          /\ \A n \in M!Nodes : /\ tab'[H][n].seq = Ev.tab[n].seq
                                /\ tab'[H][n].live = Ev.tab[n].live
                                /\ tab'[H][n].live => tab'[H][n].peers = Range(Ev.tab[n].peers)

ToggleEv == Ev.op = "toggle" /\ M!Toggle(Ev.u, Ev.v)
EndTurnEv == Ev.op = "endturn" /\ M!EndTurn
ReportEv == Ev.op = "report" /\ M!Report(Ev.n)
NextTurnEv == Ev.op = "nextturn" /\ M!NextTurn
\* the frame of the member's newest record arrives; the hub reports a refusal (ReachRefused) and a closing (ReachClosed)
RecvEv == /\ Ev.op = "recv" /\ M!Recv(M!Frame(Ev.n))
          /\ IF Ev.refused THEN Ev.n \in heard'[H] ELSE heard' = heard
          /\ Ev.closing = (said'[H] /\ ~said[H])
SubEv == Ev.op = "sub" /\ M!Sub(Ev.s)
\* o's message went to s exactly when the model's scope allows it
HandEv == /\ Ev.op = "hand"
          /\ IF Ev.got THEN M!Hand(H, Ev.o, Ev.s, FALSE) ELSE ~M!Allowed(H, Ev.o, Ev.s) /\ UNCHANGED mvars
LeaveEv == Ev.op = "leave" /\ M!Leave(Ev.n)
ExpireEv == Ev.op = "expire" /\ M!Expire(H, Ev.n)
DrainEv == Ev.op = "drain" /\ M!Drain(H, Ev.n)
ReopenEv == Ev.op = "reopen" /\ M!Reopen(H)

Init == i = 1 /\ M!Init
Step == /\ i <= Len(Trace) /\ Ev.t = "reach"
        /\ (ToggleEv \/ EndTurnEv \/ ReportEv \/ NextTurnEv \/ RecvEv \/ SubEv \/ HandEv \/ LeaveEv \/ ExpireEv \/ DrainEv
            \/ ReopenEv)
        /\ Proj
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == M!DeliverySound /\ M!EdgesGood /\ M!LabelsFresh /\ M!Bounds /\ M!BoundedReports /\ M!ClosedTold
=============================================================================
