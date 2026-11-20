------------------------- MODULE TraceConnectCarriers -------------------------
(***************************************************************************)
(* Trace validation of the life of a relay slot's carrier: pinc-connect    *)
(* client/carriers.rs.                                                      *)
(*                                                                         *)
(* The Rust test tests/trace_connect_carriers.rs drives a real            *)
(* Connectivity with one relay slot against the responder side of the     *)
(* protected carrier, in memory: packets routed before and after the       *)
(* carrier opens, the handshake answered by the configured relay or by    *)
(* another identity, a stream the network ends while dialing and while    *)
(* open, a dial left to its watchdog, a very slow node, and a relay with   *)
(* only one stream address. After each call it records what can be read   *)
(* from outside: the link state, the generation, the stream requests and   *)
(* the carrier notices the call queued, and the ids of the packets the     *)
(* responder decoded from the bytes poll_stream handed over. Every event   *)
(* must be a step of ConnectCarriersOps.tla. What the record cannot show  *)
(* (which answer the link gave in a tick, whether before_send reset the    *)
(* lease) is chosen by the check among the answers the link can give.     *)
(*                                                                         *)
(* An event "init" starts a run with a new slot and the run's addr, slow  *)
(* and cap; one file holds several runs. The recorded slow is the node's  *)
(* figure until the first drive: drive takes the node's round trip from   *)
(* the endpoint (set_node_rtt, drive.rs) before its tick, and the record  *)
(* does not show it, so at each drive the check chooses whether the node  *)
(* is slow from then on.                                                   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds                       *)
(* connect_carriers.ndjson.                                                 *)
(***************************************************************************)
EXTENDS ConnectCarriersOps, TLC, Json, IOUtils, TraceEnd

VARIABLES i, c, cf
vars == <<i, c, cf>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_carriers.ndjson")
Ev == Trace[i]

Init == i = 1 /\ c = NewC /\ cf = [addr |-> "both", cap |-> 1, slow |-> FALSE]

(* the call's result matches what was read back *)
ObsIn(W, f) == /\ W.c.link = Ev.link /\ W.c.gen = Ev.gen /\ W.io = Ev.io /\ W.nt = Ev.nt
               /\ c' = W.c /\ i' = i + 1 /\ cf' = f
Obs(W) == ObsIn(W, cf)

InitE == /\ Ev.op = "init" /\ c' = NewC /\ cf' = [addr |-> Ev.addr, cap |-> Ev.cap, slow |-> Ev.slow] /\ i' = i + 1

CallE ==
    CASE Ev.op = "route" -> \E bs \in BOOLEAN, wd \in BOOLEAN : Obs(SendPacket(W0(c), Ev.pkt, bs, wd, cf))
      [] Ev.op = "tick" -> \E d \in TickChoices(c.link) : Obs(TickStep(W0(c), d, cf))
      [] Ev.op = "drive" -> \E d \in TickChoices(c.link), wd \in BOOLEAN, sl \in BOOLEAN :
                               LET f == [cf EXCEPT !.slow = sl] IN ObsIn(DriveStep(W0(c), d, wd, f), f)
      [] Ev.op = "opened" -> Obs(StreamOpened(W0(c), Ev.ok))
      [] Ev.op = "closed" -> Obs(StreamClosed(W0(c)))
      [] Ev.op = "hs" -> \/ Obs(W0(c))
                         \/ c.car = "hs" /\ \E right \in BOOLEAN : Obs(HsDone(W0(c), right, cf))
                         \/ c.car # "none" /\ Obs(Dead(W0(c)))
      [] Ev.op = "poll" -> LET r == PollStream(W0(c), cf) IN r.sent = Ev.sent /\ Obs(r.w)
      [] OTHER -> FALSE

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (InitE \/ (Ev.op # "init" /\ CallE))) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of ConnectCarriersOps.tla
TraceAccepted == <>(i = Len(Trace) + 1)
Inv == TRUE
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one (the node's slowness
\* chosen at a drive may leave the other branch without a next step: that is not an error, so the config does not
\* check deadlock)
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
