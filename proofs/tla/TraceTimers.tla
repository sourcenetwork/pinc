----------------------------- MODULE TraceTimers ------------------------------
(***************************************************************************)
(* Trace validation of the timers and the closing state of the PINCER     *)
(* connection: pinc-transport conn/timer.rs and conn/life.rs.              *)
(*                                                                         *)
(* The Rust test tests/trace_timers.rs drives scripted pairs of real       *)
(* connections (built with the cargo feature `trace`) call by call: the    *)
(* idle timeout, local closes with their CLOSE or with a timer first,      *)
(* violations, a sleeping peer held 120 s, an unanswered WAKE, a link      *)
(* outage past 30 s, a dead path, a dial nobody answers, a dialing side    *)
(* whose Finish never reached the responder (it ends the session           *)
(* unconfirmed at its connect limit while the responder's handshake runs   *)
(* out, #390), and random runs with traffic, loss, duplicates, altered     *)
(* datagrams, sleep and wake, outages, keepalives and pulses. Every call   *)
(* of each connection must be the step the operators of TimersOps.tla      *)
(* compute from the state the previous call left, with the lifecycle       *)
(* events the code reported, and the state recorded after it must be the   *)
(* model's: poll_timeout must return the minimum the model takes over the  *)
(* recorded component deadlines; handle_timeout must close for idleness    *)
(* exactly at or after the deadline, end an outage and report a WAKE       *)
(* exactly when due (a close a component decides in it is taken from the   *)
(* events, cc; the carrier rule is decided from what the recovery timer    *)
(* read, pr: a probe timeout on a relay path whose carrier was heard       *)
(* within 6 s, with 4 in a row and 4 round trips of silence begins a close *)
(* with a CLOSE); a datagram is heard exactly when handle_datagram took it *)
(* (res "ok"), and its SLEEP and CLOSE frames are taken from the events;   *)
(* poll_transmit may write only what CanSend allows, so at most one CLOSE  *)
(* leaves each connection (Inv); the application's opens are refused once  *)
(* closing.                                                                *)
(*                                                                         *)
(* The runs start from a connected pair, or from a dialing side connected  *)
(* to a responder that still waits for the Finish (a dial nobody answers   *)
(* and that pair take nothing), so no handshake datagram reaches a dialing *)
(* side here. One that it takes without its session being established does *)
(* not restart the idle timer (conn/recv.rs believes nothing of it before  *)
(* the reply authenticated; the establishment restarts it): reading res    *)
(* "ok" as heard does not cover that case.                                 *)
(*                                                                         *)
(* Times are whole microseconds, rounded up (the test drives whole         *)
(* microseconds), with the real constants.                                 *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds timers.ndjson.        *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd
CONSTANTS IDLE, HOLD, WAKE, LDM, CF, IR
VARIABLES i, s, closes
vars == <<i, s, closes>>
INSTANCE TimersOps

K == [idle |-> IDLE, hold |-> HOLD, wake |-> WAKE, ldm |-> LDM, cf |-> CF, ir |-> IR]
Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/timers.ndjson")
E == Trace[i]
N == E.n
St == s[N]

SOf(v) == [ph |-> v.ph, close |-> v.close, keys |-> v.keys, act |-> v.act, sent |-> v.sent, ka |-> v.ka, pa |-> v.pa,
           la |-> v.la, stx |-> v.stx, wd |-> v.wd, ld |-> v.ld]
COf(v) == [conf |-> v.conf, hs |-> v.hs, rekey |-> v.rekey, rec |-> v.rec, ack |-> v.ack, amp |-> v.amp,
           paced |-> v.paced, path |-> v.path, mtu |-> v.mtu]
Has(x) == \E j \in DOMAIN E.ev : E.ev[j] = x
\* the state after the call is the model's, so are the events, and so is the idle deadline the code computed
Put(r) == /\ s' = [s EXCEPT ![N] = r.s]
          /\ r.s = SOf(E.v) /\ r.ev = E.ev /\ Idle(r.s, K) = E.v.idle
Keep(x) == Put([s |-> x, ev |-> <<>>]) /\ UNCHANGED closes

InitEv == /\ E.op = "init" /\ E.ev = <<>> /\ Idle(SOf(E.v), K) = E.v.idle
          /\ s' = [s EXCEPT ![N] = SOf(E.v)] /\ closes' = [closes EXCEPT ![N] = 0]
PollEv == E.op = "poll" /\ E.out = Poll(St, COf(E.v), K) /\ Keep(St)
\* the close a component decided in the call: the handshake's timer runs before the recovery timer, so an end it
\* reported ("hs" while handshaking, "unconf" while connected) came first and a dead path in the same call changed
\* nothing
TimeoutEv == /\ E.op = "timeout"
             /\ LET cc == IF Has("hs") THEN "hs" ELSE IF Has("unconf") THEN "unconf" ELSE IF E.pr.dead THEN "dead"
                          ELSE "none"
                    pr == [ping |-> E.pr.ping, relay |-> E.pr.relay, ch |-> E.pr.ch, pto |-> E.pr.pto, lh |-> E.pr.lh,
                           smp |-> E.pr.smp, sr |-> E.pr.sr, nd |-> E.pr.nd]
                IN Put(Timeout(St, E.now, cc, pr, K)) /\ UNCHANGED closes
RecvEv == E.op = "recv" /\ Put(Recv(St, E.now, E.res = "ok", Has("asleep"), Has("peer"))) /\ UNCHANGED closes
InjectEv == /\ E.op = "inject" /\ Open(St)
            /\ Put(IF E.kind = "bad" THEN Bad(St, E.err) ELSE Viol(St, E.now, E.err)) /\ UNCHANGED closes
CloseEv == E.op = "close" /\ Put(Close(St, E.err)) /\ UNCHANGED closes
TxEv == /\ E.op = "tx"
        /\ LET sent == E.len > 0 IN
           /\ sent => CanSend(St)
           /\ E.v.stx <= St.stx /\ (E.v.stx < St.stx => sent)
           /\ Put([s |-> Tx(St, E.now, sent, E.v.stx), ev |-> <<>>])
           /\ closes' = [closes EXCEPT ![N] = @ + IF TxClose(St, sent) THEN 1 ELSE 0]
SleepEv == E.op = "sleep" /\ Keep(Sleep(St))
WakeEv == E.op = "wake" /\ Keep(Wake(St, E.now, K))
LinkEv == E.op = "link" /\ Keep(Link(St, E.now, E.down, K))
KeepEv == E.op = "keepalive" /\ Keep(Keepalive(St, E.ka))
PulseEv == E.op = "pulse" /\ Keep(Pulse(St, E.now, E.sent))
AppEv == E.op = "app" /\ (E.ok => AppOpen(St)) /\ Keep(St)

S0 == [ph |-> "closed", close |-> None, keys |-> FALSE, act |-> 0, sent |-> 0, ka |-> None, pa |-> None,
       la |-> FALSE, stx |-> 0, wd |-> None, ld |-> None]
Init == i = 1 /\ s = [x \in {"a", "b"} |-> S0] /\ closes = [x \in {"a", "b"} |-> 0]
Step == /\ i <= Len(Trace) /\ E.t = "tmr"
        /\ (InitEv \/ PollEv \/ TimeoutEv \/ RecvEv \/ InjectEv \/ CloseEv \/ TxEv \/ SleepEv \/ WakeEv \/ LinkEv
            \/ KeepEv \/ PulseEv \/ AppEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* at most one CLOSE leaves each connection of a run
Inv == \A x \in {"a", "b"} : closes[x] <= 1
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
