---------------------------- MODULE TraceRecovery ----------------------------
(***************************************************************************)
(* Trace validation of loss recovery: vinc-transport recovery/engine.rs,   *)
(* ack.rs, loss.rs, pto.rs, sent.rs, rtt.rs and tail.rs.                   *)
(*                                                                         *)
(* The Rust test tests/trace_recovery.rs drives real engines (built with   *)
(* the cargo feature `trace`) through seeded runs of the calls a           *)
(* connection makes: packets sent (repair packets, path MTU probes, data   *)
(* frames or none) on several paths, acknowledgements (cumulative, out of  *)
(* order, with gaps, reversed, past the largest sent number), timers fired *)
(* when due, flushes, path switches, peer sleep, link down, a wait past    *)
(* the ghost retention. After every call the engine shows its state; every *)
(* event must be the step the operators of RecoveryOps.tla compute from    *)
(* the state before it (Send, Untracked, Ack, Timeout, Flush, Health,      *)
(* SetKind, SwitchPath, FollowPath, Asleep, Down, Activity, SeedRtt,       *)
(* NodeRtt, HsRtt), with the events it reported, the summary and the error *)
(* it returned, and the state the model computes must be the state         *)
(* recorded, the next timer included. An acked or lost event also names    *)
(* the path its packet left on, which must be the path of the ring slot    *)
(* with that packet number (PathOk). The tail repair tracker is checked   *)
(* on its own. The constants are the real ones: nanoseconds, a ring of 6,  *)
(* 8 paths, 200 ghosts, 32 late sends. TOP is the largest 32-bit checker   *)
(* integer: the test records a timer at or above it as TOP, and the        *)
(* model's saturating arithmetic reaches TOP in the same cases.            *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds recovery.ndjson.      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

CONSTANTS N, MS, SEC, MP, TOP, MAXG, LATEN
VARIABLES i, rs, tl
vars == <<i, rs, tl>>

INSTANCE RecoveryOps

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/recovery.ndjson")
Ev0 == Trace[i]

SlotOf(s) == [pn |-> s.pn, time |-> s.time, size |-> s.size, path |-> s.path, rep |-> s.rep, probe |-> s.probe,
              fr |-> s.fr, st |-> s.st, at |-> s.at]
ROf(v) ==
    [ring |-> [k \in 1..Len(v.ring) |-> SlotOf(v.ring[k])], ls |-> v.ls, la |-> v.la, sent |-> v.sent, acked |-> v.acked,
     lost |-> v.lost, inf |-> v.inf, infp |-> v.infp, lt |-> v.lt, pc |-> v.pc, lp |-> v.lp, asleep |-> v.asleep,
     down |-> v.down, hrd |-> v.hrd, clock |-> v.clock, tgr |-> v.tgr, lrtt |-> v.lrtt,
     rtt |-> [lat |-> v.rtt.lat, sm |-> v.rtt.sm, var |-> v.rtt.var, mn |-> v.rtt.mn, has |-> v.rtt.has],
     rel |-> [p \in 0..(MP - 1) |-> v.rel[p + 1]], prtt |-> [p \in 0..(MP - 1) |-> v.prtt[p + 1]],
     act |-> v.act, flip |-> v.flip, late |-> [k \in 1..Len(v.late) |-> <<v.late[k][1], v.late[k][2]>>],
     saved |-> v.saved,
     reo |-> [p \in 0..(MP - 1) |-> [ext |-> v.reo[p + 1][1], seen |-> v.reo[p + 1][2]]], gs |-> v.gs, lat |-> v.lat]
EvOf(e) == Ev(e[1], e[2], e[3], e[4], e[5], e[6])
EvsOf(l) == [k \in 1..Len(l) |-> EvOf(l[k])]
\* the path an acknowledgement or a loss reports is the path the packet left on (the 7th field of the event)
PathOk(r, e) == e[1] \in {"acked", "lost"} => \E k \in DOMAIN r.ring : r.ring[k].pn = e[2] /\ r.ring[k].path = e[7]
PathsOk(r, l) == \A k \in 1..Len(l) : PathOk(r, l[k])
SumOf(s) == [ap |-> s[1], ab |-> s[2], lap |-> s[3], lp |-> s[4], lb |-> s[5]]

\* the recorded state is the model's state, the next timer included
\* the code shows the time of the loss only for a slot that is a ghost
Norm(r) == [r EXCEPT !.ring = [k \in DOMAIN r.ring |-> IF r.ring[k].st = 1 THEN r.ring[k] ELSE [r.ring[k] EXCEPT !.at = 0]]]
Same(r, v) == ROf(v) = Norm(r) /\ v.nt = NextTimeout(r)

InitEv == /\ Ev0.op = "init" /\ ROf(Ev0.v) = Init0 /\ Ev0.v.nt = NextTimeout(Init0) /\ rs' = Init0
EndEv == /\ Ev0.op = "end" /\ rs' = rs
SendEv == LET X == Send(rs, [pn |-> Ev0.pn, time |-> Ev0.time, size |-> Ev0.size, path |-> Ev0.path, rep |-> Ev0.rep,
                            probe |-> Ev0.probe, fr |-> Ev0.fr])
          IN /\ Ev0.op = "send" /\ X.err = Ev0.err /\ Same(X.r, Ev0.v) /\ rs' = X.r
UntrackedEv == LET X == Untracked(rs, Ev0.pn)
               IN /\ Ev0.op = "untracked" /\ X.err = Ev0.err /\ Same(X.r, Ev0.v) /\ rs' = X.r
AckEv == LET X == Ack(rs, Ev0.now, Ev0.rgs)
         IN /\ Ev0.op = "ack" /\ X.err = Ev0.err /\ X.ev = EvsOf(Ev0.evs) /\ PathsOk(rs, Ev0.evs)
            /\ (Ev0.err = "ok" => X.s = SumOf(Ev0.sum))
            /\ Same(X.r, Ev0.v) /\ rs' = X.r
TimeoutEv == LET X == Timeout(rs, Ev0.now)
             IN /\ Ev0.op = "timeout" /\ X.ev = EvsOf(Ev0.evs) /\ PathsOk(rs, Ev0.evs) /\ X.s = SumOf(Ev0.sum) /\ X.ping = Ev0.ping
                /\ Same(X.r, Ev0.v) /\ rs' = X.r
FlushEv == LET X == Flush(rs, Ev0.now)
           IN /\ Ev0.op = "flush" /\ X.ev = EvsOf(Ev0.evs) /\ PathsOk(rs, Ev0.evs) /\ X.s = SumOf(Ev0.sum) /\ Same(X.r, Ev0.v) /\ rs' = X.r
HealthEv == /\ Ev0.op = "health" /\ Health(rs, Ev0.now) = Ev0.h /\ Same(rs, Ev0.v) /\ rs' = rs
KindEv == LET X == SetKind(rs, Ev0.path, Ev0.relay)
          IN /\ Ev0.op = "kind" /\ X.err = Ev0.err /\ Same(X.r, Ev0.v) /\ rs' = X.r
SwitchEv == LET X == SwitchPath(rs, Ev0.path)
            IN /\ Ev0.op = "switch" /\ X.err = Ev0.err /\ X.restarted = Ev0.restarted /\ Same(X.r, Ev0.v) /\ rs' = X.r
FollowEv == LET X == FollowPath(rs, Ev0.path)
            IN /\ Ev0.op = "follow" /\ X.err = Ev0.err /\ Same(X.r, Ev0.v) /\ rs' = X.r
AsleepEv == LET X == Asleep(rs, Ev0.b) IN /\ Ev0.op = "asleep" /\ Same(X, Ev0.v) /\ rs' = X
DownEv == LET X == Down(rs, Ev0.b) IN /\ Ev0.op = "down" /\ Same(X, Ev0.v) /\ rs' = X
ActivityEv == LET X == Activity(rs, Ev0.now) IN /\ Ev0.op = "activity" /\ Same(X, Ev0.v) /\ rs' = X
SeedEv == LET X == SeedRtt(rs, Ev0.x) IN /\ Ev0.op = "seed" /\ Same(X, Ev0.v) /\ rs' = X
NodeEv == LET X == NodeRtt(rs, Ev0.x) IN /\ Ev0.op = "node" /\ Same(X, Ev0.v) /\ rs' = X
HsEv == LET X == HsRtt(rs, Ev0.x) IN /\ Ev0.op = "hs" /\ Same(X, Ev0.v) /\ rs' = X

RcStep == /\ Ev0.t = "rc"
          /\ \/ InitEv \/ EndEv \/ SendEv \/ UntrackedEv \/ AckEv \/ TimeoutEv \/ FlushEv \/ HealthEv \/ KindEv
             \/ SwitchEv \/ FollowEv \/ AsleepEv \/ DownEv \/ ActivityEv \/ SeedEv \/ NodeEv \/ HsEv
          /\ UNCHANGED tl

TrStep == /\ Ev0.t = "tr"
          /\ UNCHANGED rs
          /\ \/ /\ Ev0.op = "init" /\ tl' = TailNew
             \/ /\ Ev0.op = "pkt"
                /\ LET X == TailPacket(tl, Ev0.pn, Ev0.plain, Ev0.inel)
                   IN X = [burst |-> Ev0.burst, cand |-> Ev0.cand] /\ tl' = X
             \/ /\ Ev0.op = "drain"
                /\ LET X == TailDrain(tl)
                   IN X.c = Ev0.c /\ X.t = [burst |-> Ev0.burst, cand |-> Ev0.cand] /\ tl' = X.t

Init == i = 1 /\ rs = Init0 /\ tl = TailNew
Step == /\ i <= Len(Trace) /\ (RcStep \/ TrStep) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the safety facts of the model hold on every recorded state
Inv == /\ rs.sent = rs.acked + rs.inf + rs.lost
       /\ rs.inf = SumSizes(rs.ring, 0)
       /\ Len(rs.ring) <= N
=============================================================================
