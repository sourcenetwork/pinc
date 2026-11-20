----------------------------- MODULE TraceBroadcast -----------------------------
(***************************************************************************)
(* Trace validation of the topic broadcast: pinc-broadcast msg.rs          *)
(* (on_msg, hub_store, offer, offer_held, acp_answer), gap.rs (on_have),   *)
(* floors.rs (the end of the floor wait), timers.rs (sweep) and table.rs / *)
(* log.rs behind them.                                                     *)
(*                                                                         *)
(* The Rust test tests/trace_broadcast.rs drives four real nodes (a hub,   *)
(* a publisher, two subscribers) and records every input of the message    *)
(* path (a frame, a HAVE, a timer, an access answer, the start of a node)  *)
(* with what the machine reported for it. Every event must be the step    *)
(* the operators of BroadcastNodeOps.tla (the model BroadcastNode.tla and  *)
(* the Lean port Pinc/BroadcastNode.lean use) compute: the same trace      *)
(* records in the same order, the same delivered ids, the same PACK count. *)
(*                                                                         *)
(* A message in a frame is not told apart as good or bad by the trace: the *)
(* checker keeps an oracle of the signatures (a `sign` line is the origin  *)
(* signing exactly that topic, id, body, timestamp and flag) and decides   *)
(* itself whether the presented message verifies (BroadcastAuth.tla), so a *)
(* tampered field is rejected by the model exactly when the code rejects   *)
(* it. A head cut short is a `hd` of false. Times are in units of 1/8 ms.  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds broadcast.ndjson.                                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd

CONSTANTS TTL, SeenCap, LogRing, LogCap, LogWin, FholdMax, HeldMax, ChecksMax, AcpCap, AcpMax, FloorWait, OldSlack,
          Mids, Origins, HeldDedup, HeldFullKeepsUnseen, TopicFull, AckAfterStore, Gather, EvictGuard, Revoked, AckById, KeepPrint, DueOnly, GraftStored

MidsDef == 1..400

I0 == INSTANCE BroadcastNodeOps WITH LogTrack <- FALSE, Me <- 0, IsHub <- TRUE
I1 == INSTANCE BroadcastNodeOps WITH LogTrack <- FALSE, Me <- 1, IsHub <- FALSE
I2 == INSTANCE BroadcastNodeOps WITH LogTrack <- FALSE, Me <- 2, IsHub <- FALSE
I3 == INSTANCE BroadcastNodeOps WITH LogTrack <- FALSE, Me <- 3, IsHub <- FALSE

VARIABLES i, ns, orc
vars == <<i, ns, orc>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/broadcast.ndjson")
Ev == Trace[i]

Init == i = 1 /\ ns = [n \in 0..3 |-> <<>>] /\ orc = {}

OnMsgOf(n, now, t, b, m) == CASE n = 0 -> I0!OnMsg(ns[n], now, now, t, b, m)
                              [] n = 1 -> I1!OnMsg(ns[n], now, now, t, b, m)
                              [] n = 2 -> I2!OnMsg(ns[n], now, now, t, b, m)
                              [] n = 3 -> I3!OnMsg(ns[n], now, now, t, b, m)
OnHaveOf(n, now, b, ids) == CASE n = 0 -> I0!OnHave(ns[n], now, b, ids)
                              [] n = 1 -> I1!OnHave(ns[n], now, b, ids)
                              [] n = 2 -> I2!OnHave(ns[n], now, b, ids)
                              [] n = 3 -> I3!OnHave(ns[n], now, b, ids)
OnTimerOf(n, now) == CASE n = 0 -> I0!OnTimer(ns[n], now)
                       [] n = 1 -> I1!OnTimer(ns[n], now)
                       [] n = 2 -> I2!OnTimer(ns[n], now)
                       [] n = 3 -> I3!OnTimer(ns[n], now)
AnswerOf(n, now, id, allow) == CASE n = 0 -> I0!AcpAnswer(ns[n], now, id, allow)
                                 [] n = 1 -> I1!AcpAnswer(ns[n], now, id, allow)
                                 [] n = 2 -> I2!AcpAnswer(ns[n], now, id, allow)
                                 [] n = 3 -> I3!AcpAnswer(ns[n], now, id, allow)
InitOf(n, born) == CASE n = 0 -> I0!NodeInit(born) [] n = 1 -> I1!NodeInit(born) [] n = 2 -> I2!NodeInit(born) [] n = 3 -> I3!NodeInit(born)

FrameName(ft) == CASE ft = 5 -> "PUB" [] ft = 7 -> "MSG" [] ft = 15 -> "FAN" [] ft = 16 -> "FANP" [] ft = 17 -> "MEMBER_PUSH"

\* the trace records as the Rust test writes them: the fields the code reports
Proj(o) == CASE o.k = "Stored" -> [k |-> "Stored", mid |-> o.mid, fanned |-> o.fanned]
             [] o.k = "Rejected" -> [k |-> "Rejected", mid |-> o.mid, why |-> o.why]
             [] o.k = "Delivered" -> [k |-> "Delivered", mid |-> o.mid]
             [] o.k = "Held" -> [k |-> "Held", mid |-> o.mid, why |-> o.why]
             [] o.k = "AcpAsked" -> [k |-> "AcpAsked", id |-> o.id]
             [] o.k = "AcpAnswered" -> [k |-> "AcpAnswered", id |-> o.id, allow |-> o.allow]
             [] o.k = "Repaired" -> [k |-> "Repaired", mid |-> o.mid]
             [] o.k = "FloorDone" -> [k |-> "FloorDone", used |-> o.used]
Projected(outs) == [j \in 1..Len(outs) |-> Proj(outs[j])]
Same(r) == Projected(r.outs) = Ev.out

Presented == [org |-> Ev.org, tid |-> Ev.tid, mid |-> Ev.mid, bid |-> Ev.bid, ts |-> Ev.ts, isb |-> Ev.isb]
Verified == \E p \in orc : p[1] = Ev.sig /\ p[2] = Presented

StartEv == /\ Ev.op = "start" /\ ns' = [ns EXCEPT ![Ev.n] = [InitOf(Ev.n, Ev.at) EXCEPT !.sub = FALSE]] /\ UNCHANGED orc

SubEv == /\ Ev.op = "sub" /\ ns' = [ns EXCEPT ![Ev.n].sub = TRUE] /\ UNCHANGED orc

SignEv == /\ Ev.op = "sign"
          /\ orc' = orc \union {<<Ev.sig, [org |-> Ev.org, tid |-> Ev.tid, mid |-> Ev.mid, bid |-> Ev.bid, ts |-> Ev.ts, isb |-> Ev.isb]>>}
          /\ UNCHANGED ns

FrameEv ==
    LET kind == IF ~Ev.hd THEN "badhead" ELSE IF Ev.big THEN "big" ELSE IF ~Verified THEN "badsig" ELSE "good"
        m == [mid |-> Ev.mid, origin |-> Ev.org, ts |-> Ev.ts, kind |-> kind, n |-> Ev.sz, body |-> <<Ev.bid, Ev.isb>>]
        r == OnMsgOf(Ev.n, Ev.at, FrameName(Ev.ft), Ev.boot, m)
    IN /\ Ev.op = "frame" /\ Same(r) /\ r.ack = Ev.ack /\ ns' = [ns EXCEPT ![Ev.n] = r.n] /\ UNCHANGED orc

HaveEv == LET r == OnHaveOf(Ev.n, Ev.at, Ev.boot, Ev.ids)
          IN /\ Ev.op = "have" /\ Same(r) /\ ns' = [ns EXCEPT ![Ev.n] = r.n] /\ UNCHANGED orc

TimerEv == LET r == OnTimerOf(Ev.n, Ev.at)
           IN /\ Ev.op = "timer" /\ Same(r) /\ ns' = [ns EXCEPT ![Ev.n] = r.n] /\ UNCHANGED orc

AcpEv == LET r == AnswerOf(Ev.n, Ev.at, Ev.id, Ev.allow)
         IN /\ Ev.op = "acp" /\ Same(r) /\ ns' = [ns EXCEPT ![Ev.n] = r.n] /\ UNCHANGED orc

Step == /\ i <= Len(Trace) /\ Ev.t = "bc" /\ (StartEv \/ SubEv \/ SignEv \/ FrameEv \/ HaveEv \/ TimerEv \/ AcpEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
