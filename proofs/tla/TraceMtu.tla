------------------------------ MODULE TraceMtu -------------------------------
(***************************************************************************)
(* Trace validation of path MTU discovery: pinc-transport conn/mtu.rs.     *)
(*                                                                         *)
(* The Rust test tests/trace_mtu.rs drives the real state machine (built   *)
(* with the cargo feature `trace`) through seeded runs of the calls the    *)
(* connection makes: discovery started, probes due and sent, acknowledged  *)
(* or echoed, or lost, path events, the full-size packets seen by the send *)
(* and receive paths, the black-hole suspicion and its settling. Every     *)
(* call must be the step the operators of MtuOps.tla compute, with the    *)
(* answer the code gave, and the state recorded must be the model's. The   *)
(* constants are the real ones except REPROBE and TOP (the largest 32-bit  *)
(* checker integer; a time at or above it is recorded as it).              *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds mtu.ndjson.           *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
CONSTANTS TOP, MINMTU, PROBEMTU, JFLOOR, JMTU, REPROBE
VARIABLES i, m
vars == <<i, m>>
INSTANCE MtuOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/mtu.ndjson")
Ev0 == Trace[i]

MOf(v) == [cur |-> v.cur, infl |-> v.infl, probed |-> v.probed, jdone |-> v.jdone, retry |-> v.retry,
           started |-> v.started, lbig |-> v.lbig, backed |-> v.backed, pbig |-> v.pbig,
           susp |-> <<v.susp[1], v.susp[2]>>]
Same(y, v) == MOf(v) = y

InitEv == Ev0.op = "init" /\ m' = M0 /\ Same(m', Ev0.v)
StartEv == Ev0.op = "start" /\ m' = Start(m) /\ Same(m', Ev0.v)
BigEv == Ev0.op = "big" /\ m' = SetBig(m, Ev0.lb, Ev0.ba, Ev0.pb) /\ Same(m', Ev0.v)
TargetEv == Ev0.op = "target" /\ m' = m /\ Same(m, Ev0.v)
            /\ Target(m, Ev0.allowed, Ev0.im, Ev0.ll, Ev0.now) = Ev0.r
SentEv == Ev0.op = "sent" /\ m' = ProbeSent(m, Ev0.size) /\ Same(m', Ev0.v)
RaiseEv == LET r == Raise(m, Ev0.size) IN Ev0.op = "raise" /\ r.new = Ev0.r /\ m' = r.m /\ Same(m', Ev0.v)
LostEv == Ev0.op = "lost" /\ m' = ProbeLost(m, Ev0.size, Ev0.now) /\ Same(m', Ev0.v)
EventEv == Ev0.op = "event" /\ m' = Event(m) /\ Same(m', Ev0.v)
BhEv == Ev0.op = "bh" /\ m' = BlackHole(m, Ev0.now, Ev0.rtt) /\ Same(m', Ev0.v)
BhcEv == LET r == BlackHoleCheck(m, Ev0.now) IN Ev0.op = "bhc" /\ r.dropped = Ev0.r /\ m' = r.m /\ Same(m', Ev0.v)

Init == i = 1 /\ m = M0
Step == /\ i <= Len(Trace) /\ Ev0.t = "txmt"
        /\ (InitEv \/ StartEv \/ BigEv \/ TargetEv \/ SentEv \/ RaiseEv \/ LostEv \/ EventEv \/ BhEv \/ BhcEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == m.cur >= MINMTU
=============================================================================
