------------------------------ MODULE TraceCc -------------------------------
(***************************************************************************)
(* Trace validation of congestion control and pacing: pinc-transport       *)
(* recovery/cubic.rs, round_exit.rs, delivery.rs and pacer.rs.             *)
(*                                                                         *)
(* The Rust test tests/trace_cc.rs drives a real controller and pacer      *)
(* (built with the cargo feature `trace`) through seeded runs of the calls *)
(* the recovery engine makes. After every call the controller shows its    *)
(* state; every event must be the step the operators of CcOps.tla compute  *)
(* from the state before it, and the state the model computes must be the  *)
(* state recorded. An acknowledgement in congestion avoidance is the       *)
(* bounded step of CcOps.tla (AckRel): the Lean replay computes it at full *)
(* width. The constants are the real ones: nanoseconds, a window of 44,000 *)
(* at the start, 2,400 at the least; MAXC and TOP are the largest 32-bit   *)
(* checker integer (a threshold not set, or a release time past the end,   *)
(* is recorded as TOP), and the runs keep every window far below it.       *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds cc.ndjson.            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd

CONSTANTS MS, SEC, TOP, MAXC, MINC, INITC, BETALIM, MINMSS, MAXMSS, MINSAMP, EXITCW, GFAST, GMID, U32MAX, IRTT, BURST
VARIABLES i, x, p
vars == <<i, x, p>>

INSTANCE CcOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/cc.ndjson")
Ev0 == Trace[i]

XOf(v) == [cwnd |-> v.cwnd, ss |-> v.ss, wmax |-> v.wmax, west |-> v.west, k |-> v.k, epoch |-> v.epoch, rec |-> v.rec,
           streak |-> v.streak, rend |-> v.rend, ref |-> v.ref, rmin |-> v.rmin, samp |-> v.samp, pst |-> v.pst,
           pby |-> v.pby, rate |-> v.rate, slack |-> v.slack]
Same(y, v) == XOf(v) = y

CcEv == /\ UNCHANGED p
        /\ \/ Ev0.op = "rtt" /\ x' = OnSample(x, Ev0.s) /\ Same(x', Ev0.v)
           \/ /\ Ev0.op = "ack" /\ x' = XOf(Ev0.v)
              /\ AckRel(x, [now |-> Ev0.now, acked |-> Ev0.acked, la |-> Ev0.la, np |-> Ev0.np, srtt |-> Ev0.srtt,
                            mn |-> Ev0.mn, mss |-> Ev0.mss], x')
           \/ LET r == Loss(x, Ev0.now, Ev0.newest, Ev0.lat, Ev0.mn)
              IN Ev0.op = "loss" /\ r.r = Ev0.r /\ x' = r.x /\ Same(x', Ev0.v)
           \/ Ev0.op = "newpath" /\ x' = NewPath(x, Ev0.now, Ev0.np) /\ Same(x', Ev0.v)
           \/ Ev0.op = "restore" /\ x' = Restore(x, Ev0.cw, Ev0.ss) /\ Same(x', Ev0.v)
           \/ Ev0.op = "resume" /\ x' = Resume(x, Ev0.mn) /\ Same(x', Ev0.v)
           \/ Ev0.op = "slack" /\ x' = SetSlack(x, Ev0.b) /\ Same(x', Ev0.v)
           \/ Ev0.op = "gate" /\ Ev0.cap = GateCap(x, Ev0.mn) /\ x' = x /\ Same(x, Ev0.v)
           \/ Ev0.op = "end" /\ x' = x

InitEv == /\ Ev0.op = "init" /\ x' = Cc0 /\ p' = Pc0 /\ Same(x', Ev0.v)

PcEv == /\ UNCHANGED x
        /\ \/ LET q == OnSent(p, Ev0.now, Ev0.mtu, Ev0.srtt, Ev0.cw, Ev0.lim)
              IN Ev0.op = "psent" /\ p' = q /\ q.tokens = Ev0.v.tokens /\ q.next = Ev0.v.next /\ q.start = Ev0.v.start
           \/ Ev0.op = "prel" /\ p' = p /\ NextRelease(p, Ev0.now) = Ev0.r /\ p.tokens = Ev0.v.tokens /\ p.next = Ev0.v.next
              /\ p.start = Ev0.v.start

Init == i = 1 /\ x = Cc0 /\ p = Pc0
Step == /\ i <= Len(Trace) /\ Ev0.t = "txcc"
        /\ (IF Ev0.op = "init" THEN InitEv ELSE IF Ev0.op \in {"psent", "prel"} THEN PcEv ELSE (CcEv /\ UNCHANGED p)) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == x.cwnd >= MINC /\ x.cwnd <= MAXC /\ x.streak <= 4 /\ p.tokens >= 1 /\ p.tokens <= BURST
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
