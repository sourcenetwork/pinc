------------------------------ MODULE TraceRx --------------------------------
(***************************************************************************)
(* Trace validation of the received-packet tracker: pinc-transport         *)
(* recovery/recv.rs.                                                       *)
(*                                                                         *)
(* The Rust test tests/trace_rx.rs drives real trackers (built with the    *)
(* cargo feature `trace`) through seeded runs: packets received (in order, *)
(* with gaps, old, duplicated, bulk, ack-eliciting or not), the minimum    *)
(* round trip and the acknowledgement interval set, acknowledgements sent, *)
(* the peer's acknowledgements, and queries of the ranges to report, the   *)
(* deadline and the numbers seen. Every event must be the step the         *)
(* operators of RxOps.tla compute from the state before it, with the       *)
(* outcome the code returned, and the state the model computes must be the *)
(* state recorded. Runs use the real const generic sizes (4 and 128 ranges)*)
(* and the real constants: nanoseconds, 48 and 32 table entries, 32 ranges.*)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds rx.ndjson.            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd

CONSTANTS MS, SEC, TOP, MAXPN, U32MAX, SENTN, CONFN, MAXACK
VARIABLES i, x
vars == <<i, x>>

INSTANCE RxOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/rx.ndjson")
Ev0 == Trace[i]

PairsOf(l) == [k \in 1..Len(l) |-> <<l[k][1], l[k][2]>>]
XOf(cap, v) == [items |-> PairsOf(v.items), cap |-> cap, floor |-> v.floor, pending |-> v.pending, due |-> v.due,
                every |-> v.every, mrtt |-> v.mrtt, sent |-> PairsOf(v.sent), conf |-> PairsOf(v.conf), cf |-> v.cf]
Same(y, v) == XOf(y.cap, v) = y

InitEv == /\ Ev0.op = "init" /\ x' = Init0(Ev0.cap) /\ Same(x', Ev0.v)
RecvEv == LET r == Receive(x, [pn |-> Ev0.pn, now |-> Ev0.now, elic |-> Ev0.elic, bytes |-> Ev0.bytes])
          IN /\ Ev0.op = "recv" /\ r.out = Ev0.out /\ Same(r.x, Ev0.v) /\ x' = r.x
RttEv == /\ Ev0.op = "rtt" /\ x' = SetMinRtt(x, Ev0.m) /\ Same(x', Ev0.v)
EveryEv == /\ Ev0.op = "every" /\ x' = SetEvery(x, Ev0.e) /\ Same(x', Ev0.v)
AckSentEv == /\ Ev0.op = "acksent" /\ x' = AckSent(x, Ev0.apn, Ev0.now) /\ Same(x', Ev0.v)
PeerEv == /\ Ev0.op = "peer" /\ x' = PeerAck(x, Ev0.now, PairsOf(Ev0.rgs)) /\ Same(x', Ev0.v)
QueryEv == /\ Ev0.op = "query" /\ x' = x /\ Same(x, Ev0.v)
           /\ PairsOf(Ev0.rgs) = AckRanges(x, Ev0.now)
           /\ Ev0.dl = AckDeadline(x) /\ Ev0.pend = (x.pending > 0) /\ Ev0.due = AckDue(x, Ev0.now)
           /\ Ev0.lg = Largest(x) /\ Ev0.rc = Len(x.items)
           /\ \A k \in 1..Len(Ev0.has) : Ev0.has[k][2] = Contains(x, Ev0.has[k][1])
EndEv == Ev0.op = "end" /\ x' = x

Init == i = 1 /\ x = Init0(1)
Step == /\ i <= Len(Trace) /\ Ev0.t = "txrx"
        /\ (InitEv \/ RecvEv \/ RttEv \/ EveryEv \/ AckSentEv \/ PeerEv \/ QueryEv \/ EndEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == /\ Len(x.items) <= x.cap /\ Len(x.sent) <= SENTN /\ Len(x.conf) <= CONFN
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
