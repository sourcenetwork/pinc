----------------------------- MODULE TraceStreams -----------------------------
(***************************************************************************)
(* Trace validation of the receive and credit path of the stream layer:    *)
(* vinc-transport stream/table.rs, recv.rs, flow.rs, ranges.rs and pool.rs *)
(* (Streams, Recv, Window, Meter, RangeSet, Ring over the buffer pool).    *)
(*                                                                         *)
(* The Rust test tests/trace_streams.rs drives real tables (built with the *)
(* cargo feature `trace`) over a pool of 8 chunks through seeded runs of   *)
(* the calls a connection makes: stream frames (out of order, overlapping, *)
(* past the credit, after the final size, with differing bytes, tiny ones  *)
(* that fragment the stored ranges), resets, consumes, pending control     *)
(* frames lost or acknowledged, locally opened streams with writes, sends  *)
(* and acknowledgements, other users of the pool, the close of the table.  *)
(* After every call the table shows its state; every event must be the     *)
(* step the operators of StreamsOps.tla compute from the state before it   *)
(* (Frame, Reset, Consume, Pending, CtlLostMsd, CtlLostReset,              *)
(* CtlAckedReset, OpenLocal, AppReset, Finish, ExtTo, CloseAll), with the  *)
(* error the call returned, and the state the model computes must be the   *)
(* state recorded. The constants are the real ones of the test: chunks of  *)
(* 16384 bytes, a ring of 5, 96 stored ranges, 4 slots, a pool of 8.       *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds streams.ndjson.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

CONSTANTS CH, RING, RR, N, MAXREM, B, SWC, MSWC, PM, RF, MAXOFF, RETRY, RemIds, LocIds
VARIABLES i, rs
vars == <<i, rs>>

INSTANCE StreamsOps

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/streams.ndjson")
Ev == Trace[i]

SlotOf(s) ==
    IF s.id = -1 THEN NewSlot
    ELSE [id |-> s.id, open |-> s.open, held |-> {s.held[k] : k \in 1..Len(s.held)}, rs |-> s.rs,
          read |-> s.read, hi |-> s.hi, contig |-> s.contig, fin |-> s.fin, limit |-> s.limit, size |-> s.size,
          pend |-> s.pend, defer |-> s.defer, rst |-> s.rst, obs |-> s.obs, sdone |-> s.sdone, srst |-> s.srst]

TOf(v) ==
    [slots |-> [k \in 1..N |-> SlotOf(v.slots[k])],
     rn |-> [c \in 0..1 |-> v.rn[c + 1]], lo |-> [c \in 0..1 |-> v.lo[c + 1]],
     rl |-> v.rl, ll |-> v.ll,
     ref |-> [j \in 1..RF |-> IF \E q \in {v.ref[k] : k \in 1..Len(v.ref)} : q[1] = j
                                  THEN LET q == CHOOSE q \in {v.ref[k] : k \in 1..Len(v.ref)} : q[1] = j
                                       IN [id |-> q[2], sent |-> q[3]]
                                  ELSE NoRef],
     ext |-> v.ext, tgt |-> v.tgt, m |-> [start |-> v.ms, bytes |-> v.mb, rate |-> v.mr]]

InitEv == /\ Ev.op = "init" /\ TOf(Ev.v) = Init0 /\ rs' = TOf(Ev.v)
EndEv == /\ Ev.op = "end" /\ rs' = rs
FrameEv == LET R == Frame(rs, Ev.id, Ev.off, Ev.len, Ev.fin, Ev.diff)
           IN /\ Ev.op = "frame" /\ R.err = Ev.err /\ TOf(Ev.v) = R.t /\ rs' = R.t
ResetEv == LET R == Reset(rs, Ev.id, Ev.code, Ev.fs)
           IN /\ Ev.op = "reset" /\ R.err = Ev.err /\ TOf(Ev.v) = R.t /\ rs' = R.t
ConsumeEv == LET R == Consume(rs, Ev.id, Ev.n, Ev.now, Ev.srtt)
             IN /\ Ev.op = "consume" /\ R.err = Ev.err /\ TOf(Ev.v) = R.t /\ rs' = R.t
PendingEv == LET P == Pending(rs)
             IN /\ Ev.op = "pending" /\ P.kind = Ev.kind /\ P.id = Ev.fid /\ P.max = Ev.max
                /\ TOf(Ev.v) = P.t /\ rs' = P.t
LostMsdEv == LET R == CtlLostMsd(rs, Ev.id, Ev.max)
             IN /\ Ev.op = "lostmsd" /\ TOf(Ev.v) = R /\ rs' = R
LostResetEv == LET R == CtlLostReset(rs, Ev.id)
               IN /\ Ev.op = "lostreset" /\ TOf(Ev.v) = R /\ rs' = R
AckedResetEv == LET R == CtlAckedReset(rs, Ev.id)
                IN /\ Ev.op = "ackedreset" /\ TOf(Ev.v) = R /\ rs' = R
OpenEv == LET R == OpenLocal(rs)
          IN /\ Ev.op = "open" /\ TOf(Ev.v) = R /\ rs' = R
AppResetEv == LET R == AppReset(rs, Ev.id, Ev.v.ext)
              IN /\ Ev.op = "appreset" /\ TOf(Ev.v) = R /\ rs' = R
FinishEv == LET R == Finish(rs, Ev.id, Ev.v.ext, Ev.done)
            IN /\ Ev.op = "finish" /\ TOf(Ev.v) = R /\ rs' = R
ExtEv == LET R == ExtTo(rs, Ev.ext)
         IN /\ Ev.op = "ext" /\ TOf(Ev.v) = R /\ rs' = R
CloseEv == LET R == CloseAll(rs, Ev.v.ext)
           IN /\ Ev.op = "close" /\ TOf(Ev.v) = R /\ rs' = R

Init == i = 1 /\ rs = Init0

Step ==
    /\ i <= Len(Trace)
    /\ Ev.t = "st"
    /\ \/ InitEv \/ EndEv \/ FrameEv \/ ResetEv \/ ConsumeEv \/ PendingEv \/ LostMsdEv \/ LostResetEv
       \/ AckedResetEv \/ OpenEv \/ AppResetEv \/ FinishEv \/ ExtEv \/ CloseEv
    /\ i' = i + 1

Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the safety facts of the model hold on every recorded state
Inv == /\ Used(rs) <= B
       /\ GU(rs) >= 0
=============================================================================
