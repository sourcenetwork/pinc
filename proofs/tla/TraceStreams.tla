----------------------------- MODULE TraceStreams -----------------------------
(***************************************************************************)
(* Trace validation of the receive and credit path of the stream layer:    *)
(* vinc-transport stream/table.rs, recv.rs, flow.rs, ranges.rs and pool.rs *)
(* (Streams, Recv, Window, Meter, RangeSet, Ring over the buffer pool).    *)
(*                                                                         *)
(* The Rust test tests/trace_streams.rs drives real tables (built with the *)
(* cargo feature `trace`) over a pool of 20 chunks through seeded runs of  *)
(* the calls a connection makes: stream frames (out of order, overlapping, *)
(* past the credit, after the final size, with differing bytes, tiny ones  *)
(* that fragment the stored ranges), resets, consumes, pending control     *)
(* frames lost or acknowledged, locally opened streams with writes, sends  *)
(* and acknowledgements, other users of the pool, the close of the table.  *)
(* After every call the table shows its state; every event must be the     *)
(* step the operators of StreamsOps.tla compute from the state before it   *)
(* (Frame, Reset, Consume, Pending, CtlLostMsd, CtlLostReset,              *)
(* CtlAckedReset, CtlLostStop, CtlAckedStop, StopReq, OnStop, OpenLocal,   *)
(* CtlLostMsts, RecvMaxStreams,                                            *)
(* AppReset, Finish, ExtTo, CloseAll, and the early opens of an optimistic *)
(* dial SetEarly and Establish), with the error the call returned. The     *)
(* stream frames the test sends (next_stream_frame) are the hidden steps   *)
(* SendOut, which may end a peer stream's count, over the fields cnt and   *)
(* sfl that the test does not record; after each drain a `sent` event     *)
(* lists the streams whose frames left, and each must be one the model     *)
(* lets send (CanSend: a stream we opened only once the limit covers its   *)
(* ordinal). A `pending` event gives the control frame the table gave,     *)
(* which must be the one Pending gives (a stream's control frames wait for *)
(* the limit as its data does, #432). The state the model computes must be *)
(* the state recorded. Runs 25 to 40 are optimistic dials: early opens     *)
(* from the start, streams opened past the limit with data queued, then    *)
(* the establishment; in runs 37 to 40 the last stream opened early is     *)
(* reset at once, before the limit covers it.                              *)
(* The constants are the real ones of the test: chunks of                  *)
(* 16384 bytes, a ring of 7, 96 stored ranges, 4 slots, a pool of 20, and  *)
(* windows of 5 to 6 chunks, above the 4 the ledger counts for a stream    *)
(* that has carried no data.                                               *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds streams.ndjson.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

CONSTANTS CH, RING, RR, N, MAXREM, B, SWC, MSWC, PM, MAXOFF, RETRY, RemIds, LocIds, FIRSTK, RELEASE, PERSTREAM, DISCARD
VARIABLES i, rs
vars == <<i, rs>>

INSTANCE StreamsOps

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/streams.ndjson")
Ev == Trace[i]

\* the hidden fields of a slot (cnt, sfl: whether it counts against the peer's limit, whether its send half has
\* flushed) are not recorded; the replay carries them in rs and compares the rest
PS(r) == [id |-> r.id, open |-> r.open, held |-> r.held, rs |-> r.rs, read |-> r.read, hi |-> r.hi, contig |-> r.contig,
          fin |-> r.fin, limit |-> r.limit, size |-> r.size, pend |-> r.pend, defer |-> r.defer, rst |-> r.rst,
          obs |-> r.obs, sdone |-> r.sdone, srst |-> r.srst, stop |-> r.stop, qcode |-> r.qcode, scode |-> r.scode,
          ord |-> r.ord, m |-> r.m]
PT(t) == [t EXCEPT !.slots = [k \in 1..N |-> PS(t.slots[k])]]

SlotOf(s) ==
    IF s.id = -1 THEN PS(NewSlot)
    ELSE [id |-> s.id, open |-> s.open, held |-> {s.held[k] : k \in 1..Len(s.held)}, rs |-> s.rs,
          read |-> s.read, hi |-> s.hi, contig |-> s.contig, fin |-> s.fin, limit |-> s.limit, size |-> s.size,
          pend |-> s.pend, defer |-> s.defer, rst |-> s.rst, obs |-> s.obs, sdone |-> s.sdone, srst |-> s.srst,
          stop |-> s.stop, qcode |-> s.qcode, scode |-> s.scode, ord |-> s.ord,
          m |-> [start |-> s.ms, bytes |-> s.mb, rate |-> s.mr]]

TOf(v) ==
    [slots |-> [k \in 1..N |-> SlotOf(v.slots[k])],
     rn |-> [c \in 0..1 |-> v.rn[c + 1]], lo |-> [c \in 0..1 |-> v.lo[c + 1]],
     rl |-> v.rl, ll |-> v.ll,
     ext |-> v.ext, hw |-> v.hw,
     ad |-> [lim |-> v.ad[1], adv |-> v.ad[2], at |-> v.ad[3], pend |-> v.adp, early |-> v.early]]

InitEv == /\ Ev.op = "init" /\ TOf(Ev.v) = PT(Init0) /\ rs' = Init0
EndEv == /\ Ev.op = "end" /\ rs' = rs
FrameEv == LET R == Frame(rs, Ev.id, Ev.off, Ev.len, Ev.fin, Ev.diff)
           IN /\ Ev.op = "frame" /\ R.err = Ev.err /\ TOf(Ev.v) = PT(R.t) /\ rs' = R.t
ResetEv == LET R == Reset(rs, Ev.id, Ev.code, Ev.fs)
           IN /\ Ev.op = "reset" /\ R.err = Ev.err /\ TOf(Ev.v) = PT(R.t) /\ rs' = R.t
ConsumeEv == LET R == Consume(rs, Ev.id, Ev.n, Ev.now, Ev.srtt)
             IN /\ Ev.op = "consume" /\ R.err = Ev.err /\ TOf(Ev.v) = PT(R.t) /\ rs' = R.t
PendingEv == LET P == Pending(rs)
             IN /\ Ev.op = "pending" /\ P.kind = Ev.kind /\ P.id = Ev.fid /\ P.max = Ev.max
                /\ TOf(Ev.v) = PT(P.t) /\ rs' = P.t
LostMsdEv == LET R == CtlLostMsd(rs, Ev.id, Ev.max)
             IN /\ Ev.op = "lostmsd" /\ TOf(Ev.v) = PT(R) /\ rs' = R
LostMstsEv == LET R == CtlLostMsts(rs, Ev.limit)
              IN /\ Ev.op = "lostmsts" /\ TOf(Ev.v) = PT(R) /\ rs' = R
MaxStreamsEv == LET R == RecvMaxStreams(rs, Ev.limit)
                IN /\ Ev.op = "maxstreams" /\ TOf(Ev.v) = PT(R) /\ rs' = R
LostResetEv == LET R == CtlLostReset(rs, Ev.id)
               IN /\ Ev.op = "lostreset" /\ TOf(Ev.v) = PT(R) /\ rs' = R
AckedResetEv == LET R == CtlAckedReset(rs, Ev.id)
                IN /\ Ev.op = "ackedreset" /\ TOf(Ev.v) = PT(R) /\ rs' = R
LostStopEv == LET R == CtlLostStop(rs, Ev.id)
              IN /\ Ev.op = "loststop" /\ TOf(Ev.v) = PT(R) /\ rs' = R
AckedStopEv == LET R == CtlAckedStop(rs, Ev.id)
               IN /\ Ev.op = "ackedstop" /\ TOf(Ev.v) = PT(R) /\ rs' = R
StopReqEv == LET R == StopReq(rs, Ev.id, Ev.code)
             IN /\ Ev.op = "stopreq" /\ R.err = Ev.err /\ TOf(Ev.v) = PT(R.t) /\ rs' = R.t
OnStopEv == LET R == OnStop(rs, Ev.id, Ev.code, Ev.v.ext)
            IN /\ Ev.op = "onstop" /\ R.err = Ev.err /\ R.fresh = Ev.fresh /\ TOf(Ev.v) = PT(R.t) /\ rs' = R.t
OpenEv == LET R == OpenLocal(rs)
          IN /\ Ev.op = "open" /\ TOf(Ev.v) = PT(R) /\ rs' = R
\* the dial turns early opens on; its limit of 0 for the peer's record raises nothing
EarlyEv == LET R == SetEarly(RecvMaxStreams(rs, 0), TRUE)
           IN /\ Ev.op = "early" /\ TOf(Ev.v) = PT(R) /\ rs' = R
EstablishEv == LET R == Establish(rs, Ev.limit)
               IN /\ Ev.op = "establish" /\ TOf(Ev.v) = PT(R) /\ rs' = R
\* the streams whose frames left in a drain: each held a slot the model lets send
SentEv == /\ Ev.op = "sent"
          /\ \A k \in 1..Len(Ev.ids) : FindSlot(rs, Ev.ids[k]) # 0 /\ CanSend(rs, FindSlot(rs, Ev.ids[k]))
          /\ TOf(Ev.v) = PT(rs) /\ rs' = rs
AppResetEv == LET R == AppReset(rs, Ev.id, Ev.code, Ev.v.ext)
              IN /\ Ev.op = "appreset" /\ TOf(Ev.v) = PT(R) /\ rs' = R
FinishEv == LET R == Finish(rs, Ev.id, Ev.v.ext, Ev.done)
            IN /\ Ev.op = "finish" /\ TOf(Ev.v) = PT(R) /\ rs' = R
ExtEv == LET R == ExtTo(rs, Ev.ext)
         IN /\ Ev.op = "ext" /\ TOf(Ev.v) = PT(R) /\ rs' = R
CloseEv == LET R == CloseAll(rs, Ev.v.ext)
           IN /\ Ev.op = "close" /\ TOf(Ev.v) = PT(R) /\ rs' = R

Init == i = 1 /\ rs = Init0

Step ==
    /\ i <= Len(Trace)
    /\ Ev.t = "st"
    /\ \/ InitEv \/ EndEv \/ FrameEv \/ ResetEv \/ ConsumeEv \/ PendingEv \/ LostMsdEv \/ LostMstsEv \/ MaxStreamsEv \/ LostResetEv
       \/ AckedResetEv \/ LostStopEv \/ AckedStopEv \/ StopReqEv \/ OnStopEv \/ OpenEv \/ AppResetEv \/ FinishEv \/ ExtEv \/ CloseEv
       \/ EarlyEv \/ EstablishEv \/ SentEv
    /\ i' = i + 1

\* the calls the test makes without a recorded event of their own: a stream frame leaves (next_stream_frame), which may
\* end a peer stream's count (SendOut); any slot, and the send half's end has gone or not
Hidden == /\ i <= Len(Trace)
          /\ \E k \in 1..N, f \in BOOLEAN : rs' = SendOut(rs, k, f)
          /\ i' = i
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Hidden \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the safety facts of the model hold on every recorded state
Inv == /\ Used(rs) <= B
       /\ GU(rs) >= 0
=============================================================================
