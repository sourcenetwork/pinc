---------------------------- MODULE TraceStreamSend ----------------------------
(***************************************************************************)
(* Trace validation of the send half of a stream: pinc-transport           *)
(* stream/send.rs (Send<S, C>) over its ring of chunks and its range sets. *)
(*                                                                         *)
(* The Rust test tests/trace_stream_send.rs drives real send halves (the   *)
(* probe SendProbe of stream/trace.rs, cargo feature `trace`) over a pool  *)
(* of 4 chunks and a ring of 3 through seeded runs and scripted runs of    *)
(* the calls the stream table makes: writes against the window, the ring,  *)
(* the pool and the send buffer cap, finish, a source of application       *)
(* storage (whole or short), resets (the application's, and the one a stop *)
(* request from the peer makes), window raises, frames taken for           *)
(* retransmission and for fresh data, copies of fresh and stale frames and *)
(* of frames cut by clip, losses and acknowledgements in any order (past   *)
(* 16 lost and 64 acknowledged ranges), the reset frame taken, lost and    *)
(* acknowledged, and other users of the pool. After every call the half    *)
(* shows its state; every event must be the step the operators of          *)
(* StreamSendOps.tla compute from the state before it, with the result the *)
(* call returned, and every copy must read only slots that hold the chunk  *)
(* its offsets name, never a released one (ReadsOwnOf), every write must   *)
(* stay in its own slots, a retransmitted frame must start at the          *)
(* acknowledged prefix and every frame with the end marker and every reset *)
(* frame must carry the first final size told. The ghosts rel and told are *)
(* not recorded: the replay computes them.                                 *)
(*                                                                         *)
(* The constants are the real ones of the test: chunks of 16384 bytes, a   *)
(* ring of 3, a pool of 4, 16 lost and 64 acknowledged ranges. Every       *)
(* recorded number is below 2^31 (TLC's integers): the calls at MAX_OFFSET *)
(* and at u64::MAX are asserted by the test, not recorded, and MAXOFF here *)
(* only has to lie above every recorded offset.                            *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds stream_send.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

CONSTANTS CH, RING, B, LR, AR, MAXOFF
VARIABLES i, h
vars == <<i, h>>

INSTANCE StreamSendOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/stream_send.ndjson")
Ev == Trace[i]

\* the state the probe shows, as the model computes it
PV(s) == [open |-> s.open, src |-> s.src, srcon |-> s.srcon, wr |-> s.wr, smax |-> s.smax, limit |-> s.limit,
          lost |-> s.lost, acked |-> s.acked, ap |-> s.ap, fs |-> s.fs, fin |-> s.fin, rst |-> s.rst,
          rcode |-> s.rcode, rfs |-> s.rfs, cut |-> s.cut, ext |-> s.ext, held |-> WindowHeld(s),
          avail |-> AvailC(s), buffered |-> Buffered(s), wants |-> Wants(s), flushed |-> Flushed(s),
          done |-> IsDone(s), canstop |-> CanStop(s), ctlpend |-> CtlPending(s), vlost |-> ViewLost(s),
          vsent |-> s.smax, fdone |-> FinDone(s)]
\* the recorded view
VOf(v) == [open |-> v.open, src |-> v.src, srcon |-> v.srcon, wr |-> v.wr, smax |-> v.smax, limit |-> v.limit,
           lost |-> v.lost, acked |-> v.acked, ap |-> v.ap, fs |-> v.fs, fin |-> v.fin, rst |-> v.rst,
           rcode |-> v.rcode, rfs |-> v.rfs, cut |-> v.cut, ext |-> v.ext, held |-> {v.held[k] : k \in 1..Len(v.held)},
           avail |-> v.avail, buffered |-> v.buffered, wants |-> v.wants, flushed |-> v.flushed,
           done |-> v.done, canstop |-> v.canstop, ctlpend |-> v.ctlpend, vlost |-> v.vlost,
           vsent |-> v.vsent, fdone |-> v.fdone]
Same(s) == VOf(Ev.v) = PV(s) /\ h' = s

NewEv == Ev.op = "new" /\ Same(IF Ev.open THEN Open(New, Ev.limit) ELSE New)
WriteEv == LET R == Write(h, Ev.want, Ev.room)
           IN /\ Ev.op = "write" /\ R.err = Ev.err /\ R.n = Ev.n /\ ~R.alias /\ Same(R.s)
FinishEv == LET R == Finish(h) IN Ev.op = "finish" /\ R.err = Ev.err /\ Same(R.s)
SourceEv == LET R == OpenSource(h, Ev.len, Ev.av) IN Ev.op = "source" /\ R.err = Ev.err /\ Same(R.s)
ResetEv == LET R == Reset(h, Ev.code) IN Ev.op = "reset" /\ R.err = Ev.err /\ Same(R.s)
RaiseEv == Ev.op = "raise" /\ Same(RaiseLimit(h, Ev.limit))
NextEv == LET R == NextFrame(h, Ev.retx, Ev.budget)
          IN /\ Ev.op = "next" /\ R.some = Ev.some
             /\ R.some => (R.off = Ev.off /\ R.len = Ev.len /\ R.fin = Ev.fin)
             /\ (R.some /\ Ev.retx) => R.off >= h.ap
             /\ R.fin => (R.off + R.len = h.fs /\ (h.told = -1 \/ h.told = h.fs))
             /\ Same(R.s)
CopyEv == LET R == CopyOut(h, Ev.off, Ev.len, Ev.fin, Ev.dst >= Ev.len)
          IN /\ Ev.op = "copy" /\ R.err = Ev.err /\ (R.err = "ok" => R.got = Ev.got)
             /\ ReadsOwnOf(h, R) /\ Same(R.s)
LostEv == LET R == OnLost(h, Ev.off, Ev.len, Ev.fin) IN Ev.op = "lost" /\ R.w = Ev.w /\ Same(R.s)
AckedEv == LET R == OnAcked(h, Ev.off, Ev.len, Ev.fin) IN Ev.op = "acked" /\ R.w = Ev.w /\ Same(R.s)
IsAckedEv == Ev.op = "isacked" /\ IsAcked(h, Ev.off, Ev.len) = Ev.res /\ Same(h)
ClipEv == Ev.op = "clip" /\ Clip(h, Ev.off) = Ev.res /\ Same(h)
TakeCtlEv == LET C == TakeControl(h)
             IN /\ Ev.op = "takectl" /\ C.some = Ev.some
                /\ C.some => (C.code = Ev.code /\ C.fs = Ev.fs /\ (h.told = -1 \/ h.told = C.fs))
                /\ Same(C.s)
CtlLostEv == Ev.op = "ctllost" /\ Same(ControlLost(h, Ev.code, Ev.fs))
CtlAckedEv == Ev.op = "ctlacked" /\ Same(ResetAcked(h))
ExtEv == Ev.op = "ext" /\ Same(ExtTo(h, Ev.n))

Init == i = 1 /\ h = New

Step ==
    /\ i <= Len(Trace)
    /\ Ev.t = "st"
    /\ \/ NewEv \/ WriteEv \/ FinishEv \/ SourceEv \/ ResetEv \/ RaiseEv \/ NextEv \/ CopyEv \/ LostEv \/ AckedEv
       \/ IsAckedEv \/ ClipEv \/ TakeCtlEv \/ CtlLostEv \/ CtlAckedEv \/ ExtEv
    /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the stated invariants hold on every replayed state
Inv == /\ WellFormedOf(h) /\ PoolOf(h) /\ LostBelowSentOf(h) /\ ApIsPrefixOf(h)
       /\ CreditSpentOf(h) /\ SentInWindowOf(h) /\ ResetInWindowOf(h) /\ EndWithinFinalOf(h)
       /\ HeldFromPrefixOf(h) /\ BytesHeldOf(h)
=============================================================================
