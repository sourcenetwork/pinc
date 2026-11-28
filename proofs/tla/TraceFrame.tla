----------------------------- MODULE TraceFrame -----------------------------
(***************************************************************************)
(* Trace validation of the PINCER frame codecs: pinc-transport frame/.     *)
(*                                                                         *)
(* The Rust test tests/trace_frame.rs calls the real Frame::decode,        *)
(* Frame::write, Frame::encoded_len, FrameIter, write_ack, ack_len,        *)
(* Ack::ranges, stream_overhead and datagram_overhead on every frame kind  *)
(* at the varint boundaries, into buffers of every nearby size, on every   *)
(* cut, with single bytes changed, with bytes appended, on garbage behind  *)
(* every type and on payloads of several frames, and records one event per *)
(* call: the bytes or the frame in, and the frame, the bytes consumed, the *)
(* bytes written or the error out. Each event must equal what the          *)
(* operators of FrameOps.tla give, whose properties TLC checks in          *)
(* Frame.cfg, Frame_acks.cfg and Frame_bytes.cfg.                          *)
(*                                                                         *)
(* This file reads frame.ndjson, the calls whose numbers stay below 2^28   *)
(* (no varint of more than four bytes anywhere in the input); the Lean     *)
(* replay also reads frame_wide.ndjson, with numbers up to 2^64 - 1, the   *)
(* real 2^63 and 2^62 - 1 and varints of nine bytes and more.              *)
(*                                                                         *)
(* The test records a REKEY frame without its roll count. A request it   *)
(* writes takes the roll count its written bytes carry, or for a refused   *)
(* write the least count of the length its encoded_len gives (the refusal *)
(* depends on that length only); an answer writes none and has 0 (Rolled). *)
(* A frame it decodes is compared without the roll count (Unrolled), which *)
(* is checked through the bytes the decode consumed.                       *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds frame.ndjson.         *)
(***************************************************************************)
EXTENDS FrameOps, TLC, Json, IOUtils, TraceEnd

VARIABLE c

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/frame.ndjson")

Init == c = [t |-> "root"]

\* the frame of an enc event as the test wrote it, with the roll count of a REKEY request; a model frame as the test
\* records it (no roll count)
RollOf(ev) == IF ev.ok THEN Decode(ev.b).v.roll ELSE IF ev.len - 34 <= 1 THEN 0 ELSE 128 ^ (ev.len - 35)
Rolled(ev) ==
    LET f == ev.f IN
    IF f.k = "Rekey"
    THEN [k |-> f.k, ans |-> f.ans, sh |-> f.sh, echo |-> f.echo, spn |-> f.spn, roll |-> IF f.ans THEN 0 ELSE RollOf(ev)]
    ELSE f
Unrolled(f) == IF f.k = "Rekey" THEN [k |-> f.k, ans |-> f.ans, sh |-> f.sh, echo |-> f.echo, spn |-> f.spn] ELSE f

\* the result of a write against the event: the same bytes, or the same refusal
Res(r, ev) == IF ev.ok THEN r.ok /\ r.v = ev.b ELSE ~r.ok /\ r.e = ev.err /\ r.n = ev.en

DecOK(ev) ==
    LET d == Decode(ev.b) IN
    IF ev.ok
    THEN /\ d.ok
         /\ Unrolled(d.v) = ev.f
         /\ Len(ev.b) - Len(d.r) = ev.n
         /\ ev.f.k = "Ack" => AckRanges(d.v) = ev.rg
    ELSE ~d.ok /\ d.e = ev.err /\ d.n = ev.en

EncOK(ev) == EncodedLen(Rolled(ev)) = ev.len /\ Res(Write(ev.cap, Rolled(ev)), ev)

AckOK(ev) ==
    /\ Res(WriteAck(ev.cap, ev.rs), ev)
    /\ LET l == AckLen(ev.rs) IN IF ev.lok THEN l.ok /\ l.v = ev.len ELSE ~l.ok /\ l.e = ev.lerr

IterOK(ev) ==
    LET it == Iter(ev.b) IN
    /\ Len(it.fs) = Len(ev.fs) /\ \A j \in 1..Len(it.fs) : Unrolled(it.fs[j]) = ev.fs[j]
    /\ it.e = ev.e /\ it.n = ev.en

OvhOK(ev) ==
    /\ StreamOverhead(ev.id, ev.off, ev.dlen, ev.imp) = ev.so
    /\ DatagramOverhead(ev.dlen, ev.imp) = ev.do

EventOK(ev) ==
    /\ ev.t = "txfr"
    /\ CASE ev.op = "dec" -> DecOK(ev)
         [] ev.op = "enc" -> EncOK(ev)
         [] ev.op = "ack" -> AckOK(ev)
         [] ev.op = "iter" -> IterOK(ev)
         [] ev.op = "ovh" -> OvhOK(ev)

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK == c.t = "event" => EventOK(Trace[c.i])
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
