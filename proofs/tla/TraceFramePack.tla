--------------------------- MODULE TraceFramePack ---------------------------
(***************************************************************************)
(* Trace validation of the VINCER packet builder: vinc-transport           *)
(* conn/send.rs.                                                           *)
(*                                                                         *)
(* The Rust test tests/trace_framepack.rs runs pairs of real connections   *)
(* (bulk transfers at several urgencies with and without loss and with     *)
(* GSO, datagrams and extension frames between the stream data, answered   *)
(* requests, resets and stop requests, a second path, sleep and wake, a    *)
(* keepalive, key rolls, tickets and READY, a resumption with 0-RTT        *)
(* packets, a lost tail, path MTU probes, tail repairs and CLOSE) and      *)
(* records every packet they seal through the trace view of the builder,   *)
(* and calls implicit_stream_len and put_stream_header directly.           *)
(*                                                                         *)
(* A packet (op "pkt") must be one the operators of FramePackOps.tla       *)
(* allow: the frames of the fill parse with no error, none is PADDING or   *)
(* CLOSE (CLOSE alone in the CLOSE packet) and none leaves its length out, *)
(* their kinds come in the order of the fill's slots for its mode; the     *)
(* place kept is the last frame exactly when a normal fill ends with a     *)
(* STREAM frame (where the code keeps it), with the size of the header     *)
(* before the length; Finish of the fill is the payload sealed, and that   *)
(* payload parses into the frames written, the last without its length     *)
(* when it was dropped, then one PADDING frame for the padding. A direct   *)
(* call (op "imp", "hdr") must give what ImplicitStreamLen or              *)
(* PutStreamHeader give.                                                   *)
(*                                                                         *)
(* This file reads framepack.ndjson, the events whose numbers stay below   *)
(* 2^28; the Lean replay also reads framepack_wide.ndjson (stream ids,     *)
(* offsets and lengths up to 2^64 - 1).                                    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds framepack.ndjson.     *)
(***************************************************************************)
EXTENDS FramePackOps, TLC, Json, IOUtils

VARIABLE c

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/framepack.ndjson")

Init == c = [t |-> "root"]

\* where the code keeps the place of the last STREAM frame: a normal fill that ends with one
HintOf(mode, b, fs) ==
    IF mode = "normal" /\ Len(fs) > 0 /\ fs[Len(fs)].k = "Stream"
    THEN LET l == fs[Len(fs)] IN
         <<Len(b) - EncodedLen(l), StreamOverhead(l.id, l.off, Len(l.data), FALSE) - VLen(Len(l.data))>>
    ELSE <<>>

PktOK(ev) ==
    LET it == Iter(ev.frames)
        fs == it.fs
        fin == Finish(ev.frames, ev.hint, ev.min) IN
    /\ it.e = "none" /\ Len(fs) > 0
    /\ \A i \in 1..Len(fs) : /\ fs[i].k # "Padding"
                             /\ ~(fs[i].k \in {"Stream", "Datagram"} /\ fs[i].imp)
                             /\ fs[i].k = "Close" <=> ev.mode = "close"
    /\ Ordered(ev.mode, fs)
    /\ ev.kind = "zrtt" => ev.client
    /\ ev.hint = HintOf(ev.mode, ev.frames, fs)
    /\ fin.ok
    /\ fin.pay = ev.pay
    /\ Iter(ev.pay) = [fs |-> Expected(fs, fin), e |-> "none", n |-> 0]

ImpOK(ev) ==
    LET i == ImplicitStreamLen(ev.b, ev.at, ev.head) IN
    IF ev.ok THEN i.ok /\ i.n = ev.n /\ i.out = ev.out ELSE ~i.ok /\ ev.out = ev.b

HdrOK(ev) ==
    LET h == PutStreamHeader(ev.cap, ev.id, ev.off, ev.len, ev.fin) IN
    /\ h.ok = ev.ok
    /\ h.w \o [i \in 1..(ev.cap - Len(h.w)) |-> 170] = ev.b

EventOK(ev) ==
    /\ ev.t = "txpk"
    /\ CASE ev.op = "pkt" -> PktOK(ev)
         [] ev.op = "imp" -> ImpOK(ev)
         [] ev.op = "hdr" -> HdrOK(ev)

(* Every event is an independent call, so the events are the states of one machine: the root state has one
   successor per block of 32 events and a block one per event, which TLC checks on all workers at once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK == c.t = "event" => EventOK(Trace[c.i])
=============================================================================
