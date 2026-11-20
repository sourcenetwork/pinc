---------------------------- MODULE TraceHubCodec ----------------------------
(***************************************************************************)
(* Trace validation of the hub stream codec of pinc-membership (codec.rs). *)
(*                                                                         *)
(* The Rust test tests/trace_membership.rs (part codec.rs) runs the real   *)
(* Frame::parse, Frame::read and Frame::encode on valid frames of every    *)
(* kind and boundary, on every proper cut of them, with trailing bytes,    *)
(* with single bytes changed, on streams with a partial tail, on prefixes  *)
(* that name a body above the limit, on encodings into buffers too small   *)
(* and on seeded random garbage, and records one event per call: the bytes *)
(* in and the result (the frame, or the refusal class). Each event must    *)
(* equal the result of the Decode, Read or EncodeCap operator of           *)
(* HubCodec.tla, whose properties (RoundTrip, Unique, Strict, Classes,     *)
(* Stream, Buffers) TLC checks in the HubCodec_*.cfg configs. The 64-bit  *)
(* fields are                                                              *)
(* recorded as four 16-bit limbs (TLC integers are 32 bits wide).          *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds mcodec.ndjson.        *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

H == INSTANCE HubCodec WITH f <- 0, Part <- "hello"
U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/mcodec.ndjson")

Init == c = [t |-> "root"]

W(l) == U!FromLimbs(l)
EntryJ(x) == [m |-> x.m, inc |-> W(x.inc), ver |-> x.ver, th |-> x.th, a |-> x.a]

FrameOf(j) ==
    CASE j.k = "hello" -> [k |-> "hello", inc |-> W(j.inc), ver |-> j.ver, th |-> j.th, snap |-> j.snap, homed |-> j.homed]
      [] j.k = "ack" -> [k |-> "ack"]
      [] j.k = "probe" -> [k |-> "probe"]
      [] j.k = "delta" -> [k |-> "delta", e |-> EntryJ(j.e)]
      [] j.k = "snap" -> [k |-> "snap", part |-> j.part, more |-> j.more, es |-> [i \in 1..Len(j.es) |-> EntryJ(j.es[i])]]
      [] j.k = "down" ->
           [k |-> "down", m |-> j.m, inc |-> W(j.inc), sil |-> W(j.sil),
            pr |-> [i \in 1..Len(j.pr) |-> [age |-> W(j.pr[i].age), path |-> j.pr[i].path]]]
      [] j.k = "other" -> [k |-> "other", ty |-> j.ty, topic |-> j.topic, rest |-> j.rest]

ParseEv(ev) ==
    IF "ok" \in DOMAIN ev THEN H!Decode(ev.b) = H!Ok(FrameOf(ev.ok))
    ELSE H!Decode(ev.b) = H!Err(ev.err)

ReadEv(ev) ==
    IF "ok" \in DOMAIN ev THEN H!Read(ev.b) = [err |-> "ok", f |-> FrameOf(ev.ok), n |-> ev.n]
    ELSE IF "more" \in DOMAIN ev THEN H!Read(ev.b) = [err |-> "more"]
    ELSE H!Read(ev.b) = H!Err(ev.err)

EncEv(ev) ==
    LET r == H!EncodeCap(FrameOf(ev.f), ev.cap)
    IN IF "b" \in DOMAIN ev THEN r.err = "ok" /\ r.bytes = ev.b ELSE r = H!Err(ev.err)

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK ==
    c.t = "event" =>
        LET ev == Trace[c.i]
        IN IF ev.op = "parse" THEN ParseEv(ev) ELSE IF ev.op = "read" THEN ReadEv(ev) ELSE EncEv(ev)
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
