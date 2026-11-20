--------------------------- MODULE TraceDagCborLen ---------------------------
(***************************************************************************)
(* Trace validation of pinc-dag cbor_len.rs (head_len, text_len, cid_len). *)
(*                                                                         *)
(* The Rust test tests/trace_dag_sizes.rs runs the real functions (through *)
(* the probe pinc_dag::cbor_len_trace of the `trace` feature) on every     *)
(* argument below 300, on 2^j - 1, 2^j and 2^j + 1 for every j, and on     *)
(* seeded random values, and for arguments below 300 also runs the         *)
(* pinc-wire encoder on the same piece. One event per argument:            *)
(*   head: the argument a, head_len(a), the bytes Encoder::unsigned writes *)
(*         and the lengths unsigned, negative, array and map write;        *)
(*   text: n, text_len(n) and, for n below 300, what Encoder::text and     *)
(*         Encoder::bytes write;                                           *)
(*   cid:  n, cid_len(n) and, for n below 300, what Encoder::tag_cid       *)
(*         writes for n bytes.                                             *)
(* A u64 or usize is four 16-bit limbs. Each event must equal the          *)
(* operators of DagCborLen.tla, whose properties TLC checks in             *)
(* DagCborLen.cfg.                                                         *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds tla/dag_sizes.ndjson.                              *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

L == INSTANCE DagCborLen WITH SmallMax <- 0, c <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/tla/dag_sizes.ndjson")

W(l) == L!U!FromLimbs(l)

HeadEv(ev) ==
    LET a == W(ev.a) IN
    /\ L!HeadLen(a) = ev.len
    /\ L!EncHead(0, a) = ev.bytes
    /\ ev.w = <<Len(L!EncHead(0, a)), Len(L!EncHead(1, a)), Len(L!EncHead(4, a)), Len(L!EncHead(5, a))>>

TextEv(ev) ==
    LET n == W(ev.n) IN
    /\ L!TextLen(n) = W(ev.len)
    /\ ev.w # <<>> => W(ev.w[1]) = L!WrittenString(3, n) /\ W(ev.w[2]) = L!WrittenString(2, n)

CidEv(ev) ==
    LET n == W(ev.n) IN
    /\ L!CidLen(n) = W(ev.len)
    /\ ev.w # <<>> => W(ev.w[1]) = L!WrittenCid(n)

Init == c = [t |-> "root"]

(* the house machine: the root has one successor per block of 32 events, a block one per event *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK ==
    c.t = "event" =>
        CASE Trace[c.i].t = "head" -> HeadEv(Trace[c.i])
          [] Trace[c.i].t = "text" -> TextEv(Trace[c.i])
          [] Trace[c.i].t = "cid" -> CidEv(Trace[c.i])
          [] OTHER -> FALSE
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
