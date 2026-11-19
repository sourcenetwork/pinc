----------------------------- MODULE TraceEncoder -----------------------------
(***************************************************************************)
(* Trace validation of pinc-dag RangeEncoder, encoded_len and encode_range *)
(* (tree/encode.rs).                                                       *)
(*                                                                         *)
(* The Rust test tests/trace_tla.rs records, for layouts from 0 to u64::MAX *)
(* bytes and every group size of the boundary set (every pair of the       *)
(* interesting offsets of the small layouts, narrow ranges of the big      *)
(* ones, random ranges), the complete step list of the public              *)
(* `RangeEncoder` with the result of `encoded_len` (enc), and the results  *)
(* of `encode_range` into output buffers of every size around the stream   *)
(* length, with a genuine value and outboard, a reversed range, a range     *)
(* past the end and an outboard of the wrong size (encout). Numbers that   *)
(* are u64 are four 16-bit limbs. Each recorded step list must equal the   *)
(* run of the iterator of Encoder.tla, the recorded `encoded_len` the      *)
(* fold of Encoder.tla, and each `encode_range` result the one of          *)
(* EncodeRange (on a 64-bit usize).                                        *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds tla/encoder.ndjson    *)
(* and tla/encout.ndjson.                                                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE c

E == INSTANCE Encoder WITH WalkK <- 0, c <- 0
U == INSTANCE U64
L == INSTANCE Layout WITH SmallLen <- 0, PreN <- 0, c <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/tla/encoder.ndjson")
         \o ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/tla/encout.ndjson")

Init == c = [t |-> "root"]

StepOfJson(st) ==
    IF st[1] = "p" THEN [k |-> "p", off |-> U!FromLimbs(st[2])]
    ELSE [k |-> "g", off |-> U!FromLimbs(st[2]), len |-> U!FromLimbs(st[3])]

EncEv(ev) ==
    LET len == U!FromLimbs(ev.len)
        s == U!FromLimbs(ev.s)
        e == U!FromLimbs(ev.e)
        r == E!Run(len, ev.log, s, e)
    IN IF "err" \in DOMAIN ev
       THEN IF ev.err = "range" THEN r = [err |-> "range"]
            ELSE /\ r.steps = [k \in 1..Len(ev.steps) |-> StepOfJson(ev.steps[k])]
                 /\ ~E!EncodedLenOf(r.steps).ok
       ELSE /\ ~("err" \in DOMAIN r)
            /\ r.steps = [k \in 1..Len(ev.steps) |-> StepOfJson(ev.steps[k])]
            /\ r.max <= 55
            /\ E!EncodedLenOf(r.steps) = [ok |-> TRUE, v |-> U!FromLimbs(ev.el)]

OutEv(ev) ==
    LET len == U!FromLimbs(ev.len)
        ob == IF "oblen" \in DOMAIN ev THEN U!W(ev.oblen) ELSE L!OutboardSize(len, ev.log)
        r == E!EncodeRange(len, ev.log, U!FromLimbs(ev.s), U!FromLimbs(ev.e), ob, U!W(ev.olen), 64)
    IN CASE ev.res = "ok" -> r = [ok |-> U!W(ev.n)]
         [] ev.res = "small" -> r = [err |-> "small"]
         [] ev.res = "range" -> r = [err |-> "range"]
         [] ev.res = "outboard" -> r = [err |-> "outboard"]

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. TLC's count of distinct states is the number of events plus the blocks plus one. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

(* every recorded event equals the specification *)
EventsOK == c.t = "event" => IF Trace[c.i].t = "enc" THEN EncEv(Trace[c.i]) ELSE OutEv(Trace[c.i])
=============================================================================
