----------------------------- MODULE TraceVarint -----------------------------
(***************************************************************************)
(* Trace validation of pinc-wire varint (varint.rs).                       *)
(*                                                                         *)
(* The Rust test tests/trace_tla.rs runs the real `encode` and `decode` on *)
(* the boundary values of every width (2^j - 1, 2^j, 2^j + 1), the values  *)
(* below 300, random values, every buffer size 0..10, every byte string of *)
(* up to 1 byte and of up to 4 bytes over the class alphabet, the runs of  *)
(* continuation bytes with every terminator, every encoding with every cut *)
(* and rest, and random byte strings, and records one event per call: a    *)
(* value as four 16-bit limbs (TLC integers are 32 bits wide), the buffer  *)
(* size or the input, and the result. Each event must equal the result of  *)
(* the Encode or Decode operator of Varint.tla, whose properties (EncodeOK *)
(* and DecodeOK) TLC checks exhaustively in Varint.cfg.                    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds tla/varint.ndjson.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

V == INSTANCE Varint WITH SmallMax <- 0, c <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/tla/varint.ndjson")

Init == c = [t |-> "root"]

EncEv(ev) ==
    LET v == V!U!FromLimbs(ev.v)
        r == V!Encode(v, ev.cap)
    IN IF "ok" \in DOMAIN ev
       THEN r.kind = "ok" /\ r.bytes = ev.ok
       ELSE /\ r.kind = ev.err
            /\ (ev.err = "small" => r.needed = ev.needed)

DecEv(ev) ==
    LET r == V!Decode(ev.in)
    IN IF "ok" \in DOMAIN ev
       THEN r.kind = "ok" /\ r.v = V!U!FromLimbs(ev.ok[1]) /\ r.n = ev.ok[2]
       ELSE r.kind = ev.err

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. TLC's count of distinct states is the number of events plus the blocks plus one. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

(* every recorded event equals the specification *)
EventsOK == c.t = "event" => IF Trace[c.i].t = "venc" THEN EncEv(Trace[c.i]) ELSE DecEv(Trace[c.i])
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
