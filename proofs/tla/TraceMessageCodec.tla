-------------------------- MODULE TraceMessageCodec --------------------------
(***************************************************************************)
(* Trace validation of the handshake message codec of pinc-security        *)
(* message.rs (with TicketBatch of tickets.rs) against MessageCodec.tla.   *)
(*                                                                         *)
(* The Rust test tests/trace_message.rs runs the real MessageType::of, the *)
(* parse of Initial, Reject (as PrekeyReject and as ResumeReject), Reply,  *)
(* Finish, ResumeHello, ResumeReply and IdSig (with and without the credit *)
(* record), and their write into buffers of the exact size, one byte less  *)
(* and none, on valid messages of every kind and boundary and seeded       *)
(* random ones, on cuts of them, with a trailing byte, with single bytes   *)
(* changed, on seeded random garbage, and on fields outside the documented *)
(* ranges. It records one event per call:                                  *)
(*   type   the bytes and the result of MessageType::of: TypeOf;           *)
(*   parse  the parser (kind, the type of a reject, whether a plaintext    *)
(*          has the credit record), the bytes and the result: Parse;       *)
(*   write  the message, the size of the buffer and the result: EncodeCap. *)
(* A result is a record as the model's: res is "ok" (with the message, the *)
(* type or the bytes), "truncated" or "small" (with the bytes missing),    *)
(* "unexpected" (with the reason the code gives) or "overflow". Each event *)
(* must equal the model's result, field by field.                          *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds message.ndjson.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE c

M == INSTANCE MessageCodec WITH msg <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/message.ndjson")

Init == c = [t |-> "root"]

Ok(ev) ==
    CASE ev.op = "type" -> ev.r = M!TypeOf(ev.b)
      [] ev.op = "parse" -> ev.r = M!Parse(ev.kind, ev.b, ev.ty, ev.wc)
      [] ev.op = "write" -> ev.r = M!EncodeCap(ev.m, ev.cap)
      [] OTHER -> FALSE

(* Every event is an independent call of a pure function: the root state has one successor per block of 32 events
   and a block one per event, which TLC checks on all workers at once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK == c.t = "event" => Ok(Trace[c.i])
=============================================================================
