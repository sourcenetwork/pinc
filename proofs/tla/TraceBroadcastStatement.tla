------------------------ MODULE TraceBroadcastStatement ------------------------
(***************************************************************************)
(* Trace validation of the version 2 statement codec: pinc-broadcast       *)
(* statement.rs `encode`, `content_id` and `signed_message`.               *)
(*                                                                         *)
(* The Rust test tests/trace_broadcast_statement.rs calls the real encode  *)
(* on the boundary fields of BroadcastStatement.cfg at the code's widths   *)
(* (every integer at every head boundary, topics of 0, 1, 255 and 256      *)
(* bytes, 0 to 9 parents ascending, repeated and out of order, every flag  *)
(* byte class, every algorithm) and on seeded random fields, and records   *)
(* one event per call: the fields, then the bytes written or the refusal,  *)
(* and for a statement its content id and signed message. Each event must  *)
(* equal Encode of BroadcastStatement.tla at the code's shape (32-byte ids  *)
(* and digests, 8 parents, 255-byte topics), be at most STATEMENT_MAX      *)
(* bytes, and its signed message must be the statement label followed by  *)
(* the content id. Integers are recorded as big-endian byte arrays (TLC    *)
(* integers are 32 bits wide).                                             *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds bcast/statement.ndjson.                            *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE c

S == INSTANCE BroadcastStatement WITH IdW <- 32, DigW <- 32, MaxParents <- 8, MaxTopic <- 255, Wide <- TRUE, f <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/bcast/statement.ndjson")

\* "PINC 2026 v1 statement"
Label == <<80, 73, 78, 67, 32, 50, 48, 50, 54, 32, 118, 49, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116>>

Init == c = [t |-> "root"]

FieldsOf(ev) == [alg |-> ev.alg, origin |-> ev.origin, inc |-> ev.inc, seq |-> ev.seq, topic |-> ev.topic,
                 wall |-> ev.wall, ctr |-> ev.ctr, flags |-> ev.flags, parents |-> ev.parents, body |-> ev.body]

EncEv(ev) ==
    LET r == S!Encode(FieldsOf(ev))
    IN IF "b" \in DOMAIN ev
       THEN /\ r.ok /\ r.b = ev.b /\ Len(ev.b) <= S!StatementMax
            /\ Len(ev.msg) = 54 /\ SubSeq(ev.msg, 1, 22) = Label /\ SubSeq(ev.msg, 23, 54) = ev.cid
       ELSE ~r.ok /\ r.err = ev.err

\* every event is an independent call of a pure function: a root, one state per block of 32 events, one per event
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK == c.t = "event" => (Trace[c.i].t = "st" /\ Trace[c.i].op = "encode" /\ EncEv(Trace[c.i]))
=============================================================================
