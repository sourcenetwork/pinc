--------------------------- MODULE TraceWireCursor ---------------------------
(***************************************************************************)
(* Trace validation of the bounded cursors of pinc-wire, Reader            *)
(* (reader.rs) and Writer (writer.rs).                                     *)
(*                                                                         *)
(* The Rust test tests/trace_wire_cursor.rs runs the real Reader and       *)
(* Writer: every seed of WireCursor.cfg (a read_bytes(p) or a put_slice of *)
(* p bytes, then each call of the domain) and seeded random runs, and      *)
(* records one event per run in tla/wire_cursor.ndjson under PINC_TRACE_DIR:   *)
(* "rrun" (the input and every call with its result, position and         *)
(* remaining after it) and "wrun" (the buffer size, every call with its    *)
(* result, written() and remaining() after it, and the whole buffer once   *)
(* the writer is dropped; the buffer starts filled with Fill). Each run    *)
(* must be what the operators of WireCursorOps.tla compute, call for call, *)
(* from a fresh cursor, and a cell the model never wrote must still hold   *)
(* Fill (WireCursor.tla states the properties of those operators). A u64   *)
(* or usize is four 16-bit limbs (TLC integers are 32 bits wide).          *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR.     *)
(***************************************************************************)
EXTENDS WireCursorOps, Json, IOUtils

VARIABLE c

Fill == 170
Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/tla/wire_cursor.ndjson")

Init == c = [t |-> "root"]

ToRCall(e) ==
    CASE e.op = "peek" -> [op |-> "peek"]
      [] e.op = "bytes" -> [op |-> "bytes", n |-> U!FromLimbs(e.n)]
      [] e.op = "u8" -> [op |-> "uN", k |-> 1]
      [] e.op = "u16" -> [op |-> "uN", k |-> 2]
      [] e.op = "u32" -> [op |-> "uN", k |-> 4]
      [] e.op = "u64" -> [op |-> "uN", k |-> 8]
      [] e.op = "varint" -> [op |-> "varint"]

RResOK(e, res) ==
    IF e.r.ok
    THEN /\ res.kind = "ok"
         /\ (CASE e.op = "peek" -> res.b = e.r.b
               [] e.op = "bytes" -> res.bytes = e.r.bytes
               [] OTHER -> res.v = U!FromLimbs(e.r.v))
    ELSE /\ res.kind = e.r.err
         /\ (e.r.err = "truncated" => res.needed = U!FromLimbs(e.r.needed))

RECURSIVE RFold(_, _, _)
RFold(r, cs, i) ==
    IF i > Len(cs) THEN TRUE
    ELSE LET e == cs[i]
             x == RCall(r, ToRCall(e))
         IN /\ RResOK(e, x.res)
            /\ x.st.pos = e.pos
            /\ Len(x.st.rest) = e.rem
            /\ RFold(x.st, cs, i + 1)

ToWCall(e) ==
    CASE e.op = "slice" -> [op |-> "slice", b |-> e.b]
      [] e.op = "u8" -> [op |-> "uN", k |-> 1, v |-> U!W(e.v)]
      [] e.op = "u16" -> [op |-> "uN", k |-> 2, v |-> U!FromLimbs(e.v)]
      [] e.op = "u32" -> [op |-> "uN", k |-> 4, v |-> U!FromLimbs(e.v)]
      [] e.op = "u64" -> [op |-> "uN", k |-> 8, v |-> U!FromLimbs(e.v)]
      [] e.op = "varint" -> [op |-> "varint", v |-> U!FromLimbs(e.v)]
      [] e.op = "ensure" -> [op |-> "ensure", n |-> U!FromLimbs(e.n)]

WResOK(e, res) ==
    IF e.r.ok THEN res.kind = "ok"
    ELSE /\ res.kind = e.r.err
         /\ (e.r.err = "small" => res.needed = U!FromLimbs(e.r.needed))

(* the writer after the calls, or a failure flag at the first call that differs *)
RECURSIVE WFold(_, _, _)
WFold(w, cs, i) ==
    IF i > Len(cs) THEN [ok |-> TRUE, w |-> w]
    ELSE LET e == cs[i]
             x == WCall(w, ToWCall(e))
         IN IF /\ WResOK(e, x.res)
               /\ WWritten(x.st) = e.written
               /\ WRemaining(x.st) = e.rem
            THEN WFold(x.st, cs, i + 1)
            ELSE [ok |-> FALSE, w |-> w]

EventOK(ev) ==
    CASE ev.t = "rrun" -> RFold(RNew(ev.in), ev.calls, 1)
      [] ev.t = "wrun" ->
           LET f == WFold(WNew(ev.cap), ev.calls, 1)
           IN /\ f.ok
              /\ Len(ev.buf) = ev.cap
              /\ \A i \in 1..ev.cap : ev.buf[i] = IF f.w.buf[i] = -1 THEN Fill ELSE f.w.buf[i]

(* Every event is an independent run from a fresh cursor, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK == c.t = "event" => EventOK(Trace[c.i])
=============================================================================
