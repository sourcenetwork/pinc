---------------------------- MODULE TraceWireCbor ----------------------------
(***************************************************************************)
(* Trace validation of the strict DAG-CBOR codec of pinc-wire (Decoder,    *)
(* MapReader, Encoder, MapKeys in cbor/*.rs).                              *)
(*                                                                         *)
(* The Rust test tests/trace_wire_cbor.rs runs the real codec and records  *)
(* one event per run in tla/wire_cbor.ndjson under PINC_TRACE_DIR:             *)
(*  "drun"  an input and the decoder calls made on it (next_item,          *)
(*          skip_value, MapReader::new, MapReader::next_key), each with    *)
(*          its result and, on success, position() after it; a run stops   *)
(*          at its first error;                                            *)
(*  "erun"  a buffer size and the encoder calls made into it (every        *)
(*          method, ordered_map and MapKeys::key), each with its result,   *)
(*          written() and is_complete() after a key; runs go on after an   *)
(*          error; and the whole buffer once the encoder is dropped, which *)
(*          starts filled with Fill.                                       *)
(* Each run must be what the operators of WireCborOps.tla compute, call    *)
(* for call (WireCbor.tla states their properties), with MaxDepth set to   *)
(* MAX_DEPTH. The position after an error is not compared: the code does   *)
(* not document it. A u64 is four 16-bit limbs (TLC integers are 32 bits   *)
(* wide); a float is its to_bits.                                          *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR.     *)
(***************************************************************************)
EXTENDS WireCborOps, Json, IOUtils, TraceEnd

VARIABLE c

Fill == 170
Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/tla/wire_cbor.ndjson")

Init == c = [t |-> "root"]

ItemOf(it) ==
    CASE it.k \in {"uns", "neg", "array", "map", "tag", "float"} -> [k |-> it.k, a |-> U!FromLimbs(it.a)]
      [] it.k \in {"bytes", "text"} -> [k |-> it.k, b |-> it.b]
      [] it.k = "bool" -> [k |-> "bool", v |-> it.v]
      [] it.k = "null" -> [k |-> "null"]

ErrOK(r, res) ==
    /\ res.kind = r.err
    /\ (r.err \in {"truncated", "small"} => res.needed = U!FromLimbs(r.needed))
    /\ (r.err \in {"noncanon", "unexpected"} => res.why = r.why)

DResOK(e, res) ==
    IF e.r.ok
    THEN /\ res.kind = "ok"
         /\ (CASE e.op = "next" -> res.item = ItemOf(e.r.item)
               [] e.op = "mkey" -> res.key = (IF "none" \in DOMAIN e.r THEN NoKey ELSE SomeKey(e.r.key))
               [] OTHER -> TRUE)
    ELSE ErrOK(e.r, res)

(* one decoder call: [res, mr, d] *)
DCall(d, mr, e) ==
    CASE e.op = "next" -> (LET x == NextItem(d) IN [res |-> x.res, mr |-> mr, d |-> x.d])
      [] e.op = "skip" -> (LET x == SkipValue(d) IN [res |-> x.res, mr |-> mr, d |-> x.d])
      [] e.op = "mnew" -> (LET x == MapNew(d)
                           IN [res |-> x.res, mr |-> IF x.res.kind = "ok" THEN x.mr ELSE mr, d |-> x.d])
      [] e.op = "mkey" -> NextKey(mr, d)

RECURSIVE DFold(_, _, _, _)
DFold(d, mr, cs, i) ==
    IF i > Len(cs) THEN TRUE
    ELSE LET e == cs[i]
             x == DCall(d, mr, e)
         IN /\ DResOK(e, x.res)
            /\ (e.r.ok => x.d.r.pos = e.pos)
            /\ DFold(x.d, x.mr, cs, i + 1)

ToECall(e) ==
    CASE e.op \in {"uns", "neg", "array", "map", "float"} -> [op |-> e.op, a |-> U!FromLimbs(e.a)]
      [] e.op \in {"bytes", "text", "cid"} -> [op |-> e.op, b |-> e.b]
      [] e.op = "bool" -> [op |-> "bool", v |-> e.v]
      [] e.op = "null" -> [op |-> "null"]

NoMap == [left |-> U!Zero, prev |-> NoKey]

(* one encoder call: [res, st, mk]; omap is ordered_map, key is MapKeys::key on the last ordered_map *)
ECallT(w, mk, e) ==
    CASE e.op = "omap" ->
           (LET x == EHeader(w, 5, U!FromLimbs(e.a))
            IN [res |-> x.res, st |-> x.st,
                mk |-> IF x.res.kind = "ok" THEN [left |-> U!FromLimbs(e.a), prev |-> NoKey] ELSE mk])
      [] e.op = "key" -> MKey(mk, w, e.b)
      [] OTHER -> LET x == ECall(w, ToECall(e)) IN [res |-> x.res, st |-> x.st, mk |-> mk]

EResOK(e, res) == IF e.r.ok THEN res.kind = "ok" ELSE ErrOK(e.r, res)

(* the encoder after the calls, or a failure flag at the first call that differs *)
RECURSIVE EFold(_, _, _, _)
EFold(w, mk, cs, i) ==
    IF i > Len(cs) THEN [ok |-> TRUE, w |-> w]
    ELSE LET e == cs[i]
             x == ECallT(w, mk, e)
         IN IF /\ EResOK(e, x.res)
               /\ WWritten(x.st) = e.written
               /\ (e.op = "key" => e.complete = (x.mk.left = U!Zero))
            THEN EFold(x.st, x.mk, cs, i + 1)
            ELSE [ok |-> FALSE, w |-> w]

EventOK(ev) ==
    CASE ev.t = "drun" -> DFold(Fresh(ev.in), NoMap, ev.calls, 1)
      [] ev.t = "erun" ->
           LET f == EFold(WNew(ev.cap), NoMap, ev.calls, 1)
           IN /\ f.ok
              /\ Len(ev.buf) = ev.cap
              /\ \A i \in 1..ev.cap : ev.buf[i] = IF f.w.buf[i] = -1 THEN Fill ELSE f.w.buf[i]

(* Every event is an independent run, so the events are the states of one machine: the root state has one
   successor per block of 32 events and a block one per event, which TLC checks on all workers at once. *)
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
