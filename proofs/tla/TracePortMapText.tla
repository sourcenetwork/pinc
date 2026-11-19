--------------------------- MODULE TracePortMapText ---------------------------
(***************************************************************************)
(* Trace validation of pinc-portmap text.rs.                               *)
(*                                                                         *)
(* The Rust test tests/trace_portmap_text.rs (through the probe of the     *)
(* crate's `trace` feature, pinc_portmap::text_trace) runs the real writer *)
(* (runs of puts into buffers of every size around their total, `dec` and *)
(* `ip4` into every buffer size around their length), `parse_u32`,         *)
(* `parse_ip4`, `trim`, `find`, `header` and `element` on the boundary     *)
(* sets of PortMapText.tla and on seeded random inputs, and records one    *)
(* event per call: its input and its result (for the writer the buffer     *)
(* after the run, filled with `fill` before it, and `done`, -1 for None; a *)
(* u32 as [hi, lo] = hi * 65536 + lo). Each event must equal the operator  *)
(* of PortMapText.tla for that call (Put, PutDec, PutIp4, Done, ParseU32,  *)
(* ParseIp4, Trim, Find, Header, Element), whose properties TLC checks in  *)
(* PortMapText.cfg; the writer events are also checked against WriterOK's  *)
(* bound (done is -1 or at most cap, and the bytes from the end of what    *)
(* was written to cap are still `fill`).                                   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds portmap/text.ndjson.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE c

T == INSTANCE PortMapText WITH c <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/portmap/text.ndjson")

Init == c = [t |-> "root"]

U(l) == [hi |-> l[1], lo |-> l[2]]
RECURSIVE PutAll(_, _, _)
PutAll(w, ps, k) == IF k > Len(ps) THEN w ELSE PutAll(T!Put(w, ps[k]), ps, k + 1)

\* the writer's result: done and the whole buffer, and the untouched tail
OutOK(ev, w) ==
    /\ T!Done(w) = ev.done /\ w.buf = ev.buf
    /\ ev.done <= ev.cap
    /\ \A x \in (w.n + 1)..ev.cap : ev.buf[x] = ev.fill

Ev(ev) ==
    CASE ev.op = "put" -> OutOK(ev, PutAll(T!NewOut(ev.cap, ev.fill), ev.ps, 1))
      [] ev.op = "dec" -> OutOK(ev, T!PutDec(T!NewOut(ev.cap, ev.fill), U(ev.v)))
      [] ev.op = "ip4" -> OutOK(ev, T!PutIp4(T!NewOut(ev.cap, ev.fill), ev.o))
      [] ev.op = "pu32" -> LET r == T!ParseU32(ev.b) IN r.ok = ev.ok /\ (ev.ok => r.v = U(ev.v))
      [] ev.op = "pip4" -> LET r == T!ParseIp4(ev.b) IN r.ok = ev.ok /\ (ev.ok => r.o = ev.o)
      [] ev.op = "trim" -> T!Trim(ev.b) = ev.r
      [] ev.op = "find" -> T!Find(ev.h, ev.n) = ev.p
      [] ev.op = "header" -> LET r == T!Header(ev.h, ev.name) IN r.ok = ev.ok /\ (ev.ok => r.v = ev.v)
      [] ev.op = "element" ->
           LET r == T!Element(ev.b, ev.from, ev.name)
           IN r.ok = ev.ok /\ (ev.ok => (r.text = ev.text /\ r.next = ev.next))

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK == c.t = "event" => Ev(Trace[c.i])
=============================================================================
