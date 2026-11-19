------------------------- MODULE TraceReconcileWire -------------------------
(***************************************************************************)
(* Trace validation of the reconcile wire layer (wire.rs).                 *)
(*                                                                         *)
(* The Rust test tests/trace_reconcile_wire.rs runs the real put_bound,    *)
(* read_bound, common_prefix, count, put_parts, read_parts, frame_body,    *)
(* frame_len and first_set_ref on every bound pair over a small alphabet,  *)
(* every short byte string, bounds of 254 to 300 bytes at the cap of 255,  *)
(* varints of every width, every count and `more` pair around the byte     *)
(* boundaries, frames up to 300 bytes and at the edges of the three-byte   *)
(* length, the messages of real sessions in both directions and cuts,      *)
(* flipped bytes and extensions of them. Each event must equal the         *)
(* corresponding operator of ReconcileWire.tla, whose properties TLC       *)
(* checks exhaustively in ReconcileWire*.cfg. A message event is the count *)
(* field and the head of the first part.                                   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds reconcile_wire.ndjson.*)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils

VARIABLE c

RW == INSTANCE ReconcileWire WITH MaxCpl <- 255, Alpha <- {}, BLen <- 0, RAlpha <- {}, RLen <- 0, Mode <- "none", c <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/reconcile_wire.ndjson")

Init == c = [t |-> "root"]

Has(ev, k) == k \in DOMAIN ev

(* the count field and the head of the first part of a message *)
Parse(msg, mx) ==
    LET fb == RW!FrameBody(msg)
    IN IF ~fb.ok THEN fb
       ELSE LET rp == RW!ReadParts(fb.body)
            IN IF ~rp.ok THEN rp
               ELSE IF rp.cnt = 0 THEN [ok |-> TRUE, cnt |-> 0, more |-> rp.more, head |-> FALSE]
               ELSE LET h == RW!ReadHead(<<>>, rp.rest, mx)
                    IN IF ~h.ok THEN h
                       ELSE [ok |-> TRUE, cnt |-> rp.cnt, more |-> rp.more, head |-> TRUE, kind |-> h.kind, lo |-> h.lo,
                             hi |-> h.hi, used |-> Len(fb.body) - Len(h.rest)]

FirstSetRef(msg) ==
    LET fb == RW!FrameBody(msg)
    IN IF ~fb.ok THEN fb
       ELSE LET n == RW!Count(fb.body)
            IN IF ~n.ok THEN n ELSE RW!ReadBytes(n.v, n.rest)

EventOK(ev) ==
    CASE ev.e = "pb" -> RW!PutBound(ev.last, ev.b).bytes = ev.out
      [] ev.e = "rb" ->
           LET r == RW!ReadBound(ev.last, ev.in, ev.mx)
           IN IF Has(ev, "ok")
              THEN r.ok /\ r.b = ev.ok /\ Len(ev.in) - Len(r.rest) = ev.used
              ELSE ~r.ok /\ r.r = ev.err
      [] ev.e = "cp" -> RW!Cpl(ev.a, ev.b) = ev.out
      [] ev.e = "ct" ->
           LET r == RW!Count(ev.in)
           IN IF Has(ev, "ok")
              THEN r.ok /\ r.v = ev.ok /\ Len(ev.in) - Len(r.rest) = ev.used
              ELSE ~r.ok /\ r.r = ev.err
      [] ev.e = "pp" -> RW!PutParts(ev.cnt, ev.more) = ev.out
      [] ev.e = "rp" ->
           LET r == RW!ReadParts(ev.in)
           IN IF Has(ev, "cnt")
              THEN r.ok /\ r.cnt = ev.cnt /\ r.more = ev.more /\ Len(ev.in) - Len(r.rest) = ev.used
              ELSE ~r.ok /\ r.r = ev.err
      [] ev.e = "fb" ->
           LET r == RW!FrameBody(ev.in)
           IN IF Has(ev, "ok") THEN r.ok /\ Len(r.body) = ev.ok ELSE ~r.ok /\ r.r = ev.err
      [] ev.e = "fl" ->
           LET r == RW!FrameCheck(ev.hdr, ev.blen)
           IN IF Has(ev, "ok") THEN r.ok /\ ev.ok = ev.blen ELSE ~r.ok /\ r.r = ev.err
      [] ev.e = "msg" ->
           LET r == Parse(ev.in, ev.mx)
           IN IF Has(ev, "err") THEN ~r.ok /\ r.r = ev.err
              ELSE r.ok /\ r.cnt = ev.cnt /\ r.more = ev.more /\ r.head = Has(ev, "head")
                   /\ (Has(ev, "head") =>
                         /\ r.kind = ev.head.kind /\ r.lo = ev.head.lo /\ r.used = ev.head.used
                         /\ IF Has(ev.head, "hi") THEN ~r.hi.none /\ r.hi.v = ev.head.hi ELSE r.hi.none)
      [] ev.e = "fsr" ->
           LET r == FirstSetRef(ev.in)
           IN IF Has(ev, "ok") THEN r.ok /\ r.v = ev.ok ELSE ~r.ok /\ r.r = ev.err

(* Every event is an independent call of a pure function, so the events are the states of one machine, checked
   on all workers at once (see TraceVarint.tla). *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK == c.t = "event" => EventOK(Trace[c.i])
=============================================================================
