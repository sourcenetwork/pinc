------------------------- MODULE TraceIntegrationCodecs -------------------------
(***************************************************************************)
(* Trace validation of the small round trips of the integration layer: the *)
(* relay path addresses, the stream tag and the stream id at the head of a *)
(* range-proof body.                                                       *)
(*                                                                         *)
(* The Rust test tests/trace_integration_codecs.rs runs the real           *)
(* relay_addr and relay_parts, write_tag and read_tag (over a real         *)
(* loopback connection, one stream per call) and head_sid and with_sid on  *)
(* boundary, mutated and seeded random inputs, and records one event per   *)
(* call in codecs_relay.ndjson, codecs_tag.ndjson and codecs_sid.ndjson.   *)
(* Each event must equal what the operators of IntegrationCodecsOps.tla    *)
(* give, with the real constants (IntegrationCodecs.tla states the         *)
(* properties of those operators). A stream id is four 16-bit limbs (TLC   *)
(* integers are 32 bits wide).                                             *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and VINC_TRACE_DIR.     *)
(***************************************************************************)
EXTENDS IntegrationCodecsOps, Json, IOUtils

VARIABLE c

Dir == IOEnv.VINC_TRACE_DIR
Trace == ndJsonDeserialize(Dir \o "/codecs_relay.ndjson") \o ndJsonDeserialize(Dir \o "/codecs_tag.ndjson")
         \o ndJsonDeserialize(Dir \o "/codecs_sid.ndjson")

Init == c = [t |-> "root"]

HasErr(ev) == "err" \in DOMAIN ev

EventOK(ev) ==
    CASE ev.t = "raddr" ->
           RelayAddr(ev.v6, ev.relay, ev.peer) = [v6 |-> ev.v6, s |-> ev.s] /\ ev.port = 0
      [] ev.t = "rparts" ->
           LET r == RelayParts([v6 |-> ev.v6, s |-> ev.s]) IN
           IF ev.some THEN r.ok /\ r.relay = ev.relay /\ r.peer = ev.peer ELSE ~r.ok
      [] ev.t = "wtag" ->
           LET r == TagWrite(ev.tag) IN
           IF HasErr(ev) THEN ~r.ok /\ ev.err = r.e ELSE r.ok /\ r.b = ev.b
      [] ev.t = "rtag" ->
           LET r == TagRead(ev.b) IN
           IF HasErr(ev) THEN ~r.ok /\ r.e = ev.err /\ (ev.err = "config" => r.rest = ev.rest)
           ELSE r.ok /\ r.tag = ev.tag /\ r.rest = ev.rest
      [] ev.t = "hsid" ->
           LET r == HeadSid(ev.b) IN
           IF ev.ok THEN r.ok /\ r.v = U!FromLimbs(ev.sid) ELSE ~r.ok
      [] ev.t = "wsid" ->
           LET r == WithSid(ev.b, U!FromLimbs(ev.sid)) IN
           IF ev.ok THEN r.ok /\ r.out = ev.out ELSE ~r.ok

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK == c.t = "event" => EventOK(Trace[c.i])
=============================================================================
