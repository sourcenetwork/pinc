--------------------------- MODULE TracePortMapUpnp ---------------------------
(***************************************************************************)
(* Trace validation of the parsers of pinc-portmap upnp.rs.                *)
(*                                                                         *)
(* The Rust test tests/trace_portmap_upnp.rs runs the real `Url::new`,     *)
(* `parse_location`, `http_response`, `ssdp_location`, `control_of`,       *)
(* `soap_result`, `external_ip` and `is_ssdp_answer` (all public) on the   *)
(* case sets of PortMapUpnp.tla and on seeded random inputs (random bytes  *)
(* and random edits of valid forms), and records one event per call: its  *)
(* input and its result. Each event must equal the operator of             *)
(* PortMapUpnp.tla for that call and satisfy the property PortMapUpnp.cfg  *)
(* checks for it (LocationForm, HttpForm, SsdpForm, ControlTrust,          *)
(* SoapForm). A URL is [ip, port, path]; a u32 is [hi, lo].                *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds portmap/upnp.ndjson.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLE c

P == INSTANCE PortMapUpnp WITH c <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/portmap/upnp.ndjson")

Init == c = [t |-> "root"]

U(l) == [hi |-> l[1], lo |-> l[2]]
\* a recorded URL result against the model's [ok, u]
UrlIs(ev, r) == r.ok = ev.ok /\ (ev.ok => r.u = ev.u)

Ev(ev) ==
    CASE ev.op = "url" -> UrlIs(ev, P!UrlNew(ev.ip, ev.port, ev.path))
      [] ev.op = "loc" -> UrlIs(ev, P!ParseLocation(ev.b)) /\ P!LocationForm(ev.b)
      [] ev.op = "resp" ->
           LET r == P!HttpResponse(ev.b)
           IN r.ok = ev.ok /\ (ev.ok => (r.status = ev.status /\ r.body = ev.body)) /\ P!HttpForm(ev.b)
      [] ev.op = "ssdp" -> UrlIs(ev, P!SsdpLocation(ev.b)) /\ P!SsdpForm(ev.b)
      [] ev.op = "ctl" ->
           LET r == P!ControlOf(ev.b, ev.base)
           IN r.ok = ev.ok /\ (ev.ok => (r.u = ev.u /\ r.k = ev.k)) /\ P!ControlTrust(ev.b, ev.base)
      [] ev.op = "soap" ->
           LET r == P!SoapResult(ev.b)
           IN /\ r.k = ev.k /\ P!SoapForm(ev.b)
              /\ ev.k = "ok" => r.body = ev.body
              /\ ev.k = "fault" => r.code = U(ev.code)
      [] ev.op = "extip" -> LET r == P!ExternalIp(ev.b) IN r.ok = ev.ok /\ (ev.ok => r.o = ev.o)
      [] ev.op = "ssdpans" -> P!IsSsdpAnswer(ev.port, ev.b) = ev.r

(* Every event is an independent call of a pure function, so the events are the states of one machine: the root
   state has one successor per block of 32 events and a block one per event, which TLC checks on all workers at
   once. *)
Next ==
    \/ c.t = "root" /\ \E b \in 0..((Len(Trace) - 1) \div 32) : c' = [t |-> "block", b |-> b]
    \/ c.t = "block" /\ \E k \in (32 * c.b + 1)..(IF 32 * c.b + 32 < Len(Trace) THEN 32 * c.b + 32 ELSE Len(Trace)) :
           c' = [t |-> "event", i |-> k]

TraceSpec == Init /\ [][Next]_c

EventsOK == c.t = "event" => Ev(Trace[c.i])
\* the end check (TraceEnd.tla): the state of the last line was reached in a trace that has one
ReplayAtEnd == ReplaySeen(c.t = "event" /\ c.i = Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
