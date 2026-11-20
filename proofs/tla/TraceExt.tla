------------------------------ MODULE TraceExt ------------------------------
(***************************************************************************)
(* Trace validation of the extension frame registry and its dispatch:      *)
(* pinc-transport frame/ext.rs and the Co::Extension arm of pinc-core      *)
(* events.rs.                                                              *)
(*                                                                         *)
(* The Rust test tests/trace_ext.rs reads the registry from the code       *)
(* (op "tbl": EXTENSION_BASE, the constants, REACH_BODY_MAX and ASSIGNED), *)
(* then carries one extension frame at a time between real endpoints on a  *)
(* simulated link: every registered type and types between and beyond them *)
(* (one to eight bytes of varint), bodies of 0, 1, 2, 3, 100, 153, 154 and *)
(* 1100 bytes, to a session that may release (allowed, its answer          *)
(* fresh) and to one the access check has not allowed                      *)
(* (op "route"), and a real second protocol dialled over a session         *)
(* (op "sub").                                                             *)
(*                                                                         *)
(* A "tbl" event must equal the model's constants and table. A "route"     *)
(* event must be what ExtOps.tla's Route says of the type, the length and  *)
(* the answer of the access check: the ring (frames the endpoint holds for *)
(* the application) has one frame exactly when Route is "ring", and it is  *)
(* the type and length sent; the endpoint's REACH_OUT event comes exactly  *)
(* when Route is "reach", with the body length sent. A "sub" event is a    *)
(* child accepted from a sub-session open: nothing in either ring, and the *)
(* model hands a sub-session open to the sub-session layer.                *)
(*                                                                         *)
(* This file reads ext.ndjson, the events whose numbers stay below 2^28;   *)
(* the Lean replay also reads ext_wide.ndjson (types up to 2^62 - 1).      *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds ext.ndjson.           *)
(***************************************************************************)
EXTENDS ExtOps, TLC, Json, IOUtils, TraceEnd

VARIABLE c

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/ext.ndjson")

Init == c = [t |-> "root"]

TblOK(ev) ==
    /\ ev.base = BASE /\ ev.sub = SUB /\ ev.reach = REACH /\ ev.reachmax = REACHMAX
    /\ ev.proofreq = PROOFREQ /\ ev.proof = PROOFFRAME
    /\ ev.testfirst = TESTFIRST /\ ev.testlast = TESTLAST
    /\ Len(ev.assigned) = Len(Tab)
    /\ \A i \in 1..Len(Tab) : ev.assigned[i] = <<Tab[i].lo, Tab[i].hi>>
    /\ Uniq(Tab)

RouteOK(ev) ==
    LET d == Route(ev.ty, ev.len, ev.allowed) IN
    /\ ev.ring = (IF d = "ring" THEN 1 ELSE 0)
    /\ IF d = "ring" THEN ev.rty = ev.ty /\ ev.rlen = ev.len ELSE ev.rty = -1 /\ ev.rlen = -1
    /\ ev.reach = (IF d = "reach" THEN 1 ELSE 0)
    /\ IF d = "reach" THEN ev.reachlen = ev.len ELSE ev.reachlen = -1
    /\ Decodes(ev.ty)
    /\ d = "ring" => Owner(ev.ty) \notin {"sub", "reach"}

SubOK(ev) ==
    /\ ev.child = 1 /\ ev.ring = 0 /\ ev.reach = 0
    /\ Route(SUB, 1, TRUE) = "sub"

EventOK(ev) ==
    /\ ev.t = "txex"
    /\ CASE ev.op = "tbl" -> TblOK(ev)
         [] ev.op = "route" -> RouteOK(ev)
         [] ev.op = "sub" -> SubOK(ev)

(* Every event is an independent call, so the events are the states of one machine: the root state has one
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
