----------------------------- MODULE TraceNodeDue -----------------------------
(***************************************************************************)
(* Trace check of the node's deadline cache against NodeDue.tla's         *)
(* properties on the real node: tests/trace_node_due.rs (file              *)
(* node_due.ndjson) drives a node over the scripted endpoint of            *)
(* tests/node_script.rs and, after every call, asks the probe `trace_due`, *)
(* which reads the cache, answers due() as the host would, and works the   *)
(* answer out fresh. One line per ask:                                     *)
(*   {call, kind, due, ep, layers, layers_at, fresh, fresh_layers}         *)
(* call: the node call before the ask ("command", "data", "transmit",      *)
(* "routed", "timeout", "poll", "other"); kind: the cache before the ask   *)
(* ("stale", "ep", "known"); due: the answer; ep: the endpoint's deadline; *)
(* layers: the layers' part the answer used; layers_at: layers_deadline at *)
(* the clock that part was taken at, worked out again; fresh, fresh_layers:*)
(* with_endpoint(layers_deadline(io.now)) and layers_deadline(io.now).    *)
(* A time is [t / 2^30, t % 2^30] (TLC's integers are 32 bits), none is [].*)
(*                                                                         *)
(* Checked (AllOK): the answer is the endpoint's and the layers' part      *)
(* (Coherent: the code's debug assertions, here in any build), never later *)
(* than the fresh one (NeverLate), and a call that may move everything     *)
(* leaves the cache stale (StaleAfter). TraceNodeDue_exact.cfg (Exact:     *)
(* the answer equals the fresh one) is not registered: the early answer of *)
(* NodeDue_exact needs the connectivity layer's watchdog to pass between   *)
(* two data commands, and on the scripted endpoint, which answers no       *)
(* probe, the layers' deadline stays put, so every answer of this trace    *)
(* equals the fresh one. The witness state needs a probe answered by a     *)
(* peer; this trace does not hold it.                                      *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds node_due.ndjson.      *)
(***************************************************************************)
EXTENDS Integers, Sequences, Json, IOUtils, TraceEnd

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/node_due.ndjson")

\* none is later than every time
Le(a, b) == \/ b = <<>>
            \/ a # <<>> /\ (a[1] < b[1] \/ (a[1] = b[1] /\ a[2] <= b[2]))
Min(a, b) == IF Le(a, b) THEN a ELSE b

Coherent(e) == /\ e.due = Min(e.ep, e.layers)
               /\ e.kind # "stale" => e.layers = e.layers_at
               /\ e.kind = "stale" => e.layers = e.fresh_layers
NeverLate(e) == Le(e.due, e.fresh)
StaleAfter(e) == e.call \in {"command", "routed", "timeout", "poll"} => e.kind = "stale"

AllOK == \A k \in 1..Len(Trace) : Coherent(Trace[k]) /\ NeverLate(Trace[k]) /\ StaleAfter(Trace[k])
Exact == \A k \in 1..Len(Trace) : Trace[k].due = Trace[k].fresh

VARIABLE x
Init == x = 0
Next == UNCHANGED x
\* the end check (TraceEnd.tla): the one state checks every line of a trace that has one
ReplayAtEnd == ReplaySeen(TRUE)
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
