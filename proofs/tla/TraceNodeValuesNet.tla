-------------------------- MODULE TraceNodeValuesNet --------------------------
(***************************************************************************)
(* Trace validation of the values layer's tables (pinc-node               *)
(* values_net.rs, Net and next_fetch_id) and of the roots a node serves   *)
(* (values_provide.rs, Node::values_provide and values_unprovide).        *)
(*                                                                         *)
(* The Rust test tests/trace_node_values_net.rs drives a real Net through *)
(* the probe values_net::probe (cargo feature `trace`), which fills all   *)
(* but W slots of the provider table and all but W streams of the stream  *)
(* table with fillers that are never given back, so the W slots and       *)
(* streams left behave as tables of W and are what each event records:    *)
(* numbers and stream numbers are written relative to the first one past  *)
(* the fillers. Every call must be the step the operators of              *)
(* NodeValuesNetOps.tla compute, and the recorded tables must be the      *)
(* model's. next_fetch_id is checked on its own over u32 ids written as   *)
(* two 16-bit limbs. The roots are checked on a real node over a scripted *)
(* endpoint with all but W roots registered by fillers: every answer must *)
(* be the model's.                                                         *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds node_values_net.ndjson.*)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd
VARIABLES i, s, w, pv, pw
vars == <<i, s, w, pv, pw>>
INSTANCE NodeValuesNetOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/node_values_net.ndjson")
Ev0 == Trace[i]
Set(q) == {q[k] : k \in DOMAIN q}
\* the recorded window: the slots, the streams, the running fetches' lists, the refusals, the last stream number
Same(m, v) == /\ m.provs = v.provs
              /\ m.streams = Set(v.streams)
              /\ m.held = Set(v.held)
              /\ m.refused = v.refused
              /\ m.next = v.next

NetEv(x) == s' = x /\ Same(x, Ev0.v) /\ UNCHANGED <<w, pv, pw>>
InitEv == Ev0.op = "init" /\ w' = Ev0.w /\ s' = Net0 /\ Same(Net0, Ev0.v) /\ UNCHANGED <<pv, pw>>
StartEv == /\ Ev0.op = "start" /\ Ev0.f \notin Running(s)
           /\ LET r == Start(s, Ev0.f, Ev0.peers, w) IN r.ok = Ev0.ok /\ NetEv(r.n)
DoneEv == Ev0.op = "startdone" /\ LET r == StartDone(s, Ev0.peers, w) IN r.ok = Ev0.ok /\ NetEv(r.n)
EndEv == Ev0.op = "end" /\ NetEv(EndFetch(s, Ev0.f))
ServeEv == Ev0.op = "serve" /\ LET r == Serve(s, Ev0.p, w, w) IN r.lid = Ev0.lid /\ NetEv(r.n)
OpenEv == /\ Ev0.op = "open" /\ Ev0.f \in Running(s) /\ Ev0.k \in 1..Len(HeldOf(s, Ev0.f))
          /\ LET r == OpenFor(s, Ev0.f, Ev0.k, w) IN r.lid = Ev0.lid /\ NetEv(r.n)
DropEv == /\ Ev0.op = "drop" /\ Ev0.ok = (Ev0.lid \in {x.lid : x \in s.streams})
          /\ NetEv(Drop(s, Ev0.lid))
\* the recorded running ids are a few, so an id is always free and the loop ends
IdEv == /\ Ev0.op = "nextid"
        /\ NextIdFrom(Ev0.last, Set(Ev0.running), 65536, 0).id = Ev0.id
        /\ UNCHANGED <<s, w, pv, pw>>
PInitEv == Ev0.op = "pinit" /\ pw' = Ev0.w /\ pv' = {} /\ UNCHANGED <<s, w>>
ProvEv == /\ Ev0.op = "provide" /\ LET x == Provide(pv, Ev0.r, pw) IN x.ok = Ev0.ok /\ pv' = x.pv
          /\ UNCHANGED <<s, w, pw>>
UnprovEv == /\ Ev0.op = "unprovide" /\ LET x == Unprovide(pv, Ev0.r) IN x.ok = Ev0.ok /\ pv' = x.pv
            /\ UNCHANGED <<s, w, pw>>

Init == i = 1 /\ s = Net0 /\ w = 0 /\ pv = {} /\ pw = 0
Step == /\ i <= Len(Trace) /\ Ev0.t = "vnet"
        /\ (InitEv \/ StartEv \/ DoneEv \/ EndEv \/ ServeEv \/ OpenEv \/ DropEv \/ IdEv \/ PInitEv \/ ProvEv \/ UnprovEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == /\ Len(s.provs) <= w /\ Cardinality(s.streams) <= w /\ s.provs = Trim(s.provs) /\ Exact(s)
       /\ Cardinality(pv) <= pw
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
