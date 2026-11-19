---------------------------- MODULE TraceNodeValues ----------------------------
(***************************************************************************)
(* Snapshot check of the values layer joined to the node's sessions        *)
(* (pinc-node values.rs over values_net.rs), the invariants of            *)
(* NodeValues.tla on real nodes.                                           *)
(*                                                                         *)
(* The Rust test tests/trace_node_values.rs runs members of a simulated    *)
(* network fetching values from each other (providers that answer, that   *)
(* lie and are evicted, that crash and come back and so supersede their   *)
(* older incoming session, fetches cancelled and fetches that finish), and *)
(* records every 50 ms of simulated time, for every member, the view the  *)
(* probe Node::values_view gives (cargo feature `trace`): the values       *)
(* sessions of the layer table, the sessions we dialed, the provider       *)
(* table, the streams with their provider, owner and session, and the     *)
(* running fetches' provider lists. Sessions and peers are written as      *)
(* small numbers the test assigns in the order it first sees them.         *)
(*                                                                         *)
(* This is a check of the invariants on each recorded state, not of each   *)
(* step: the calls between two snapshots are many and inside the           *)
(* simulator. What is checked on every snapshot: the use counts are        *)
(* exactly the holders and every number held is in the table (Exact of     *)
(* NodeValuesNetOps), the tables within TABLE_MAX, every stream on a       *)
(* values session of the table, every fetch's stream owned by a running    *)
(* fetch, every dialed session an outgoing values session of the table,    *)
(* and at most SERVERS (32) served streams.                                *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the *)
(* directory that holds node_values.ndjson.                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils
VARIABLES i, v
vars == <<i, v>>
INSTANCE NodeValuesNetOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/node_values.ndjson")
Ev0 == Trace[i]
Set(q) == {q[k] : k \in DOMAIN q}
V0 == [lsess |-> <<>>, lout |-> <<>>, provs |-> <<>>, streams |-> <<>>, held |-> <<>>]

\* the net of a view, in the record NodeValuesNetOps reads
NetOf(w) == [provs |-> w.provs,
             streams |-> {[lid |-> x.lid, prov |-> x.prov, owner |-> x.owner] : x \in Set(w.streams)},
             next |-> 0, held |-> Set(w.held), refused |-> 0]
LIds(w) == {x.sid : x \in Set(w.lsess)}

Init == i = 1 /\ v = V0
Step == /\ i <= Len(Trace) /\ Ev0.t = "vsnap" /\ v' = Ev0.v /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TraceSpec == Init /\ [][Step \/ Finished]_vars

TABLE_MAX == 4096
SERVERS == 32
\* every line was taken: a line that breaks the step leaves i short of the end
Done == i > Len(Trace) \/ ENABLED Step
Inv == LET m == NetOf(v) IN
       /\ Done
       /\ Len(v.provs) <= TABLE_MAX /\ Cardinality(m.streams) <= TABLE_MAX /\ Exact(m)
       /\ v.provs = Trim(v.provs)
       /\ \A x \in Set(v.streams) : x.ses \in LIds(v)
       /\ \A x \in m.streams : x.owner # 0 => x.owner \in Running(m)
       /\ \A o \in Set(v.lout) : \E x \in Set(v.lsess) : x.sid = o.sid /\ x.peer = o.peer /\ ~x.inc
       /\ Cardinality({x \in m.streams : x.owner = 0}) <= SERVERS
=============================================================================
