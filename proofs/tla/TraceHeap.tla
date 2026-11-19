----------------------------- MODULE TraceHeap ------------------------------
(***************************************************************************)
(* Trace validation of the endpoint's deadline heap: pinc-core heap.rs.    *)
(*                                                                         *)
(* The Rust test tests/trace_heap.rs drives real heaps (built with the     *)
(* cargo feature `trace`) with seeded calls: deadlines for new and held    *)
(* ids, which move an element up, down and not at all, removals of the     *)
(* root, of a leaf and of the rest, ids outside the heap, with deadlines   *)
(* that are few (many equal) and at the edges, and at the end a pop of     *)
(* everything. Every call must be the step the operators of HeapOps.tla    *)
(* compute, and the heap array, the position index and the stored          *)
(* deadlines recorded must be the model's; so must the answers of `peek`   *)
(* and `deadline`.                                                         *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds heap.ndjson.          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils
VARIABLES i, s
vars == <<i, s>>
CONSTANT TIEHI
INSTANCE HeapOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/heap.ndjson")
Ev0 == Trace[i]
\* the recorded heap: the array, then the position and the deadline of each id (arrays count from 1)
Same(y, v) == /\ y.hp = v.heap
              /\ DOMAIN y.pos = 0..(Len(v.pos) - 1) /\ DOMAIN y.at = 0..(Len(v.at) - 1)
              /\ \A id \in DOMAIN y.pos : y.pos[id] = v.pos[id + 1] /\ y.at[id] = v.at[id + 1]
              /\ Len(y.hp) = v.len

InitEv == /\ Ev0.op = "init" /\ s' = Heap0(Ev0.n) /\ Same(s', Ev0.v)
SetEv == LET x == Set(s, Ev0.id, Ev0.has, Ev0.at)
         IN /\ Ev0.op = "set" /\ s' = x /\ Same(s', Ev0.v)
            /\ Peek(x) = Ev0.pk
            /\ Ev0.dl = IF Ev0.id \in DOMAIN x.pos /\ x.pos[Ev0.id] # NONE THEN <<x.at[Ev0.id]>> ELSE <<>>

Init == i = 1 /\ s = Heap0(1)
Step == /\ i <= Len(Trace) /\ Ev0.t = "cohp" /\ (InitEv \/ SetEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the heap never holds more than its ids, and each one once
Inv == /\ Len(s.hp) <= Cardinality(DOMAIN s.pos)
       /\ \A id \in DOMAIN s.pos : s.pos[id] # NONE => (s.pos[id] < Len(s.hp) /\ H(s.hp, s.pos[id]) = id)
=============================================================================
