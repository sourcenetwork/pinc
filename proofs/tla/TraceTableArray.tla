--------------------------- MODULE TraceTableArray ---------------------------
(***************************************************************************)
(* Trace validation of the array by position: pinc-table array.rs.        *)
(*                                                                         *)
(* The Rust test tests/trace_table_array.rs drives real arrays (records of *)
(* 2 bytes, a big-endian u16 value) with seeded calls: sets of absent and  *)
(* present places, records of the wrong length, positions past the end,    *)
(* removals of present and absent places, walk orders with many equal keys *)
(* and key slices of the wrong length, and fills every place. Every call  *)
(* must be the step the operators of TableArrayOps.tla compute, with the   *)
(* result recorded, and the array the public API shows after it (`get` of  *)
(* every place, `order`, `iter`, `len`) must be the model's.               *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds table_array.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd
VARIABLES i, s
vars == <<i, s>>
INSTANCE TableArrayOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/table_array.ndjson")
Ev0 == Trace[i]

(* the recorded view: `get` of every place ([] or [value]), `order`, `iter` ([position, value] pairs), `len`;
   compared element by element (JSON arrays count from 1) *)
Same(y, v) == /\ v.len = y.cnt
              /\ Len(v.get) = y.p /\ \A q \in 0..(y.p - 1) : v.get[q + 1] = Get(y, q)
              /\ Len(v.order) = y.p /\ \A q \in 0..(y.p - 1) : v.order[q + 1] = y.ord[q]
              /\ LET it == Iter(y) IN Len(v.iter) = Len(it) /\ \A k \in 1..Len(it) : v.iter[k] = it[k]

InitEv == /\ Ev0.op = "init" /\ s' = Array0(Ev0.places) /\ Same(s', Ev0.v)
SetEv == LET x == Set(s, Ev0.pos, Ev0.good, Ev0.val)
         IN /\ Ev0.op = "set" /\ x.r = Ev0.res /\ s' = x.s /\ Same(s', Ev0.v)
RemoveEv == LET x == Remove(s, Ev0.pos)
            IN /\ Ev0.op = "remove" /\ x.r = Ev0.res /\ s' = x.s /\ Same(s', Ev0.v)
OrderEv == LET x == SetOrder(s, Ev0.keys)
           IN /\ Ev0.op = "order" /\ x.r = Ev0.res /\ s' = x.s /\ Same(s', Ev0.v)

Init == i = 1 /\ s = Array0(0)
Step == /\ i <= Len(Trace) /\ Ev0.t = "tarr"
        /\ (InitEv \/ SetEv \/ RemoveEv \/ OrderEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the order is a permutation of the places, and the count is the places present
Inv == /\ {s.ord[q] : q \in 0..(s.p - 1)} = 0..(s.p - 1)
       /\ s.cnt = Cardinality({q \in 0..(s.p - 1) : s.fl[q]})
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
