---------------------------- MODULE TraceTableRing ----------------------------
(***************************************************************************)
(* Trace validation of the ring: pinc-table ring.rs.                      *)
(*                                                                         *)
(* The Rust test tests/trace_table_ring.rs drives real rings (records of 2 *)
(* bytes, a big-endian u16 value; pinc-table built with the cargo feature  *)
(* `trace` for the head) with seeded calls: pushes until full and past it, *)
(* records of the wrong length, pops until empty and past it, clears, and *)
(* long runs that wrap the head around the block many times, on rings of   *)
(* capacity 0, 1, 2, 3, 7 and 64. Every call must be the step the          *)
(* operators of TableRingOps.tla compute, with the result and the record   *)
(* popped, and the ring after it (head, `len`, `get` of every record held, *)
(* `peek`, `is_full`) must be the model's.                                 *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds table_ring.ndjson.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLES i, s
vars == <<i, s>>
INSTANCE TableRingOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/table_ring.ndjson")
Ev0 == Trace[i]

(* the recorded view: head, len, the records oldest first, peek ([] or [value]), is_full *)
Same(y, v) == /\ v.head = y.head /\ v.len = y.len
              /\ Len(v.items) = y.len /\ \A k \in 1..y.len : v.items[k] = Items(y)[k]
              /\ v.peek = GetAt(y, 0)
              /\ v.full = (y.len = y.cap)

InitEv == /\ Ev0.op = "init" /\ s' = Ring0(Ev0.cap) /\ Same(s', Ev0.v)
PushEv == LET x == Push(s, Ev0.good, Ev0.val)
          IN /\ Ev0.op = "push" /\ x.r = <<"push", Ev0.res, 0>> /\ s' = x.s /\ Same(s', Ev0.v)
PopEv == LET x == Pop(s)
         IN /\ Ev0.op = "pop" /\ x.r = <<"pop", Ev0.res, Ev0.val>> /\ s' = x.s /\ Same(s', Ev0.v)
ClearEv == LET x == Clear(s)
           IN /\ Ev0.op = "clear" /\ s' = x.s /\ Same(s', Ev0.v)

Init == i = 1 /\ s = Ring0(0)
Step == /\ i <= Len(Trace) /\ Ev0.t = "tring"
        /\ (InitEv \/ PushEv \/ PopEv \/ ClearEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* len <= capacity, and head < capacity on a ring with places
Inv == /\ s.len <= s.cap
       /\ IF s.cap > 0 THEN s.head < s.cap ELSE s.head = 0
=============================================================================
