---------------------------- MODULE TraceTableSlab ----------------------------
(***************************************************************************)
(* Trace validation of the sorted slab: pinc-table slab.rs.               *)
(*                                                                         *)
(* The Rust test tests/trace_table_slab.rs drives real slabs (keys and     *)
(* values of 2 bytes, big-endian u16; pinc-table built with the cargo      *)
(* feature `trace` for the index entries) with seeded calls: inserts of    *)
(* new and held keys until full and past it, keys and values of the wrong  *)
(* length, removals of the first, last, middle and absent keys, `retain`   *)
(* with random kept sets (none, all, some) changing the values or not, and *)
(* clears, on slabs of capacity 0, 1, 3, 8 and 64 (2-byte index entries)   *)
(* and 70,000 (4-byte entries). Every call must be the step the operators  *)
(* of TableSlabOps.tla compute, with the result (and for `retain` the      *)
(* number removed and the keys the closure saw, in order), and the slab    *)
(* after it (each position's slot, key and value, first, last, and get,    *)
(* contains, first_at_or_after and next_after of a few keys) must be the   *)
(* model's.                                                                *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds table_slab.ndjson.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils
VARIABLES i, s
vars == <<i, s>>
INSTANCE TableSlabOps

(* the closure of the test bumps a kept u16 value v to v % 65535 + 1 *)
VMax == 65535

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/table_slab.ndjson")
Ev0 == Trace[i]

(* the recorded view: len; for each position in key order [slot, key, value]; first and last ([] or [key, value]);
   for each probe key, get ([] or [value]), contains, first_at_or_after and next_after ([] or [key, value]) *)
Same(y, v) == /\ v.len = y.len
              /\ Len(v.slots) = y.len
              /\ \A p \in 0..(y.len - 1) :
                    v.slots[p + 1] = <<y.idx[p], y.recs[y.idx[p]][1], y.recs[y.idx[p]][2]>>
              /\ v.first = First(y) /\ v.last = Last(y)
              /\ \A k \in 1..Len(v.qs) :
                    LET qq == v.qs[k]
                    IN /\ GetV(y, qq.key) = qq.get
                       /\ Contains(y, qq.key) = qq.has
                       /\ AtOrAfter(y, qq.key) = qq.aoa
                       /\ NextAfter(y, qq.key) = qq.nxt

InitEv == /\ Ev0.op = "init" /\ s' = Slab0(Ev0.cap) /\ Same(s', Ev0.v)
InsertEv == LET x == Insert(s, Ev0.kg, Ev0.vg, Ev0.key, Ev0.val)
            IN /\ Ev0.op = "insert" /\ x.r = <<"insert", Ev0.res, 0>> /\ s' = x.s /\ Same(s', Ev0.v)
RemoveEv == LET x == Remove(s, Ev0.key)
            IN /\ Ev0.op = "remove" /\ x.r = <<"remove", Ev0.res, 0>> /\ s' = x.s /\ Same(s', Ev0.v)
RetainEv == LET x == Retain(s, {Ev0.keep[k] : k \in 1..Len(Ev0.keep)}, Ev0.mut, VMax)
            IN /\ Ev0.op = "retain" /\ x.r = <<"retain", "ok", Ev0.res>> /\ SeqEq(x.calls, Ev0.calls)
               /\ s' = x.s /\ Same(s', Ev0.v)
ClearEv == LET x == Clear(s)
           IN /\ Ev0.op = "clear" /\ s' = x.s /\ Same(s', Ev0.v)

Init == i = 1 /\ s = Slab0(0)
Step == /\ i <= Len(Trace) /\ Ev0.t = "tslab"
        /\ (InitEv \/ InsertEv \/ RemoveEv \/ RetainEv \/ ClearEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the index is a permutation of the slots in strictly ascending key order, and len <= capacity
Inv == /\ s.len <= s.cap
       /\ {s.idx[p] : p \in 0..(s.len - 1)} = 0..(s.len - 1)
       /\ \A p \in 0..(s.len - 2) : s.recs[s.idx[p]][1] < s.recs[s.idx[p + 1]][1]
=============================================================================
