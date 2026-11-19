---------------------------- MODULE TraceCoreTable ----------------------------
(***************************************************************************)
(* Trace validation of the endpoint's connection-id table: pinc-core       *)
(* table.rs, Table.                                                        *)
(*                                                                         *)
(* The Rust test tests/trace_core_table.rs drives real tables (built with  *)
(* the cargo feature `trace`) of 1 to 16 entries and a random seed, so a   *)
(* random bucket function, through insert, insert_room, insert_dup,        *)
(* remove, remove_pair, touch, get, matches::<M> (M from 0 to 5) and       *)
(* clear, on a small key space (a few hot keys, so keys get many holders), *)
(* until the table fills, evicts and refuses. Every call must be the step  *)
(* the operators of CoreTableOps.tla compute, with the result the code     *)
(* returned; the table after the call must show the entry at every array   *)
(* position, the entries from the oldest to the newest and the length the  *)
(* model computes, and index_of must give the position find computes. The  *)
(* bucket function is read off the table (`trace_bucket`) at each call for *)
(* the key of the call; it must stay the same function of the key.         *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds core_table.ndjson.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLES i, t, bk, cap
vars == <<i, t, bk, cap>>
INSTANCE CoreTableOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/core_table.ndjson")
Ev == Trace[i]

\* the table the code shows: the entry at each array position (an empty sequence for a free one), the entries from the
\* oldest to the newest, and len
Shows(n, tt, v) ==
    /\ Len(v.slots) = n
    /\ \A p \in 0..(n - 1) :
         LET r == v.slots[p + 1]
         IN IF Len(r) = 0 THEN ~tt.en[p].live ELSE tt.en[p].live /\ tt.en[p].k = r[1] /\ tt.en[p].v = r[2]
    /\ LET ix == Iter(n, tt)
       IN /\ Len(ix) = Len(v.order)
          /\ \A p \in 1..Len(ix) : tt.en[ix[p]].k = v.order[p][1] /\ tt.en[ix[p]].v = v.order[p][2]
    /\ tt.len = v.len

\* the bucket function so far, with the key of this call (it must agree with what was seen)
Known == (Ev.k \in DOMAIN bk => bk[Ev.k] = Ev.b)
BkNow == IF Ev.k \in DOMAIN bk THEN bk ELSE (Ev.k :> Ev.b) @@ bk

InitEv == /\ Ev.op = "init"
          /\ cap' = Ev.n /\ bk' = <<>> /\ t' = New(Ev.n) /\ Shows(Ev.n, t', Ev.v)

\* a call of a key: the table after it is tt, the bucket function the extended one, and the position of the key is Ev.at
Done(tt) == /\ Known /\ bk' = BkNow /\ t' = tt /\ Shows(cap, tt, Ev.v) /\ Find(cap, BkNow, tt, Ev.k) = Ev.at

CallEv ==
    /\ Ev.op # "init" /\ Ev.op # "clear" => Ev.b \in 0..(cap - 1)
    /\ \/ /\ Ev.op = "insert"
          /\ LET r == Insert(cap, BkNow, t, Ev.k, Ev.x) IN r.ev = Ev.out /\ Done(r.t)
       \/ /\ Ev.op = "room"
          /\ LET r == InsertRoom(cap, BkNow, t, Ev.k, Ev.x) IN r.ok = Ev.ok /\ Done(r.t)
       \/ /\ Ev.op = "dup"
          /\ LET r == InsertDup(cap, BkNow, t, Ev.k, Ev.x) IN r.ok = Ev.ok /\ Done(r.t)
       \/ /\ Ev.op = "remove"
          /\ LET r == Remove(cap, BkNow, t, Ev.k) IN r.v = Ev.out /\ Done(r.t)
       \/ /\ Ev.op = "rempair"
          /\ LET r == RemovePair(cap, BkNow, t, Ev.k, Ev.x) IN r.ok = Ev.ok /\ Done(r.t)
       \/ /\ Ev.op = "touch"
          /\ Done(Touch(cap, BkNow, t, Ev.k))
       \/ /\ Ev.op = "get"
          /\ LET f == Find(cap, BkNow, t, Ev.k) IN Ev.out = (IF f = Nil THEN <<>> ELSE <<t.en[f].v>>)
          /\ Done(t)
       \/ /\ Ev.op = "matches"
          /\ LET ix == Matches(cap, BkNow, t, Ev.k, Ev.m)
             IN Ev.out = [q \in 1..Len(ix) |-> t.en[ix[q]].v]
          /\ Done(t)
       \/ /\ Ev.op = "clear"
          /\ t' = Clear(cap) /\ Shows(cap, t', Ev.v) /\ bk' = bk

Init == i = 1 /\ t = New(1) /\ bk = <<>> /\ cap = 1
Step == /\ i <= Len(Trace) /\ Ev.t = "cota"
        /\ (InitEv \/ CallEv) /\ i' = i + 1
        /\ (Ev.op # "init" => UNCHANGED cap)
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the table never holds more than its capacity, and its order list has len entries
Inv == /\ t.len <= cap
       /\ Len(Iter(cap, t)) = t.len
       /\ (t.free = Nil) = (t.len = cap)
=============================================================================
