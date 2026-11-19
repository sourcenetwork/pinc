------------------------------ MODULE TableSlab ------------------------------
(***************************************************************************)
(* The sorted slab of pinc-table (slab.rs, `SortedSlab`: insert, remove,   *)
(* retain, clear, get, contains, entry, first, last, first_at_or_after,    *)
(* next_after, iter, is_full) over every sequence of calls at small sizes: *)
(* capacity C, keys 1..K (K > C, so a new key meets a full slab), values   *)
(* 1..V, a key or a value of the wrong length, removals of keys not held   *)
(* (0 and K + 1, below and above every key, among them), and `retain`     *)
(* with every set of keys kept, changing the kept values or not.           *)
(* TableSlabOps.tla has the operators of the code.                         *)
(*                                                                         *)
(* The specification beside the code is `m`, the map from the keys held   *)
(* to their values, changed as the documentation of each call says.       *)
(*                                                                         *)
(* Checked, in every state reached (slab.rs module comment):               *)
(*  - IndexPerm: the index holds each slot in 0..len-1 exactly once;       *)
(*  - Ascending: in strictly ascending key order; NoDupKeys: no two        *)
(*    records share a key;                                                 *)
(*  - Bounded: len <= capacity; FullOK: is_full exactly when `m` holds     *)
(*    capacity keys;                                                       *)
(*  - AbsOK: the records are the map `m`;                                  *)
(*  - IterOK: `iter` and `entry` walk the map in key order, each key once; *)
(*  - QueriesOK: get, contains, first, last, first_at_or_after and         *)
(*    next_after (the cursor step) answer as the map says, for every key   *)
(*    0..K+1;                                                              *)
(*  - ResultOK: every call returns what the specification says (Length     *)
(*    before Full, Full only for a new key on a full slab, whether a key   *)
(*    was replaced or held, the number `retain` removed), and `retain`     *)
(*    calls its closure once per record in key order;                     *)
(* and in every step:                                                      *)
(*  - RefusedUnchanged: a refused insert (Length, Full) and a remove of a  *)
(*    key not held change nothing (error.rs: "The table is unchanged after *)
(*    any of them").                                                       *)
(* The `break` of retain's second pass, which the code marks unreachable,  *)
(* stops TLC with an error if reached.                                     *)
(* Witnesses: TableSlab_full (an insert refused Full), TableSlab_move (a   *)
(* kept record moved into a hole by retain's second pass).                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS C, K, V
VARIABLES s, m, res, want, moved
vars == <<s, m, res, want, moved>>

INSTANCE TableSlabOps

Init == /\ s = Slab0(C)
        /\ m = [j \in {} |-> 0]
        /\ res = <<"init", "ok", 0>>
        /\ want = <<"init", "ok", 0>>
        /\ moved = "none"

Held == DOMAIN m
(* the number of keys held below k, and the key of rank r *)
Rank(k) == Cardinality({j \in Held : j < k})
KeysInOrder == [r \in 1..Cardinality(Held) |-> CHOOSE j \in Held : Rank(j) = r - 1]
MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y
MaxOf(S) == CHOOSE x \in S : \A y \in S : x >= y
SpecEntry(S) == IF S = {} THEN <<>> ELSE <<MinOf(S), m[MinOf(S)]>>

DoInsert(kg, vg, k, v) ==
    LET x == Insert(s, kg, vg, k, v)
        new == k \notin Held
        room == ~new \/ Cardinality(Held) < C
    IN /\ s' = x.s
       /\ res' = x.r
       /\ moved' = x.mv
       /\ want' = <<"insert", IF ~kg \/ ~vg THEN "length" ELSE IF ~new THEN "true"
                              ELSE IF ~room THEN "full" ELSE "false", 0>>
       /\ m' = IF kg /\ vg /\ room THEN [j \in Held \cup {k} |-> IF j = k THEN v ELSE m[j]] ELSE m

DoRemove(k) ==
    LET x == Remove(s, k)
    IN /\ s' = x.s
       /\ res' = x.r
       /\ moved' = x.mv
       /\ want' = <<"remove", IF k \in Held THEN "true" ELSE "false", 0>>
       /\ m' = [j \in Held \ {k} |-> m[j]]

DoRetain(keep, mut) ==
    LET x == Retain(s, keep, mut, V)
    IN /\ s' = x.s
       /\ res' = <<"retain", IF SeqEq(x.calls, KeysInOrder) THEN "ok" ELSE "out of order", x.r[3]>>
       /\ moved' = x.mv
       /\ want' = <<"retain", "ok", Cardinality(Held \ keep)>>
       /\ m' = [j \in Held \cap keep |-> IF mut THEN Bump(m[j], V) ELSE m[j]]

DoClear ==
    LET x == Clear(s)
    IN /\ s' = x.s /\ res' = x.r /\ moved' = x.mv /\ want' = <<"clear", "ok", 0>>
       /\ m' = [j \in {} |-> 0]

Next == \/ \E kg, vg \in BOOLEAN, k \in 1..K, v \in 1..V : ((kg /\ vg) \/ (k = 1 /\ v = 1)) /\ DoInsert(kg, vg, k, v)
        \/ \E k \in 0..(K + 1) : DoRemove(k)
        \/ \E keep \in SUBSET (1..K), mut \in BOOLEAN : DoRetain(keep, mut)
        \/ DoClear
Spec == Init /\ [][Next]_vars

TypeOK == /\ s.len \in 0..C
          /\ DOMAIN s.recs = 0..(s.len - 1)
          /\ DOMAIN s.idx = 0..(s.len - 1)
          /\ Held \subseteq 1..K
Bounded == s.len <= s.cap
IndexPerm == {s.idx[p] : p \in 0..(s.len - 1)} = 0..(s.len - 1)
Ascending == \A p \in 0..(s.len - 2) : s.recs[s.idx[p]][1] < s.recs[s.idx[p + 1]][1]
NoDupKeys == \A a, b \in 0..(s.len - 1) : a # b => s.recs[a][1] # s.recs[b][1]
AbsOK == /\ Held = {s.recs[j][1] : j \in 0..(s.len - 1)}
         /\ \A j \in 0..(s.len - 1) : m[s.recs[j][1]] = s.recs[j][2]
IterOK == LET it == Iter(s)
          IN /\ Len(it) = Cardinality(Held)
             /\ \A k \in 1..Len(it) : /\ it[k][1] \in Held
                                      /\ it[k][2] = m[it[k][1]]
                                      /\ Rank(it[k][1]) = k - 1
                                      /\ Entry(s, k - 1) = it[k]
             /\ Entry(s, Len(it)) = <<>>
QueriesOK == /\ \A k \in 0..(K + 1) :
                  /\ GetV(s, k) = IF k \in Held THEN <<m[k]>> ELSE <<>>
                  /\ Contains(s, k) = (k \in Held)
                  /\ AtOrAfter(s, k) = SpecEntry({j \in Held : j >= k})
                  /\ NextAfter(s, k) = SpecEntry({j \in Held : j > k})
             /\ First(s) = SpecEntry(Held)
             /\ Last(s) = IF Held = {} THEN <<>> ELSE <<MaxOf(Held), m[MaxOf(Held)]>>
FullOK == (s.len = s.cap) = (Cardinality(Held) = C)
ResultOK == res = want

RefusedUnchanged == [][(res'[2] \in {"length", "full"} \/ res' = <<"remove", "false", 0>>) => UNCHANGED <<s, m>>]_vars

\* reachability witnesses: an insert refused Full; a record moved into a hole by retain's second pass
NeverFull == res[2] # "full"
NoRetainMove == moved # "retain"
=============================================================================
