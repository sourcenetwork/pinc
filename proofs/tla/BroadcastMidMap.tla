----------------------------- MODULE BroadcastMidMap -----------------------------
(***************************************************************************)
(* The open-addressing map of vinc-broadcast table.rs (MidMap), slot for   *)
(* slot: linear probing, a stored value held as value + 1 so that zero     *)
(* marks an empty slot, no tombstones, and backward-shift deletion. Slots  *)
(* is the (power of two) size of the arrays, Cap the capacity (the code    *)
(* allocates at least 2 * Cap slots, so the load is at most one half and   *)
(* every probe meets an empty slot). Keys are small so that several share  *)
(* a home slot (the home is key & mask, as in the code).                   *)
(*                                                                         *)
(* An abstract partial function is kept beside the arrays and compared     *)
(* after every operation. Checked in every reachable state: a lookup       *)
(* returns exactly what the abstract function holds; `len` counts the      *)
(* occupied slots and stays within Cap; a key occupies one slot; every     *)
(* occupied slot is reached from its home slot over occupied slots alone   *)
(* (the invariant that makes the early exit of `slot` correct and that     *)
(* backward-shift deletion must keep); an insert past Cap is refused and   *)
(* changes nothing.                                                        *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/BroadcastTable.lean (the map is the  *)
(* association it implements; the table theorems there are about that      *)
(* association, and this model is the link from the slot arrays to it).    *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Slots, Cap, Keys, Vals

None == -1
Mask == Slots - 1
Idx == 0..(Slots - 1)
Home(k) == k % Slots                       \* key & mask for a power of two

VARIABLES ks, vs, len, ab
vars == <<ks, vs, len, ab>>

Next1(i) == (i + 1) % Slots

\* slot(): the index of `key`, or None at the first empty slot (at most Slots probes)
RECURSIVE SlotLoop(_, _, _, _, _)
SlotLoop(K, V, key, i, n) == IF n = 0 THEN None
                              ELSE IF V[i] = 0 THEN None
                              ELSE IF K[i] = key THEN i ELSE SlotLoop(K, V, key, Next1(i), n - 1)
Slot(K, V, key) == SlotLoop(K, V, key, Home(key), Slots)

Get(K, V, key) == IF Slot(K, V, key) = None THEN None ELSE V[Slot(K, V, key)] - 1

RECURSIVE FirstEmpty(_, _)
FirstEmpty(V, i) == IF V[i] = 0 THEN i ELSE FirstEmpty(V, Next1(i))

\* does `slot0` lie cyclically in (hole, j]? (the entry stays: moving it would break its probe chain)
Stays(hole, j, slot0) == IF hole <= j THEN hole < slot0 /\ slot0 <= j ELSE hole < slot0 \/ slot0 <= j

\* the backward shift after removing the entry at `found`
RECURSIVE Shift(_, _, _, _, _)
Shift(K, V, hole, j, dummy) ==
    LET j1 == Next1(j)
    IN IF V[j1] = 0 THEN [k |-> K, v |-> [V EXCEPT ![hole] = 0]]
       ELSE IF Stays(hole, j1, Home(K[j1])) THEN Shift(K, V, hole, j1, 0)
       ELSE Shift([K EXCEPT ![hole] = K[j1]], [V EXCEPT ![hole] = V[j1]], j1, j1, 0)

Init == /\ ks = [i \in Idx |-> 0] /\ vs = [i \in Idx |-> 0] /\ len = 0 /\ ab = [k \in Keys |-> None]

Insert(key, val) ==
    LET i == Slot(ks, vs, key)
    IN IF i # None
       THEN /\ vs' = [vs EXCEPT ![i] = val + 1] /\ ab' = [ab EXCEPT ![key] = val] /\ UNCHANGED <<ks, len>>
       ELSE IF len >= Cap THEN UNCHANGED vars
       ELSE LET e == FirstEmpty(vs, Home(key))
            IN /\ ks' = [ks EXCEPT ![e] = key] /\ vs' = [vs EXCEPT ![e] = val + 1]
               /\ len' = len + 1 /\ ab' = [ab EXCEPT ![key] = val]

Remove(key) ==
    LET found == Slot(ks, vs, key)
    IN IF found = None THEN UNCHANGED vars
       ELSE LET r == Shift(ks, vs, found, found, 0)
            IN /\ ks' = r.k /\ vs' = r.v /\ len' = len - 1 /\ ab' = [ab EXCEPT ![key] = None]

Next == \E k \in Keys : \/ \E v \in Vals : Insert(k, v)
                        \/ Remove(k)
Spec == Init /\ [][Next]_vars

TypeOK == /\ len \in 0..Cap /\ \A i \in Idx : vs[i] \in 0..(Cap + 1)

Abstraction == \A k \in Keys : Get(ks, vs, k) = ab[k]

LenIsCount == len = Cardinality({i \in Idx : vs[i] # 0})

CapBound == Cardinality({k \in Keys : ab[k] # None}) = len /\ len <= Cap

OneSlotPerKey == \A i, j \in Idx : (i # j /\ vs[i] # 0 /\ vs[j] # 0) => ks[i] # ks[j]

\* every slot from the home of an entry up to the entry holds an entry
RECURSIVE Reach(_, _, _)
Reach(h, i, n) == IF h = i THEN TRUE
                  ELSE vs[h] # 0 /\ n > 0 /\ Reach(Next1(h), i, n - 1)
ProbeChain == \A i \in Idx : vs[i] # 0 => Reach(Home(ks[i]), i, Slots)
=============================================================================
