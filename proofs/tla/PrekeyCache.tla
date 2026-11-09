----------------------------- MODULE PrekeyCache -----------------------------
(***************************************************************************)
(* The responder's prekey cache of vinc-security/src/cache.rs: a bounded   *)
(* LRU keyed by the prekey hash.                                           *)
(*                                                                         *)
(* The implementation is a sequence of N slots (an entry with its stamp,   *)
(* or an empty slot) and a clock. Every get and insert first advances the  *)
(* clock and stamps with the new value (the code's u64 wrapping_add; the   *)
(* wrap needs 2^64 operations and is a documented ceiling, proved around   *)
(* in Lean as the hypothesis n < 2^64). A get refreshes the stamp of the   *)
(* entry it finds. An insert of a cached hash only refreshes its stamp (the *)
(* cached key is kept); a new hash takes the first empty slot, else        *)
(* replaces the entry with the lowest stamp. N = 0 caches nothing.         *)
(*                                                                         *)
(* The reference is an independent model that has no stamps: a sequence of *)
(* entries ordered by recency, most recent first. A get moves a hit to the *)
(* front; an insert moves a known hash to the front, or puts a new one at  *)
(* the front and drops the last entry when there are more than N. The      *)
(* model runs both side by side: the answers of every get must agree and   *)
(* the entries of the implementation, ordered by stamp, must be exactly    *)
(* the reference (the refinement), so the least recently used entry is the *)
(* one evicted.                                                            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS N, Hashes, Vals, MaxClock

None == [full |-> FALSE]

Min(a, b) == IF a < b THEN a ELSE b
MinOf(S) == CHOOSE i \in S : \A j \in S : i <= j

Occ(slots) == {i \in 1..Len(slots) : slots[i].full}
Empties(slots) == {i \in 1..Len(slots) : ~slots[i].full}
Found(slots, h) == {i \in Occ(slots) : slots[i].hash = h}

Entry(h, v, c) == [full |-> TRUE, hash |-> h, val |-> v, stamp |-> c]
Put(slots, at, e) == IF at = 0 THEN slots ELSE [slots EXCEPT ![at] = e]

\* the slot a new entry takes: the first empty one, else the least recently used
Evict(slots) ==
    IF Empties(slots) /= {} THEN MinOf(Empties(slots))
    ELSE IF slots = <<>> THEN 0
    ELSE CHOOSE i \in Occ(slots) : \A j \in Occ(slots) \ {i} : slots[i].stamp < slots[j].stamp

Refresh(e, c) == Entry(e.hash, e.val, c)

\* get: the result (hit or not, the key) and the cache after it
ImplGetAt(c, h, i) ==
    [c |-> [slots |-> [c.slots EXCEPT ![i] = Refresh(c.slots[i], c.clock + 1)], clock |-> c.clock + 1],
     hit |-> TRUE, val |-> c.slots[i].val]

ImplGet(c, h) ==
    IF Found(c.slots, h) = {} THEN [c |-> [slots |-> c.slots, clock |-> c.clock + 1], hit |-> FALSE, val |-> 0]
    ELSE ImplGetAt(c, h, MinOf(Found(c.slots, h)))

ImplInsertKnown(c, i) ==
    [slots |-> [c.slots EXCEPT ![i] = Refresh(c.slots[i], c.clock + 1)], clock |-> c.clock + 1]

ImplInsert(c, h, v) ==
    IF Found(c.slots, h) /= {} THEN ImplInsertKnown(c, MinOf(Found(c.slots, h)))
    ELSE [slots |-> Put(c.slots, Evict(c.slots), Entry(h, v, c.clock + 1)), clock |-> c.clock + 1]

\* the reference: entries by recency, most recent first
Pos(L, h) == {k \in 1..Len(L) : L[k].hash = h}
WithoutAt(L, k) == SubSeq(L, 1, k - 1) \o SubSeq(L, k + 1, Len(L))
ToFront(L, k) == <<L[k]>> \o WithoutAt(L, k)

RefGet(L, h) ==
    IF Pos(L, h) = {} THEN [L |-> L, hit |-> FALSE, val |-> 0]
    ELSE [L |-> ToFront(L, MinOf(Pos(L, h))), hit |-> TRUE, val |-> L[MinOf(Pos(L, h))].val]

RefInsert(L, h, v) ==
    IF Pos(L, h) /= {} THEN ToFront(L, MinOf(Pos(L, h)))
    ELSE SubSeq(<<[hash |-> h, val |-> v]>> \o L, 1, Min(N, Len(L) + 1))

\* the implementation's entries by recency: sorted by decreasing stamp
NewestOf(slots, S) == CHOOSE i \in S : \A j \in S \ {i} : slots[i].stamp > slots[j].stamp

RECURSIVE ByStamp(_, _)
ByStamp(slots, S) ==
    IF S = {} THEN <<>>
    ELSE <<NewestOf(slots, S)>> \o ByStamp(slots, S \ {NewestOf(slots, S)})

Abs(c) == [k \in 1..Cardinality(Occ(c.slots)) |->
              [hash |-> c.slots[ByStamp(c.slots, Occ(c.slots))[k]].hash,
               val |-> c.slots[ByStamp(c.slots, Occ(c.slots))[k]].val]]

(* ---- the model ---- *)

VARIABLES c, L, out
vars == <<c, L, out>>

Init == c = [slots |-> [i \in 1..N |-> None], clock |-> 0] /\ L = <<>> /\ out = <<TRUE, TRUE>>

GetStep == \E h \in Hashes :
    /\ c' = ImplGet(c, h).c
    /\ L' = RefGet(L, h).L
    /\ out' = <<ImplGet(c, h).hit = RefGet(L, h).hit, ImplGet(c, h).val = RefGet(L, h).val>>

InsertStep == \E h \in Hashes, v \in Vals :
    /\ c' = ImplInsert(c, h, v)
    /\ L' = RefInsert(L, h, v)
    /\ out' = <<TRUE, TRUE>>

Next == GetStep \/ InsertStep

Spec == Init /\ [][Next]_vars

Bounded == c.clock <= MaxClock

(* ---- invariants ---- *)

TypeOK ==
    /\ Len(c.slots) = N
    /\ c.clock \in Nat
    /\ \A i \in Occ(c.slots) : c.slots[i].hash \in Hashes /\ c.slots[i].stamp \in 1..c.clock

\* never more than N entries; N = 0 caches nothing
LenBound == Cardinality(Occ(c.slots)) <= N /\ Len(L) <= N
ZeroCachesNothing == N = 0 => Occ(c.slots) = {} /\ L = <<>>

\* the hashes in the cache are pairwise distinct; so are the stamps (the order of use)
HashesDistinct == \A i, j \in Occ(c.slots) : c.slots[i].hash = c.slots[j].hash => i = j
StampsDistinct == \A i, j \in Occ(c.slots) : c.slots[i].stamp = c.slots[j].stamp => i = j

\* a get answers like the reference (same hit, same key)
GetAgrees == out[1] /\ out[2]

\* the implementation ordered by stamp is the reference: recency order is stamp order
Refines == Abs(c) = L

\* insertion into a full cache evicts exactly the least recently used entry and keeps every other
EvictsLRU ==
    \A h \in Hashes, v \in Vals :
        (N > 0 /\ Found(c.slots, h) = {} /\ Empties(c.slots) = {}) =>
            \A r \in {ImplInsert(c, h, v)} :
                \E at \in 1..N :
                    /\ {i \in 1..N : r.slots[i] /= c.slots[i]} = {at}
                    /\ r.slots[at] = Entry(h, v, r.clock)
                    /\ c.slots[at].hash = L[Len(L)].hash
                    /\ \A j \in Occ(c.slots) \ {at} : c.slots[at].stamp < c.slots[j].stamp

\* a new hash fills the first empty slot, nothing is evicted
FillsEmpty ==
    \A h \in Hashes, v \in Vals :
        (N > 0 /\ Found(c.slots, h) = {} /\ Empties(c.slots) /= {}) =>
            \A r \in {ImplInsert(c, h, v)} :
                {i \in 1..N : r.slots[i] /= c.slots[i]} = {MinOf(Empties(c.slots))}

\* a get refreshes exactly the entry it hits
GetRefreshes ==
    \A h \in Hashes : \A r \in {ImplGet(c, h)} :
        IF Found(c.slots, h) = {}
        THEN ~r.hit /\ r.c.slots = c.slots
        ELSE r.hit /\ {i \in 1..N : r.c.slots[i] /= c.slots[i]} = {MinOf(Found(c.slots, h))}
                /\ r.c.slots[MinOf(Found(c.slots, h))].stamp = r.c.clock

\* insert of a cached hash keeps one copy and its key
InsertKnownKeeps ==
    \A h \in Hashes, v \in Vals :
        Found(c.slots, h) /= {} =>
            \A r \in {ImplInsert(c, h, v)} :
                /\ Cardinality(Occ(r.slots)) = Cardinality(Occ(c.slots))
                /\ r.slots[MinOf(Found(c.slots, h))].val = c.slots[MinOf(Found(c.slots, h))].val

\* a get right after an insert hits (N > 0)
HitAfterInsert ==
    \A h \in Hashes, v \in Vals :
        N > 0 => \A r \in {ImplInsert(c, h, v)} : ImplGet(r, h).hit

=============================================================================
