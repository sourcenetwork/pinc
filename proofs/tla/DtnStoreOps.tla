----------------------------- MODULE DtnStoreOps -----------------------------
(***************************************************************************)
(* The operations of pinc-dtn/src/store.rs (Ledger<N>), step for step, over *)
(* a ledger record [budget, used, seq, slots]. One definition serves two    *)
(* uses: DtnStore.tla and DtnCustody.tla model check it exhaustively with a *)
(* small saturation maximum MaxU (u64::MAX in the code), TraceDtnStore.tla *)
(* replays the recorded events of the real code through it.                 *)
(*                                                                          *)
(* A slot is None or an entry [key, bytes, cls, exp, seq]; a key is the     *)
(* pair <<space, id>> (space 1 is bundles, 2 is mailbox items; equal bytes  *)
(* are an equal id). The slots are visited in index order as the code does. *)
(*                                                                          *)
(*  ExpireAt   expire: every slot whose entry has expires <= now is taken,  *)
(*             reported in slot order                                       *)
(*  Admit      admit: expire first; then Contains(key) after the sweep is   *)
(*             "dup"; then exp <= now is "expired"; then the fits test;    *)
(*             then take the oldest transit item (least (seq, index))      *)
(*             while the free bytes are fewer than needed or no slot is     *)
(*             free; then the first free slot takes the entry with the next *)
(*             seq. Every refusal ("dup", "expired", "custody", "full")     *)
(*             returns the swept ledger and the expired items as the events *)
(*  Release    release: the first slot holding the key is taken             *)
(*  Reclass    reclass: the class of the item changes, no room is needed    *)
(*                                                                          *)
(* u64 arithmetic: SatAdd and SatSub are the code's saturating_add and      *)
(* saturating_sub; the plain `used -= bytes` and `used += bytes` cannot     *)
(* leave the u64 range because used is the sum of the sizes and at most the *)
(* budget, and Assert stops TLC if that were ever false. `next_seq += 1`    *)
(* needs 2^64 admissions (a documented ceiling); seq is unbounded here.     *)
(*                                                                          *)
(* The Lean counterpart is proofs/lean/Pinc/DtnStore*.lean.                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT MaxU

None == [full |-> FALSE]
Entry(key, bytes, cls, exp, seq) == [full |-> TRUE, key |-> key, bytes |-> bytes, cls |-> cls, exp |-> exp, seq |-> seq]

SatAdd(a, b) == IF a + b > MaxU THEN MaxU ELSE a + b
SatSub(a, b) == IF a > b THEN a - b ELSE 0

Occ(slots) == {i \in 1..Len(slots) : slots[i].full}
Ents(L) == {L.slots[i] : i \in Occ(L.slots)}
Count(L) == Cardinality(Occ(L.slots))
Contains(L, key) == \E i \in Occ(L.slots) : L.slots[i].key = key

RECURSIVE SumOf(_, _)
SumOf(slots, S) == IF S = {} THEN 0 ELSE LET i == CHOOSE j \in S : TRUE IN slots[i].bytes + SumOf(slots, S \ {i})
Total(L) == SumOf(L.slots, Occ(L.slots))

New(budget, n) == [budget |-> budget, used |-> 0, seq |-> 0, slots |-> [i \in 1..n |-> None]]

\* take: empty slot i, used -= bytes
Take(L, i) ==
    LET e == L.slots[i] IN
    [L EXCEPT !.used = IF Assert(L.used >= e.bytes, "used underflows") THEN L.used - e.bytes ELSE 0,
              !.slots[i] = None]

\* expire: returns the ledger and the evicted entries in slot order
RECURSIVE ExpireAt(_, _, _)
ExpireAt(L, now, i) ==
    IF i > Len(L.slots) THEN [L |-> L, ev |-> <<>>]
    ELSE IF L.slots[i].full /\ L.slots[i].exp <= now
         THEN LET r == ExpireAt(Take(L, i), now, i + 1) IN [L |-> r.L, ev |-> <<L.slots[i]>> \o r.ev]
         ELSE ExpireAt(L, now, i + 1)
Expire(L, now) == ExpireAt(L, now, 1)

Transit(L) == {i \in Occ(L.slots) : L.slots[i].cls = "transit"}

\* oldest_transit: the transit slot with the least (seq, index); 0 if none
OldestTransit(L) ==
    IF Transit(L) = {} THEN 0
    ELSE CHOOSE i \in Transit(L) :
             \A j \in Transit(L) : L.slots[i].seq < L.slots[j].seq \/ (L.slots[i].seq = L.slots[j].seq /\ i <= j)

\* the saturating fold of the sizes of the transit items, in slot order
RECURSIVE TransitBytesFrom(_, _, _)
TransitBytesFrom(slots, i, acc) ==
    IF i > Len(slots) THEN acc
    ELSE IF slots[i].full /\ slots[i].cls = "transit" THEN TransitBytesFrom(slots, i + 1, SatAdd(acc, slots[i].bytes))
    ELSE TransitBytesFrom(slots, i + 1, acc)

\* the test before any eviction
Fits(L, bytes) ==
    /\ SatAdd(SatSub(L.budget, L.used), TransitBytesFrom(L.slots, 1, 0)) >= bytes
    /\ (Len(L.slots) - Count(L) > 0 \/ Cardinality(Transit(L)) > 0)

\* the while condition of the eviction loop
Room(L, bytes) == SatSub(L.budget, L.used) < bytes \/ Count(L) = Len(L.slots)

RECURSIVE EvictLoop(_, _, _)
EvictLoop(L, bytes, ev) ==
    IF Room(L, bytes)
    THEN LET at == OldestTransit(L) IN
         IF at = 0 THEN [L |-> L, ev |-> ev, stuck |-> Assert(FALSE, "the eviction loop found no transit item")]
         ELSE EvictLoop(Take(L, at), bytes, ev \o <<L.slots[at]>>)
    ELSE [L |-> L, ev |-> ev, stuck |-> FALSE]

FirstFree(slots) == IF \E i \in 1..Len(slots) : ~slots[i].full THEN CHOOSE i \in 1..Len(slots) : ~slots[i].full /\ \A j \in 1..(i - 1) : slots[j].full ELSE 0

\* admit: [err, L, ev] with err one of "ok", "dup", "expired", "custody" (CustodyRefused), "full"
Admit(L, key, bytes, cls, exp, now) ==
    LET refused == IF cls = "custody" THEN "custody" ELSE "full"
        x == Expire(L, now)
        y == EvictLoop(x.L, bytes, x.ev)
        at == FirstFree(y.L.slots)
        added == [y.L EXCEPT !.used = IF Assert(y.L.used + bytes <= MaxU, "used overflows") THEN y.L.used + bytes ELSE 0,
                             !.seq = y.L.seq + 1,
                             !.slots[at] = Entry(key, bytes, cls, exp, y.L.seq)]
    IN IF Contains(x.L, key) THEN [err |-> "dup", L |-> x.L, ev |-> x.ev]
       ELSE IF exp <= now THEN [err |-> "expired", L |-> x.L, ev |-> x.ev]
       ELSE IF ~Fits(x.L, bytes) THEN [err |-> refused, L |-> x.L, ev |-> x.ev]
       ELSE IF at = 0 THEN [err |-> refused, L |-> y.L, ev |-> y.ev, stuck |-> Assert(FALSE, "no free slot after the loop")]
       ELSE [err |-> "ok", L |-> added, ev |-> y.ev]

KeySlot(L, key) == IF Contains(L, key) THEN CHOOSE i \in Occ(L.slots) : L.slots[i].key = key /\ \A j \in 1..(i - 1) : ~(L.slots[j].full /\ L.slots[j].key = key) ELSE 0

\* release: [got, L, e]
Release(L, key) ==
    LET at == KeySlot(L, key) IN
    IF at = 0 THEN [got |-> FALSE, L |-> L, e |-> None] ELSE [got |-> TRUE, L |-> Take(L, at), e |-> L.slots[at]]

\* reclass: [ok, L]
Reclass(L, key, cls) ==
    IF Contains(L, key)
    THEN [ok |-> TRUE, L |-> [L EXCEPT !.slots = [i \in 1..Len(L.slots) |->
                IF L.slots[i].full /\ L.slots[i].key = key THEN [L.slots[i] EXCEPT !.cls = cls] ELSE L.slots[i]]]]
    ELSE [ok |-> FALSE, L |-> L]

(* ---- independent statements the properties are made of (no slot arithmetic of the code) ---- *)

\* the entries of the ledger that expire at now, in slot order
RECURSIVE ExpiredFrom(_, _, _)
ExpiredFrom(slots, now, i) ==
    IF i > Len(slots) THEN <<>>
    ELSE IF slots[i].full /\ slots[i].exp <= now THEN <<slots[i]>> \o ExpiredFrom(slots, now, i + 1)
    ELSE ExpiredFrom(slots, now, i + 1)
ExpiredSeq(L, now) == ExpiredFrom(L.slots, now, 1)

\* the ledger with the expired items removed and nothing else changed
WithoutExpired(L, now) ==
    [L EXCEPT !.slots = [i \in 1..Len(L.slots) |-> IF L.slots[i].full /\ L.slots[i].exp <= now THEN None ELSE L.slots[i]],
              !.used = L.used - SumOf(L.slots, {i \in Occ(L.slots) : L.slots[i].exp <= now})]

\* the items that can never be evicted before they expire
Hard(L) == {i \in Occ(L.slots) : L.slots[i].cls = "custody"}
\* an item fits exactly when custody leaves room for it in bytes and in slots
FitsSpec(L, bytes) == SumOf(L.slots, Hard(L)) + bytes <= L.budget /\ Cardinality(Hard(L)) < Len(L.slots)
=============================================================================
