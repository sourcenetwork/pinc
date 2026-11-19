---------------------------- MODULE CoreTableOps -----------------------------
(***************************************************************************)
(* The operators of the pinc-core endpoint's connection-id table           *)
(* (crates/pinc-core/src/table.rs, Table), step for step: a hash table     *)
(* with chaining over a fixed array of N entries, a free list threaded     *)
(* through the entries' `chain` links, and a second list through `older`   *)
(* and `newer` that holds the entries in insertion order. CoreTable.tla    *)
(* checks them over every interleaving and every bucket function;          *)
(* TraceCoreTable.tla replays the recorded calls of the real table.        *)
(*                                                                         *)
(* A table is t = [heads, en, free, oldest, newest, len, ctr]: heads maps  *)
(* a bucket to the index of the first entry of its chain, en maps an index *)
(* to an entry [live, k, v, s, chain, older, newer] (live is `kv` being    *)
(* Some; chain is the next entry of the bucket, or of the free list for an *)
(* entry that is not live), Nil is the code's NIL. The fields s and ctr    *)
(* are ghosts: s is the number of pushes before this entry's, so the       *)
(* order in which entries were pushed can be told; no operator reads them  *)
(* to decide anything. bk maps a key to its bucket, the code's keyed hash  *)
(* reduced modulo N, an arbitrary function here. N is a parameter of every *)
(* operator (the code's const generic); each walk along a list has the     *)
(* bound N (a list of a well formed table is never longer), which the     *)
(* model check shows is never what stops a walk.                           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

Nil == -1
EmptyE(ch) == [live |-> FALSE, k |-> 0, v |-> 0, s |-> 0, chain |-> ch, older |-> Nil, newer |-> Nil]
New(n) == [heads |-> [b \in 0..(n - 1) |-> Nil],
           en |-> [i \in 0..(n - 1) |-> EmptyE(IF i + 1 < n THEN i + 1 ELSE Nil)],
           free |-> 0, oldest |-> Nil, newest |-> Nil, len |-> 0, ctr |-> 0]
At(n, i) == i \in 0..(n - 1)

\* Table::find_from and find: the first live entry of k along the chain, or Nil
RECURSIVE FindFrom(_, _, _, _, _)
FindFrom(n, t, i, k, fuel) ==
    IF fuel = 0 \/ ~At(n, i) THEN Nil
    ELSE IF t.en[i].live /\ t.en[i].k = k THEN i
    ELSE FindFrom(n, t, t.en[i].chain, k, fuel - 1)
Find(n, bk, t, k) == FindFrom(n, t, t.heads[bk[k]], k, n)

\* Table::matches::<M>: the indexes of the first M live entries of k along the chain (the code keeps walking after M)
RECURSIVE MatchFrom(_, _, _, _, _, _, _)
MatchFrom(n, t, i, k, m, acc, fuel) ==
    IF fuel = 0 \/ ~At(n, i) THEN acc
    ELSE LET e == t.en[i]
             acc2 == IF e.live /\ e.k = k /\ Len(acc) < m THEN Append(acc, i) ELSE acc
         IN MatchFrom(n, t, e.chain, k, m, acc2, fuel - 1)
Matches(n, bk, t, k, m) == MatchFrom(n, t, t.heads[bk[k]], k, m, <<>>, n)

\* Table::link_newest
LinkNewest(n, t, i) ==
    LET tail == t.newest
        t1 == [t EXCEPT !.en[i].older = tail, !.en[i].newer = Nil]
        t2 == IF At(n, tail) THEN [t1 EXCEPT !.en[tail].newer = i] ELSE [t1 EXCEPT !.oldest = i]
    IN [t2 EXCEPT !.newest = i]

\* Table::unlink_order
UnlinkOrder(n, t, i) ==
    LET older == t.en[i].older
        newer == t.en[i].newer
        t1 == IF At(n, older) THEN [t EXCEPT !.en[older].newer = newer] ELSE [t EXCEPT !.oldest = newer]
    IN IF At(n, newer) THEN [t1 EXCEPT !.en[newer].older = older] ELSE [t1 EXCEPT !.newest = older]

\* Table::push: ok is FALSE (and nothing changes) when the free list is empty
Push(n, bk, t, k, v) ==
    LET i == t.free IN
    IF ~At(n, i) THEN [t |-> t, ok |-> FALSE]
    ELSE LET nf == t.en[i].chain
             b == bk[k]
             t1 == [t EXCEPT !.en[i] = [live |-> TRUE, k |-> k, v |-> v, s |-> t.ctr, chain |-> t.heads[b],
                                        older |-> Nil, newer |-> Nil],
                             !.heads[b] = i, !.free = nf]
             t2 == LinkNewest(n, t1, i)
         IN [t |-> [t2 EXCEPT !.len = t.len + 1, !.ctr = t.ctr + 1], ok |-> TRUE]

\* the loop of Table::pop that finds the entry before i in its chain and links it to next
RECURSIVE Unchain(_, _, _, _, _, _)
Unchain(n, t, i, next, cur, fuel) ==
    IF fuel = 0 \/ ~At(n, cur) THEN t
    ELSE IF t.en[cur].chain = i THEN [t EXCEPT !.en[cur].chain = next]
    ELSE Unchain(n, t, i, next, t.en[cur].chain, fuel - 1)

\* Table::pop: got is FALSE (and nothing changes) when i is not a live entry
Pop(n, bk, t, i) ==
    IF ~At(n, i) \/ ~t.en[i].live THEN [t |-> t, got |-> FALSE, k |-> 0, v |-> 0]
    ELSE LET e == t.en[i]
             b == bk[e.k]
             t1 == IF t.heads[b] = i THEN [t EXCEPT !.heads[b] = e.chain]
                   ELSE Unchain(n, t, i, e.chain, t.heads[b], n)
             t2 == UnlinkOrder(n, t1, i)
             t3 == [t2 EXCEPT !.en[i] = EmptyE(t2.free), !.free = i, !.len = t2.len - 1]
         IN [t |-> t3, got |-> TRUE, k |-> e.k, v |-> e.v]

\* Table::insert: ev is <<>> or the pair evicted
Insert(n, bk, t, k, v) ==
    LET f == Find(n, bk, t, k) IN
    IF f # Nil THEN [t |-> [t EXCEPT !.en[f].v = v], ev |-> <<>>]
    ELSE IF t.len = n
         THEN LET p == Pop(n, bk, t, t.oldest)
                  q == Push(n, bk, p.t, k, v)
              IN [t |-> q.t, ev |-> IF p.got THEN <<p.k, p.v>> ELSE <<>>]
         ELSE [t |-> Push(n, bk, t, k, v).t, ev |-> <<>>]

\* Table::insert_room
InsertRoom(n, bk, t, k, v) ==
    LET f == Find(n, bk, t, k) IN
    IF f # Nil THEN [t |-> [t EXCEPT !.en[f].v = v], ok |-> TRUE] ELSE Push(n, bk, t, k, v)

\* Table::insert_dup
InsertDup(n, bk, t, k, v) == Push(n, bk, t, k, v)

\* Table::remove: v is <<>> or <<the value>>
Remove(n, bk, t, k) ==
    LET f == Find(n, bk, t, k) IN
    IF f = Nil THEN [t |-> t, v |-> <<>>]
    ELSE LET p == Pop(n, bk, t, f) IN [t |-> p.t, v |-> IF p.got THEN <<p.v>> ELSE <<>>]

\* the first entry along the chain of k that holds exactly k and v
RECURSIVE PairFrom(_, _, _, _, _, _)
PairFrom(n, t, i, k, v, fuel) ==
    IF fuel = 0 \/ ~At(n, i) THEN Nil
    ELSE IF t.en[i].live /\ t.en[i].k = k /\ t.en[i].v = v THEN i
    ELSE PairFrom(n, t, t.en[i].chain, k, v, fuel - 1)

\* Table::remove_pair
RemovePair(n, bk, t, k, v) ==
    LET f == PairFrom(n, t, t.heads[bk[k]], k, v, n) IN
    IF f = Nil THEN [t |-> t, ok |-> FALSE]
    ELSE LET p == Pop(n, bk, t, f) IN [t |-> p.t, ok |-> p.got]

\* Table::touch
Touch(n, bk, t, k) ==
    LET f == Find(n, bk, t, k) IN
    IF f # Nil /\ t.newest # f THEN LinkNewest(n, UnlinkOrder(n, t, f), f) ELSE t

\* Table::iter: the indexes from the oldest to the newest
RECURSIVE IterFrom(_, _, _, _)
IterFrom(n, t, i, fuel) == IF fuel = 0 \/ ~At(n, i) THEN <<>> ELSE <<i>> \o IterFrom(n, t, t.en[i].newer, fuel - 1)
Iter(n, t) == IterFrom(n, t, t.oldest, n)

\* Table::clear
Clear(n) == New(n)
=============================================================================
