-------------------------- MODULE ConnectTableOps --------------------------
(***************************************************************************)
(* The operators of the bounded tables of vinc-connect/src/relay/table.rs, *)
(* step for step: Table (open addressing, linear probing, backward-shift   *)
(* deletion, retain) and Cache (direct mapped).                            *)
(*                                                                         *)
(* A table is t = [s |-> slots, len |-> n] where s is a function from the  *)
(* slot indexes 0..N-1 to [k |-> key, v |-> value]; key 0 is an empty slot *)
(* (node ids are keys 1 and up). bk maps a key to its bucket, the code's   *)
(* hash reduced modulo N. N is the capacity, a parameter of every          *)
(* operator; the code's N is a const generic and the model checks small    *)
(* ones. Each loop of the code has the same bound here: `for _ in 0..N`.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

Free == [k |-> 0, v |-> 0]
NewTable(n) == [s |-> [i \in 0..(n - 1) |-> Free], len |-> 0]

\* Table::find: the slot of k, or -1
RECURSIVE FindFrom(_, _, _, _, _)
FindFrom(n, t, k, i, left) ==
    IF left = 0 THEN -1
    ELSE IF t.s[i].k = 0 THEN -1
    ELSE IF t.s[i].k = k THEN i
    ELSE FindFrom(n, t, k, (i + 1) % n, left - 1)
Find(n, bk, t, k) == FindFrom(n, t, k, bk[k], n)

\* the first empty slot from i within `left` probes, or -1
RECURSIVE FirstFree(_, _, _, _)
FirstFree(n, t, i, left) ==
    IF left = 0 THEN -1 ELSE IF t.s[i].k = 0 THEN i ELSE FirstFree(n, t, (i + 1) % n, left - 1)

\* Table::insert; res is "ok" (old is 0 when the key was new) or "full"
Insert(n, bk, t, k, v) ==
    LET f == Find(n, bk, t, k) IN
    IF f >= 0 THEN [t |-> [t EXCEPT !.s[f] = [k |-> k, v |-> v]], res |-> "ok", old |-> t.s[f].v]
    ELSE IF t.len >= n THEN [t |-> t, res |-> "full", old |-> 0]
    ELSE LET p == FirstFree(n, t, bk[k], n) IN
         IF p < 0 THEN [t |-> t, res |-> "full", old |-> 0]
         ELSE [t |-> [s |-> [t.s EXCEPT ![p] = [k |-> k, v |-> v]], len |-> t.len + 1], res |-> "ok", old |-> 0]

\* the cyclic test of remove_at: the entry at j may not move into the hole unless its ideal slot lies outside (hole, j]
Stays(hole, j, ideal) == IF hole <= j THEN hole < ideal /\ ideal <= j ELSE hole < ideal \/ ideal <= j

\* the backward shift loop of remove_at, from `hole`, scanning j = hole + 1 ...
RECURSIVE Shift(_, _, _, _, _, _)
Shift(n, bk, s, hole, j, left) ==
    IF left = 0 THEN s
    ELSE LET j2 == (j + 1) % n IN
         IF s[j2].k = 0 THEN s
         ELSE IF Stays(hole, j2, bk[s[j2].k]) THEN Shift(n, bk, s, hole, j2, left - 1)
         ELSE Shift(n, bk, [s EXCEPT ![hole] = s[j2], ![j2] = Free], j2, j2, left - 1)

\* Table::remove_at (the slot is occupied)
RemoveAt(n, bk, t, i) ==
    [s |-> Shift(n, bk, [t.s EXCEPT ![i] = Free], i, i, n), len |-> t.len - 1]

\* Table::remove: found is whether k was present and v its value
Remove(n, bk, t, k) ==
    LET f == Find(n, bk, t, k) IN
    IF f < 0 THEN [t |-> t, found |-> FALSE, v |-> 0]
    ELSE [t |-> RemoveAt(n, bk, t, f), found |-> TRUE, v |-> t.s[f].v]

\* Table::retain with the predicate "the value is odd": the scan index only moves on when the slot was kept or empty.
\* visited is the set of keys the predicate was called on.
RECURSIVE RetainFrom(_, _, _, _, _)
RetainFrom(n, bk, t, i, vis) ==
    IF i >= n THEN [t |-> t, vis |-> vis]
    ELSE IF t.s[i].k = 0 THEN RetainFrom(n, bk, t, i + 1, vis)
    ELSE IF t.s[i].v % 2 = 1 THEN RetainFrom(n, bk, t, i + 1, vis \cup {t.s[i].k})
    ELSE RetainFrom(n, bk, RemoveAt(n, bk, t, i), i, vis \cup {t.s[i].k})
RetainOdd(n, bk, t) == RetainFrom(n, bk, t, 0, {})

\* the map the slots hold
Keys(t, n) == {t.s[i].k : i \in {j \in 0..(n - 1) : t.s[j].k # 0}}
MapOf(t, n) == [k \in Keys(t, n) |-> t.s[CHOOSE i \in 0..(n - 1) : t.s[i].k = k].v]

\* the entries in slot order, as Table::iter
RECURSIVE Entries(_, _, _)
Entries(n, t, i) == IF i >= n THEN <<>> ELSE IF t.s[i].k = 0 THEN Entries(n, t, i + 1) ELSE <<t.s[i]>> \o Entries(n, t, i + 1)

(* Cache: one slot per bucket *)
NewCache(n) == [i \in 0..(n - 1) |-> Free]
CachePut(c, bk, k, v) == [c EXCEPT ![bk[k]] = [k |-> k, v |-> v]]
CacheHit(c, bk, k) == c[bk[k]].k = k
=============================================================================
