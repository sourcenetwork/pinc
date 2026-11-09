--------------------------- MODULE ConnectTable ---------------------------
(***************************************************************************)
(* Model check of Table and Cache (relay/table.rs) over ConnectTableOps.   *)
(* The bucket function bk is chosen once, arbitrarily, so every hash is    *)
(* covered: the check holds for all of them (small N and key set).         *)
(*                                                                         *)
(*  SizeOk     len is the number of occupied slots and at most N          *)
(*  Unique     a key is in at most one slot                                *)
(*  Reachable  every key is found from its bucket without crossing an      *)
(*             empty slot (the probe invariant), so Find never misses it   *)
(*  Refines    after every operation the slots hold exactly the map that   *)
(*             a plain bounded map would: insert replaces or adds (and    *)
(*             answers "full" for a new key at capacity), remove returns  *)
(*             the value, retain keeps what the predicate keeps            *)
(*  Visited    retain calls the predicate on every entry at least once     *)
(*  CacheRule  put evicts exactly the previous occupant of the key's      *)
(*             bucket; get hits iff the bucket holds the key               *)
(* Lean: Vinc/ConnectTable.lean.                                           *)
(***************************************************************************)
EXTENDS ConnectTableOps

CONSTANTS N, KeySet, Vals, Mode
VARIABLES bk, t, m, vis, c, cm
vars == <<bk, t, m, vis, c, cm>>

Init == /\ bk \in [KeySet -> 0..(N - 1)]
        /\ t = NewTable(N) /\ m = [k \in {} |-> 0] /\ vis = {}
        /\ c = NewCache(N) /\ cm = [k \in {} |-> 0]

Del(f, k) == [x \in DOMAIN f \ {k} |-> f[x]]
Put(f, k, v) == [x \in DOMAIN f \cup {k} |-> IF x = k THEN v ELSE f[x]]

DoInsert(k, v) ==
    LET r == Insert(N, bk, t, k, v) IN
    /\ t' = r.t
    /\ m' = IF k \in DOMAIN m \/ Cardinality(DOMAIN m) < N THEN Put(m, k, v) ELSE m
    /\ (r.res = "ok") = (k \in DOMAIN m \/ Cardinality(DOMAIN m) < N)
    /\ r.res = "ok" /\ k \in DOMAIN m => r.old = m[k]
    /\ UNCHANGED <<bk, vis, c, cm>>

DoRemove(k) ==
    LET r == Remove(N, bk, t, k) IN
    /\ t' = r.t /\ m' = Del(m, k)
    /\ r.found = (k \in DOMAIN m) /\ (r.found => r.v = m[k])
    /\ UNCHANGED <<bk, vis, c, cm>>

DoRetain ==
    LET r == RetainOdd(N, bk, t) IN
    /\ t' = r.t /\ vis' = r.vis
    /\ m' = [k \in {x \in DOMAIN m : m[x] % 2 = 1} |-> m[k]]
    /\ DOMAIN m \subseteq r.vis
    /\ UNCHANGED <<bk, c, cm>>

DoCachePut(k, v) == /\ c' = CachePut(c, bk, k, v)
                    /\ cm' = Put([x \in DOMAIN cm \ {c[bk[k]].k} |-> cm[x]], k, v)
                    /\ UNCHANGED <<bk, t, m, vis>>

\* Mode "table" checks the Table operations, Mode "cache" the Cache; both together only multiply the state space
Next == \/ Mode = "table" /\ (\/ \E k \in KeySet, v \in Vals : DoInsert(k, v)
                              \/ \E k \in KeySet : DoRemove(k)
                              \/ DoRetain)
        \/ Mode = "cache" /\ \E k \in KeySet, v \in Vals : DoCachePut(k, v)

Spec == Init /\ [][Next]_vars

Occ == {i \in 0..(N - 1) : t.s[i].k # 0}
SizeOk == t.len = Cardinality(Occ) /\ t.len <= N
Unique == \A i, j \in Occ : t.s[i].k = t.s[j].k => i = j
\* the slots from the bucket of the key at i up to i are all occupied
Reachable == \A i \in Occ : \A d \in 0..(N - 1) :
                 (d <= (i - bk[t.s[i].k] + N) % N) => t.s[(bk[t.s[i].k] + d) % N].k # 0
Refines == /\ MapOf(t, N) = m /\ Cardinality(DOMAIN m) <= N
           /\ \A k \in KeySet : (Find(N, bk, t, k) >= 0) = (k \in DOMAIN m)
CacheRule == /\ \A k \in KeySet : CacheHit(c, bk, k) = (k \in DOMAIN cm)
             /\ \A k \in DOMAIN cm : c[bk[k]].k = k /\ c[bk[k]].v = cm[k]
=============================================================================
