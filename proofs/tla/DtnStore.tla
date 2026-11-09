------------------------------- MODULE DtnStore -------------------------------
(***************************************************************************)
(* Model check of the charged store, vinc-dtn/src/store.rs (the Ledger).    *)
(* The operations are DtnStoreOps.tla, the definitions the trace check also *)
(* uses. The environment calls admit, expire, release and reclass with any  *)
(* key (of the bundle space 1 or the mailbox space 2: one ledger, one       *)
(* budget), any size, class and expiry, at any time (the clock of a call is *)
(* an input and may go back).                                               *)
(*                                                                          *)
(* The properties are stated on (L, act): act records the call, the ledger  *)
(* before it (pre) and what it returned, so each is a statement about one   *)
(* step, checked in every reachable state:                                  *)
(*   Inv                the charge is the sum of the sizes, within the      *)
(*                      budget; keys and admission numbers are distinct     *)
(*   LiveCustodyKept    no call evicts custody that has not expired         *)
(*   RefusalMovesNothing  every refused admission (a duplicate and an       *)
(*                      already expired item included) removes only the     *)
(*                      expired items: the swept ledger, the expired events *)
(*   AdmitIffFits       accepted exactly when the key is new after the      *)
(*                      sweep, the item is not itself expired (exp > now)   *)
(*                      and custody leaves room in bytes and in slots       *)
(*                      (FitsSpec does not use the code's sums); the error  *)
(*                      is dup, else expired, else the class's refusal      *)
(*   SweptKeyIsFresh    a key that expired but was not swept is admitted    *)
(*                      fresh, never refused as a duplicate                 *)
(*   EvictionOrder      expired items in slot order, then transit items     *)
(*                      only, oldest admission first, none older remains,   *)
(*                      and the last one was needed                         *)
(*   ReclassNeedsNoRoom, ReleaseExits, ExpireExits                          *)
(*   NoCrossEviction    (witness config) a mailbox admission evicting a     *)
(*                      bundle item: the ledger is shared                   *)
(* The Lean counterpart is proofs/lean/Vinc/DtnStore*.lean (every ledger).  *)
(***************************************************************************)
EXTENDS DtnStoreOps

CONSTANTS N, Budget, Keys, ByteVals, ExpVals, NowVals, MaxSeq

VARIABLES L, cross
vars == <<L, cross>>

Classes == {"custody", "transit"}
\* the keys of the check: two bundle ids and one mailbox id
KeysDef == {<<1, 1>>, <<1, 2>>, <<2, 1>>}

(* ---- the properties of one call, over the ledger before it (pre), the call and its result ---- *)

LiveCustodyKept(pre, post, now) ==
    \A e \in Ents(pre) : (e.cls = "custody" /\ e.exp > now) => e \in Ents(post)

AdmitProps(pre, key, bytes, cls, exp, now, r) ==
    LET post == r.L
        ev1 == ExpiredSeq(pre, now)
        sw == WithoutExpired(pre, now)
        ev2 == SubSeq(r.ev, Len(ev1) + 1, Len(r.ev))
    IN /\ LiveCustodyKept(pre, post, now)
       \* every refusal (duplicate and expired item included) removes only the expired items
       /\ r.err \in {"dup", "expired", "custody", "full"} => post = sw /\ r.ev = ev1
       \* the error: dup when the key is kept after the sweep, else expired, else the refusal of the class
       /\ (r.err = "dup") = Contains(sw, key)
       /\ (r.err = "expired") = (~Contains(sw, key) /\ exp <= now)
       /\ r.err \in {"custody", "full"} => r.err = IF cls = "custody" THEN "custody" ELSE "full"
       \* a key that expired but was not swept is admitted fresh
       /\ (\E e \in Ents(pre) : e.key = key /\ e.exp <= now) => r.err # "dup"
       \* accepted exactly when the key is new after the sweep, the item is live and custody leaves room
       /\ (r.err = "ok") = (~Contains(sw, key) /\ exp > now /\ FitsSpec(sw, bytes))
       /\ r.err = "ok" =>
            /\ Entry(key, bytes, cls, exp, pre.seq) \in Ents(post)
            /\ post.seq = pre.seq + 1
            /\ post.used <= post.budget
            /\ Len(r.ev) >= Len(ev1)
            /\ SubSeq(r.ev, 1, Len(ev1)) = ev1
            /\ \A k \in 1..Len(ev2) : ev2[k].cls = "transit" /\ ev2[k].exp > now
            /\ \A k \in 1..(Len(ev2) - 1) : ev2[k].seq < ev2[k + 1].seq
            /\ \A k \in 1..Len(ev2), q \in Ents(post) : q.cls = "transit" => ev2[k].seq < q.seq
            \* the last eviction was needed: without it the item would not have fit
            /\ ev2 # <<>> => (SatSub(post.budget, post.used - bytes + ev2[Len(ev2)].bytes) < bytes
                              \/ Count(post) = Len(post.slots))

ExpireProps(pre, now, r) ==
    /\ LiveCustodyKept(pre, r.L, now)
    /\ r.ev = ExpiredSeq(pre, now)
    /\ r.L = WithoutExpired(pre, now)

ReleaseProps(pre, key, r) ==
    /\ r.got = Contains(pre, key)
    /\ r.got => /\ Ents(r.L) = Ents(pre) \ {r.e} /\ r.e.key = key /\ r.L.used = pre.used - r.e.bytes
    /\ ~r.got => r.L = pre

ReclassProps(pre, key, r) ==
    /\ r.L.used = pre.used /\ r.L.seq = pre.seq /\ Count(r.L) = Count(pre)
    /\ r.ok = Contains(pre, key)
    /\ \A i \in 1..Len(pre.slots) : (pre.slots[i].full /\ pre.slots[i].key # key) => r.L.slots[i] = pre.slots[i]

Init == L = New(Budget, N) /\ cross = FALSE

AdmitStep == \E key \in Keys, bytes \in ByteVals, cls \in Classes, exp \in ExpVals, now \in NowVals :
    LET r == Admit(L, key, bytes, cls, exp, now) IN
    /\ Assert(AdmitProps(L, key, bytes, cls, exp, now, r), "an admission property is violated")
    /\ L' = r.L
    /\ cross' = (r.err = "ok" /\ key[1] = 2 /\ \E k \in 1..Len(r.ev) : r.ev[k].key[1] = 1 /\ r.ev[k].exp > now)

ExpireStep == \E now \in NowVals :
    LET r == Expire(L, now) IN
    /\ Assert(ExpireProps(L, now, r), "an expiry property is violated")
    /\ L' = r.L /\ cross' = FALSE

ReleaseStep == \E key \in Keys :
    LET r == Release(L, key) IN
    /\ Assert(ReleaseProps(L, key, r), "a release property is violated")
    /\ L' = r.L /\ cross' = FALSE

ReclassStep == \E key \in Keys, cls \in Classes :
    LET r == Reclass(L, key, cls) IN
    /\ Assert(ReclassProps(L, key, r), "a reclass property is violated")
    /\ L' = r.L /\ cross' = FALSE

Next == AdmitStep \/ ExpireStep \/ ReleaseStep \/ ReclassStep

Spec == Init /\ [][Next]_vars

Bounded == L.seq <= MaxSeq

(* ---- invariants ---- *)

Inv ==
    /\ Len(L.slots) = N
    /\ L.used = Total(L)
    /\ L.used <= L.budget
    /\ \A i, j \in Occ(L.slots) : i # j => L.slots[i].key # L.slots[j].key /\ L.slots[i].seq # L.slots[j].seq
    /\ \A i \in Occ(L.slots) : L.slots[i].seq < L.seq

\* witness: a mailbox admission that evicts a live bundle item (the ledger is shared by both spaces)
NoCrossEviction == ~cross
=============================================================================
