---------------------------- MODULE CoreRouteIndex ----------------------------
(***************************************************************************)
(* The endpoint's table of sessions by address (vinc-core endpoint.rs:     *)
(* by_route, sync_route, free_slot, session_from; Meta::route in slot.rs;  *)
(* the call of sync_route in timers.rs settle_core).                       *)
(*                                                                         *)
(* The story. A hub holds sessions in a few slots. A session's active path *)
(* may be validated and direct, from a remote address (cur). A datagram    *)
(* from that address is the session's: the hub's node and its relay ask    *)
(* the endpoint who sent it. The endpoint keeps a table from the address   *)
(* to the slot (idx), and each slot remembers the address it holds an      *)
(* entry under (route). Inputs (a datagram, a timer, a command) change a   *)
(* session's path inside an endpoint call: it is validated, it migrates,   *)
(* the peer's NAT rebinds, it stops being validated. Every call settles    *)
(* the sessions it touched before it returns, and settling brings the      *)
(* slot's entry in line with its path. A session that ends frees its slot, *)
(* which drops its entry. One more thing can happen inside any call: the   *)
(* table of address pairs evicts a pair, so a session that was not touched *)
(* loses its path without a settle (Evict).                                *)
(*                                                                         *)
(* What must never happen: between calls (no settle pending), the lookup   *)
(* gives a set of sessions other than the walk of every live session       *)
(* (Agree); a slot holds an entry its route does not name, two entries, or *)
(* the table holds more entries than there are slots (Exact).              *)
(*                                                                         *)
(* RED configurations, each a guard of the code taken away:                *)
(*  - CoreRouteIndex_nosync: settling leaves the entry alone (no call of   *)
(*    sync_route in settle_core). A validated path is never in the table, *)
(*    so the lookup misses its session: Agree fails.                       *)
(*  - CoreRouteIndex_nofree: free_slot keeps the slot's entry. The slot's  *)
(*    next session starts with no route (Meta::begin), so an entry is left *)
(*    that no route names: Exact fails.                                    *)
(*  - CoreRouteIndex_noverify: the lookup answers every holder without     *)
(*    checking its path. After an eviction the holder's path is gone but  *)
(*    its entry stays until its next settle, and the lookup answers it:    *)
(*    Agree fails.                                                         *)
(*  - CoreRouteIndex_keepold: a settle adds the new entry without taking   *)
(*    the old one out (a migration). The slot holds two entries: Exact     *)
(*    fails.                                                               *)
(* Lean counterpart: proofs/lean/Vinc/CoreRouteIndex*.lean (Inv, sync_inv, *)
(* free_inv, len_le, candidates_eq_walk, settle_complete, lose_complete).  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

\* Slots: the endpoint's slots (its K). Addrs: the remote addresses. None: no address.
\* SYNC, FREE, VERIFY, REMOVE_OLD: the guards of the code; a RED configuration sets one to FALSE.
CONSTANTS Slots, Addrs, None, SYNC, FREE, VERIFY, REMOVE_OLD

\* live: the slot holds a session. cur: the address of the session's validated direct path, or None.
\* route: Meta::route. idx: the table's entries <<address, slot>>, oldest first. pending: slots touched by the
\* current call and not settled yet; empty between calls.
VARIABLES live, cur, route, idx, pending
vars == <<live, cur, route, idx, pending>>

\* The table holds at most one entry per slot: insert_dup refuses past that.
K == Cardinality(Slots)

\* The sequence without its first copy of e (Table::remove_pair; nothing when e is not held).
RemoveOne(s, e) ==
    IF \E j \in 1..Len(s) : s[j] = e
    THEN LET j == CHOOSE j \in 1..Len(s) : s[j] = e /\ \A m \in 1..(j - 1) : s[m] # e
         IN SubSeq(s, 1, j - 1) \o SubSeq(s, j + 1, Len(s))
    ELSE s

\* The slots the table holds under address a (Table::holders).
Holders(a) == {idx[j][2] : j \in {m \in 1..Len(idx) : idx[m][1] = a}}

\* session_from before its min: the holders of a whose path is from a now (unless VERIFY is off).
Lookup(a) == {i \in Holders(a) : ~VERIFY \/ (live[i] /\ cur[i] = a)}

\* The walk the table replaces: every live session whose path is from a now.
Walk(a) == {i \in Slots : live[i] /\ cur[i] = a}

Init ==
    /\ live = [i \in Slots |-> FALSE]
    /\ cur = [i \in Slots |-> None]
    /\ route = [i \in Slots |-> None]
    /\ idx = <<>>
    /\ pending = {}

\* A new session takes a free slot: Meta::begin clears its route. It is settled before the call returns.
Open(i) ==
    /\ pending = {}
    /\ ~live[i]
    /\ live' = [live EXCEPT ![i] = TRUE]
    /\ cur' = [cur EXCEPT ![i] = None]
    /\ route' = [route EXCEPT ![i] = None]
    /\ pending' = {i}
    /\ UNCHANGED idx

\* An input gives the session a validated direct path from a: validation, migration, a NAT rebind.
Path(i, a) ==
    /\ pending = {}
    /\ live[i]
    /\ cur' = [cur EXCEPT ![i] = a]
    /\ pending' = {i}
    /\ UNCHANGED <<live, route, idx>>

\* An input takes the path away (no longer validated, or the active path is a relay's).
Unpath(i) ==
    /\ pending = {}
    /\ live[i]
    /\ cur' = [cur EXCEPT ![i] = None]
    /\ pending' = {i}
    /\ UNCHANGED <<live, route, idx>>

\* Inside some call, the table of address pairs evicts the pair of session i's path: its path is gone and nobody
\* settles it for it. Its own next input settles it.
Evict(i) ==
    /\ live[i]
    /\ cur[i] # None
    /\ cur' = [cur EXCEPT ![i] = None]
    /\ UNCHANGED <<live, route, idx, pending>>

\* settle_core's sync_route: when the entry and the path disagree, the old entry leaves (REMOVE_OLD) and the new one
\* goes in while the table has room; a refused one leaves the slot without an entry.
Settle(i) ==
    /\ i \in pending
    /\ pending' = pending \ {i}
    /\ IF SYNC /\ route[i] # cur[i]
       THEN LET kept == IF REMOVE_OLD /\ route[i] # None THEN RemoveOne(idx, <<route[i], i>>) ELSE idx
            IN IF cur[i] # None /\ Len(kept) < K
               THEN /\ idx' = Append(kept, <<cur[i], i>>)
                    /\ route' = [route EXCEPT ![i] = cur[i]]
               ELSE /\ idx' = kept
                    /\ route' = [route EXCEPT ![i] = None]
       ELSE UNCHANGED <<idx, route>>
    /\ UNCHANGED <<live, cur>>

\* The session ends and free_slot runs: the slot's entry leaves (FREE) and the slot holds none.
Close(i) ==
    /\ pending = {}
    /\ live[i]
    /\ live' = [live EXCEPT ![i] = FALSE]
    /\ cur' = [cur EXCEPT ![i] = None]
    /\ idx' = IF FREE /\ route[i] # None THEN RemoveOne(idx, <<route[i], i>>) ELSE idx
    /\ route' = [route EXCEPT ![i] = None]
    /\ UNCHANGED pending

Next ==
    \/ \E i \in Slots : Open(i) \/ Unpath(i) \/ Evict(i) \/ Settle(i) \/ Close(i)
    \/ \E i \in Slots, a \in Addrs : Path(i, a)

Spec == Init /\ [][Next]_vars

\* The types.
TypeOK ==
    /\ live \in [Slots -> BOOLEAN]
    /\ cur \in [Slots -> Addrs \cup {None}]
    /\ route \in [Slots -> Addrs \cup {None}]
    /\ pending \subseteq Slots

\* Between calls the lookup finds exactly the sessions the walk finds, at every address.
Agree == pending = {} => \A a \in Addrs : Lookup(a) = Walk(a)

\* Every entry is the one its slot's route names, a slot holds at most one, and the table holds at most K.
Exact ==
    /\ Len(idx) <= K
    /\ \A j \in 1..Len(idx) : route[idx[j][2]] = idx[j][1]
    /\ \A j, m \in 1..Len(idx) : j # m => idx[j][2] # idx[m][2]
    /\ \A i \in Slots : route[i] # None => \E j \in 1..Len(idx) : idx[j] = <<route[i], i>>
=============================================================================
