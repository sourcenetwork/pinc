------------------------------- MODULE CorePairs -------------------------------
(***************************************************************************)
(* The endpoint's table of address pairs (pinc-core endpoint.rs paths,     *)
(* path_id_minted, retain_pair, release_pair, drop_unheld_pair, free_slot, *)
(* the assertion of with_slots; timers.rs settle_core and sync_pairs;      *)
(* rx.rs deliver; commands.rs FlightPaths, Punch, connect; iface.rs        *)
(* addr_change; table.rs insert, which evicts the oldest entry when full). *)
(*                                                                         *)
(* The story. A call names pairs of addresses: a datagram its source, a    *)
(* command (a dial, the flight paths, a punch, an address change) up to NP *)
(* of them. Each is looked up; a pair the table lacks is minted into a     *)
(* free entry (an entry is evicted when the table is full) with the        *)
(* generation of the counter, and its id is the entry and the generation.  *)
(* The settle then brings the table in line with the paths the session    *)
(* now holds (sync_pairs): an id it took is retained, one it let go is     *)
(* released, and the last holder removes the pair; the counter advances    *)
(* when a pair goes from no holder to one. A pair the call minted that no  *)
(* session took is removed (drop_unheld_pair). A datagram that did not     *)
(* authenticate changes no session's paths. A session also loses a path   *)
(* (path_lost): the connection keeps its id as a gone path, which holds no *)
(* pair, and forgets it later. A closed session releases all its pairs    *)
(* (free_slot). Two sessions may hold one pair; it stays until both let   *)
(* go. A session holds at most NP paths, gone ones included.               *)
(*                                                                         *)
(* What must never happen: a pair a session holds is not in the table, or  *)
(* the table evicted a pair some session held (HeldStays); between calls   *)
(* the table holds exactly the pairs the sessions hold, each with as many  *)
(* references as holders (Exact), so at most NP * K pairs (Bound); an id a *)
(* connection keeps, a gone one included, never names another pair than   *)
(* the one it was minted for (NoAlias: the generation against a reused     *)
(* entry). The table of D = NP * (K + 1) holds the NP * K pairs held and   *)
(* the NP a command mints for a session that holds NP.                     *)
(*                                                                         *)
(* RED configurations:                                                     *)
(*  - CorePairs_mintfirst: a minted pair stays though nobody took it (the  *)
(*    code before drop_unheld_pair): forged datagrams fill the table and   *)
(*    push held pairs out. HeldStays fails.                                *)
(*  - CorePairs_norelease: a path a session drops keeps its entry (the     *)
(*    code before the release of dropped paths; EPHYRA_REPLAY=11:625 of    *)
(*    world, where a punch that failed churned the pairs). HeldStays fails.*)
(*  - CorePairs_tight: D = NP * K + 1, what the assertion of with_slots    *)
(*    admits: a command that mints NP pairs for a session that holds NP    *)
(*    evicts a held pair. HeldStays fails.                                 *)
(*  - CorePairs_nogen: the counter never advances: a gone id names the     *)
(*    pair minted later into its entry. NoAlias fails.                     *)
(*                                                                         *)
(* Not modelled: the order of the table (a full table evicts its lowest   *)
(* entry, the code its oldest; NoEvict, no eviction at all, does not      *)
(* depend on which); the wrap of the 32-bit counter (the check is bounded: it  *)
(* explores the behaviours whose counter stays at most GMAX); a path made  *)
(* gone in the call that minted it.                                        *)
(*                                                                         *)
(* Why the earlier model let it through: CoreRouteIndex took the eviction  *)
(* as a given input (Evict) and checked only that the route index agrees   *)
(* after it; nothing asked who may cause an eviction or what it evicts.    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Sess, NP, Addrs, D, GMAX, MINT_FIRST, RELEASE, GEN

Idx == 1..D
Free == [p |-> 0, g |-> 0, refs |-> 0]

\* tab[x]: entry x (p 0: free). ng: the generation counter. ev: an eviction took a
\* pair some session held. hold[s]: the ids of session s's live paths; gone[s]: the ids of its gone paths. An id is
\* <<entry, generation, pair>>: the pair is the model's own record of what the id was minted for, the code has only
\* the entry and the generation.
VARIABLES tab, ng, ev, evs, hold, gone
vars == <<tab, ng, ev, evs, hold, gone>>

St == [tab |-> tab, ng |-> ng, ev |-> ev, evs |-> evs]
Put(st) == tab' = st.tab /\ ng' = st.ng /\ ev' = st.ev /\ evs' = st.evs

Used(tb) == {x \in Idx : tb[x].p # 0}
Resolve(st, id) == st.tab[id[1]].p # 0 /\ st.tab[id[1]].g = id[2]
RemoveAt(st, x) == [st EXCEPT !.tab[x] = Free]
Lowest(S) == CHOOSE x \in S : \A z \in S : x <= z
Held(st, x) == \E s \in Sess : \E id \in hold[s] : id[1] = x /\ Resolve(st, id)

\* path_id_minted: the id of pair p, minted into the lowest free entry when the table lacks it
Mint(st, p) ==
    IF \E x \in Idx : st.tab[x].p = p
    THEN LET x == CHOOSE x \in Idx : st.tab[x].p = p
         IN [st |-> st, id |-> <<x, st.tab[x].g, p>>, m |-> FALSE]
    ELSE LET full == Used(st.tab) = Idx
             x0 == Lowest(Idx)
             s1 == IF full THEN [RemoveAt(st, x0) EXCEPT !.ev = @ \/ Held(st, x0), !.evs = TRUE] ELSE st
             y == Lowest({z \in Idx : s1.tab[z].p = 0})
         IN [st |-> [s1 EXCEPT !.tab[y] = [p |-> p, g |-> s1.ng, refs |-> 0]],
             id |-> <<y, s1.ng, p>>, m |-> TRUE]

Retain(st, id) ==
    IF ~Resolve(st, id) THEN st
    ELSE [st EXCEPT !.tab[id[1]].refs = @ + 1, !.ng = IF GEN /\ st.tab[id[1]].refs = 0 THEN @ + 1 ELSE @]
Release(st, id) ==
    IF ~RELEASE \/ ~Resolve(st, id) THEN st
    ELSE IF st.tab[id[1]].refs <= 1 THEN RemoveAt(st, id[1])
    ELSE [st EXCEPT !.tab[id[1]].refs = @ - 1]
DropUnheld(st, id) ==
    IF ~MINT_FIRST /\ Resolve(st, id) /\ st.tab[id[1]].refs = 0 THEN RemoveAt(st, id[1]) ELSE st

RECURSIVE MintAll(_, _), RetainAll(_, _), ReleaseAll(_, _), DropAll(_, _)
MintAll(st, P) ==
    IF P = {} THEN [st |-> st, ids |-> {}, ms |-> {}]
    ELSE LET p == CHOOSE p \in P : TRUE
             a == Mint(st, p)
             r == MintAll(a.st, P \ {p})
         IN [st |-> r.st, ids |-> r.ids \cup {a.id}, ms |-> r.ms \cup (IF a.m THEN {a.id} ELSE {})]
RetainAll(st, S) == IF S = {} THEN st ELSE LET x == CHOOSE x \in S : TRUE IN RetainAll(Retain(st, x), S \ {x})
ReleaseAll(st, S) == IF S = {} THEN st ELSE LET x == CHOOSE x \in S : TRUE IN ReleaseAll(Release(st, x), S \ {x})
DropAll(st, S) == IF S = {} THEN st ELSE LET x == CHOOSE x \in S : TRUE IN DropAll(DropUnheld(st, x), S \ {x})

\* sync_pairs: retain what the session took, then release what it let go
Sync(st, old, new) == ReleaseAll(RetainAll(st, new \ old), old \ new)

\* the paths session s holds after a call that named ids C: it takes each of them it does not hold, and when its NP
\* slots (gone paths included) are full a new path replaces a live one (new_path_slot); it drops paths with Drop
Room(s) == NP - Cardinality(gone[s])
Settle(s, C) ==
    LET new == C \ hold[s]
        all == hold[s] \cup new
        n == IF Cardinality(all) <= Room(s) THEN Cardinality(all) ELSE Room(s)
    IN {H \in SUBSET all : Cardinality(H) = n /\ (new \subseteq H \/ H \subseteq new)}

Init == /\ tab = [x \in Idx |-> Free] /\ ng = 1 /\ ev = FALSE /\ evs = FALSE
        /\ hold = [s \in Sess |-> {}] /\ gone = [s \in Sess |-> {}]

\* A call for session s that names the pairs P and whose session takes them (an authenticated datagram, a command).
Call(s, P) ==
    LET a == MintAll(St, P)
    IN \E H \in Settle(s, a.ids) :
         /\ Put(DropAll(Sync(a.st, hold[s], H), a.ms))
         /\ hold' = [hold EXCEPT ![s] = H]
         /\ UNCHANGED gone

\* A datagram from pair p that did not authenticate: it changes no session's paths.
Forged(p) ==
    LET a == MintAll(St, {p})
    IN /\ Put(DropAll(a.st, a.ms))
       /\ UNCHANGED <<hold, gone>>

\* The session lets a path go (a slot replaced, removal, idle out); the settle releases its pair.
Drop(s, id) ==
    /\ id \in hold[s]
    /\ Put(Sync(St, hold[s], hold[s] \ {id}))
    /\ hold' = [hold EXCEPT ![s] = @ \ {id}]
    /\ UNCHANGED gone

\* forget_gone: the connection forgets a gone path.
Forget(s, id) ==
    /\ id \in gone[s]
    /\ gone' = [gone EXCEPT ![s] = @ \ {id}]
    /\ UNCHANGED <<tab, ng, ev, evs, hold>>

\* path_lost: the connection keeps the id as a gone path, and the settle releases its pair.
Lose(s, id) ==
    /\ id \in hold[s]
    /\ Put(Sync(St, hold[s], hold[s] \ {id}))
    /\ hold' = [hold EXCEPT ![s] = @ \ {id}]
    /\ gone' = [gone EXCEPT ![s] = @ \cup {id}]

\* free_slot: the session closes and gives back every pair; a new session may take the slot.
Close(s) ==
    /\ hold[s] \cup gone[s] # {}
    /\ Put(ReleaseAll(St, hold[s]))
    /\ hold' = [hold EXCEPT ![s] = {}]
    /\ gone' = [gone EXCEPT ![s] = {}]

Next ==
    \/ \E p \in Addrs : Forged(p)
    \/ \E s \in Sess :
        \/ \E P \in SUBSET Addrs : P # {} /\ Cardinality(P) <= NP /\ Call(s, P)
        \/ \E id \in hold[s] : Lose(s, id) \/ Drop(s, id)
        \/ \E id \in gone[s] : Forget(s, id)
        \/ Close(s)

Spec == Init /\ [][Next]_vars

Small == ng <= GMAX
\* the main configs name the sessions and the pairs by model values: no rule tells two pairs or two sessions apart
Sym == Permutations(Addrs) \cup Permutations(Sess)

AllIds == UNION {hold[s] \cup gone[s] : s \in Sess}
TypeOK == /\ \A s \in Sess : Cardinality(hold[s]) + Cardinality(gone[s]) <= NP
HeldStays == ~ev /\ \A s \in Sess : \A id \in hold[s] : Resolve(St, id) /\ tab[id[1]].p = id[3]
Exact == /\ Used(tab) = {id[1] : id \in UNION {hold[s] : s \in Sess}}
         /\ \A x \in Used(tab) : tab[x].refs = Cardinality({s \in Sess : <<x, tab[x].g, tab[x].p>> \in hold[s]})
Bound == Cardinality(Used(tab)) <= NP * Cardinality(Sess)
\* the table never evicts (pair_evictions stays 0)
NoEvict == ~evs
NoAlias == \A id \in AllIds : Resolve(St, id) => tab[id[1]].p = id[3]
=============================================================================
