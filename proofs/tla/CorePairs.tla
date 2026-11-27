------------------------------- MODULE CorePairs -------------------------------
(***************************************************************************)
(* The endpoint's table of address pairs (pinc-core endpoint.rs paths,     *)
(* path_id; rx.rs deliver; table.rs insert, which evicts the oldest pair   *)
(* when the table is full).                                                *)
(*                                                                         *)
(* The story. A datagram arrives from a pair of addresses. If the table    *)
(* holds the pair, its id is used. If not, an id is minted for it and the  *)
(* datagram goes to its session, which keeps the path only once the        *)
(* datagram authenticated (and within its four path slots). A command      *)
(* (a dial, a punch) adds a pair the session holds at once. A session      *)
(* drops a path (a slot replaced, a path lost, the session closed). The    *)
(* honest paths are bounded: four per session and ten table entries per    *)
(* session, so they fill at most HMAX < D entries.                         *)
(*                                                                         *)
(* What must never happen: a pair a session holds is not in the table     *)
(* (HeldStays), and the table holds a pair no session holds between calls *)
(* (Exact).                                                                *)
(*                                                                         *)
(* RED configurations:                                                     *)
(*  - CorePairs_mintfirst: the pair is minted, and kept, before the        *)
(*    datagram authenticated (the code before the fix of rx.rs deliver):   *)
(*    D forged datagrams with a known connection id push every held pair   *)
(*    out. HeldStays fails.                                                *)
(*  - CorePairs_norelease: a path a session drops keeps its entry (the     *)
(*    code before the release of dropped paths): orphans fill the table    *)
(*    and a new honest path pushes a held one out (EPHYRA_REPLAY=11:625 of *)
(*    world, where a punch that failed churned the pairs). HeldStays fails.*)
(*                                                                         *)
(* Why the earlier model let it through: CoreRouteIndex took the eviction  *)
(* as a given input (Evict) and checked only that the route index agrees   *)
(* after it; nothing asked who may cause an eviction or what it evicts.    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Pairs, D, HMAX, MINT_FIRST, RELEASE

VARIABLES tab, held
vars == <<tab, held>>

Range(s) == {s[i] : i \in DOMAIN s}
Without(s, p) == SelectSeq(s, LAMBDA x : x # p)
\* Insert as table.rs insert does: the oldest goes when the table is full.
Insert(s, p) == IF Len(s) < D THEN Append(s, p) ELSE Append(Tail(s), p)

Init == tab = <<>> /\ held = {}

\* A datagram from pair p; auth: it authenticated, and its session keeps the path.
Deliver(p, auth) ==
    LET keep == auth /\ Cardinality(held) < HMAX
    IN  IF p \in Range(tab)
        THEN /\ tab' = Append(Without(tab, p), p)
             /\ held' = IF keep THEN held \cup {p} ELSE held
        ELSE /\ tab' = IF keep \/ MINT_FIRST THEN Insert(tab, p) ELSE tab
             /\ held' = IF keep THEN held \cup {p} ELSE held

\* A command adds a path its session holds at once.
Add(p) == /\ Cardinality(held) < HMAX /\ p \notin held
          /\ tab' = Insert(Without(tab, p), p) /\ held' = held \cup {p}

\* A session drops a path.
Drop(p) == /\ p \in held /\ held' = held \ {p}
           /\ tab' = IF RELEASE THEN Without(tab, p) ELSE tab

Next == \E p \in Pairs : \/ Deliver(p, TRUE) \/ Deliver(p, FALSE) \/ Add(p) \/ Drop(p)

Spec == Init /\ [][Next]_vars

TypeOK == Len(tab) <= D /\ Cardinality(Range(tab)) = Len(tab) /\ held \subseteq Pairs
HeldStays == held \subseteq Range(tab)
Exact == Range(tab) = held
=============================================================================
