------------------------------- MODULE CidOps -------------------------------
(***************************************************************************)
(* The operations of vinc-transport conn/cid.rs (Cids), step for step:     *)
(* the connection ids of one connection, derived from the session secret. *)
(* Cid.tla checks them over every interleaving at small sizes;             *)
(* TraceCid.tla replays the recorded calls of the real code.               *)
(*                                                                         *)
(* An id is known here by its index: the code derives the id of index i    *)
(* as a keyed hash of the direction and i, so two indices are two ids      *)
(* (the hash is a function of the index; a collision of four bytes is the  *)
(* candidate case the code leaves to the packet's authentication). Index 0 *)
(* is the id the handshake carried, in both directions, and is not in the  *)
(* table.                                                                  *)
(*                                                                         *)
(* The state c: ent (the LOCAL_SLOTS slots; idx = -1 is an empty slot,     *)
(* otherwise the derived index, the tick of its last use and whether an    *)
(* authenticated packet used it), hi (the highest index seen on an         *)
(* authenticated packet), tick, ns (the next index the sender takes), sec  *)
(* (the secret is installed), fr (the peer's first id is known).           *)
(*                                                                         *)
(* FIXED selects the eviction rule of the code: a stale entry (one below   *)
(* the highest seen index that no packet used) may make room as well as a  *)
(* seen one. FALSE is the earlier rule, which let stale entries fill the   *)
(* table until a lookahead id no longer had a slot (Cid_stale.cfg).        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS SLOTS, LOOK, FIXED

Empty == [idx |-> -1, used |-> 0, seen |-> FALSE]
Init0 == [ent |-> [s \in 1..SLOTS |-> Empty], hi |-> 0, tick |-> 0, ns |-> 0, sec |-> FALSE, fr |-> FALSE]

Has(c, k) == \E s \in 1..SLOTS : c.ent[s].idx = k
Evictable(c, e) == e.idx >= 0 /\ (e.seen \/ (FIXED /\ e.idx <= c.hi))
Cands(c) == {s \in 1..SLOTS : Evictable(c, c.ent[s])}
\* min over (used, slot) lexicographic
Lex(c, s, t) == c.ent[s].used < c.ent[t].used \/ (c.ent[s].used = c.ent[t].used /\ s <= t)
Victim(c) == CHOOSE s \in Cands(c) : \A t \in Cands(c) : Lex(c, s, t)
Free(c) == {s \in 1..SLOTS : c.ent[s].idx < 0}
FirstFree(c) == CHOOSE s \in Free(c) : \A t \in Free(c) : s <= t

\* refill for one index: the entry and the index evicted (-1 for none)
Refill1(c, k) ==
    IF Has(c, k) THEN [c |-> c, ev |-> -1]
    ELSE IF Free(c) # {}
         THEN LET s == FirstFree(c)
              IN [c |-> [c EXCEPT !.ent[s] = [idx |-> k, used |-> c.tick, seen |-> FALSE]], ev |-> -1]
         ELSE IF Cands(c) # {}
              THEN LET s == Victim(c)
                   IN [c |-> [c EXCEPT !.ent[s] = [idx |-> k, used |-> c.tick, seen |-> FALSE]], ev |-> c.ent[s].idx]
              ELSE [c |-> c, ev |-> -1]

\* refill: the indices hi + 1 .. hi + LOOK, in order; ev is the set of indices evicted
RECURSIVE RefillFrom(_, _, _)
RefillFrom(c, j, ev) ==
    IF j > c.hi + LOOK THEN [c |-> c, ev |-> ev]
    ELSE LET r == Refill1(c, j)
         IN RefillFrom(r.c, j + 1, IF r.ev >= 0 THEN ev \cup {r.ev} ELSE ev)
Refill(c) == IF ~c.sec THEN [c |-> c, ev |-> {}] ELSE RefillFrom(c, c.hi + 1, {})

\* install: start deriving; the lookahead ids become routable
Install(c) == LET r == Refill([c EXCEPT !.sec = TRUE]) IN r

\* on_authenticated for the id of index k (0 is the first id, which is not in the table, and any index not held)
Auth(c, k) ==
    LET c1 == [c EXCEPT !.tick = c.tick + 1]
        s == CHOOSE t \in 1..SLOTS : c1.ent[t].idx = k
    IN IF k < 1 \/ ~Has(c1, k) THEN [c |-> c1, ev |-> {}]
       ELSE LET c2 == [c1 EXCEPT !.ent[s].seen = TRUE, !.ent[s].used = c1.tick]
            IN IF k > c.hi THEN Refill([c2 EXCEPT !.hi = k]) ELSE [c |-> c2, ev |-> {}]

SetFirstRemote(c) == [c EXCEPT !.fr = TRUE]

\* claim_remote: the index of the id for a path that needs one of its own, or -1
Claim(c) ==
    IF ~c.fr \/ (c.ns > 0 /\ ~c.sec) THEN [c |-> c, k |-> -1]
    ELSE [c |-> [c EXCEPT !.ns = c.ns + 1], k |-> c.ns]

IsLocal(c, k) == k = 0 \/ Has(c, k)
Held(c) == {c.ent[s].idx : s \in {t \in 1..SLOTS : c.ent[t].idx >= 0}}
Epoch(c) == (2 * c.hi) + (IF c.sec THEN 1 ELSE 0)
=============================================================================
