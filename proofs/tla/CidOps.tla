------------------------------- MODULE CidOps -------------------------------
(***************************************************************************)
(* The operations of vinc-transport conn/cid.rs (Cids), step for step:     *)
(* the connection ids of one connection, derived from the session secret. *)
(* Cid.tla checks them over every interleaving at small sizes;             *)
(* TraceCid.tla replays the recorded calls of the real code.               *)
(*                                                                         *)
(* The code derives the id of index i as a keyed hash of the direction    *)
(* and i. Id(i) is that id, named by the least index that has it: two      *)
(* indices may share one (a collision of the hash, which a peer can search *)
(* for), Id(0) = 0 is the id the handshake carried, in both directions,    *)
(* and is not in the table. With no collision Id is the identity.          *)
(*                                                                         *)
(* The state c: ent (the LOCAL_SLOTS slots; idx = -1 is an empty slot,     *)
(* otherwise the derived index, the tick of its last use and whether an    *)
(* authenticated packet used it), hi (the highest index seen on an         *)
(* authenticated packet), tick, ns (the next index the sender takes), cf   *)
(* (the highest index the peer acknowledged a packet on), ru (how many ids *)
(* of the window were handed out again), sec (the secret is installed), fr *)
(* (the peer's first id is known).                                         *)
(*                                                                         *)
(* FIXED selects the eviction rule. TRUE is the rule of the code: an entry *)
(* at least LOOK below the highest index seen may make room, used by a     *)
(* packet or not, so the entries from hi - LOOK + 1 up are never evicted   *)
(* (a sender may still use them: its window is the LOOK indices after the  *)
(* highest one the peer answered on). FALSE is the earliest rule (only an  *)
(* entry a packet used makes room), which let unused entries fill the      *)
(* table until a lookahead id no longer had a slot (Cid_stale.cfg).        *)
(*                                                                         *)
(* SKIP selects the refill rule. TRUE is the rule of the code: from hi + 1 *)
(* on, until LOOK indices are held, within 2 * LOOK indices, an index      *)
(* whose id the table already accepts (the first id, or another index's)   *)
(* is not kept again and the next index takes its place, so no id is       *)
(* listed twice. FALSE is the rule before: the indices hi + 1 .. hi + LOOK *)
(* whatever their ids (Cid_dupid.cfg: an id listed twice).                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS SLOTS, LOOK, FIXED, SKIP, Id(_)

Empty == [idx |-> -1, used |-> 0, seen |-> FALSE]
Init0 == [ent |-> [s \in 1..SLOTS |-> Empty], hi |-> 0, tick |-> 0, ns |-> 0, cf |-> 0, ru |-> 0,
          sec |-> FALSE, fr |-> FALSE]

Has(c, k) == \E s \in 1..SLOTS : c.ent[s].idx = k
\* the table holds the id x (under any index)
HasId(c, x) == \E s \in 1..SLOTS : c.ent[s].idx >= 0 /\ Id(c.ent[s].idx) = x
\* is_local: the id x is the first id or one the table holds
IdLocal(c, x) == x = Id(0) \/ HasId(c, x)
Evictable(c, e) == e.idx >= 0 /\ (IF FIXED THEN e.idx + LOOK <= c.hi ELSE e.seen)
Cands(c) == {s \in 1..SLOTS : Evictable(c, c.ent[s])}
\* min over (used, slot) lexicographic
Lex(c, s, t) == c.ent[s].used < c.ent[t].used \/ (c.ent[s].used = c.ent[t].used /\ s <= t)
Victim(c) == CHOOSE s \in Cands(c) : \A t \in Cands(c) : Lex(c, s, t)
Free(c) == {s \in 1..SLOTS : c.ent[s].idx < 0}
FirstFree(c) == CHOOSE s \in Free(c) : \A t \in Free(c) : s <= t

\* refill for one index that is not held: the entry (ok, when a slot was free or could be made free) and the index
\* evicted (-1 for none)
Refill1(c, k) ==
    IF Free(c) # {}
    THEN LET s == FirstFree(c)
         IN [ok |-> TRUE, c |-> [c EXCEPT !.ent[s] = [idx |-> k, used |-> c.tick, seen |-> FALSE]], ev |-> -1]
    ELSE IF Cands(c) # {}
         THEN LET s == Victim(c)
              IN [ok |-> TRUE, c |-> [c EXCEPT !.ent[s] = [idx |-> k, used |-> c.tick, seen |-> FALSE]],
                  ev |-> c.ent[s].idx]
         ELSE [ok |-> FALSE, c |-> c, ev |-> -1]

\* refill from index j on, cov indices held or added so far; ev is the set of indices evicted. The code's loop: while
\* fewer than LOOK are covered and the index is below hi + 2 * LOOK, take the next index: a held one counts, one
\* whose id the table accepts is passed over, any other is added when a slot can be had and counts then
RECURSIVE RefillFrom(_, _, _, _)
RefillFrom(c, j, cov, ev) ==
    IF cov >= LOOK \/ j > c.hi + 2 * LOOK THEN [c |-> c, ev |-> ev]
    ELSE IF Has(c, j) THEN RefillFrom(c, j + 1, cov + 1, ev)
    ELSE IF IdLocal(c, Id(j)) THEN RefillFrom(c, j + 1, cov, ev)
    ELSE LET r == Refill1(c, j)
         IN RefillFrom(r.c, j + 1, IF r.ok THEN cov + 1 ELSE cov, IF r.ev >= 0 THEN ev \cup {r.ev} ELSE ev)

\* the rule before: the indices hi + 1 .. hi + LOOK, in order, whatever their ids
RECURSIVE RefillOld(_, _, _)
RefillOld(c, j, ev) ==
    IF j > c.hi + LOOK THEN [c |-> c, ev |-> ev]
    ELSE IF Has(c, j) THEN RefillOld(c, j + 1, ev)
    ELSE LET r == Refill1(c, j)
         IN RefillOld(r.c, j + 1, IF r.ev >= 0 THEN ev \cup {r.ev} ELSE ev)

Refill(c) ==
    IF ~c.sec THEN [c |-> c, ev |-> {}]
    ELSE IF SKIP THEN RefillFrom(c, c.hi + 1, 0, {}) ELSE RefillOld(c, c.hi + 1, {})

\* install: start deriving; the lookahead ids become routable
Install(c) == LET r == Refill([c EXCEPT !.sec = TRUE]) IN r

\* on_authenticated for a packet addressed to the id of index k: the first slot that holds that id is used and seen,
\* and the highest index moves up to its index (the first id is not in the table: a packet to it, or to an id no slot
\* holds, only moves the tick)
SlotsOf(c, x) == {t \in 1..SLOTS : c.ent[t].idx >= 0 /\ Id(c.ent[t].idx) = x}
Auth(c, k) ==
    LET c1 == [c EXCEPT !.tick = c.tick + 1]
        S == SlotsOf(c1, Id(k))
        s == CHOOSE t \in S : \A u \in S : t <= u
        j == c1.ent[s].idx
    IN IF S = {} THEN [c |-> c1, ev |-> {}]
       ELSE LET c2 == [c1 EXCEPT !.ent[s].seen = TRUE, !.ent[s].used = c1.tick]
            IN IF j > c.hi THEN Refill([c2 EXCEPT !.hi = j]) ELSE [c |-> c2, ev |-> {}]

SetFirstRemote(c) == [c EXCEPT !.fr = TRUE]

\* claim_remote: the index of the id for a path that needs one of its own, or -1. The next index while it is within
\* LOOK of the highest one confirmed, otherwise an index of that window again, turn by turn.
ClaimFresh(c) == c.ns <= c.cf + LOOK
ClaimIndex(c) == IF ClaimFresh(c) THEN c.ns ELSE c.cf + 1 + (c.ru % LOOK)
Claim(c) ==
    IF ~c.fr \/ (ClaimIndex(c) > 0 /\ ~c.sec) THEN [c |-> c, k |-> -1]
    ELSE [c |-> IF ClaimFresh(c) THEN [c EXCEPT !.ns = c.ns + 1] ELSE [c EXCEPT !.ru = c.ru + 1],
          k |-> ClaimIndex(c)]

\* confirm_remote: the peer acknowledged a packet sent with the id of index k
Confirm(c, k) == [c EXCEPT !.cf = IF k > c.cf THEN k ELSE c.cf]
\* remote_usable: the peer is known to accept the id of index k
RemoteUsable(c, k) == k = 0 \/ k > c.cf

IsLocal(c, k) == IdLocal(c, Id(k))
Held(c) == {c.ent[s].idx : s \in {t \in 1..SLOTS : c.ent[t].idx >= 0}}
Epoch(c) == (2 * c.hi) + (IF c.sec THEN 1 ELSE 0)
=============================================================================
