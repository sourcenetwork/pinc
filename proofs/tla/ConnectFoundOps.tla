--------------------------- MODULE ConnectFoundOps ---------------------------
(***************************************************************************)
(* The cache of verified lookup answers of the connect client             *)
(* (pinc-connect client/conn.rs: the fields `found` and `found_next`,      *)
(* written by                                                              *)
(* `dns_answer`, read by `found` and `found_fresh`, cleared per peer by    *)
(* `forget_found`) as pure operators, at a ring of N slots (FOUND, 8 in    *)
(* the code) and a lifetime TTL (FOUND_TTL, 30 s). ConnectFound.tla (the   *)
(* model check) and MbtConnectFound.tla (the model-based test) use them.   *)
(*                                                                         *)
(* The cache is a record: `ring`, the slots as a sequence (the code's slot *)
(* k is ring[k + 1]), each empty (NONE) or an entry of a peer `p` with the *)
(* record's sequence `seq`, its home `h` (the content a later answer of    *)
(* the same sequence may change) and the clock `t` it was stored at; and   *)
(* `next`, the code's `found_next`, in 0 .. N - 1.                         *)
(*                                                                         *)
(* Answer is the rule since 6bd2f4db: a peer already held is rewritten in  *)
(* the first slot that names it and `next` stays; a peer not held takes    *)
(* the slot at `next` (whatever entry is there goes) and `next` moves on;  *)
(* an answer whose sequence is lower than the held entry's leaves the slot *)
(* as it is, its time included. AnswerOld is the rule before: every answer *)
(* takes the slot at `next`, whatever it holds, and `next` moves on.       *)
(* `found` and `found_fresh` read the first slot that names the peer.      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS N, TTL

NONE == [e |-> FALSE, p |-> 0, seq |-> 0, h |-> 0, t |-> 0]
Ent(p, q, h, t) == [e |-> TRUE, p |-> p, seq |-> q, h |-> h, t |-> t]

Slots == 1..N

C0 == [ring |-> [k \in Slots |-> NONE], next |-> 0]

Names(r, k, p) == r[k].e /\ r[k].p = p

Held(c, p) == {k \in Slots : Names(c.ring, k, p)}

(* the first slot naming p (Iterator::position, Iterator::find), 0 when none *)
First(c, p) == IF Held(c, p) = {} THEN 0 ELSE CHOOSE k \in Held(c, p) : \A j \in Held(c, p) : k <= j

(* dns_answer on a verified record of p with sequence q and home h, at the clock t *)
Answer(c, p, q, h, t) ==
    LET k == First(c, p)
        n == c.next % N
        slot == IF k > 0 THEN k ELSE n + 1
        old == c.ring[slot]
    IN [ring |-> IF old.e /\ old.p = p /\ q < old.seq THEN c.ring ELSE [c.ring EXCEPT ![slot] = Ent(p, q, h, t)],
        next |-> IF k > 0 THEN c.next ELSE (n + 1) % N]

(* dns_answer before 6bd2f4db *)
AnswerOld(c, p, q, h, t) ==
    LET n == c.next % N
    IN [ring |-> [c.ring EXCEPT ![n + 1] = Ent(p, q, h, t)], next |-> (n + 1) % N]

(* forget_found *)
Forget(c, p) == [c EXCEPT !.ring = [k \in Slots |-> IF Names(c.ring, k, p) THEN NONE ELSE c.ring[k]]]

(* found: the entry (its record), NONE for None *)
Found(c, p) == IF First(c, p) > 0 THEN c.ring[First(c, p)] ELSE NONE

SatSub(a, b) == IF a < b THEN 0 ELSE a - b

(* found_fresh at now: now.saturating_sub(at) < FOUND_TTL *)
FoundFresh(c, now, p) == LET f == Found(c, p) IN IF f.e /\ SatSub(now, f.t) < TTL THEN f ELSE NONE

(* the cache turned so that `next` is 0: slot j + 1 holds what the code's slot (j + next) % N holds *)
Rot(c) == [ring |-> [k \in Slots |-> c.ring[((k - 1 + c.next) % N) + 1]], next |-> 0]
=============================================================================
