----------------------------- MODULE ConnectFound -----------------------------
(***************************************************************************)
(* Model check of the connect client's cache of verified lookup answers    *)
(* (pinc-connect client/conn.rs, `dns_answer`, `found`, `found_fresh`,     *)
(* `forget_found`; the operators are ConnectFoundOps.tla) over every       *)
(* interleaving of answers (every peer of PEERS, sequence of SEQS and home *)
(* of HOMES, stored at the clock), forgets and the clock moving on to      *)
(* TMAX, at a ring of N slots (FOUND, 8 in the code) and a lifetime of TTL *)
(* ticks (FOUND_TTL). OLD = TRUE answers with the rule before 6bd2f4db.    *)
(*                                                                         *)
(* `want` is the documented rule apart from the ring: for each peer, the   *)
(* entry with the highest sequence answered for it since its entry was     *)
(* last dropped (by a forget, or by an answer for another peer that left   *)
(* it no slot), the latest of equal sequences, with the clock of that      *)
(* answer. `ev` is the last step: its kind, peer and sequence.             *)
(*                                                                         *)
(* Checked, in every state reached:                                        *)
(*  - TypeOK;                                                              *)
(*  - OneSlot: at most one slot names a peer;                              *)
(*  - Newest: `found` gives `want` for every peer;                         *)
(*  - FreshTTL: `found_fresh` at any time n gives `want` when n is before  *)
(*    its time plus TTL and nothing at or after it;                        *)
(* and in every step:                                                      *)
(*  - LowerKeeps: an answer with a lower sequence than the held entry's    *)
(*    changes nothing of the cache (the entry, its time, `next`);          *)
(*  - HeldNoEvict: an answer for a held peer leaves `next` and every other *)
(*    peer's entry as they are;                                            *)
(*  - EvictAtNext: an entry goes only by a forget of its peer or by an     *)
(*    answer for a peer not held, and then it is the entry in the slot at  *)
(*    `next`. The ring's order is the order of first answers, not of use   *)
(*    or age: rewriting a held peer does not move it, so the entry that    *)
(*    goes is the one at `next`, which may have been answered last, and it *)
(*    goes even when another slot is empty (witness NoEvictWhileFree).     *)
(* Witnesses (TLC must violate them):                                      *)
(*  - with OLD: OneSlot (ConnectFound_w_old_slot.cfg) and Newest           *)
(*    (ConnectFound_w_old_newest.cfg), what 6bd2f4db fixed;                *)
(*  - NotLowerKept (an answer with a lower sequence was kept out),         *)
(*    NotStale (`found` gives an entry `found_fresh` does not), so those   *)
(*    cases are reached;                                                   *)
(*  - NoEvictWhileFree (ConnectFound_w_free.cfg): a FINDING, an answer for *)
(*    a peer not held evicts another peer's entry while a slot is empty;   *)
(*    only `forget_found` empties a slot, and nothing in the tree calls it *)
(*    yet.                                                                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N, PEERS, SEQS, HOMES, TTL, TMAX, OLD

ASSUME N >= 1 /\ TTL >= 1 /\ OLD \in BOOLEAN /\ 0 \notin PEERS

VARIABLES c, clock, want, ev
vars == <<c, clock, want, ev>>

INSTANCE ConnectFoundOps

Ev0 == [op |-> "init", p |-> 0, q |-> 0]

Init == c = C0 /\ clock = 0 /\ want = [p \in PEERS |-> NONE] /\ ev = Ev0

(* the documented rule for the answered peer: a lower sequence keeps what is wanted, an equal or higher one
   replaces it *)
Want(w, p, q, h, t) == IF w.e /\ q < w.seq THEN w ELSE Ent(p, q, h, t)

AnswerA ==
    \E p \in PEERS, q \in SEQS, h \in HOMES :
        LET c2 == IF OLD THEN AnswerOld(c, p, q, h, clock) ELSE Answer(c, p, q, h, clock)
        IN /\ c' = c2
           /\ want' = [x \in PEERS |-> IF x = p THEN Want(want[p], p, q, h, clock)
                                       ELSE IF Held(c2, x) = {} THEN NONE ELSE want[x]]
           /\ ev' = [op |-> "answer", p |-> p, q |-> q]
           /\ UNCHANGED clock

ForgetA ==
    \E p \in PEERS :
        /\ c' = Forget(c, p)
        /\ want' = [want EXCEPT ![p] = NONE]
        /\ ev' = [Ev0 EXCEPT !.op = "forget", !.p = p]
        /\ UNCHANGED clock

TickA ==
    /\ clock < TMAX
    /\ clock' = clock + 1
    /\ ev' = Ev0
    /\ UNCHANGED <<c, want>>

Next == AnswerA \/ ForgetA \/ TickA
Spec == Init /\ [][Next]_vars

Entries == {NONE} \cup {Ent(p, q, h, t) : p \in PEERS, q \in SEQS, h \in HOMES, t \in 0..clock}

TypeOK == /\ c.next \in 0..(N - 1)
          /\ clock \in 0..TMAX
          /\ \A k \in Slots : c.ring[k] \in Entries
          /\ \A p \in PEERS : want[p] \in Entries

OneSlot == \A p \in PEERS : Cardinality(Held(c, p)) <= 1

Newest == \A p \in PEERS : Found(c, p) = want[p]

FreshTTL == \A p \in PEERS, n \in 0..(TMAX + TTL) :
               FoundFresh(c, n, p) = IF want[p].e /\ n < want[p].t + TTL THEN want[p] ELSE NONE

LowerKeeps == [][(ev'.op = "answer" /\ Found(c, ev'.p).e /\ ev'.q < Found(c, ev'.p).seq) => c' = c]_vars

HeldNoEvict == [][(ev'.op = "answer" /\ Held(c, ev'.p) # {})
                  => (c'.next = c.next /\ \A x \in PEERS \ {ev'.p} : Found(c', x) = Found(c, x))]_vars

EvictAtNext == [][\A x \in PEERS : (Found(c, x).e /\ ~Found(c', x).e)
                    => \/ ev'.op = "forget" /\ ev'.p = x
                       \/ ev'.op = "answer" /\ Held(c, ev'.p) = {} /\ Names(c.ring, c.next + 1, x)]_vars

\* reachability witnesses
NotLowerKept == ~(ev.op = "answer" /\ Found(c, ev.p).e /\ ev.q < Found(c, ev.p).seq)
NotStale == ~(\E p \in PEERS : Found(c, p).e /\ ~FoundFresh(c, clock, p).e)

\* FINDING witness: eviction is by ring position, not by room
NoEvictWhileFree == [][(ev'.op = "answer" /\ \E x \in PEERS : Found(c, x).e /\ ~Found(c', x).e)
                       => \A k \in Slots : c.ring[k].e]_vars
=============================================================================
