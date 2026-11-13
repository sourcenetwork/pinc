----------------------------- MODULE OrphanOps ------------------------------
(***************************************************************************)
(* The operations of vinc-core orphan.rs (Orphans), step for step: the     *)
(* endpoint's table of handshake fragments that arrived ahead of the       *)
(* datagram that starts their message. Orphan.tla checks them over every   *)
(* interleaving at small sizes; TraceOrphan.tla replays the recorded calls *)
(* of the real code.                                                       *)
(*                                                                         *)
(* The state o: slots (a fixed number of entries, each None or a held      *)
(* datagram), order (the place in the order of arrival the next datagram   *)
(* takes) and the four counters of the code. A held datagram is            *)
(* <<at, ord, key, loc, len, tag>>: when it arrived, its place in the      *)
(* order of arrival, the message it is a part of (the destination id, the  *)
(* message length and the address it came from, compared as one value),    *)
(* the local address it arrived on, its length, and tag, which stands for  *)
(* its bytes. max is the largest datagram held and life how long one stays *)
(* useful. The table has at least one entry (the code has 4).              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

None == <<>>
Orphan0(n) == [slots |-> [k \in 1..n |-> None], order |-> 0,
               held |-> 0, replayed |-> 0, expired |-> 0, evicted |-> 0]

Ord(s) == IF s = None THEN 0 ELSE s[2]
\* the code subtracts saturating at 0: a datagram stamped after `now` is not old
Stale(s, life, now) == s # None /\ now - s[1] > life
\* the first entry with the least order among the entries m
Least(sl, m) == CHOOSE k \in m : \A j \in m : Ord(sl[k]) < Ord(sl[j]) \/ (Ord(sl[k]) = Ord(sl[j]) /\ k <= j)
Lowest(m) == CHOOSE k \in m : \A j \in m : k <= j

\* expire: every datagram older than life is let go and counted
Expire(o, life, now) ==
    [o EXCEPT !.slots = [k \in DOMAIN o.slots |-> IF Stale(o.slots[k], life, now) THEN None ELSE o.slots[k]],
              !.expired = @ + Cardinality({k \in DOMAIN o.slots : Stale(o.slots[k], life, now)})]

\* hold: a datagram longer than max is refused before anything else; else the old ones are let go and the new one
\* takes the first free entry, or the entry of the oldest arrival, which is counted as evicted
Hold(o, max, life, now, key, loc, len, tag) ==
    IF len > max THEN [ok |-> FALSE, o |-> o]
    ELSE LET o1 == Expire(o, life, now)
             free == {k \in DOMAIN o1.slots : o1.slots[k] = None}
             k == IF free # {} THEN Lowest(free) ELSE Least(o1.slots, DOMAIN o1.slots)
         IN [ok |-> TRUE,
             o |-> [o1 EXCEPT !.slots[k] = <<now, o1.order, key, loc, len, tag>>,
                              !.order = @ + 1, !.held = @ + 1,
                              !.evicted = IF free = {} THEN @ + 1 ELSE @]]

\* take: the old ones are let go; the oldest arrival of the message `key` still held leaves the table and is given out
Take(o, life, now, key) ==
    LET o1 == Expire(o, life, now)
        m == {k \in DOMAIN o1.slots : o1.slots[k] # None /\ o1.slots[k][3] = key}
    IN IF m = {} THEN [out |-> None, o |-> o1]
       ELSE LET k == Least(o1.slots, m)
            IN [out |-> o1.slots[k], o |-> [o1 EXCEPT !.slots[k] = None, !.replayed = @ + 1]]

Waiting(o) == Cardinality({k \in DOMAIN o.slots : o.slots[k] # None})
=============================================================================
