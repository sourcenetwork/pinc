------------------------------ MODULE ReachOps ------------------------------
(***************************************************************************)
(* The operations of vinc-core reach.rs (ReachRing), step for step: the    *)
(* REACH_OUT bodies received from peers, in N (REACH_SLOTS = 4) places     *)
(* numbered from 0, each holding a session, its body and the stamp of its  *)
(* put, or nothing, and the ring's put counter `clock`.                    *)
(*                                                                         *)
(* A body is <<id, len>>: its place in the order of puts (0 where a trace  *)
(* does not know it) and its length; a held place is <<session, body,      *)
(* stamp>>. MX is REACH_BODY_MAX = 153. The code checks the length         *)
(* against MX itself.                                                      *)
(* Put: the counter moves on by one for every put, a refused one too. A    *)
(* body longer than MX changes nothing else and is lost: put returns 1.    *)
(* Otherwise the place is that of the session if it is held, else the     *)
(* first empty place, else the place with the smallest stamp, the body put *)
(* longest ago (min_by_key: the first such place, though the stamps of     *)
(* held places all differ); that place gets the session, the body and the  *)
(* counter as its stamp, so a refresh of a held session counts as a put.   *)
(* Put returns 1 when it overwrote the body of another session, else 0.    *)
(* Get: the body of the session, or None. N is at least 1 (the code       *)
(* returns 1 and keeps nothing for a ring of no places).                   *)
(*                                                                         *)
(* Two wrong rules for witness configs: dup puts a session that is held    *)
(* into a new place too (two bodies for a session), and newest overwrites  *)
(* the place with the largest stamp, the body put last, when the ring is   *)
(* full.                                                                   *)
(***************************************************************************)
EXTENDS Integers, Sequences

None == <<>>
Reach0(n) == [cells |-> [i \in 0..n - 1 |-> None], clock |-> 0]

Occ(c, n) == {i \in 0..n - 1 : c[i] # None}
Has(c, n, s) == \E i \in 0..n - 1 : c[i] # None /\ c[i][1] = s
Pos(c, n, s) == CHOOSE i \in 0..n - 1 : c[i] # None /\ c[i][1] = s
Full(c, n) == Occ(c, n) = 0..n - 1
\* position(Option::is_none)
FirstFree(c, n) == CHOOSE i \in 0..n - 1 : c[i] = None /\ \A j \in 0..i - 1 : c[j] # None
\* min_by_key over the stamps of a full ring: the first place of the smallest
Oldest(c, n) == CHOOSE i \in 0..n - 1 : /\ \A j \in 0..n - 1 : c[i][3] <= c[j][3]
                                        /\ \A j \in 0..i - 1 : c[i][3] < c[j][3]
Newest(c, n) == CHOOSE i \in 0..n - 1 : \A j \in 0..n - 1 : c[j][3] <= c[i][3]

RAt(r, n, s, dup, newest) ==
    IF ~dup /\ Has(r.cells, n, s) THEN Pos(r.cells, n, s)
    ELSE IF ~Full(r.cells, n) THEN FirstFree(r.cells, n)
    ELSE IF newest THEN Newest(r.cells, n)
    ELSE Oldest(r.cells, n)

RPut(r, n, mx, s, b, dup, newest) ==
    LET t == r.clock + 1
    IN IF b[2] > mx THEN [r EXCEPT !.clock = t]
       ELSE [cells |-> [r.cells EXCEPT ![RAt(r, n, s, dup, newest)] = <<s, b, t>>], clock |-> t]

\* what put returns: how many bodies were lost
RLost(r, n, mx, s, b, dup, newest) ==
    IF b[2] > mx THEN 1
    ELSE IF ~dup /\ Has(r.cells, n, s) THEN 0
    ELSE IF r.cells[RAt(r, n, s, dup, newest)] # None THEN 1 ELSE 0

RGet(r, n, s) == IF Has(r.cells, n, s) THEN r.cells[Pos(r.cells, n, s)][2] ELSE None
=============================================================================
