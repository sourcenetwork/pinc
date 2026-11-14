------------------------------ MODULE ReachOps ------------------------------
(***************************************************************************)
(* The operations of vinc-core reach.rs (ReachRing), step for step: the    *)
(* REACH_OUT bodies received from peers, in N (REACH_SLOTS = 4) places     *)
(* numbered from 0, each holding a session and its body or nothing, and a  *)
(* pointer `next`, the place the next session that is not held takes.      *)
(*                                                                         *)
(* A body is <<id, len>>: its place in the order of puts (0 where a trace  *)
(* does not know it) and its length; MX is REACH_BODY_MAX = 153. The code  *)
(* checks the length against MX itself: a longer body changes nothing.     *)
(* Put: the place of the session if it is held, else the place `next`;     *)
(* that place gets the session and the body; and the pointer moves on one  *)
(* (modulo N) when the place written was `next`, whether the session was   *)
(* held or not. Nothing counts a body that is overwritten or refused; the  *)
(* code has no counter. Get: the body of the session, or None.             *)
(*                                                                         *)
(* Two wrong rules for witness configs: dup puts a session that is held    *)
(* into the place `next` too (two bodies for a session), and newest        *)
(* overwrites the place filled last, not `next`, when the ring is full.    *)
(***************************************************************************)
EXTENDS Integers, Sequences

None == <<>>
Reach0(n) == [cells |-> [i \in 0..n - 1 |-> None], next |-> 0]

Occ(c, n) == {i \in 0..n - 1 : c[i] # None}
Has(c, n, s) == \E i \in 0..n - 1 : c[i] # None /\ c[i][1] = s
Pos(c, n, s) == CHOOSE i \in 0..n - 1 : c[i] # None /\ c[i][1] = s
Full(c, n) == Occ(c, n) = 0..n - 1

RAt(r, n, s, dup, newest) ==
    IF ~dup /\ Has(r.cells, n, s) THEN Pos(r.cells, n, s)
    ELSE IF newest /\ Full(r.cells, n) THEN (r.next + n - 1) % n
    ELSE r.next

RPut(r, n, mx, s, b, dup, newest) ==
    IF b[2] > mx THEN r
    ELSE LET at == RAt(r, n, s, dup, newest)
         IN [cells |-> [r.cells EXCEPT ![at] = <<s, b>>],
             next |-> IF at = r.next THEN (r.next + 1) % n ELSE r.next]

RGet(r, n, s) == IF Has(r.cells, n, s) THEN r.cells[Pos(r.cells, n, s)][2] ELSE None
=============================================================================
