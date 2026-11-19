------------------------------- MODULE Machines -------------------------------
(***************************************************************************)
(* The pool of handshake state-machine boxes the connections of a node     *)
(* share, pinc-transport conn/handshake.rs with `alloc`: Machines (`take`, *)
(* `put`, MACHINE_BOXES cells), `boxed` (Handshake::new takes a box, or    *)
(* allocates one when the pool is empty) and `Handshake::retire_machine`   *)
(* (from `confirm` and from Drop: shed the machine's secrets, give the box *)
(* back, or free it when the pool is full; nothing when it holds none).    *)
(*                                                                         *)
(* cells are the pool's cells (0 for empty, else a box id), hs the         *)
(* handshakes (0 when it holds no machine, else its box; a handshake that  *)
(* retired its machine may be replaced by a new connection's), secret the  *)
(* boxes whose machine holds secrets, freed the boxes deallocated, nb the  *)
(* next fresh box id.                                                      *)
(*                                                                         *)
(* Checked, from the docs of Machines, MACHINE_BOXES, the module and       *)
(* `retire_machine`:                                                       *)
(*  - OneHolder: a box is in exactly one place: one handshake, one cell,   *)
(*    or freed;                                                            *)
(*  - NoSecretIdle: a box returned to the pool holds no secrets;           *)
(*  - IdleBound: at most MACHINE_BOXES idle boxes;                         *)
(*  - AllocOnlyEmpty: a handshake allocates only when it finds the pool    *)
(*    empty (and takes an idle box otherwise);                             *)
(*  - FreeOnlyFull: a box is freed only when it finds the pool full;       *)
(*  - DoneHoldsNone: a handshake that retired (an established session, or  *)
(*    a connection gone) holds no machine.                                 *)
(* Machines_full is a reachability witness: a box finds the pool full and  *)
(* is freed.                                                               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets
CONSTANTS B, H, NB
ASSUME B >= 1 /\ H >= 1
VARIABLES cells, hs, done, secret, freed, nb, last
vars == <<cells, hs, done, secret, freed, nb, last>>

Cells == 0..(B - 1)
Hs == 1..H
Idle == {cells[j] : j \in {k \in Cells : cells[k] # 0}}
InHand == {hs[h] : h \in {k \in Hs : hs[k] # 0}}

\* `take`: the first non-empty cell's box, or 0
TakeCell == IF \E j \in Cells : cells[j] # 0
            THEN CHOOSE j \in Cells : cells[j] # 0 /\ \A m \in Cells : m < j => cells[m] = 0
            ELSE -1
\* `put`'s vacant cell: the first empty one, or -1
PutCell == IF \E j \in Cells : cells[j] = 0
           THEN CHOOSE j \in Cells : cells[j] = 0 /\ \A m \in Cells : m < j => cells[m] # 0
           ELSE -1

Init == /\ cells = [j \in Cells |-> 0] /\ hs = [h \in Hs |-> 0] /\ done = [h \in Hs |-> TRUE]
        /\ secret = {} /\ freed = {} /\ nb = 1 /\ last = "init"

\* Handshake::new through `boxed`: a new connection's handshake in place h (free, or retired)
Open == \E h \in Hs :
    /\ done[h]
    /\ LET j == TakeCell
       IN IF j >= 0
          THEN /\ hs' = [hs EXCEPT ![h] = cells[j]] /\ cells' = [cells EXCEPT ![j] = 0]
               /\ secret' = secret \cup {cells[j]} /\ UNCHANGED nb /\ last' = "took"
          ELSE /\ nb <= NB
               /\ hs' = [hs EXCEPT ![h] = nb] /\ nb' = nb + 1 /\ UNCHANGED cells
               /\ secret' = secret \cup {nb} /\ last' = "allocated"
    /\ done' = [done EXCEPT ![h] = FALSE] /\ UNCHANGED freed
\* `retire_machine` (from `confirm` or Drop): shed, then `put`, or free the box when no cell is vacant
Retire == \E h \in Hs :
    /\ ~done[h] /\ hs[h] # 0
    /\ LET b == hs[h]
           j == PutCell
       IN /\ secret' = secret \ {b}
          /\ IF j >= 0 THEN cells' = [cells EXCEPT ![j] = b] /\ UNCHANGED freed /\ last' = "returned"
             ELSE freed' = freed \cup {b} /\ UNCHANGED cells /\ last' = "freed"
    /\ hs' = [hs EXCEPT ![h] = 0] /\ done' = [done EXCEPT ![h] = TRUE] /\ UNCHANGED nb
\* `retire_machine` with no machine: returns at once
RetireNone == \E h \in Hs : hs[h] = 0 /\ UNCHANGED <<cells, hs, done, secret, freed, nb>> /\ last' = "none"

Next == Open \/ Retire \/ RetireNone
Spec == Init /\ [][Next]_vars

TypeOK == /\ \A j \in Cells : cells[j] \in 0..NB
          /\ \A h \in Hs : hs[h] \in 0..NB
OneHolder == /\ \A j, k \in Cells : (j # k /\ cells[j] # 0) => cells[j] # cells[k]
             /\ \A g, h \in Hs : (g # h /\ hs[g] # 0) => hs[g] # hs[h]
             /\ Idle \cap InHand = {} /\ Idle \cap freed = {} /\ InHand \cap freed = {}
             /\ Idle \cup InHand \cup freed = 1..(nb - 1)
NoSecretIdle == Idle \cap secret = {}
IdleBound == Cardinality(Idle) <= B
DoneHoldsNone == \A h \in Hs : done[h] => hs[h] = 0
AllocOnlyEmpty == [][nb' > nb => Idle = {}]_vars
FreeOnlyFull == [][freed' # freed => Cardinality(Idle) = B]_vars

\* a reachability witness: a box finds the pool full and is freed
NoneFreed == freed = {}
=============================================================================
