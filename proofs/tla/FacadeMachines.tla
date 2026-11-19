---------------------------- MODULE FacadeMachines ----------------------------
(***************************************************************************)
(* Which pool of handshake machine boxes the facade's endpoints take:      *)
(* crates/pinc/src/node.rs `machines()` (with `std`: a clone of the        *)
(* thread's `MACHINES`; without: `Machines::new()`, the endpoint's own)    *)
(* and `AnyEp::new`, which calls it once and hands it to the endpoint with *)
(* `share_machines` before any slot exists (pinc-core endpoint.rs: only    *)
(* slots made after the call take it, and there are none yet).             *)
(*                                                                         *)
(* Two endpoints of one thread, each with H handshakes at once. STD picks  *)
(* the rule: one pool for both, or one each. A pool behaves as             *)
(* Machines.tla says (take the first full cell, put in the first empty     *)
(* one, allocate on an empty pool, free on a full one); its TakeCell and   *)
(* PutCell are reused here, instanced per pool, not rewritten. own[b] is   *)
(* the endpoint whose handshake allocated box b; cross records that a      *)
(* handshake took a box another endpoint allocated.                        *)
(*                                                                         *)
(* Checked, from the docs of `machines()` (both builds), MACHINES and      *)
(* `share_machines`:                                                       *)
(*  - OneHolder: a box is in one place: one handshake, one cell of one     *)
(*    pool, or freed;                                                      *)
(*  - OwnPool (without std): every box an endpoint holds or keeps idle is  *)
(*    one its own handshakes allocated (no box crosses endpoints);         *)
(*  - IdleBound: the idle boxes of the thread are at most B with std (one  *)
(*    pool however many endpoints) and B per endpoint without;            *)
(*  - AllocOnlyEmpty: a handshake allocates only when its endpoint's pool  *)
(*    is empty, so with std it reuses a box another endpoint returned.     *)
(* FacadeMachines_cross is a witness: with std a handshake takes a box     *)
(* the other endpoint allocated (NoCross fails).                           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets
CONSTANTS B, H, NB, STD
ASSUME B >= 1 /\ H >= 1 /\ NB >= 1 /\ STD \in BOOLEAN
VARIABLES cl, hs, own, freed, nb, cross
vars == <<cl, hs, own, freed, nb, cross>>

\* the pool's own operators, on the cells c of one pool (the other variables of Machines are not read by them)
M(c) == INSTANCE Machines WITH cells <- c, hs <- <<>>, done <- <<>>, secret <- {}, freed <- {}, nb <- 1,
                               last <- "init"

Eps == 1..2
Cells == 0..(B - 1)
Slots == 1..H
Home(e) == IF STD THEN 1 ELSE e

IdleIn(q) == {cl[q][j] : j \in {k \in Cells : cl[q][k] # 0}}
Idle == IdleIn(1) \cup IdleIn(2)
HeldBy(e) == {hs[e][h] : h \in {k \in Slots : hs[e][k] # 0}}
Held == HeldBy(1) \cup HeldBy(2)

Init == /\ cl = [q \in Eps |-> [j \in Cells |-> 0]]
        /\ hs = [e \in Eps |-> [h \in Slots |-> 0]]
        /\ own = [b \in 1..NB |-> 0]
        /\ freed = {} /\ nb = 1 /\ cross = FALSE

\* a handshake of endpoint e starts in slot h: `boxed` takes from the endpoint's pool, or allocates
Open(e, h) ==
    /\ hs[e][h] = 0
    /\ LET q == Home(e)
           j == M(cl[q])!TakeCell
       IN IF j >= 0
          THEN /\ hs' = [hs EXCEPT ![e][h] = cl[q][j]]
               /\ cl' = [cl EXCEPT ![q][j] = 0]
               /\ cross' = (cross \/ own[cl[q][j]] # e)
               /\ UNCHANGED <<own, nb>>
          ELSE /\ nb <= NB
               /\ hs' = [hs EXCEPT ![e][h] = nb]
               /\ own' = [own EXCEPT ![nb] = e]
               /\ nb' = nb + 1
               /\ UNCHANGED <<cl, cross>>
    /\ UNCHANGED freed

\* the handshake retires its machine (`confirm` or the connection's drop): put in the endpoint's pool, or freed
Retire(e, h) ==
    /\ hs[e][h] # 0
    /\ LET q == Home(e)
           b == hs[e][h]
           j == M(cl[q])!PutCell
       IN IF j >= 0 THEN cl' = [cl EXCEPT ![q][j] = b] /\ UNCHANGED freed
          ELSE freed' = freed \cup {b} /\ UNCHANGED cl
    /\ hs' = [hs EXCEPT ![e][h] = 0]
    /\ UNCHANGED <<own, nb, cross>>

Next == \E e \in Eps, h \in Slots : Open(e, h) \/ Retire(e, h)
Spec == Init /\ [][Next]_vars

TypeOK == /\ \A q \in Eps, j \in Cells : cl[q][j] \in 0..NB
          /\ \A e \in Eps, h \in Slots : hs[e][h] \in 0..NB
          /\ nb \in 1..(NB + 1) /\ cross \in BOOLEAN
OneHolder ==
    /\ \A q \in Eps : \A j, k \in Cells : (j # k /\ cl[q][j] # 0) => cl[q][j] # cl[q][k]
    /\ \A e, f \in Eps : \A g, h \in Slots : (<<e, g>> # <<f, h>> /\ hs[e][g] # 0) => hs[e][g] # hs[f][h]
    /\ IdleIn(1) \cap IdleIn(2) = {}
    /\ Idle \cap Held = {} /\ Idle \cap freed = {} /\ Held \cap freed = {}
    /\ Idle \cup Held \cup freed = 1..(nb - 1)
OwnPool == ~STD =>
    /\ \A e \in Eps : \A b \in HeldBy(e) \cup IdleIn(e) : own[b] = e
    /\ ~cross
IdleBound == Cardinality(Idle) <= (IF STD THEN B ELSE 2 * B)
AllocOnlyEmpty == [][nb' > nb => IdleIn(Home(own'[nb])) = {}]_vars

\* witness (with std): no handshake ever takes a box the other endpoint allocated
NoCross == ~cross
=============================================================================
