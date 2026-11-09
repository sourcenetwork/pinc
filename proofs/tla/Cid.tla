--------------------------------- MODULE Cid --------------------------------
(***************************************************************************)
(* Connection ids of vinc-transport conn/cid.rs over every interleaving of *)
(* the calls the connection makes, at small sizes (CidOps.tla has the      *)
(* operators).                                                             *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the table holds each derived index at most once and at most SLOTS    *)
(*    ids (Distinct);                                                      *)
(*  - once the secret is installed the LOOK indices after the highest one  *)
(*    seen are always held, so a packet on a fresh path is routable        *)
(*    (Lookahead);                                                         *)
(*  - an index the table forgot is below the highest one seen and is never *)
(*    held again (RetiredStay, RetiredNeverBack): a retired id is never    *)
(*    accepted again;                                                      *)
(*  - the sender takes each index once, in order, and never reuses one     *)
(*    (IssuedOnce); it takes none before the peer's first id is known, and *)
(*    none beyond index 0 before the secret is installed (ClaimGate);      *)
(*  - the epoch changes whenever the set of accepted ids does              *)
(*    (EpochMoves).                                                        *)
(* Lean counterpart: proofs/lean/Vinc/TransportCid*.lean.                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS SLOTS, LOOK, FIXED, KMAX, IDXMAX
VARIABLES c, ret, issued, k, gate
vars == <<c, ret, issued, k, gate>>

INSTANCE CidOps

Init == c = Init0 /\ ret = {} /\ issued = {} /\ k = 0 /\ gate = TRUE

InstA == ~c.sec /\ LET r == Install(c) IN c' = r.c /\ ret' = ret \cup r.ev /\ UNCHANGED <<issued, gate>>
FrA == ~c.fr /\ c' = SetFirstRemote(c) /\ UNCHANGED <<ret, issued, gate>>
AuthA == \E i \in 0..IDXMAX :
           LET r == Auth(c, i) IN c' = r.c /\ ret' = ret \cup r.ev /\ UNCHANGED <<issued, gate>>
ClaimA == LET r == Claim(c)
          IN /\ c' = r.c
             /\ issued' = IF r.k >= 0 THEN issued \cup {r.k} ELSE issued
             /\ gate' = (gate /\ (r.k >= 0 => (r.k \notin issued /\ (r.k = 0 \/ c.sec) /\ c.fr)))
             /\ UNCHANGED ret

Next == (InstA \/ FrA \/ AuthA \/ ClaimA) /\ k' = k + 1
Spec == Init /\ [][Next]_vars
Bound == k <= KMAX

Distinct == \A s, t \in 1..SLOTS : (s # t /\ c.ent[s].idx >= 0) => c.ent[s].idx # c.ent[t].idx
Lookahead == c.sec => \A j \in (c.hi + 1)..(c.hi + LOOK) : Has(c, j)
RetiredStay == \A r \in ret : r <= c.hi /\ ~Has(c, r)
IssuedOnce == issued = {j \in 0..(c.ns - 1) : TRUE} /\ gate
Inv == Distinct /\ RetiredStay /\ IssuedOnce
\* no accepted id appears or disappears without the epoch moving
EpochMoves == [][(Held(c') # Held(c)) => Epoch(c') # Epoch(c)]_vars
=============================================================================
