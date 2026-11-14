--------------------------------- MODULE Cid --------------------------------
(***************************************************************************)
(* Connection ids of vinc-transport conn/cid.rs over every interleaving of *)
(* the calls the connection makes, at small sizes (CidOps.tla has the      *)
(* operators).                                                             *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the table holds each derived index at most once and at most SLOTS    *)
(*    ids (Distinct), and lists no id twice: no two of its indices share   *)
(*    an id and none has the first id (IdsOnce; the refill before, which   *)
(*    took the LOOK next indices whatever their ids, breaks it when two    *)
(*    ids collide, Cid_dupid.cfg);                                         *)
(*  - once the secret is installed the id of each of the LOOK indices      *)
(*    after the highest one seen is accepted, so a packet on a fresh path  *)
(*    is routable (Lookahead; with no collision each of those indices is   *)
(*    held). Found: with a collision this does not hold. An index whose id *)
(*    an older entry holds is passed over, and that entry, once LOOK below *)
(*    the highest index seen, may make room, even for the index after the  *)
(*    one passed over, so the id of an index the sender may take next is   *)
(*    no longer accepted (Cid_collevict.cfg, at the code's sizes too).     *)
(*    The same holds of the ids of the LOOK indices up to the highest one  *)
(*    seen, which a sender may still use (WindowAccepted,                  *)
(*    Cid_collwin.cfg).                                                    *)
(*    Collisions with the first id only, which is never evicted, keep both *)
(*    (Cid_coll.cfg). A full table must hold an entry that may make room:  *)
(*    the entries that may not are the 2 * LOOK indices hi - LOOK + 1 ..   *)
(*    hi + LOOK, one of which is the index being added, so this needs      *)
(*    SLOTS >= 2 * LOOK (Cid.cfg is the tightest case; with one slot less  *)
(*    the lookahead is lost, Cid_slots.cfg);                               *)
(*  - an index the table forgot is at least LOOK below the highest one     *)
(*    seen and is never held again (RetiredStay): a retired id is never    *)
(*    accepted again, and no id from hi - LOOK + 1 up is ever retired;     *)
(*  - the sender takes none before the peer's first id is known, and none  *)
(*    beyond index 0 before the secret is installed (ClaimGate);           *)
(*  - an index the sender takes is 0 or one of the LOOK indices after the  *)
(*    highest one confirmed at that moment (ClaimWindow);                  *)
(*  - an index the sender takes for the first time is the next one, so the *)
(*    indices taken are 0 .. ns - 1 with none skipped, and an index it     *)
(*    takes otherwise is one it took before (FreshInOrder);                *)
(*  - the highest index confirmed is one the sender took (ConfirmedIssued; *)
(*    the connection confirms only the index a path claimed);              *)
(*  - the epoch changes whenever the set of accepted ids does              *)
(*    (EpochMoves).                                                        *)
(* The sender no longer takes each index once: past the window of the      *)
(* highest index confirmed it takes an index of the window again.          *)
(* IssuedOnce is the earlier statement, which Cid_reuse.cfg shows to fail. *)
(* Lean counterpart: proofs/lean/Vinc/TransportCid*.lean.                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS SLOTS, LOOK, FIXED, SKIP, KMAX, IDXMAX,
          COLL   \* the collisions: a set of <<j, i>>, i < j, i not itself in a pair as j: index j has the id of index i
VARIABLES c, ret, issued, k, gate, win, order, once
vars == <<c, ret, issued, k, gate, win, order, once>>
flags == <<gate, win, order, once>>

\* the collision sets of the configs, chosen with COLL <- in the .cfg
CollNone == {}
CollFirst == {<<1, 0>>, <<4, 0>>}   \* two indices with the first id
CollDup == {<<2, 1>>}               \* the first two indices share an id
CollEvict == {<<9, 1>>}             \* index 9 has the id of index 1, at the code's sizes
CollWin == {<<3, 2>>}               \* index 3 has the id of index 2

Id(j) == IF \E p \in COLL : p[1] = j THEN (CHOOSE p \in COLL : p[1] = j)[2] ELSE j
ASSUME \A p \in COLL : p[2] < p[1] /\ p[1] >= 1 /\ \A q \in COLL : q[1] # p[2] /\ (q[1] = p[1] => q = p)

INSTANCE CidOps

Init == c = Init0 /\ ret = {} /\ issued = {} /\ k = 0 /\ gate = TRUE /\ win = TRUE /\ order = TRUE /\ once = TRUE

InstA == ~c.sec /\ LET r == Install(c) IN c' = r.c /\ ret' = ret \cup r.ev /\ UNCHANGED <<issued, flags>>
FrA == ~c.fr /\ c' = SetFirstRemote(c) /\ UNCHANGED <<ret, issued, flags>>
AuthA == \E i \in 0..IDXMAX :
           LET r == Auth(c, i) IN c' = r.c /\ ret' = ret \cup r.ev /\ UNCHANGED <<issued, flags>>
ClaimA == LET r == Claim(c)
              took == r.k >= 0
              fresh == r.c.ns # c.ns
          IN /\ c' = r.c
             /\ issued' = IF took THEN issued \cup {r.k} ELSE issued
             /\ gate' = (gate /\ (took => ((r.k = 0 \/ c.sec) /\ c.fr)))
             /\ win' = (win /\ (took => (r.k = 0 \/ (c.cf < r.k /\ r.k <= c.cf + LOOK))))
             /\ order' = (order /\ (took => IF fresh THEN r.k = c.ns /\ r.c.ns = c.ns + 1 /\ r.k \notin issued
                                                     ELSE r.k \in issued)
                                /\ (~took => r.c = c))
             /\ once' = (once /\ (took => r.k \notin issued))
             /\ UNCHANGED ret
\* the connection confirms the index a path claimed
ConfirmA == \E j \in issued : c' = Confirm(c, j) /\ UNCHANGED <<ret, issued, flags>>

Next == (InstA \/ FrA \/ AuthA \/ ClaimA \/ ConfirmA) /\ k' = k + 1
Spec == Init /\ [][Next]_vars
Bound == k <= KMAX

Distinct == \A s, t \in 1..SLOTS : (s # t /\ c.ent[s].idx >= 0) => c.ent[s].idx # c.ent[t].idx
Lookahead == c.sec => \A j \in (c.hi + 1)..(c.hi + LOOK) : IsLocal(c, j)
IdsOnce == \A s, t \in 1..SLOTS : c.ent[s].idx >= 0 =>
               /\ Id(c.ent[s].idx) # Id(0)
               /\ (s # t /\ c.ent[t].idx >= 0 => Id(c.ent[s].idx) # Id(c.ent[t].idx))
RetiredStay == \A r \in ret : r + LOOK <= c.hi /\ ~Has(c, r)
ClaimGate == gate
ClaimWindow == win
FreshInOrder == issued = {j \in 0..(c.ns - 1) : TRUE} /\ order
ConfirmedIssued == c.cf = 0 \/ c.cf \in issued
Inv == Distinct /\ IdsOnce /\ RetiredStay /\ ClaimGate /\ ClaimWindow /\ FreshInOrder /\ ConfirmedIssued
\* with no collision the LOOK indices after the highest one seen are held themselves (the earlier statement)
HeldAhead == c.sec => \A j \in (c.hi + 1)..(c.hi + LOOK) : Has(c, j)
\* the ids a sender may still use, the indices from hi - LOOK + 1 to hi + LOOK, are all accepted (RetiredStay says it of
\* the indices the table held; this says it of the ids)
WindowAccepted == c.sec => \A j \in (c.hi - LOOK + 1)..(c.hi + LOOK) : j >= 1 => IsLocal(c, j)
\* the earlier statement: the sender takes each index once, in order, and never reuses one (false of the code now)
IssuedOnce == issued = {j \in 0..(c.ns - 1) : TRUE} /\ gate /\ once
\* no accepted id appears or disappears without the epoch moving
EpochMoves == [][(Held(c') # Held(c)) => Epoch(c') # Epoch(c)]_vars
=============================================================================
