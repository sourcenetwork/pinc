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
(*    (Lookahead). A full table must hold an entry that may make room: the *)
(*    entries that may not are the 2 * LOOK indices hi - LOOK + 1 .. hi +  *)
(*    LOOK, one of which is the index being added, so this needs SLOTS >=  *)
(*    2 * LOOK (Cid.cfg is the tightest case; with one slot less the       *)
(*    lookahead is lost, Cid_slots.cfg);                                   *)
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
CONSTANTS SLOTS, LOOK, FIXED, KMAX, IDXMAX
VARIABLES c, ret, issued, k, gate, win, order, once
vars == <<c, ret, issued, k, gate, win, order, once>>
flags == <<gate, win, order, once>>

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
Lookahead == c.sec => \A j \in (c.hi + 1)..(c.hi + LOOK) : Has(c, j)
RetiredStay == \A r \in ret : r + LOOK <= c.hi /\ ~Has(c, r)
ClaimGate == gate
ClaimWindow == win
FreshInOrder == issued = {j \in 0..(c.ns - 1) : TRUE} /\ order
ConfirmedIssued == c.cf = 0 \/ c.cf \in issued
Inv == Distinct /\ RetiredStay /\ ClaimGate /\ ClaimWindow /\ FreshInOrder /\ ConfirmedIssued
\* the earlier statement: the sender takes each index once, in order, and never reuses one (false of the code now)
IssuedOnce == issued = {j \in 0..(c.ns - 1) : TRUE} /\ gate /\ once
\* no accepted id appears or disappears without the epoch moving
EpochMoves == [][(Held(c') # Held(c)) => Epoch(c') # Epoch(c)]_vars
=============================================================================
