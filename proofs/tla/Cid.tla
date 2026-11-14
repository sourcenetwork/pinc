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
(*    held, HeldAhead), and so is the id of each of the LOOK indices up to *)
(*    the highest one seen, which a sender may still use (WindowAccepted), *)
(*    with collisions too: an index whose id an entry holds makes that     *)
(*    entry stand for it, with the newer index, so the entry is kept until *)
(*    every index it stands for is LOOK below the highest one seen         *)
(*    (Cid_collevict.cfg: index 9 with the id of index 1, at the code's 8  *)
(*    slots; Cid_collwin.cfg: index 3 with the id of index 2;              *)
(*    Cid_collmany.cfg: a class of three, a second pair and an index with  *)
(*    the first id; Cid_coll.cfg: two indices with the first id, which is  *)
(*    never evicted). The rule before #398 (BUMP = FALSE: the entry keeps  *)
(*    its older index and may make room while the index passed over is     *)
(*    still one a sender may use) fails both: Cid_skipevict.cfg            *)
(*    (Lookahead) and Cid_skipwin.cfg (WindowAccepted) are its witnesses.  *)
(*    A full table must hold an entry that may make room: the entries that *)
(*    may not are the 2 * LOOK indices hi - LOOK + 1 .. hi + LOOK, one of  *)
(*    which is the index being added, so with no collision this needs      *)
(*    SLOTS >= 2 * LOOK (Cid.cfg is the tightest case; with one slot less  *)
(*    the lookahead is lost, Cid_slots.cfg);                               *)
(*  - an entry the table evicted had its index (the newest it stood for)   *)
(*    at least LOOK below the highest one seen, and that index is never    *)
(*    held again (RetiredStay): no index from hi - LOOK + 1 up is ever     *)
(*    retired, and with no collision a retired id is never accepted again  *)
(*    (with one, the same id comes back only as the id of a later index    *)
(*    that derives it);                                                    *)
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
(*                                                                         *)
(* The highest index seen and the sender's index. A packet to an id that   *)
(* an entry holds for several indices moves the highest index seen to the  *)
(* newest of them, which the code cannot tell from the one the sender      *)
(* used; a packet to an index with the first id does not move it. With     *)
(* SENDER the model keeps top, the highest index of a packet the table     *)
(* accepted, and takes packets only to indices up to top + LOOK (a sender  *)
(* takes no index past LOOK above the highest one it saw confirmed, which  *)
(* is at most top; a late packet may carry any older index). The indices   *)
(* a sender may still use are then those from top - LOOK + 1 to           *)
(* top + LOOK, and TrueWindow says their ids are accepted. With no         *)
(* collision hi = top and TrueWindow is WindowAccepted. Found: with        *)
(* collisions it does not hold, at the code's 8 slots. hi can run ahead of *)
(* top (by up to 2 * LOOK for each packet to an entry a refill extended,   *)
(* with no bound but the number of collisions), and an entry of an index   *)
(* the sender may still use then makes room: Cid_overstate.cfg (index 7    *)
(* with the id of index 1 and index 9 with the id of index 8; packets to   *)
(* indices 2, 4, 6 and 8, the last read as 9, and index 7 loses its id)    *)
(* and Cid_overlate.cfg (index 8 with the id of index 3; with packets up  *)
(* to index 6, a late packet to index 3 is read as 8 and index 5 loses its *)
(* id). hi can also stay behind top: Cid_firstlag.cfg                      *)
(* (index 2 with the first id: a packet to it does not move hi, and index  *)
(* 4, which the sender takes once index 2 is confirmed, is not accepted    *)
(* until a packet to index 3 arrives). Each needs a collision of derived   *)
(* ids of four bytes, which a peer can search for and which harms only its *)
(* own connection.                                                         *)
(* Lean counterpart: proofs/lean/Vinc/TransportCid*.lean.                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS SLOTS, LOOK, FIXED, SKIP, BUMP, KMAX, IDXMAX,
          SENDER, \* packets only to indices a sender can have used: up to top + LOOK (TRUE), or to any index (FALSE)
          COLL   \* the collisions: a set of <<j, i>>, i < j, i not itself in a pair as j: index j has the id of index i
VARIABLES c, ret, issued, k, gate, win, order, once, top
vars == <<c, ret, issued, k, gate, win, order, once, top>>
flags == <<gate, win, order, once>>

\* the collision sets of the configs, chosen with COLL <- in the .cfg
CollNone == {}
CollFirst == {<<1, 0>>, <<4, 0>>}   \* two indices with the first id
CollDup == {<<2, 1>>}               \* the first two indices share an id
CollEvict == {<<9, 1>>}             \* index 9 has the id of index 1, at the code's sizes
CollWin == {<<3, 2>>}               \* index 3 has the id of index 2
CollMany == {<<3, 1>>, <<5, 1>>, <<4, 2>>, <<6, 0>>}   \* three indices with one id, a pair, one with the first id
CollOver == {<<7, 1>>, <<9, 8>>}    \* index 7 has the id of index 1, index 9 that of index 8
CollLate == {<<8, 3>>}              \* index 8 has the id of index 3
CollLag == {<<2, 0>>}               \* index 2 has the first id

Id(j) == IF \E p \in COLL : p[1] = j THEN (CHOOSE p \in COLL : p[1] = j)[2] ELSE j
ASSUME \A p \in COLL : p[2] < p[1] /\ p[1] >= 1 /\ \A q \in COLL : q[1] # p[2] /\ (q[1] = p[1] => q = p)

INSTANCE CidOps

Init == /\ c = Init0 /\ ret = {} /\ issued = {} /\ k = 0 /\ gate = TRUE /\ win = TRUE /\ order = TRUE /\ once = TRUE
        /\ top = 0

InstA == ~c.sec /\ LET r == Install(c) IN c' = r.c /\ ret' = ret \cup r.ev /\ UNCHANGED <<issued, flags, top>>
FrA == ~c.fr /\ c' = SetFirstRemote(c) /\ UNCHANGED <<ret, issued, flags, top>>
\* a packet to the id of index i authenticated; top moves only with SENDER (it stays 0 otherwise)
AuthA == \E i \in 0..IDXMAX :
           /\ SENDER => i <= top + LOOK
           /\ LET r == Auth(c, i) IN c' = r.c /\ ret' = ret \cup r.ev /\ UNCHANGED <<issued, flags>>
           /\ top' = IF SENDER /\ IsLocal(c, i) /\ i > top THEN i ELSE top
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
             /\ UNCHANGED <<ret, top>>
\* the connection confirms the index a path claimed
ConfirmA == \E j \in issued : c' = Confirm(c, j) /\ UNCHANGED <<ret, issued, flags, top>>

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
\* with SENDER: the ids of the indices a sender may still use, from top - LOOK + 1 to top + LOOK, are all accepted
TrueWindow == c.sec => \A j \in (top - LOOK + 1)..(top + LOOK) : j >= 1 => IsLocal(c, j)
\* the earlier statement: the sender takes each index once, in order, and never reuses one (false of the code now)
IssuedOnce == issued = {j \in 0..(c.ns - 1) : TRUE} /\ gate /\ once
\* no accepted id appears or disappears without the epoch moving
EpochMoves == [][(Held(c') # Held(c)) => Epoch(c') # Epoch(c)]_vars
=============================================================================
