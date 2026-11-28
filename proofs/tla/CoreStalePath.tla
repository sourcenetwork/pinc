---------------------------- MODULE CoreStalePath ----------------------------
(***************************************************************************)
(* A connection's path whose address pair the endpoint no longer holds,   *)
(* and the order in which a datagram finds its addresses (pinc-core tx.rs  *)
(* poll_transmit, batch, send_stash, lose_path; timers.rs settle_core and  *)
(* sync_pairs; endpoint.rs path_addrs, free_slot; pinc-transport           *)
(* conn/path.rs path_lost, choose_path, forget_gone, set_path_info).       *)
(*                                                                         *)
(* The story. The endpoint names a path by an id into its table of        *)
(* address pairs; a pair stays while a session holds it (CorePairs.tla).  *)
(* A datagram finds the addresses of its path when it is built, before    *)
(* the settle of the call that built it (poll_transmit, batch); a          *)
(* datagram kept for the next call (another destination or size than the  *)
(* batch) keeps the addresses it was built with (StashMeta) and leaves for *)
(* them (send_stash looks nothing up). The settle may release a pair the   *)
(* datagram was built on: the connection forgot the path, or the session   *)
(* closed and freed its slot, its CLOSE built just before (Close); the     *)
(* datagram still leaves. A datagram built on a path whose pair is gone    *)
(* is dropped, and with TELL the connection is told (path_lost): the path  *)
(* is gone and unvalidated, the connection moves to a usable path at once *)
(* if it has one, or as soon as one validates, and forgets the gone path  *)
(* once it is not the active one. Only a fault takes the pair of a held    *)
(* path out (Evict, with FAULT: a table smaller than its bound, the        *)
(* eviction pair_evictions counts). The peer's datagrams mint new ids      *)
(* (Mint): a relayed path is validated at once (set_path_info), a direct   *)
(* one when its challenge is answered (Validate). The connection moves    *)
(* among usable paths by its own rules (Choose) and forgets a path that   *)
(* is not active (Forget, which releases its pair).                       *)
(*                                                                         *)
(* Checked:                                                                *)
(*  Told        an active path a datagram found without an address is     *)
(*              gone: the connection was told;                             *)
(*  Left        the connection stays on such a path only while it has no  *)
(*              other usable path the endpoint resolves;                   *)
(*  KeptLeaves  a datagram built while its pair was there is never         *)
(*              dropped: a kept one, a CLOSE whose settle freed the slot;  *)
(*  NeverLost   with no fault (CoreStalePath_nofault), no datagram is ever *)
(*              dropped.                                                   *)
(* RED configuration CoreStalePath_silent, TELL = FALSE (the code before  *)
(* the fix: the drop is only counted): the connection keeps the dead id   *)
(* as its active path while a resolvable path is usable beside it: Left   *)
(* fails.                                                                  *)
(* RED configuration CoreStalePath_late, LATE = TRUE (the order before:   *)
(* the addresses found after the settle, and a kept datagram's at the     *)
(* next call): a CLOSE whose settle freed the slot, or a kept datagram     *)
(* whose path was forgotten, finds nothing and is dropped: KeptLeaves      *)
(* fails, with no fault at all.                                            *)
(* Witness: CoreStalePath_w_recover (NoRecover: after a drop the active   *)
(* path is validated and resolvable again).                                *)
(* Not modelled: the endpoint's other sessions (only the fault's          *)
(* evictions), a pair shared by two sessions (CorePairs.tla), the          *)
(* recovery's repair of what was dropped, time.                           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

\* NP: the connection's path slots. TELL: the endpoint tells the connection of a drop. LATE: a datagram finds its
\* addresses after the settle, a kept one at the next call (the order before the fix). FAULT: a held pair can be evicted.
CONSTANTS NP, TELL, LATE, FAULT

Slots == 1..NP

\* t[x]: slot x. h: the connection tracks a path in it; v: validated; g: gone; r: the endpoint resolves its id;
\* f: a datagram on it found no address. act: the active slot. seen: a datagram was dropped. kept: the datagram kept for
\* the next call (s: its slot, 0 none, -1 a path since forgotten; at: its pair was there when it was built; b: it holds
\* its addresses; live: its pair is still there). freed: the session closed. lostBuilt: a datagram built while its pair
\* was there was dropped.
VARIABLES t, act, seen, kept, freed, lostBuilt
vars == <<t, act, seen, kept, freed, lostBuilt>>

Empty == [h |-> FALSE, v |-> FALSE, g |-> FALSE, r |-> FALSE, f |-> FALSE]
NoKept == [s |-> 0, at |-> FALSE, b |-> FALSE, live |-> FALSE]

\* the paths the connection may move onto: tracked, validated, not gone
Usable(tt) == {y \in Slots : tt[y].h /\ tt[y].v /\ ~tt[y].g}

\* choose_path from a gone active path: any usable path at once (the cost is not modelled), else stay
Reselect(tt, a) == IF tt[a].g /\ Usable(tt) # {} THEN Usable(tt) ELSE {a}

\* forget_gone: every gone path but the active one is forgotten (its pair released)
ForgetGone(tt, a) == [x \in Slots |-> IF x # a /\ tt[x].g THEN Empty ELSE tt[x]]

\* the kept datagram once the connection's paths are tt: a slot forgotten is no longer the datagram's path, and its pair
\* is gone once the slot no longer resolves
KeptAfter(tt) ==
    IF kept.s > 0 /\ ~(tt[kept.s].h /\ tt[kept.s].r)
    THEN [kept EXCEPT !.live = FALSE, !.s = IF tt[kept.s].h THEN kept.s ELSE -1]
    ELSE kept

\* the endpoint tells the connection path p is lost (path_lost): gone and unvalidated, then the reselect and forget_gone
Lose(tt, p) == LET uu == [tt EXCEPT ![p].g = TRUE, ![p].v = FALSE]
               IN \E a \in Reselect(uu, act) : /\ act' = a /\ t' = ForgetGone(uu, a)

Init ==
    /\ t = [x \in Slots |-> IF x = 1 THEN [Empty EXCEPT !.h = TRUE, !.v = TRUE, !.r = TRUE] ELSE Empty]
    /\ act = 1
    /\ seen = FALSE
    /\ kept = NoKept
    /\ freed = FALSE
    /\ lostBuilt = FALSE

\* A datagram of the peer from a new address mints an id into a free slot; a relayed one is validated at once.
Mint(x) ==
    /\ ~freed /\ ~t[x].h
    /\ \E v \in BOOLEAN :
         LET tt == [t EXCEPT ![x] = [Empty EXCEPT !.h = TRUE, !.v = v, !.r = TRUE]]
         IN \E a \in Reselect(tt, act) : /\ act' = a /\ t' = ForgetGone(tt, a)
    /\ kept' = KeptAfter(t')
    /\ UNCHANGED <<seen, freed, lostBuilt>>

\* A challenge on a direct path is answered: its datagrams must leave, so the endpoint resolves it.
Validate(x) ==
    /\ ~freed
    /\ t[x].h /\ ~t[x].v /\ ~t[x].g /\ t[x].r
    /\ LET tt == [t EXCEPT ![x].v = TRUE]
       IN \E a \in Reselect(tt, act) : /\ act' = a /\ t' = ForgetGone(tt, a)
    /\ kept' = KeptAfter(t')
    /\ UNCHANGED <<seen, freed, lostBuilt>>

\* The connection's own move onto a usable path (choose_path for a lower round trip, follow_peer, relay_fallback).
Choose ==
    /\ ~freed
    /\ \E y \in Usable(t) : /\ act' = y /\ t' = ForgetGone(t, y)
    /\ kept' = KeptAfter(t')
    /\ UNCHANGED <<seen, freed, lostBuilt>>

\* The fault: the table evicts the pair of a tracked path; nobody tells the connection.
Evict(x) ==
    /\ FAULT /\ ~freed
    /\ t[x].h /\ t[x].r
    /\ t' = [t EXCEPT ![x].r = FALSE]
    /\ kept' = KeptAfter(t')
    /\ UNCHANGED <<act, seen, freed, lostBuilt>>

\* A datagram built on the active path finds no address and is dropped; with TELL the connection is told (path_lost).
Send ==
    /\ ~freed
    /\ ~t[act].r
    /\ seen' = TRUE
    /\ IF TELL
       THEN Lose([t EXCEPT ![act].f = TRUE], act)
       ELSE /\ t' = [t EXCEPT ![act].f = TRUE]
            /\ UNCHANGED act
    /\ kept' = KeptAfter(t')
    /\ UNCHANGED <<freed, lostBuilt>>

\* A datagram built on the active path is kept for the next call. It holds its addresses unless LATE; a datagram whose
\* pair is not there when it is built is the drop of Send, unless LATE, where nothing is looked up yet.
Keep ==
    /\ ~freed
    /\ kept.s = 0
    /\ LATE \/ t[act].r
    /\ kept' = [s |-> act, at |-> t[act].r, b |-> ~LATE, live |-> t[act].r]
    /\ UNCHANGED <<t, act, seen, freed, lostBuilt>>

\* The next call deals with the kept datagram first (send_stash): it leaves for the addresses it holds; with LATE it
\* leaves only if its pair is still there, else it is dropped and, with TELL, the path it was built on is told if the
\* connection still tracks it.
KeptOut ==
    /\ ~freed
    /\ kept.s # 0
    /\ kept' = NoKept
    /\ IF kept.b \/ kept.live
       THEN UNCHANGED <<t, act, seen, freed, lostBuilt>>
       ELSE /\ seen' = TRUE
            /\ lostBuilt' = (lostBuilt \/ kept.at)
            /\ IF kept.s < 0
               THEN UNCHANGED <<t, act>>
               ELSE IF TELL
               THEN Lose([t EXCEPT ![kept.s].f = TRUE], kept.s)
               ELSE /\ t' = [t EXCEPT ![kept.s].f = TRUE]
                    /\ UNCHANGED act
            /\ UNCHANGED freed

\* The connection closes: its CLOSE is built on the active path, then the settle frees the slot (free_slot), which
\* releases every pair. The CLOSE found its addresses when it was built and leaves; with LATE it finds them after the
\* settle, and they are gone.
Close ==
    /\ ~freed
    /\ kept.s = 0
    /\ freed' = TRUE
    /\ seen' = (seen \/ LATE \/ ~t[act].r)
    /\ lostBuilt' = (lostBuilt \/ (LATE /\ t[act].r))
    /\ t' = [x \in Slots |-> Empty]
    /\ UNCHANGED <<act, kept>>

\* The connection forgets a path that is not active (idle out, removal); the settle releases its pair.
Forget(x) ==
    /\ ~freed
    /\ t[x].h /\ x # act
    /\ t' = [t EXCEPT ![x] = Empty]
    /\ kept' = KeptAfter(t')
    /\ UNCHANGED <<act, seen, freed, lostBuilt>>

\* the session is gone: nothing more happens
Done == freed /\ UNCHANGED vars

Next ==
    \/ Send \/ Choose \/ Keep \/ KeptOut \/ Close \/ Done
    \/ \E x \in Slots : Mint(x) \/ Validate(x) \/ Evict(x) \/ Forget(x)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ t \in [Slots -> [h : BOOLEAN, v : BOOLEAN, g : BOOLEAN, r : BOOLEAN, f : BOOLEAN]]
    /\ act \in Slots
    /\ freed \/ t[act].h
    /\ seen \in BOOLEAN /\ freed \in BOOLEAN /\ lostBuilt \in BOOLEAN
    /\ kept \in [s : -1..NP, at : BOOLEAN, b : BOOLEAN, live : BOOLEAN]

\* An active path a datagram found without an address is gone: the connection was told.
Told == t[act].f => t[act].g

\* The connection stays on such a path only while no other usable path is one the endpoint resolves.
Left == t[act].f => ~\E y \in Usable(t) : y # act /\ t[y].r

\* A datagram built while its pair was there is never dropped.
KeptLeaves == ~lostBuilt

\* With no fault no datagram is dropped.
NeverLost == ~seen

\* Witness: after a drop the active path is validated and resolvable again (TLC must violate it).
NoRecover == ~(seen /\ t[act].r /\ t[act].v)
=============================================================================
