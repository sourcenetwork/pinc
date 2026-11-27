---------------------------- MODULE CoreStalePath ----------------------------
(***************************************************************************)
(* A connection's path whose address pair the endpoint no longer holds    *)
(* (pinc-core tx.rs poll_transmit, batch, send_stash and path_addrs in    *)
(* endpoint.rs; pinc-transport conn/path.rs path_lost, choose_path,        *)
(* forget_gone, set_path_info).                                            *)
(*                                                                         *)
(* The story. The endpoint names a path by an id into its table of        *)
(* address pairs. The table is bounded: a datagram of any session that     *)
(* arrives from a new address inserts a pair, and a full table evicts the  *)
(* oldest one, which may be the pair of another session's path (Evict).   *)
(* That connection is not told and still holds the id, validated. A       *)
(* datagram it builds on the id finds no address and is dropped (Send).   *)
(* With TELL the endpoint then tells the connection the path is lost      *)
(* (path_lost): the path is gone and unvalidated, the connection moves to  *)
(* a usable path at once if it has one, or as soon as one validates, and  *)
(* forgets the gone path once it is not the active one. The peer's        *)
(* datagrams mint new ids (Mint): a relayed path is validated at once     *)
(* (set_path_info), a direct one when its challenge is answered          *)
(* (Validate, which needs the path's datagrams to leave). The connection  *)
(* moves among usable paths by its own rules (Choose: round trips, the    *)
(* peer's data, the fall back to a relay), never knowing which ids the    *)
(* endpoint still resolves, and it forgets a path that is not active      *)
(* (Forget: idle out, removal).                                           *)
(*                                                                         *)
(* Checked:                                                                *)
(*  Told  an active path a datagram found without an address is gone: the  *)
(*        connection was told;                                             *)
(*  Left  the connection stays on such a path only while it has no other   *)
(*        usable path the endpoint resolves.                               *)
(* RED configuration: CoreStalePath_silent, TELL = FALSE (the code before  *)
(* the fix: the drop is only counted). The connection keeps the dead id   *)
(* as its active path, and a choice can move it back onto it, while a     *)
(* resolvable path is usable beside it: Left fails.                       *)
(* Witness: CoreStalePath_w_recover (NoRecover: after a drop the active   *)
(* path is validated and resolvable again).                                *)
(* Not modelled: the endpoint's other sessions (only their evictions), the *)
(* recovery's repair of what was dropped (a probe timeout or loss          *)
(* detection resends it on the new path), time.                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

\* NP: the connection's path slots. TELL: the endpoint tells the connection of a drop (the fix).
CONSTANTS NP, TELL

Slots == 1..NP

\* t[x]: slot x. h: the connection tracks a path in it; v: validated; g: gone; r: the endpoint resolves its id;
\* f: a datagram on it found no address. act: the active slot (the connection always has one). seen: a drop happened.
VARIABLES t, act, seen
vars == <<t, act, seen>>

Empty == [h |-> FALSE, v |-> FALSE, g |-> FALSE, r |-> FALSE, f |-> FALSE]

\* the paths the connection may move onto: tracked, validated, not gone
Usable(tt) == {y \in Slots : tt[y].h /\ tt[y].v /\ ~tt[y].g}

\* choose_path from a gone active path: any usable path at once (the cost is not modelled), else stay
Reselect(tt, a) == IF tt[a].g /\ Usable(tt) # {} THEN Usable(tt) ELSE {a}

\* forget_gone: every gone path but the active one is forgotten
ForgetGone(tt, a) == [x \in Slots |-> IF x # a /\ tt[x].g THEN Empty ELSE tt[x]]

Init ==
    /\ t = [x \in Slots |-> IF x = 1 THEN [Empty EXCEPT !.h = TRUE, !.v = TRUE, !.r = TRUE] ELSE Empty]
    /\ act = 1
    /\ seen = FALSE

\* A datagram of the peer from a new address mints an id into a free slot; a relayed one is validated at once.
Mint(x) ==
    /\ ~t[x].h
    /\ \E v \in BOOLEAN :
         LET tt == [t EXCEPT ![x] = [Empty EXCEPT !.h = TRUE, !.v = v, !.r = TRUE]]
         IN \E a \in Reselect(tt, act) : /\ act' = a /\ t' = ForgetGone(tt, a)
    /\ UNCHANGED seen

\* A challenge on a direct path is answered: its datagrams must leave, so the endpoint resolves it.
Validate(x) ==
    /\ t[x].h /\ ~t[x].v /\ ~t[x].g /\ t[x].r
    /\ LET tt == [t EXCEPT ![x].v = TRUE]
       IN \E a \in Reselect(tt, act) : /\ act' = a /\ t' = ForgetGone(tt, a)
    /\ UNCHANGED seen

\* The connection's own move onto a usable path (choose_path for a lower round trip, follow_peer, relay_fallback).
Choose ==
    /\ \E y \in Usable(t) : /\ act' = y /\ t' = ForgetGone(t, y)
    /\ UNCHANGED seen

\* The table of address pairs evicts the pair of a tracked path; nobody tells the connection.
Evict(x) ==
    /\ t[x].h /\ t[x].r
    /\ t' = [t EXCEPT ![x].r = FALSE]
    /\ UNCHANGED <<act, seen>>

\* A datagram on the active path finds no address and is dropped; with TELL the connection is told (path_lost).
Send ==
    /\ ~t[act].r
    /\ seen' = TRUE
    /\ IF TELL
       THEN LET tt == [t EXCEPT ![act].f = TRUE, ![act].g = TRUE, ![act].v = FALSE]
            IN \E a \in Reselect(tt, act) : /\ act' = a /\ t' = ForgetGone(tt, a)
       ELSE /\ t' = [t EXCEPT ![act].f = TRUE]
            /\ UNCHANGED act

\* The connection forgets a path that is not active (idle out, removal).
Forget(x) ==
    /\ t[x].h /\ x # act
    /\ t' = [t EXCEPT ![x] = Empty]
    /\ UNCHANGED <<act, seen>>

Next ==
    \/ Send \/ Choose
    \/ \E x \in Slots : Mint(x) \/ Validate(x) \/ Evict(x) \/ Forget(x)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ t \in [Slots -> [h : BOOLEAN, v : BOOLEAN, g : BOOLEAN, r : BOOLEAN, f : BOOLEAN]]
    /\ act \in Slots
    /\ t[act].h
    /\ seen \in BOOLEAN

\* An active path a datagram found without an address is gone: the connection was told.
Told == t[act].f => t[act].g

\* The connection stays on such a path only while no other usable path is one the endpoint resolves.
Left == t[act].f => ~\E y \in Usable(t) : y # act /\ t[y].r

\* Witness: after a drop the active path is validated and resolvable again (TLC must violate it).
NoRecover == ~(seen /\ t[act].r /\ t[act].v)
=============================================================================
