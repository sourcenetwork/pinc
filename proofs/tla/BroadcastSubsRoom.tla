---------------------------- MODULE BroadcastSubsRoom ----------------------------
(***************************************************************************)
(* A recipient of a subscriber list sent in pieces, and the room its       *)
(* stream has for them. Code: crates/vinc-broadcast/src/subs.rs            *)
(* (flush_stale, the send of the local set to the other hubs), host.rs     *)
(* backlogged and peer_writable. The recipient is a member (the list of a  *)
(* topic) or a hub (the set of the other hub's local subscribers): one     *)
(* function in the code decides what each is sent, and so does one         *)
(* operator here (Need).                                                   *)
(*                                                                         *)
(* The stream holds Hold pieces when empty. Its room now is `room`; pieces *)
(* the hub queued (q) and frames of other traffic (the rest) take room;    *)
(* FreeOther and Deliver free it, a piece leaving the stream reaches the   *)
(* recipient, which gathers the pieces of one list in rank order and holds *)
(* a list only when it has all of them (held). The hub owes the whole list *)
(* to a stale recipient and keeps its place (the next piece).              *)
(*  - Rule "new": a list of at most Hold pieces, at place 0, is queued     *)
(*    whole when room for all its pieces is there, nothing when it is not  *)
(*    (the recipient stays owed); a larger list goes one piece a step from *)
(*    the place, and a change puts the place back to 0 (vinc#643 would     *)
(*    keep it).                                                            *)
(*  - Rule "tip": the rule before: one piece a step for every list, the    *)
(*    place back to 0 by a change.                                         *)
(*  - Rule "hubtip": the rule before for a hub: the whole set is written   *)
(*    in one call that stops at the first refusal, and is tried again only *)
(*    at the next change (Attempt, armed), the hub never owing it.         *)
(*                                                                         *)
(* The version is abstracted so that a list that changes forever is a      *)
(* finite state space: a piece carries c, whether it is of the list as it  *)
(* is now, and a change turns c to FALSE in every queued piece and in the  *)
(* gathering (the hub's list gets a new version, which this abstraction     *)
(* does not count). Two older lists are not told apart, so an older        *)
(* gathering could join an older piece of another list. That only adds     *)
(* completions: Rule "new" never puts pieces of two lists inside one       *)
(* gathering for a list that fits (a group is queued whole, ahead of the   *)
(* next one), and the runs of Rule "tip" and "hubtip" that never complete  *)
(* need no join. A piece that does not follow its gathering breaks it; the *)
(* member's ASK, which would put the place back to 0, is not modelled, and *)
(* no property here uses it. Frames are not lost here (BroadcastSubsDelta  *)
(* has the loss and the versions).                                         *)
(*                                                                         *)
(* NotLeftPart (safety): a recipient whose list fits the stream is never   *)
(* left with a part of it: a gathering of such a list always has its next  *)
(* piece in the stream, a change or not. Rule "tip" violates it            *)
(* (BroadcastSubsRoom_cut.cfg).                                            *)
(* Live (liveness): with room freed again and again (weak fairness of      *)
(* FreeOther and Deliver) and the hub's step taken again and again (weak   *)
(* fairness of HubSend and Attempt), a recipient that is stale and whose   *)
(* list fits its stream comes to hold a whole list, while the list changes *)
(* forever (BroadcastSubsRoom.cfg, Rule "new"). Rule "tip" has a run in    *)
(* which it never does (BroadcastSubsRoom_tip.cfg). For the hub, with no   *)
(* further local change, the other hub comes to hold the set whole under   *)
(* Rule "new" (BroadcastSubsRoom_hubset.cfg); the rule of the tip has a    *)
(* refused hub sent no more (BroadcastSubsRoom_hubtip.cfg).                *)
(* What is NOT shown: a list larger than the stream holds, changing        *)
(* forever, never being held whole is the limit of the rule (vinc#643);    *)
(* BroadcastSubsRoom_large.cfg checks its safety only and claims no        *)
(* liveness, and BroadcastSubsRoom_largequiet.cfg shows such a list        *)
(* arriving when it stops changing. New foreign traffic that keeps the     *)
(* stream short of room for the list forever is outside the premise (room  *)
(* freed again and again).                                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

\* Hold: the pieces a stream holds when empty; Sizes: the sizes in pieces a list may have; Rule: "new", "tip" or
\* "hubtip"; Changes: whether the list changes (it may, forever, when TRUE).
CONSTANTS Hold, Sizes, Rule, Changes

\* n: the pieces of the list now; place: the pieces of it the hub handed over (0 when none or all); stale: the hub owes
\* the list; armed: a send of the set is due (Rule "hubtip"); room: the pieces the stream has room for now; q: the pieces
\* queued in the stream, oldest first (r: rank, c: of the list as it is now, t: the pieces of its list); gather: the
\* recipient's gathering (g pieces counted); held: the recipient came to hold a whole list.
VARIABLES n, place, stale, armed, room, q, gather, held
vars == <<n, place, stale, armed, room, q, gather, held>>

NoG == [on |-> FALSE, g |-> 0, c |-> FALSE, t |-> 0]

\* The frames of other traffic in the stream.
Other == Hold - room - Len(q)

\* The pieces handed over in one step: all of a list that fits at place 0 (Rule "new"), one otherwise.
Need == IF Rule = "new" /\ place = 0 /\ n <= Hold THEN n ELSE 1

Init ==
    /\ n \in Sizes /\ place = 0 /\ stale = TRUE /\ armed = TRUE
    /\ room \in 0..Hold /\ q = <<>> /\ gather = NoG /\ held = FALSE

\* subs.rs flush_stale, a stale recipient and its stream with room for the step: the next pieces are queued, and the
\* recipient stays owed until the last.
HubSend ==
    /\ Rule # "hubtip" /\ stale /\ room >= Need
    /\ q' = q \o [i \in 1..Need |-> [r |-> place + i - 1, c |-> TRUE, t |-> n]]
    /\ room' = room - Need
    /\ place' = IF place + Need = n THEN 0 ELSE place + Need
    /\ stale' = (place + Need # n)
    /\ UNCHANGED <<n, armed, gather, held>>

\* The rule of the tip for a hub: the set is written from its first piece while the stream takes pieces, in one call,
\* and the hub is not owed it afterwards.
Attempt ==
    /\ Rule = "hubtip" /\ armed
    /\ LET k == IF room < n THEN room ELSE n
       IN /\ q' = q \o [i \in 1..k |-> [r |-> i - 1, c |-> TRUE, t |-> n]]
          /\ room' = room - k
    /\ armed' = FALSE /\ stale' = FALSE
    /\ UNCHANGED <<n, place, gather, held>>

\* The list changes to one of Sizes pieces: the places go back to 0, what was queued and gathered is of an older list.
Change ==
    /\ Changes
    /\ \E k \in Sizes : n' = k
    /\ place' = 0 /\ armed' = TRUE
    /\ q' = [i \in 1..Len(q) |-> [q[i] EXCEPT !.c = FALSE]]
    /\ gather' = [gather EXCEPT !.c = FALSE]
    /\ UNCHANGED <<stale, room, held>>

\* The stream sends a frame of other traffic: room is freed.
FreeOther ==
    /\ Other > 0
    /\ room' = room + 1
    /\ UNCHANGED <<n, place, stale, armed, q, gather, held>>

\* The recipient takes piece e: rank 0 starts a gathering (a list of one piece is held at once); a later piece joins
\* the gathering of its list when it follows it; any other breaks it.
Recv(e) ==
    LET joins == gather.on /\ gather.g = e.r /\ gather.c = e.c /\ gather.t = e.t
    IN IF e.r = 0
       THEN IF e.t = 1
            THEN /\ held' = TRUE /\ gather' = NoG
            ELSE /\ gather' = [on |-> TRUE, g |-> 1, c |-> e.c, t |-> e.t] /\ UNCHANGED held
       ELSE IF joins
            THEN IF e.r + 1 = e.t
                 THEN /\ held' = TRUE /\ gather' = NoG
                 ELSE /\ gather' = [gather EXCEPT !.g = @ + 1] /\ UNCHANGED held
            ELSE /\ gather' = NoG /\ UNCHANGED held

\* The oldest queued piece leaves the stream and reaches the recipient: room is freed.
Deliver ==
    /\ q # <<>>
    /\ Recv(Head(q))
    /\ q' = Tail(q)
    /\ room' = room + 1
    /\ UNCHANGED <<n, place, stale, armed>>

Next == HubSend \/ Attempt \/ Change \/ FreeOther \/ Deliver

Spec == Init /\ [][Next]_vars /\ WF_vars(HubSend) /\ WF_vars(Attempt) /\ WF_vars(FreeOther) /\ WF_vars(Deliver)

TypeOK ==
    /\ n \in Sizes /\ place \in 0..(n - 1) /\ room \in 0..Hold /\ Len(q) + room <= Hold
    /\ stale \in BOOLEAN /\ armed \in BOOLEAN /\ held \in BOOLEAN
    /\ \A i \in 1..Len(q) : q[i].r < q[i].t /\ q[i].c \in BOOLEAN
    /\ gather.g <= gather.t

\* A recipient whose list fits the stream is never left with a part of it: the next piece of its gathering is queued.
NotLeftPart == (gather.on /\ gather.t <= Hold) => \E i \in 1..Len(q) : q[i].r = gather.g /\ q[i].t = gather.t

\* A recipient that is stale comes to hold a whole list.
Live == <>held
=============================================================================
