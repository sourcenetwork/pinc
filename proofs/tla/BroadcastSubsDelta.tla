---------------------------- MODULE BroadcastSubsDelta ----------------------------
(***************************************************************************)
(* The subscriber list a hub replicates to its members, sent as changes.   *)
(* Code: crates/pinc-broadcast/src/subs.rs (tell_members, flush_stale,     *)
(* announce, Topics::announce_topic, note_publisher, subs_writable,        *)
(* on_subs with FULL, DELTA and ASK, held_ver, cur_ver), gap.rs send_sub,  *)
(* on_sub and on_unsub, behind.rs peer_writable.                           *)
(*                                                                         *)
(* The story. A hub keeps, per topic, the list of its subscribers (the     *)
(* lowest Max ids). Each member that is a subscriber or a recent publisher *)
(* at a hub (a recipient) keeps a copy, for the day no hub is reachable.   *)
(* Every list has a version: the hub's life (its incarnation) and a number *)
(* raised at every change. The hub sends a change (ids added, ids removed, *)
(* the version it makes) instead of the whole list. Frames can be lost on  *)
(* the way (a relay drop), a session can end (its stream is lost) and a    *)
(* hub can restart (it starts a new life with an empty list).              *)
(*  - The gap rule: a member applies a change only on the version just     *)
(*    before it, the one it holds; otherwise it applies nothing, waits,    *)
(*    and asks the hub for the whole list (ASK).                           *)
(*  - Every SUB carries the version the member holds; the hub sends the    *)
(*    whole list unless it is the current one.                             *)
(*  - A member applies changes only from the hub its whole list came from. *)
(*  - A change is taken between the capped lists.                          *)
(* The hub also sends the whole list on its own to a new publisher and to  *)
(* a recipient whose stream refused a frame ("stale"), once there is room. *)
(* (The code finds the stale recipients of a stream with room through an   *)
(* index, `owed`, that holds every recipient a stream refused: a lookup    *)
(* per writable stream, not a walk of the topics. Writable below is that   *)
(* step.) A frame that changes no list is traced (SubsDropped).            *)
(* A member also takes join hints (node.rs Topics::hint): nodes it may    *)
(* reach with no hub. A hint is kept beside the list, in its own set of at *)
(* most HintMax nodes (max_subscribers in the code; a full set refuses a   *)
(* new hint); a hub's list is the hub's at its version, so a hint never    *)
(* enters it, and a list that names a hinted node drops the hint (the code *)
(* also drops the hints of a topic the member leaves; the model has no     *)
(* leave).                                                                 *)
(*                                                                         *)
(* Assumptions the model makes. One limit: Max is the limit of the hubs    *)
(* and of the members alike. In the code a member's max_subscribers may be *)
(* under its hub's: its list is then cut, and it takes a change that       *)
(* removes an id as a missed one (asks for the whole list), because the id *)
(* past the cut is not in the change (subs.rs peers_cut); not modelled.    *)
(* A hub is never a stranger: the member's primary hub and the hub of its  *)
(* list are not told apart, so the fix that makes a change from the        *)
(* primary the source after a late list from another hub (take_subs) is    *)
(* not modelled either; a change from another hub than the list's is here  *)
(* ignored for good. A change not newer than the version held is ignored   *)
(* in the code; the model's counterpart is the loss of that frame (Lose),  *)
(* which changes nothing at the member. A held subscriber is not a state of *)
(* the model (Unsub stands for hold). Hub-to-hub mirroring (the other hubs' *)
(* reports in a hub's list) is not modelled: a hub's list is its own       *)
(* subscribers. The SUB's version is read at the hub's step; in the code it *)
(* is the one in the frame the member sent earlier.                        *)
(*                                                                         *)
(* What must never happen (ViewIsHubSet): a member holds a version of a    *)
(* hub's list and a list that is not what that hub's list was at that      *)
(* version. So a member is never wrong without knowing it, and one that    *)
(* holds the hub's current version holds the hub's list (Synced).          *)
(*                                                                         *)
(* Guards, each switched off by one RED configuration, each of which must  *)
(* violate ViewIsHubSet:                                                   *)
(*  GapRule   - the base check (BroadcastSubsDelta_nogap.cfg);             *)
(*  FromCheck - changes only from the hub of the list                      *)
(*              (BroadcastSubsDelta_nofrom.cfg);                           *)
(*  CapDelta  - the change between the capped lists, not the raw sets      *)
(*              (BroadcastSubsDelta_nocap.cfg);                            *)
(*  HintGuard - a hint beside the list, never into a list that came from  *)
(*              a hub (BroadcastSubsDelta_nohint.cfg).                     *)
(* The whole list on a SUB, on an ASK, to a new publisher and to a stale   *)
(* recipient bring a member back up to date; they are what makes progress, *)
(* not what keeps a list right, so they have no RED of their own.          *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/BroadcastSubsDelta.lean (the change  *)
(* of two sorted lists, applied, gives the new list: Apply below).         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

\* Hubs: the hubs; Members: the members (numbers, so they have an order); Max: max_subscribers; StreamCap: the frames a
\* stream holds; MaxSteps: how many steps a run takes at most; MaxLives: how many lives a hub has at most; Hinted: the
\* members that take join hints (every member in the code; fewer keep a large configuration small); HintMax: how many
\* hints a member keeps (max_subscribers in the code); the four guards are booleans (TRUE in the code).
CONSTANTS Hubs, Members, Max, StreamCap, MaxSteps, MaxLives, Hinted, HintMax, GapRule, FromCheck, CapDelta, HintGuard

\* live: each hub's subscribers; pubs: its recent publishers; told: the list it last told; life: its incarnation;
\* seq: the number of its list; hist: every (life, number, list) it ever had; stale: the recipients it owes the whole
\* list; asks: the members whose ASK is on its way to it; chan: the frames on the stream from a hub to a member, oldest
\* first; peers: each member's list; from: the hub that list came from ("none" before any); pver: the version the
\* member holds (None while it waits for a whole list); hints: each member's join hints, kept beside its list;
\* steps: the steps taken, which bounds the runs.
VARIABLES live, pubs, told, life, seq, hist, stale, asks, chan, peers, from, pver, hints, steps
vars == <<live, pubs, told, life, seq, hist, stale, asks, chan, peers, from, pver, hints, steps>>

\* A member that holds no version.
None == <<0, 0>>
\* The lowest Max ids of a set: what build_list keeps.
Cap(S) == {x \in S : Cardinality({y \in S : y < x}) < Max}
\* The members a hub sends its list to: its live subscribers and its recent publishers.
Rcpt(h) == live[h] \cup pubs[h]
\* A hub's current version.
Cur(h) == <<life[h], seq[h]>>
\* The whole list at version v, as a frame.
Full(v, S) == [k |-> "full", v |-> v, s |-> S, add |-> {}, rem |-> {}]
\* A change making version v, as a frame.
Delta(v, a, r) == [k |-> "delta", v |-> v, s |-> {}, add |-> a, rem |-> r]
\* A member applies a change: drop the removed, add the added, keep the lowest Max (subs.rs apply).
Apply(P, a, r) == Cap((P \ r) \cup a)
\* The version of h's list member m holds: what its SUB to h carries (held_ver).
Held(m, h) == IF from[m] = h THEN pver[m] ELSE None

Init ==
    /\ live = [h \in Hubs |-> {}] /\ pubs = [h \in Hubs |-> {}] /\ told = [h \in Hubs |-> {}]
    /\ life = [h \in Hubs |-> 1] /\ seq = [h \in Hubs |-> 0]
    /\ hist = [h \in Hubs |-> {<<1, 0, {}>>}]
    /\ stale = [h \in Hubs |-> {}] /\ asks = [h \in Hubs |-> {}]
    /\ chan = [h \in Hubs |-> [m \in Members |-> <<>>]]
    /\ peers = [m \in Members |-> {}] /\ from = [m \in Members |-> "none"] /\ pver = [m \in Members |-> None]
    /\ hints = [m \in Members |-> {}]
    /\ steps = 0

\* Hub h's set became nl and its publishers np; fresh are owed the whole list; ch is what its streams hold. This is
\* announce: tell_members sends the change to the recipients that are not stale, then flush_stale sends the whole list
\* to the stale ones that have room.
Announce(h, nl, np, fresh, ch) ==
    LET rc == nl \cup np
        \* the new list, and whether it changed
        nt == Cap(nl)
        chg == nt # told[h]
        \* the new version: one more when the list changed
        v == <<life[h], IF chg THEN seq[h] + 1 ELSE seq[h]>>
        \* the change: between the capped lists in the code; between the raw sets without the guard
        a == IF CapDelta THEN nt \ told[h] ELSE nl \ live[h]
        r == IF CapDelta THEN told[h] \ nt ELSE live[h] \ nl
        \* owed the whole list: the fresh ones and those already stale, if still recipients
        s1 == (fresh \cup stale[h]) \cap rc
        \* the other recipients are sent the change, if there is one
        dto == IF chg THEN rc \ s1 ELSE {}
        \* a stream with no room refuses its frame, and its recipient becomes stale
        refused == {p \in dto : Len(ch[p]) >= StreamCap}
        c1 == [p \in Members |-> IF p \in dto \ refused THEN Append(ch[p], Delta(v, a, r)) ELSE ch[p]]
        s2 == s1 \cup refused
        \* the stale recipients whose stream has room take the whole list and are no longer stale
        ok == {p \in s2 : Len(c1[p]) < StreamCap}
    IN  /\ live' = [live EXCEPT ![h] = nl]
        /\ pubs' = [pubs EXCEPT ![h] = np]
        /\ told' = [told EXCEPT ![h] = nt]
        /\ seq' = [seq EXCEPT ![h] = v[2]]
        /\ hist' = [hist EXCEPT ![h] = @ \cup {<<v[1], v[2], nt>>}]
        /\ chan' = [chan EXCEPT ![h] = [p \in Members |-> IF p \in ok THEN Append(c1[p], Full(v, nt)) ELSE c1[p]]]
        /\ stale' = [stale EXCEPT ![h] = s2 \ ok]
        /\ UNCHANGED <<life, asks, peers, from, pver, hints>>

\* What on_sub owes the whole list: a subscriber that is new, or whose SUB does not carry the current version.
SubFresh(h, m, isnew) == IF isnew \/ Held(m, h) # Cur(h) THEN {m} ELSE {}

\* gap.rs on_sub: m subscribes at h.
Sub(h, m) == m \notin live[h] /\ Announce(h, live[h] \cup {m}, pubs[h], SubFresh(h, m, TRUE), chan[h])

\* gap.rs on_unsub, and subs.rs hold and release: m stops being a live subscriber at h.
Unsub(h, m) == m \in live[h] /\ Announce(h, live[h] \ {m}, pubs[h], {}, chan[h])

\* The periodic gap check's SUB (gap_ae), which carries the version m holds.
Gap(h, m) == m \in live[h] /\ Announce(h, live[h], pubs[h], SubFresh(h, m, FALSE), chan[h])

\* A new session: what the old stream held is lost, and m subscribes again on it (resubscribe, then on_sub).
Resub(h, m) == m \in live[h] /\ Announce(h, live[h], pubs[h], SubFresh(h, m, FALSE), [chan[h] EXCEPT ![m] = <<>>])

\* subs.rs note_publisher: a member that is not a subscriber publishes at h; it is owed the whole list.
Pub(h, m) == m \notin live[h] /\ m \notin pubs[h] /\ Announce(h, live[h], pubs[h] \cup {m}, {m}, chan[h])

\* behind.rs peer_writable, subs.rs subs_writable: m's stream has room and m is stale: it is sent the whole list.
Writable(h, m) ==
    /\ m \in stale[h] /\ m \in Rcpt(h) /\ Len(chan[h][m]) < StreamCap
    /\ chan' = [chan EXCEPT ![h][m] = Append(@, Full(Cur(h), told[h]))]
    /\ stale' = [stale EXCEPT ![h] = @ \ {m}]
    /\ UNCHANGED <<live, pubs, told, life, seq, hist, asks, peers, from, pver, hints>>

\* subs.rs on_subs ASK at the hub: a recipient that asked is stale, and is sent the whole list if its stream has room.
HubAsk(h, m) ==
    /\ m \in asks[h]
    /\ asks' = [asks EXCEPT ![h] = @ \ {m}]
    /\ IF m \in Rcpt(h) /\ Len(chan[h][m]) < StreamCap
       THEN /\ chan' = [chan EXCEPT ![h][m] = Append(@, Full(Cur(h), told[h]))]
            /\ stale' = [stale EXCEPT ![h] = @ \ {m}]
       ELSE /\ stale' = [stale EXCEPT ![h] = IF m \in Rcpt(h) THEN @ \cup {m} ELSE @]
            /\ UNCHANGED chan
    /\ UNCHANGED <<live, pubs, told, life, seq, hist, peers, from, pver, hints>>

\* A frame is lost on the way and nobody is told (a relay drop).
Lose(h, m) ==
    /\ Len(chan[h][m]) > 0
    /\ chan' = [chan EXCEPT ![h][m] = Tail(@)]
    /\ UNCHANGED <<live, pubs, told, life, seq, hist, stale, asks, peers, from, pver, hints>>

\* The hub restarts: a new life with no subscribers and an empty list; its streams and the asks to it are lost.
Restart(h) ==
    /\ life[h] < MaxLives
    /\ life' = [life EXCEPT ![h] = @ + 1]
    /\ seq' = [seq EXCEPT ![h] = 0]
    /\ live' = [live EXCEPT ![h] = {}] /\ pubs' = [pubs EXCEPT ![h] = {}] /\ told' = [told EXCEPT ![h] = {}]
    /\ hist' = [hist EXCEPT ![h] = @ \cup {<<life[h] + 1, 0, {}>>}]
    /\ stale' = [stale EXCEPT ![h] = {}] /\ asks' = [asks EXCEPT ![h] = {}]
    /\ chan' = [chan EXCEPT ![h] = [m \in Members |-> <<>>]]
    /\ UNCHANGED <<peers, from, pver, hints>>

\* subs.rs on_subs at a member: the oldest frame on the stream from h arrives.
Deliver(h, m) ==
    /\ Len(chan[h][m]) > 0
    /\ LET f == Head(chan[h][m])
           \* the frame applies to this member's list: from its hub (with the guard)
           mine == ~FromCheck \/ from[m] = h
           \* the base check: the change starts from the version the member holds (with the guard)
           onbase == ~GapRule \/ pver[m] = <<f.v[1], f.v[2] - 1>>
       IN
       \* a whole list replaces the member's, names its hub and its version
       IF f.k = "full"
       THEN /\ peers' = [peers EXCEPT ![m] = f.s]
            /\ from' = [from EXCEPT ![m] = h]
            /\ pver' = [pver EXCEPT ![m] = f.v]
            /\ UNCHANGED asks
       ELSE IF mine /\ onbase
       \* a change on its base is applied and the member holds the new version
       THEN /\ peers' = [peers EXCEPT ![m] = Apply(@, f.add, f.rem)]
            /\ pver' = [pver EXCEPT ![m] = f.v]
            /\ UNCHANGED <<from, asks>>
       ELSE IF mine /\ pver[m] # None
       \* a change on another base: the member applies nothing, waits, and asks for the whole list
       THEN /\ pver' = [pver EXCEPT ![m] = None]
            /\ asks' = [asks EXCEPT ![h] = @ \cup {m}]
            /\ UNCHANGED <<peers, from>>
       \* a change from another hub, or while the member already waits: ignored
       ELSE UNCHANGED <<peers, from, pver, asks>>
    \* a list that names a hinted node covers it: the hint is dropped
    /\ hints' = [hints EXCEPT ![m] = @ \ peers'[m]]
    /\ chan' = [chan EXCEPT ![h][m] = Tail(@)]
    /\ UNCHANGED <<live, pubs, told, life, seq, hist, stale>>

\* node.rs Topics::hint: member m takes n as a join hint. It is kept in m's own set of hints (at most HintMax, a full set
\* refuses it) and never enters the list; with the guard off, it goes into the list (while it has room) even when the list
\* came from a hub.
Hint(m, n) ==
    /\ n # m /\ n \notin peers[m]
    /\ IF HintGuard
       THEN /\ n \notin hints[m] /\ Cardinality(hints[m]) < HintMax
            /\ hints' = [hints EXCEPT ![m] = @ \cup {n}]
            /\ UNCHANGED peers
       ELSE /\ Cardinality(peers[m]) < Max
            /\ peers' = [peers EXCEPT ![m] = @ \cup {n}]
            /\ UNCHANGED hints
    /\ UNCHANGED <<live, pubs, told, life, seq, hist, stale, asks, chan, from, pver>>

\* Any member and hub take any step, up to MaxSteps steps in all.
Next == /\ steps < MaxSteps
        /\ steps' = steps + 1
        /\ \/ \E h \in Hubs : Restart(h)
           \/ \E h \in Hubs, m \in Members :
                \/ Sub(h, m) \/ Unsub(h, m) \/ Gap(h, m) \/ Resub(h, m) \/ Pub(h, m)
                \/ Writable(h, m) \/ HubAsk(h, m) \/ Lose(h, m) \/ Deliver(h, m)
           \/ \E m \in Hinted, n \in Members : Hint(m, n)
Spec == Init /\ [][Next]_vars

\* Every variable holds what it should.
TypeOK ==
    /\ \A h \in Hubs : live[h] \subseteq Members /\ pubs[h] \subseteq Members /\ told[h] \subseteq Members
    /\ \A h \in Hubs : stale[h] \subseteq Members /\ asks[h] \subseteq Members
    /\ \A h \in Hubs, m \in Members : Len(chan[h][m]) <= StreamCap
    /\ \A m \in Members : peers[m] \subseteq Members /\ from[m] \in Hubs \cup {"none"}
    /\ \A m \in Members : hints[m] \subseteq Members /\ Cardinality(hints[m]) <= HintMax

\* A hub's list is its subscribers' lowest Max ids, and its current version names it in the history.
ToldIsList == \A h \in Hubs : told[h] = Cap(live[h]) /\ <<life[h], seq[h], told[h]>> \in hist[h]

\* A member that holds a version of a hub's list holds what that hub's list was at that version.
ViewIsHubSet == \A m \in Members :
    (from[m] # "none" /\ pver[m] # None) => <<pver[m][1], pver[m][2], peers[m]>> \in hist[from[m]]

\* A member that holds its hub's current version holds its hub's list.
Synced == \A m \in Members :
    (from[m] # "none" /\ pver[m] = Cur(from[m])) => peers[m] = told[from[m]]

\* A hint is never a node the member's list names: the list covers it (and a member's reach is the two sets together,
\* each node once).
HintsApart == \A m \in Members : hints[m] \cap peers[m] = {}

\* A stale entry is always a recipient: the hub owes the whole list only to those it tells.
StaleAreRecipients == \A h \in Hubs : stale[h] \subseteq Rcpt(h)
=============================================================================
