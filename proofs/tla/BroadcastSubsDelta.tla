---------------------------- MODULE BroadcastSubsDelta ----------------------------
(***************************************************************************)
(* The subscriber list a hub replicates to its members, sent as changes.   *)
(* Code: crates/vinc-broadcast/src/subs.rs (tell_members, flush_stale,     *)
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
(* The whole list travels as ordered pieces of Piece ids (the lowest ranks *)
(* first), all at one version; a list of at most Piece ids is one piece.   *)
(* The hub keeps each stale recipient's place (the next piece). A list that *)
(* fits the stream (its pieces are at most StreamCap, what a stream holds  *)
(* when empty, counted in pieces) is queued whole or not at all: a         *)
(* recipient at place 0 is sent every piece in one step when the room for  *)
(* them is there, nothing when it is not (FitWhole; one function, Need and *)
(* Can, for Announce, Writable and HubAsk). A larger list goes one piece a *)
(* step from the recipient's place; a recipient stays stale until its last *)
(* piece. The places go back to 0 only on a change to the list, a restart, *)
(* an ASK and the end of the recipient's session (Resub); a fresh SUB from *)
(* a recipient in the middle of a list keeps its place (KeepPlace; the new *)
(* subscriber and the new publisher are not stale yet, their place is 0    *)
(* already). A member gathers the pieces of each hub apart and never acts  *)
(* on a partial list:                                                      *)
(*  - first 0 and the piece is the whole list: take it now, drop the       *)
(*    gathering of that hub;                                               *)
(*  - first 0 and more due: start (or restart) that hub's gathering;       *)
(*  - first above 0: join the unbroken gathering of that hub only when it  *)
(*    has the same version and total and has counted exactly `first` ids   *)
(*    (the chain check); at the last piece take the gathered list and its  *)
(*    version;                                                             *)
(*  - anything else breaks the gathering: nothing is taken, the member     *)
(*    asks that hub once per broken gathering, and drops the version it    *)
(*    holds if that hub is its list's hub.                                 *)
(* A piece that does not complete the list changes nothing the member      *)
(* holds: its list, version and hints stay.                                *)
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
(* Assumptions the model makes. In the code a change of more than a piece  *)
(* of ids is not sent: the recipients get the whole list; the model sends  *)
(* the change whatever its size. Hub-to-hub pieces (a hub's report of its  *)
(* own subscribers to another hub) are not modelled, as the report is not; *)
(* the hub as a recipient of a set is in BroadcastSubsRoom.tla. The stream *)
(* is counted in frames, a delta takes a frame as a piece does (in the     *)
(* code the room is bytes and a delta is smaller). That a recipient left   *)
(* waiting for room is offered again, and that a list changed forever      *)
(* still ends, are liveness: BroadcastSubsRoom.tla (the version is         *)
(* unbounded here, so a run is bounded by MaxSteps and carries no          *)
(* liveness).                                                              *)
(* One limit: Max is the limit of the hubs                                 *)
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
(*  ChainCheck - a piece joins a gathering only on its version, its total  *)
(*              and its rank (BroadcastSubsDelta_nochain.cfg);             *)
(*  WholeOnly - a gathering is taken only whole, never into the list as    *)
(*              the pieces arrive (BroadcastSubsDelta_partial.cfg).        *)
(* The whole list on a SUB, on an ASK, to a new publisher and to a stale   *)
(* recipient bring a member back up to date; they are what makes progress, *)
(* not what keeps a list right, so they have no RED of their own. The same *)
(* holds for the place resets and the ASK on a broken gathering.           *)
(* PartIsPrefix: an unbroken gathering holds the lowest ids of the hub's   *)
(* list at its version, as many as it has counted; with ViewIsHubSet this  *)
(* is "the member's view equals the hub's set" across the pieces.          *)
(* PlaceKept (an action property): a recipient's place goes back to 0 while *)
(* it is still owed the list only when the list changed, when it asked, or *)
(* when its session ended. KeepPlace off (the place reset by every fresh   *)
(* SUB) violates it: BroadcastSubsDelta_keepnot.cfg.                       *)
(* FitPlaceZero: a recipient whose list fits the stream is never owed it   *)
(* from the middle, so a change cannot leave it a part of that list.       *)
(* FitWhole off (every list piece by piece) violates it:                   *)
(* BroadcastSubsDelta_nofit.cfg.                                           *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/BroadcastSubsDelta.lean (the change  *)
(* of two sorted lists, applied, gives the new list: Apply below).         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

\* Hubs: the hubs; Members: the members (numbers, so they have an order); Max: max_subscribers; StreamCap: the frames a
\* stream holds; MaxSteps: how many steps a run takes at most; MaxLives: how many lives a hub has at most; Hinted: the
\* members that take join hints (every member in the code; fewer keep a large configuration small); HintMax: how many
\* hints a member keeps (max_subscribers in the code); Piece: how many ids a piece of the whole list carries (SUBS_PIECE
\* in the code; Max makes every list one piece); the six guards are booleans (TRUE in the code).
\* KeepPlace: a fresh SUB keeps the place of a recipient that is stale. FitWhole: a list that fits the stream goes whole or
\* not at all. StreamCap is also what a stream holds when empty, in frames.
CONSTANTS Hubs, Members, Max, StreamCap, MaxSteps, MaxLives, Hinted, HintMax, Piece,
          GapRule, FromCheck, CapDelta, HintGuard, ChainCheck, WholeOnly, KeepPlace, FitWhole

\* live: each hub's subscribers; pubs: its recent publishers; told: the list it last told; life: its incarnation;
\* seq: the number of its list; hist: every (life, number, list) it ever had; stale: the recipients it owes the whole
\* list; place: the next piece of the whole list a stale recipient is owed (0 for any other); asks: the members whose
\* ASK is on its way to it; chan: the frames on the stream from a hub to a member, oldest first; peers: each member's
\* list; from: the hub that list came from ("none" before any); pver: the version the member holds (None while it waits
\* for a whole list); part: each member's gathering of the pieces from each hub (NoPart when there is none); hints:
\* each member's join hints, kept beside its list; steps: the steps taken, which bounds the runs.
VARIABLES live, pubs, told, life, seq, hist, stale, place, asks, chan, peers, from, pver, part, hints, steps
vars == <<live, pubs, told, life, seq, hist, stale, place, asks, chan, peers, from, pver, part, hints, steps>>

\* A member that holds no version.
None == <<0, 0>>
\* A member with no gathering from a hub; a gathering has the version and total of the list, the ids counted so far, the
\* ids kept (the lowest ones, in order), and whether a piece broke it.
NoPart == [on |-> FALSE, v |-> None, total |-> 0, got |-> 0, ids |-> {}, broken |-> FALSE]
\* The lowest n ids of a set.
Low(S, n) == {x \in S : Cardinality({y \in S : y < x}) < n}
\* The lowest Max ids of a set: what build_list keeps.
Cap(S) == Low(S, Max)
\* The ids of piece j of a list: the ranks j * Piece to (j + 1) * Piece - 1.
Ids(S, j) == Low(S, (j + 1) * Piece) \ Low(S, j * Piece)
\* Whether piece j is the last piece of the list.
Last(S, j) == (j + 1) * Piece >= Cardinality(S)
\* The members a hub sends its list to: its live subscribers and its recent publishers.
Rcpt(h) == live[h] \cup pubs[h]
\* A hub's current version.
Cur(h) == <<life[h], seq[h]>>
\* The number of pieces of the whole list S (an empty list is one piece).
Np(S) == IF S = {} THEN 1 ELSE (Cardinality(S) + Piece - 1) \div Piece
\* Whether the whole list S fits what the stream holds when empty.
Fits(S) == Np(S) <= StreamCap
\* The pieces handed over in one step to a recipient at place j: all of a list that fits, one otherwise.
Need(S, j) == IF FitWhole /\ j = 0 /\ Fits(S) THEN Np(S) ELSE 1
\* Whether the stream ch has room for the pieces of that step.
Can(S, j, ch) == StreamCap - Len(ch) >= Need(S, j)
\* Whether that step hands over the last piece.
Done(S, j) == Last(S, j + Need(S, j) - 1)
\* Piece j of the whole list S at version v, as a frame.
PieceF(v, S, j) ==
    [k |-> "piece", v |-> v, s |-> Ids(S, j), add |-> {}, rem |-> {}, first |-> j * Piece, total |-> Cardinality(S)]
\* The frames of a step at place j: Need(S, j) pieces from piece j.
Pieces(v, S, j) == [i \in 1..Need(S, j) |-> PieceF(v, S, j + i - 1)]
\* A change making version v, as a frame.
Delta(v, a, r) == [k |-> "delta", v |-> v, s |-> {}, add |-> a, rem |-> r, first |-> 0, total |-> 0]
\* A member applies a change: drop the removed, add the added, keep the lowest Max (subs.rs apply).
Apply(P, a, r) == Cap((P \ r) \cup a)
\* The version of h's list member m holds: what its SUB to h carries (held_ver).
Held(m, h) == IF from[m] = h THEN pver[m] ELSE None

Init ==
    /\ live = [h \in Hubs |-> {}] /\ pubs = [h \in Hubs |-> {}] /\ told = [h \in Hubs |-> {}]
    /\ life = [h \in Hubs |-> 1] /\ seq = [h \in Hubs |-> 0]
    /\ hist = [h \in Hubs |-> {<<1, 0, {}>>}]
    /\ stale = [h \in Hubs |-> {}] /\ asks = [h \in Hubs |-> {}]
    /\ place = [h \in Hubs |-> [m \in Members |-> 0]]
    /\ chan = [h \in Hubs |-> [m \in Members |-> <<>>]]
    /\ peers = [m \in Members |-> {}] /\ from = [m \in Members |-> "none"] /\ pver = [m \in Members |-> None]
    /\ part = [m \in Members |-> [h \in Hubs |-> NoPart]]
    /\ hints = [m \in Members |-> {}]
    /\ steps = 0

\* Hub h's set became nl and its publishers np; fresh are owed the whole list; rst are the recipients whose session
\* ended; ch is what its streams hold. This is announce: tell_members sends the change to the recipients that are not
\* stale, then flush_stale sends the next pieces of the whole list to the stale ones that have room.
Announce(h, nl, np, fresh, rst, ch) ==
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
        \* where each owed recipient is: a change, an ended session and a refused change put it at piece 0; a fresh SUB
        \* keeps the place of one in the middle of a list (without KeepPlace it puts it at 0)
        pl == [p \in Members |-> IF chg \/ p \in rst \/ p \notin s2 \/ (~KeepPlace /\ p \in fresh) THEN 0
                                 ELSE place[h][p]]
        \* the stale recipients whose stream has room for their next step take it
        ok == {p \in s2 : Can(nt, pl[p], c1[p])}
        \* those that took the last piece are no longer stale
        done == {p \in ok : Done(nt, pl[p])}
    IN  /\ live' = [live EXCEPT ![h] = nl]
        /\ pubs' = [pubs EXCEPT ![h] = np]
        /\ told' = [told EXCEPT ![h] = nt]
        /\ seq' = [seq EXCEPT ![h] = v[2]]
        /\ hist' = [hist EXCEPT ![h] = @ \cup {<<v[1], v[2], nt>>}]
        /\ chan' = [chan EXCEPT ![h] = [p \in Members |-> IF p \in ok THEN c1[p] \o Pieces(v, nt, pl[p]) ELSE c1[p]]]
        /\ stale' = [stale EXCEPT ![h] = s2 \ done]
        /\ place' = [place EXCEPT ![h] = [p \in Members |-> IF p \in done THEN 0 ELSE IF p \in ok THEN pl[p] + Need(nt, pl[p]) ELSE pl[p]]]
        /\ UNCHANGED <<life, asks, peers, from, pver, part, hints>>

\* What on_sub owes the whole list: a subscriber that is new, or whose SUB does not carry the current version.
SubFresh(h, m, isnew) == IF isnew \/ Held(m, h) # Cur(h) THEN {m} ELSE {}

\* gap.rs on_sub: m subscribes at h.
Sub(h, m) == m \notin live[h] /\ Announce(h, live[h] \cup {m}, pubs[h], SubFresh(h, m, TRUE), {}, chan[h])

\* gap.rs on_unsub, and subs.rs hold and release: m stops being a live subscriber at h.
Unsub(h, m) == m \in live[h] /\ Announce(h, live[h] \ {m}, pubs[h], {}, {}, chan[h])

\* The periodic gap check's SUB (gap_ae), which carries the version m holds.
Gap(h, m) == m \in live[h] /\ Announce(h, live[h], pubs[h], SubFresh(h, m, FALSE), {}, chan[h])

\* A new session: what the old stream held is lost, and m subscribes again on it (resubscribe, then on_sub).
Resub(h, m) == m \in live[h] /\ Announce(h, live[h], pubs[h], SubFresh(h, m, FALSE), {m}, [chan[h] EXCEPT ![m] = <<>>])

\* subs.rs note_publisher: a member that is not a subscriber publishes at h; it is owed the whole list.
Pub(h, m) == m \notin live[h] /\ m \notin pubs[h] /\ Announce(h, live[h], pubs[h] \cup {m}, {m}, {}, chan[h])

\* behind.rs peer_writable, subs.rs subs_writable: m's stream has room for its next step and m is stale: it is sent the
\* next piece (all the pieces of a list that fits, from place 0), and stays stale until the last one.
Writable(h, m) ==
    /\ m \in stale[h] /\ m \in Rcpt(h) /\ Can(told[h], place[h][m], chan[h][m])
    /\ chan' = [chan EXCEPT ![h][m] = @ \o Pieces(Cur(h), told[h], place[h][m])]
    /\ IF Done(told[h], place[h][m])
       THEN /\ stale' = [stale EXCEPT ![h] = @ \ {m}]
            /\ place' = [place EXCEPT ![h][m] = 0]
       ELSE /\ place' = [place EXCEPT ![h][m] = @ + Need(told[h], place[h][m])]
            /\ UNCHANGED stale
    /\ UNCHANGED <<live, pubs, told, life, seq, hist, asks, peers, from, pver, part, hints>>

\* subs.rs on_subs ASK at the hub: a recipient that asked is stale at piece 0, and is sent its first step if its stream
\* has room for it.
HubAsk(h, m) ==
    /\ m \in asks[h]
    /\ asks' = [asks EXCEPT ![h] = @ \ {m}]
    /\ LET rcpt == m \in Rcpt(h)
           go == rcpt /\ Can(told[h], 0, chan[h][m])
           fin == go /\ Done(told[h], 0)
       IN /\ chan' = [chan EXCEPT ![h][m] = IF go THEN @ \o Pieces(Cur(h), told[h], 0) ELSE @]
          /\ stale' = [stale EXCEPT ![h] = IF fin THEN @ \ {m} ELSE IF rcpt THEN @ \cup {m} ELSE @]
          /\ place' = [place EXCEPT ![h][m] = IF go /\ ~fin THEN Need(told[h], 0) ELSE 0]
    /\ UNCHANGED <<live, pubs, told, life, seq, hist, peers, from, pver, part, hints>>

\* A frame is lost on the way and nobody is told (a relay drop).
Lose(h, m) ==
    /\ Len(chan[h][m]) > 0
    /\ chan' = [chan EXCEPT ![h][m] = Tail(@)]
    /\ UNCHANGED <<live, pubs, told, life, seq, hist, stale, place, asks, peers, from, pver, part, hints>>

\* The hub restarts: a new life with no subscribers and an empty list; its streams, its places and the asks to it are
\* lost.
Restart(h) ==
    /\ life[h] < MaxLives
    /\ life' = [life EXCEPT ![h] = @ + 1]
    /\ seq' = [seq EXCEPT ![h] = 0]
    /\ live' = [live EXCEPT ![h] = {}] /\ pubs' = [pubs EXCEPT ![h] = {}] /\ told' = [told EXCEPT ![h] = {}]
    /\ hist' = [hist EXCEPT ![h] = @ \cup {<<life[h] + 1, 0, {}>>}]
    /\ stale' = [stale EXCEPT ![h] = {}] /\ asks' = [asks EXCEPT ![h] = {}]
    /\ place' = [place EXCEPT ![h] = [m \in Members |-> 0]]
    /\ chan' = [chan EXCEPT ![h] = [m \in Members |-> <<>>]]
    /\ UNCHANGED <<peers, from, pver, part, hints>>

\* Member m takes the list S at version v from hub h: it replaces its list, names its hub and its version.
Take(m, h, v, S) ==
    /\ peers' = [peers EXCEPT ![m] = S]
    /\ from' = [from EXCEPT ![m] = h]
    /\ pver' = [pver EXCEPT ![m] = v]

\* A gathering's ids reach the member's list as they come: what a member that does not wait for the whole list does.
Prefix(m, h, v, S) == IF WholeOnly THEN UNCHANGED <<peers, from, pver>> ELSE Take(m, h, v, S)

\* subs.rs on_subs at a member: the oldest frame on the stream from h arrives.
Deliver(h, m) ==
    /\ Len(chan[h][m]) > 0
    /\ LET f == Head(chan[h][m])
           \* the frame applies to this member's list: from its hub (with the guard)
           mine == ~FromCheck \/ from[m] = h
           \* the base check: the change starts from the version the member holds (with the guard)
           onbase == ~GapRule \/ pver[m] = <<f.v[1], f.v[2] - 1>>
           \* the gathering of h's pieces, how many ids the piece carries, and the ids and count with it
           p == part[m][h]
           cnt == Cardinality(f.s)
           same == p.v = f.v /\ p.total = f.total
           chained == p.on /\ ~p.broken /\ (~ChainCheck \/ (same /\ p.got = f.first))
           \* the broken gathering of this frame's version (gather: a gap)
           broke == [on |-> TRUE, v |-> f.v, total |-> f.total, got |-> 0, ids |-> {}, broken |-> TRUE]
           gathered == [on |-> TRUE, v |-> f.v, total |-> f.total, got |-> p.got + cnt, ids |-> p.ids \cup f.s,
                        broken |-> FALSE]
       IN
       \* the first piece is the whole list: it replaces the member's, names its hub and its version
       IF f.k = "piece" /\ f.first = 0 /\ cnt = f.total
       THEN /\ Take(m, h, f.v, f.s)
            /\ part' = [part EXCEPT ![m][h] = NoPart]
            /\ UNCHANGED asks
       \* the first of more pieces: the gathering of h starts again, and the member takes nothing yet
       ELSE IF f.k = "piece" /\ f.first = 0
       THEN /\ part' = [part EXCEPT ![m][h] = [on |-> TRUE, v |-> f.v, total |-> f.total, got |-> cnt, ids |-> f.s,
                                                  broken |-> FALSE]]
            /\ Prefix(m, h, f.v, f.s)
            /\ UNCHANGED asks
       \* a later piece that follows the gathering: with the last one the member takes the gathered list
       ELSE IF f.k = "piece" /\ chained
       THEN /\ IF gathered.got >= f.total
               THEN /\ Take(m, h, f.v, gathered.ids)
                    /\ part' = [part EXCEPT ![m][h] = NoPart]
               ELSE /\ part' = [part EXCEPT ![m][h] = gathered]
                    /\ Prefix(m, h, f.v, gathered.ids)
            /\ UNCHANGED asks
       \* a later piece that does not follow: the gathering is broken and the member takes nothing; it asks h once per
       \* broken gathering, and drops its version if h is its list's hub
       ELSE IF f.k = "piece"
       THEN /\ part' = [part EXCEPT ![m][h] = IF p.on /\ p.broken /\ same THEN p ELSE broke]
            /\ asks' = [asks EXCEPT ![h] = IF p.on /\ p.broken /\ same THEN @ ELSE @ \cup {m}]
            /\ pver' = [pver EXCEPT ![m] = IF from[m] = h THEN None ELSE @]
            /\ UNCHANGED <<peers, from>>
       \* a change on its base is applied and the member holds the new version
       ELSE IF mine /\ onbase
       THEN /\ peers' = [peers EXCEPT ![m] = Apply(@, f.add, f.rem)]
            /\ pver' = [pver EXCEPT ![m] = f.v]
            /\ UNCHANGED <<from, asks, part>>
       ELSE IF mine /\ pver[m] # None
       \* a change on another base: the member applies nothing, waits, and asks for the whole list
       THEN /\ pver' = [pver EXCEPT ![m] = None]
            /\ asks' = [asks EXCEPT ![h] = @ \cup {m}]
            /\ UNCHANGED <<peers, from, part>>
       \* a change from another hub, or while the member already waits: ignored
       ELSE UNCHANGED <<peers, from, pver, asks, part>>
    \* a list that names a hinted node covers it: the hint is dropped
    /\ hints' = [hints EXCEPT ![m] = @ \ peers'[m]]
    /\ chan' = [chan EXCEPT ![h][m] = Tail(@)]
    /\ UNCHANGED <<live, pubs, told, life, seq, hist, stale, place>>

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
    /\ UNCHANGED <<live, pubs, told, life, seq, hist, stale, place, asks, chan, from, pver, part>>

\* Any member and hub take any step, up to MaxSteps steps in all.
Next == /\ steps < MaxSteps
        /\ steps' = steps + 1
        /\ \/ \E h \in Hubs : Restart(h)
           \/ \E h \in Hubs, m \in Members :
                \/ Sub(h, m) \/ Unsub(h, m) \/ Gap(h, m) \/ Resub(h, m) \/ Pub(h, m)
                \/ Writable(h, m) \/ HubAsk(h, m) \/ Lose(h, m) \/ Deliver(h, m)
           \/ \E m \in Hinted, n \in Members : Hint(m, n)
Spec == Init /\ [][Next]_vars

\* Every variable holds what it should. A place is 0 unless the recipient is stale.
TypeOK ==
    /\ \A h \in Hubs : live[h] \subseteq Members /\ pubs[h] \subseteq Members /\ told[h] \subseteq Members
    /\ \A h \in Hubs : stale[h] \subseteq Members /\ asks[h] \subseteq Members
    /\ \A h \in Hubs, m \in Members : place[h][m] \in 0..Max /\ (m \notin stale[h] => place[h][m] = 0)
    /\ \A h \in Hubs, m \in Members : Len(chan[h][m]) <= StreamCap
    /\ \A m \in Members : peers[m] \subseteq Members /\ from[m] \in Hubs \cup {"none"}
    /\ \A m \in Members, h \in Hubs : part[m][h].ids \subseteq Members /\ part[m][h].got <= Max
    /\ \A m \in Members : hints[m] \subseteq Members /\ Cardinality(hints[m]) <= HintMax

\* A hub's list is its subscribers' lowest Max ids, and its current version names it in the history.
ToldIsList == \A h \in Hubs : told[h] = Cap(live[h]) /\ <<life[h], seq[h], told[h]>> \in hist[h]

\* A member that holds a version of a hub's list holds what that hub's list was at that version.
ViewIsHubSet == \A m \in Members :
    (from[m] # "none" /\ pver[m] # None) => <<pver[m][1], pver[m][2], peers[m]>> \in hist[from[m]]

\* A member that holds its hub's current version holds its hub's list.
Synced == \A m \in Members :
    (from[m] # "none" /\ pver[m] = Cur(from[m])) => peers[m] = told[from[m]]

\* A recipient whose list fits the stream is never owed it from the middle: a list that fits goes whole or not at all.
FitPlaceZero == \A h \in Hubs, m \in Members : (m \in stale[h] /\ Fits(told[h])) => place[h][m] = 0

\* A recipient's place goes back to 0 while it is still owed the list only when the list changed, when it asked, or when
\* its session ended.
PlaceKept == [][\A h \in Hubs, m \in Members :
                  (place[h][m] > 0 /\ place'[h][m] = 0 /\ m \in stale'[h]) =>
                      \/ told'[h] # told[h]
                      \/ (m \in asks[h] /\ m \notin asks'[h])
                      \/ Resub(h, m)]_vars

\* A hint is never a node the member's list names: the list covers it (and a member's reach is the two sets together,
\* each node once).
HintsApart == \A m \in Members : hints[m] \cap peers[m] = {}

\* A stale entry is always a recipient: the hub owes the whole list only to those it tells.
StaleAreRecipients == \A h \in Hubs : stale[h] \subseteq Rcpt(h)

\* An unbroken gathering holds exactly the lowest ids it has counted of the hub's list at its version, and that list
\* has the gathering's total.
PartIsPrefix == \A m \in Members, h \in Hubs :
    (part[m][h].on /\ ~part[m][h].broken) =>
        \E e \in hist[h] : /\ e[1] = part[m][h].v[1] /\ e[2] = part[m][h].v[2]
                           /\ Cardinality(e[3]) = part[m][h].total
                           /\ Cardinality(part[m][h].ids) = part[m][h].got
                           /\ part[m][h].ids = Low(e[3], part[m][h].got)
=============================================================================
