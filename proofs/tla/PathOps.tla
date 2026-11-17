------------------------------- MODULE PathOps -------------------------------
(***************************************************************************)
(* The path table of vinc-transport conn/path.rs and what a connection's   *)
(* datagram input does to it (conn/recv.rs handle_inner, on_handshake,     *)
(* process_payload; conn/drive.rs follow_reply), call for call, and the    *)
(* choice of the active path (conn/path.rs rank, best_path, choose_path,   *)
(* set_path_info; conn/timer.rs; the fall-back of conn/path_fall.rs).      *)
(* ReplyPath.tla checks the operators over every interleaving and every    *)
(* input; TraceReplyPath.tla replays the recorded runs of the real code.   *)
(*                                                                         *)
(* A table t is NP slots: Empty, or the path's id (from 1), whether it     *)
(* is validated (v), its kind (k: "direct", or "relay", a path through a   *)
(* relay), its cost (r: 0 for none, else 1..RT; the session's estimate     *)
(* stamped on it) and whether it is seen (sn: a packet sent on it was      *)
(* acknowledged; a fact of its own, apart from the cost: a seen path has   *)
(* a cost, a stamped one need not be seen). lf is a ghost the properties   *)
(* read, not a field of the code: the session left the path at the         *)
(* probe-timeout bound with nothing acknowledged on it, and has not        *)
(* moved since. A relay path is valid from the moment the connection       *)
(* tracks it and is never challenged, so a relay path is always            *)
(* validated; a path a connection learns by receiving on it is direct      *)
(* until the endpoint names it a relay path (SetInfo, which validates      *)
(* it). act is the slot of the active path.                                *)
(*                                                                         *)
(* Learn is new_path_slot as learn_path calls it, the one rule of both     *)
(* roles for a path the connection learns by receiving on it: the slot of  *)
(* the path if it is held already, else the first empty slot, else the     *)
(* first unvalidated path that is not the active one is given up, else no  *)
(* path is added. Place is that rule without the look-up, the rule before  *)
(* the correction that followed #399: it adds a path it already holds      *)
(* again.                                                                  *)
(*                                                                         *)
(* The active path is chosen by rank. The usable paths (held and           *)
(* validated) are ranked by <<Unseen, Cost, slot>>, least first (Best).    *)
(* A path is Unseen when it is a relay path that is not seen (sn) and is   *)
(* either not the active path, or is the active path after PTO_FALLBACK    *)
(* probe timeouts in a row (f). Cost is the path's cost, and RT + 1 more   *)
(* for a relay path. Rank says how much of that rule the model applies:    *)
(* "full" is the rule of the code; "noescape" has no escape (the active    *)
(* path is never unseen); "cost" is the rule of the second round, which    *)
(* read "seen" off the cost (so a stamped path counts as seen); "none"     *)
(* is the rule before: the cost and the slot alone. Choose is              *)
(* choose_path: it moves to the best path at once from a relay path (or    *)
(* from none), and the path it leaves takes the session's estimate as      *)
(* its cost, if there is one, and stays as unseen as it was (Switch).      *)
(* Timer is a timer pass: the fall-back of a failed direct path            *)
(* (Fallback), then Choose. SetInfo is set_path_info, Measure an           *)
(* acknowledged packet (the active path is seen and has a cost, the        *)
(* sample is there, f is cleared), Fail the third probe timeout in a       *)
(* row. With RT = 0 no path has a cost and nothing of it changes a         *)
(* table. A path that takes a slot (Learn, Place) takes it with no cost    *)
(* and unseen; Forget = FALSE is the rule before, in which an evicted      *)
(* path hands its cost and its seen fact to the path that takes its        *)
(* slot.                                                                   *)
(*                                                                         *)
(* Outside the model: an acknowledgement of a packet sent on a path the    *)
(* session is not on, which includes one sent on an earlier occupant of a  *)
(* slot (only the active path is measured; the library keeps the reorder   *)
(* state of a slot and clears only its round trip and its seen fact when   *)
(* another path takes it, and counts an acknowledgement for the slot only  *)
(* when its packet was sent by the slot's present occupant, a rule of the  *)
(* occupant and not of a clock: Recovery.tla states it, as                 *)
(* Recovery_forget). A standby relay path cannot become seen here: a step  *)
(* marks only the active path seen, and the library's datagram to a        *)
(* validated relay path that stands by carries its PING and PATH frames    *)
(* only, no tracked stream data, so nothing is acknowledged on it while it *)
(* stands by. The stamp is the same positive cost on every path (two       *)
(* stamped paths are not compared); the frames of any datagram are not     *)
(* modelled; and fail-over between relay paths (vinc#625, not built): a    *)
(* failing relay path is left only for a path that ranks before it.        *)
(*                                                                         *)
(* A connection c: t and act; hs, the handshake ("wait": the first flight  *)
(* is out, "key": a Reply waits for the key host, "done": established);    *)
(* rf, reply_from (the path of the last message the handshake took, 0 for  *)
(* none); pend, the path of the Reply that waits for the key host (0 for   *)
(* none), a ghost the properties read, not a field of the code; smp, the   *)
(* round trip estimate has a sample; f, the active path failed             *)
(* PTO_FALLBACK probe timeouts in a row; hd, the handshake_dropped count.  *)
(*                                                                         *)
(* What a dialing side's handshake packet completes (Kinds), as its        *)
(* machine answers it: "none" no message (a fragment of one, or no         *)
(* handshake packet), "bad" a message that fails authentication (counted), *)
(* "other" one refused for another reason, "rej" a reject with the right   *)
(* echo (taken; nothing authenticated), "pend" a Reply that passed its     *)
(* first checks (the key host decides), "auth" a resume Reply, or a late   *)
(* one, that authenticated (the session is established at once). A Reply   *)
(* or a reject that arrives while a Reply waits for the key host is        *)
(* refused (UnexpectedMessage).                                            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NP,
          RelayKeep, \* TRUE: the rule of the code, the path a session leaves keeps its validity if it is a relay path;
                     \* FALSE: the rule before the correction, whatever the kind the path it leaves is unvalidated
          RT,        \* the largest round trip a path holds; 0: the model has no round trips and nothing to choose by
          Forget,    \* TRUE: the rule of the code, a path that takes a slot takes it with no cost and unseen;
                     \* FALSE: an evicted path hands its cost and its seen fact to the path that takes its slot
          Rank       \* "full": the rule of the code; "noescape": no escape for the active path; "cost": the second
                     \* round (the cost read as seen); "none": no unseen key

PKinds == {"direct", "relay"}
Empty == [id |-> 0, v |-> FALSE, k |-> "direct", r |-> 0, sn |-> FALSE, lf |-> FALSE]
Kinds == {"none", "bad", "other", "rej", "pend", "auth"}

\* the least element of a set of slots, 0 for none
First(S) == IF S = {} THEN 0 ELSE CHOOSE i \in S : \A j \in S : i <= j

\* the greatest element of a set of slots, 0 for none
Last(S) == IF S = {} THEN 0 ELSE CHOOSE i \in S : \A j \in S : j <= i

\* Paths::find: the first slot that holds the path id, 0 for none
Find(t, id) == First({i \in 1..NP : t[i].id = id})

\* new_path_slot: the first empty slot, else the first unvalidated path that is not the active one, 0 for none
Slot(t, act) ==
    LET free == {i \in 1..NP : t[i].id = 0}
    IN IF free # {} THEN First(free) ELSE First({i \in 1..NP : t[i].id # 0 /\ i # act /\ ~t[i].v})

\* the path id takes a slot that held old: unvalidated, direct, with no cost and unseen (Forget), or with the cost and
\* the seen fact of old (the rule before)
Takes(old, id) ==
    [id |-> id, v |-> FALSE, k |-> "direct", r |-> IF Forget THEN 0 ELSE old.r, sn |-> IF Forget THEN FALSE ELSE old.sn,
     lf |-> FALSE]

\* the path id joins at Slot, unvalidated, whether it is held or not (the rule before the correction); i = 0 when
\* the table has no room
Place(t, act, id) ==
    LET i == Slot(t, act)
    IN IF i = 0 THEN [t |-> t, i |-> 0]
       ELSE [t |-> [t EXCEPT ![i] = Takes(t[i], id)], i |-> i]

\* learn_path (new_path_slot): the slot of a path already held, its state untouched, else Place
Learn(t, act, id) == IF Find(t, id) # 0 THEN [t |-> t, i |-> Find(t, id)] ELSE Place(t, act, id)

\* add_path: a path the endpoint names (a held one stays as it is); i = 0 is TooMany
AddPath(t, act, id) == Learn(t, act, id)

\* remove_path: r is "ok", "unknown" or "active" (the active path is not removed)
RemovePath(t, act, id) ==
    LET i == Find(t, id)
    IN IF i = 0 THEN [t |-> t, r |-> "unknown"]
       ELSE IF i = act THEN [t |-> t, r |-> "active"]
       ELSE [t |-> [t EXCEPT ![i] = Empty], r |-> "ok"]

\* the path a session moves off (Path::left): a direct path is no longer validated, a relay path stays valid for as long
\* as the connection tracks it
Left(s) == [s EXCEPT !.v = IF RelayKeep /\ s.k = "relay" THEN @ ELSE FALSE]

\* the cost a path the session leaves is stamped with when a sample is held: any positive one (two stamped relay
\* paths are not compared by the model), none when the model has no round trips
Sample == IF RT > 0 THEN 1 ELSE 0

\* the path a session leaves by its own choice (switch_active) takes the connection's sample as its own cost; it is not
\* seen for that
Stamp(s, smp) == IF smp /\ s.id # 0 THEN [s EXCEPT !.r = Sample] ELSE s

\* no path is marked as left at the bound (a move of the session that is not the choice of the active path)
ClearLf(t) == [j \in 1..NP |-> [t[j] EXCEPT !.lf = FALSE]]

\* follow_reply: the reply's path is learnt (found when it is held); the session moves to it, which is validated, and
\* the path it leaves is left (Left) and stamped. With no room for it the session stays on its path.
FollowReply(c) ==
    LET id == c.rf
        l == Learn(c.t, c.act, id)
        c0 == [c EXCEPT !.rf = 0]
    IN IF id = 0 \/ l.i = 0 THEN c0
       ELSE IF l.i = c.act THEN [c0 EXCEPT !.t = l.t]
       ELSE [c0 EXCEPT !.t = ClearLf([l.t EXCEPT ![c.act] = Stamp(Left(l.t[c.act]), c.smp), ![l.i].v = TRUE]),
                       !.act = l.i]

\* pump at the establishment: follow_reply, then the round trip sample feed took if the first flight went unrepeated (s)
Establish(c, s) ==
    LET d == FollowReply([c EXCEPT !.hs = "done", !.pend = 0])
    IN [d EXCEPT !.smp = c.smp \/ s]

\* on_handshake of a dialing side: what the machine's answer to a completed message does (Drop::Empty once established)
HsMsg(c, id, k, s) ==
    IF c.hs = "done" THEN c
    ELSE CASE k = "bad" -> [c EXCEPT !.hd = @ + 1]
           [] k = "rej" /\ c.hs = "wait" -> [c EXCEPT !.rf = id]
           [] k = "pend" /\ c.hs = "wait" -> [c EXCEPT !.rf = id, !.pend = id, !.hs = "key"]
           [] k = "auth" -> Establish([c EXCEPT !.rf = id], s)
           [] OTHER -> c

\* A datagram on path id at a dialing side: its handshake packet (k) and a 1-RTT packet behind it (coal). old is the rule
\* before #399: a handshake packet on a path the session does not hold is dropped (NoPath). The 1-RTT packet opens only
\* once the session is established (before, it is held and later taken on the active path); process_payload takes the
\* slot handle_inner found at the start of the datagram, and learns the path when there was none: after the reply that
\* learnt it in the same datagram, Learn finds it. look = FALSE is the rule before the correction (Place), which adds
\* the path a second time.
Rx(c, id, k, coal, s, old, look) ==
    LET known == Find(c.t, id)
        c1 == IF old /\ known = 0 THEN c ELSE HsMsg(c, id, k, s)
        l == IF look THEN Learn(c1.t, c1.act, id) ELSE Place(c1.t, c1.act, id)
    IN IF coal /\ c1.hs = "done" /\ known = 0 THEN [c1 EXCEPT !.t = l.t] ELSE c1

\* A key answer (on_key_response): "ok" the Reply authenticated and the session is established; "more" another key
\* request follows (the signature of the Finish); "bad" the Reply failed a check once the key host answered (counted;
\* the dial waits on)
Key(c, r, s) ==
    IF c.hs # "key" THEN c
    ELSE CASE r = "ok" -> Establish(c, s)
           [] r = "bad" -> [c EXCEPT !.hs = "wait", !.pend = 0, !.hd = @ + 1]
           [] OTHER -> c

\* An established connection, either role, takes a 1-RTT packet on a path it does not hold: process_payload learns it.
App(c, id) == IF c.hs = "done" /\ Find(c.t, id) = 0 THEN [c EXCEPT !.t = Learn(c.t, c.act, id).t] ELSE c

\* A responder's handshake datagram on path id (handle_inner): a path it does not hold is learnt while it is in its
\* handshake or holds none (else the handshake packet is NoPath). est: the datagram establishes the session, which
\* validates the active path.
RRx(c, id, est) ==
    LET empty == \A i \in 1..NP : c.t[i].id = 0
        c1 == IF Find(c.t, id) = 0 /\ (empty \/ c.hs # "done") THEN [c EXCEPT !.t = Learn(c.t, c.act, id).t] ELSE c
    IN IF est /\ c1.hs # "done" /\ Find(c1.t, id) # 0 /\ c1.t[c1.act].id # 0
       THEN [c1 EXCEPT !.hs = "done", !.t[c1.act].v = TRUE] ELSE c1

\* ---- the choice of the active path ----

\* a path is usable: held and validated
Usable(c, i) == c.t[i].id # 0 /\ c.t[i].v

\* The relay path of slot i is unseen under rank rk: it is not seen (under "cost", it has no cost), and it is not the
\* active path, or (the escape, "full" and "cost") it is the active path after PTO_FALLBACK probe timeouts in a row.
\* "none" has no unseen key.
UnseenBy(rk, c, i) ==
    /\ c.t[i].id # 0 /\ c.t[i].k = "relay"
    /\ IF rk = "cost" THEN c.t[i].r = 0 ELSE ~c.t[i].sn
    /\ IF rk = "none" THEN FALSE ELSE IF rk = "noescape" THEN i # c.act ELSE i # c.act \/ c.f
Unseen(c, i) == UnseenBy(Rank, c, i)

\* the cost of a path: its round trip, and one more than any round trip for a relay path
Cost(s) == s.r + IF s.k = "relay" THEN RT + 1 ELSE 0

\* the rank of slot i, and the order of ranks (the least wins; the slot makes every rank distinct)
RankKey(c, i) == <<IF Unseen(c, i) THEN 1 ELSE 0, Cost(c.t[i]), i>>
Before(a, b) == a[1] < b[1] \/ (a[1] = b[1] /\ (a[2] < b[2] \/ (a[2] = b[2] /\ a[3] < b[3])))

\* the slot of S of least rank, 0 for none
Ranked(c, S) == IF S = {} THEN 0 ELSE CHOOSE i \in S : \A j \in S : ~Before(RankKey(c, j), RankKey(c, i))

\* best_path: the usable path of least rank
Best(c) == Ranked(c, {i \in 1..NP : Usable(c, i)})

\* the active path is a relay path that failed PTO_FALLBACK probe timeouts in a row and is not seen
AtBound(c) == LET a == c.t[c.act] IN c.f /\ a.id # 0 /\ a.k = "relay" /\ ~a.sn

\* switch_active: the session moves to slot i by its own choice; the path it leaves is stamped with the sample (its cost
\* only) and, when it is a relay path left at the bound with nothing acknowledged on it, marked lf; no other is marked
Switch(c, i) ==
    IF i = c.act \/ c.t[i].id = 0 THEN c
    ELSE [c EXCEPT !.t = [j \in 1..NP |->
                              IF j = c.act THEN [Stamp(c.t[j], c.smp) EXCEPT !.lf = AtBound(c)]
                              ELSE [c.t[j] EXCEPT !.lf = FALSE]],
                   !.act = i]

\* choose_path: to the best path at once from a relay path (or from none); from a direct path only for a gain, which the
\* model leaves out
Choose(c) ==
    LET b == Best(c)
    IN IF b = 0 \/ ~(c.t[c.act].id = 0 \/ c.t[c.act].k = "relay") THEN c ELSE Switch(c, b)

\* fail_over and relay_fallback: the active direct path failed PTO_FALLBACK probe timeouts in a row; it is no longer
\* validated, and the session moves to the validated relay path of least rank, else to the last relay path. Without a
\* relay path nothing moves: the code challenges the failed path (the model leaves challenges out).
Fallback(c) ==
    LET a == c.t[c.act]
        rel == {i \in 1..NP : c.t[i].id # 0 /\ c.t[i].k = "relay"}
        vrel == {i \in rel : c.t[i].v}
        tgt == IF vrel # {} THEN Ranked(c, vrel) ELSE Last(rel)
    IN IF ~c.f \/ a.id = 0 \/ a.k # "direct" \/ ~a.v \/ tgt = 0 THEN c
       ELSE Switch([c EXCEPT !.t[c.act].v = FALSE], tgt)

\* a timer pass: the fall-back of a failed direct path, then the choice (on_path_timers)
Timer(c) == Choose(Fallback(c))

\* the endpoint names the kind of the path id (set_path_info) when the connection holds it and it differs
SetKind(c, id, kd) ==
    LET i == Find(c.t, id)
    IN IF i = 0 THEN c ELSE [c EXCEPT !.t[i].k = kd]

\* set_path_info: the new kind first, then the choice (Choose moves only from a relay path or from none), then a path
\* named a relay's is validated, as every relay path is
SetInfo(c, id, kd) ==
    LET i == Find(c.t, id)
        c1 == Choose(SetKind(c, id, kd))
    IN IF i = 0 \/ c.t[i].k = kd THEN c
       ELSE IF kd = "relay" THEN [c1 EXCEPT !.t[i].v = TRUE] ELSE c1

\* an acknowledged packet of an established connection: the active path is seen and has a cost r, the sample is there
\* and the probe timeouts in a row are over
Measure(c, r) ==
    IF c.hs # "done" \/ c.t[c.act].id = 0 THEN c
    ELSE [c EXCEPT !.t[c.act].r = r, !.t[c.act].sn = TRUE, !.smp = TRUE, !.f = FALSE]

\* the third probe timeout in a row on the active path of an established connection
Fail(c) == IF c.hs # "done" \/ c.t[c.act].id = 0 THEN c ELSE [c EXCEPT !.f = TRUE]
=============================================================================
