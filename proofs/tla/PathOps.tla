------------------------------- MODULE PathOps -------------------------------
(***************************************************************************)
(* The path table of pinc-transport conn/path.rs and what a connection's  *)
(* datagram input does to it (conn/recv.rs handle_inner, on_handshake,     *)
(* process_payload; conn/drive.rs follow_reply, on_hs_event), call for     *)
(* call. ReplyPath.tla checks the operators over every interleaving and    *)
(* every input; TraceReplyPath.tla replays the recorded runs of the real   *)
(* code.                                                                   *)
(*                                                                         *)
(* A table t is NP slots: Empty, or the path's id (from 1) and whether it  *)
(* is validated (v). act is the slot of the active path. Learn is          *)
(* new_path_slot as learn_path calls it, the one rule of both roles for a  *)
(* path the connection learns by receiving on it: the slot of the path if *)
(* it is held already, else the first empty slot, else the first          *)
(* unvalidated path that is not the active one is given up, else no path  *)
(* is added. A responder in its handshake gives up a path it owes its     *)
(* flight to only when every such path is owed (LearnR). Place is that    *)
(* rule without the look-up, the rule before the correction that followed *)
(* #399: it adds a path it already holds again.                           *)
(*                                                                         *)
(* A connection c: t and act; hs, the handshake ("wait": the first flight  *)
(* is out, "key": a Reply waits for its verdict, the key host's answer to  *)
(* its Decapsulate request, "sign": the Finish waits for its signature,    *)
(* "done": established);                                                   *)
(* rf, reply_from (the path of the last message the handshake took, 0 for  *)
(* none); pend, the path of the Reply that waits for the key host (0 for   *)
(* none), a ghost the properties read, not a field of the code; smp, the   *)
(* round trip estimate has a sample; hd, the handshake_dropped count; fan, *)
(* the paths owed a copy of the handshake flight beside the active one     *)
(* (the fan-out set of conn/hooks.rs: a dialing side's Finish to a path    *)
(* only the reply named, a responder's flight to every path its first      *)
(* message completed on); asked, a ghost: the held paths a responder's     *)
(* first message completed on; ev, a ghost: at a responder's               *)
(* establishment, the paths its flight had gone to and the paths the      *)
(* establishment validated; rp, the path a resumed responder's Reply went  *)
(* to while its proof of receipt is owed (0 for none: not resumed, proved, *)
(* or the Reply left on a second path); hq, the handshake datagrams held   *)
(* while a Reply waits for its verdict, in arrival order, each with its    *)
(* path and what its message completes once it is tried (conn/recv.rs      *)
(* hold_part, conn/handshake_rx.rs hold).                                  *)
(*                                                                         *)
(* What a dialing side's handshake packet completes (Kinds), as its        *)
(* machine answers it: "none" no message (a fragment of one, or no         *)
(* handshake packet), "bad" a message that fails authentication (counted), *)
(* "other" one refused for another reason, "rej" a reject with the right  *)
(* echo (taken; nothing authenticated), "pend" a Reply that passed its     *)
(* first checks (the key host decides), "auth" a resume Reply, or a late  *)
(* one, that authenticated (the session is established at once). While a   *)
(* Reply waits for its verdict every handshake datagram is held and none   *)
(* is applied (the hold, hold = TRUE): a failed verdict (counted) tries    *)
(* them in arrival order, up to the one that makes the dial wait again,    *)
(* and any other answer drops them (conn/drive.rs after_verdict). A        *)
(* message the same fragment completed for the other candidate (ready) is  *)
(* the first held one, on the Reply's path. hold = FALSE is the rule       *)
(* before: such a Reply or reject is refused (UnexpectedMessage), and one  *)
(* that fails authentication is counted, one that authenticates taken, at  *)
(* once. While the Finish waits for its signature nothing is held: a Reply *)
(* or a reject is refused.                                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NP

Empty == [id |-> 0, v |-> FALSE]
Kinds == {"none", "bad", "other", "rej", "pend", "auth"}

\* the least element of a set of slots, 0 for none
First(S) == IF S = {} THEN 0 ELSE CHOOSE i \in S : \A j \in S : i <= j

\* Paths::find: the first slot that holds the path id, 0 for none
Find(t, id) == First({i \in 1..NP : t[i].id = id})

\* the ids the table holds
HeldIds(t) == {t[i].id : i \in {j \in 1..NP : t[j].id # 0}}

\* new_path_slot: the first empty slot, else the first unvalidated path that is not the active one, 0 for none
Slot(t, act) ==
    LET free == {i \in 1..NP : t[i].id = 0}
    IN IF free # {} THEN First(free) ELSE First({i \in 1..NP : t[i].id # 0 /\ i # act /\ ~t[i].v})

\* the path id joins at Slot, unvalidated, whether it is held or not (the rule before the correction); i = 0 when
\* the table has no room
Place(t, act, id) ==
    LET i == Slot(t, act)
    IN IF i = 0 THEN [t |-> t, i |-> 0] ELSE [t |-> [t EXCEPT ![i] = [id |-> id, v |-> FALSE]], i |-> i]

\* learn_path (new_path_slot): the slot of a path already held, its state untouched, else Place
Learn(t, act, id) == IF Find(t, id) # 0 THEN [t |-> t, i |-> Find(t, id)] ELSE Place(t, act, id)

\* new_path_slot of a responder in its handshake: as Slot, but a path it owes its flight to is never given up (when
\* every path it may give up is owed, the new one is not learnt; with fan empty it is Slot)
SlotR(t, act, fan) ==
    LET free == {i \in 1..NP : t[i].id = 0}
        loose == {i \in 1..NP : t[i].id # 0 /\ i # act /\ ~t[i].v}
        spare == {i \in loose : t[i].id \notin fan}
    IN IF free # {} THEN First(free) ELSE First(spare)

LearnR(t, act, fan, id) ==
    IF Find(t, id) # 0 THEN [t |-> t, i |-> Find(t, id)]
    ELSE LET i == SlotR(t, act, fan)
         IN IF i = 0 THEN [t |-> t, i |-> 0] ELSE [t |-> [t EXCEPT ![i] = [id |-> id, v |-> FALSE]], i |-> i]

\* add_path: a path the endpoint names (a held one stays as it is); i = 0 is TooMany
AddPath(t, act, id) == Learn(t, act, id)

\* remove_path: r is "ok", "unknown" or "active" (the active path is not removed)
RemovePath(t, act, id) ==
    LET i == Find(t, id)
    IN IF i = 0 THEN [t |-> t, r |-> "unknown"]
       ELSE IF i = act THEN [t |-> t, r |-> "active"]
       ELSE [t |-> [t EXCEPT ![i] = Empty], r |-> "ok"]

\* follow_reply: the reply's path is learnt (found when it is held). A path the dial held (an address the endpoint
\* chose and sent the flight to) is validated and becomes the active one; the path it leaves is no longer validated.
\* A path only the reply named proves nothing, since anyone can send a copy of the reply from any source: it joins
\* unvalidated, is challenged (the challenge is not this model's) and is owed a copy of the Finish within its budget
\* (fan), and the session stays on its path. move = TRUE is the rule before: the session moved to that path too. With
\* no room for it the session stays on its path.
FollowReplyM(c, move) ==
    LET id == c.rf
        held == Find(c.t, id) # 0
        l == Learn(c.t, c.act, id)
        c0 == [c EXCEPT !.rf = 0]
    IN IF id = 0 \/ l.i = 0 THEN c0
       ELSE IF l.i = c.act THEN [c0 EXCEPT !.t = l.t]
       ELSE IF held \/ move
            THEN [c0 EXCEPT !.t = [l.t EXCEPT ![c.act].v = FALSE, ![l.i].v = held], !.act = l.i]
            ELSE [c0 EXCEPT !.t = l.t, !.fan = {id}]

\* pump at the establishment: follow_reply, and the round trip sample feed took if the first flight went unrepeated (s)
EstablishM(c, s, move) == FollowReplyM([c EXCEPT !.hs = "done", !.pend = 0, !.smp = @ \/ s], move)

\* on_handshake of a dialing side: what the machine's answer to a completed message does (Drop::Empty once established);
\* while a Reply waits for its verdict the datagram is held, applied to nothing (hold_part)
HsMsgM(c, id, k, s, move, hold) ==
    IF c.hs = "done" THEN c
    ELSE IF hold /\ c.hs = "key" THEN [c EXCEPT !.hq = Append(@, [id |-> id, k |-> k])]
    ELSE CASE k = "bad" -> [c EXCEPT !.hd = @ + 1]
           [] k = "rej" /\ c.hs = "wait" -> [c EXCEPT !.rf = id]
           [] k = "pend" /\ c.hs = "wait" -> [c EXCEPT !.rf = id, !.pend = id, !.hs = "key"]
           [] k = "auth" -> EstablishM([c EXCEPT !.rf = id], s, move)
           [] OTHER -> c

\* A datagram on path id at a dialing side: its handshake packet (k) and a 1-RTT packet behind it (coal). old is the rule
\* before #399: a handshake packet on a path the session does not hold is dropped (NoPath). The 1-RTT packet opens only
\* once the session is established (before, it is held and later taken on the active path); process_payload takes the
\* slot handle_inner found at the start of the datagram, and learns the path when there was none: after the reply that
\* learnt it in the same datagram, Learn finds it. look = FALSE is the rule before the correction (Place), which adds
\* the path a second time.
RxM(c, id, k, coal, s, old, look, move, hold) ==
    LET known == Find(c.t, id)
        c1 == IF old /\ known = 0 THEN c ELSE HsMsgM(c, id, k, s, move, hold)
        l == IF look THEN Learn(c1.t, c1.act, id) ELSE Place(c1.t, c1.act, id)
    IN IF coal /\ c1.hs = "done" /\ known = 0 THEN [c1 EXCEPT !.t = l.t] ELSE c1

\* after a failed verdict (after_verdict): the held messages x is given, in arrival order, until one makes the dial wait
\* for a verdict again (the rest stay held) or none is left; once the session is established the rest is dropped (it
\* takes no handshake message)
RECURSIVE ReplayM(_, _, _, _)
ReplayM(x, q, s, move) ==
    IF q = <<>> \/ x.hs = "done" THEN [x EXCEPT !.hq = <<>>]
    ELSE IF x.hs = "key" THEN [x EXCEPT !.hq = q]
    ELSE ReplayM(HsMsgM(x, Head(q).id, Head(q).k, s, move, TRUE), Tail(q), s, move)

\* A key answer (on_key_response, answer_soft): "ok" the Reply authenticated and the session is established; "more"
\* another key request follows (the signature of the Finish); "bad" the Reply failed a check once the key host answered
\* (counted; the dial waits on), and the messages held meanwhile are tried. "ok" and "more" drop them.
KeyM(c, r, s, move, hold) ==
    IF c.hs \notin {"key", "sign"} THEN c
    ELSE CASE r = "ok" -> EstablishM([c EXCEPT !.hq = <<>>], s, move)
           [] r = "more" -> [c EXCEPT !.hs = "sign", !.hq = <<>>]
           [] r = "bad" -> ReplayM([c EXCEPT !.hs = "wait", !.pend = 0, !.hd = @ + 1, !.hq = <<>>], c.hq, s, move)
           [] OTHER -> c

\* the code's rule (TraceReplyPath.tla replays the code with these)
FollowReply(c) == FollowReplyM(c, FALSE)
Rx(c, id, k, coal, s, old, look) == RxM(c, id, k, coal, s, old, look, FALSE, TRUE)
Key(c, r, s) == KeyM(c, r, s, FALSE, TRUE)

\* An established connection, either role, takes a 1-RTT packet on a path it does not hold: process_payload learns it.
App(c, id) == IF c.hs = "done" /\ Find(c.t, id) = 0 THEN [c EXCEPT !.t = Learn(c.t, c.act, id).t] ELSE c

\* where a responder's flight goes: rule "active" (the rule before) the active path only; else the paths it owes
Targets(c, rule) == IF rule = "active" THEN HeldIds(c.t) \cap {c.t[c.act].id} ELSE c.fan

\* where a resumed responder's Reply leaves (send.rs target_order): the paths it is owed on, or the active path when it
\* is owed on none
Dest(c, rule) == IF Targets(c, rule) = {} THEN HeldIds(c.t) \cap {c.t[c.act].id} ELSE Targets(c, rule)

\* the Reply of a resumed responder leaves: the dialer's first 1-RTT packet proves receipt at the one path it went to,
\* and once it leaves on a second path the keys no longer say where (send.rs reply_left_on; that path is challenged,
\* PathMove's rule)
ReplyLeft(c, rule) == IF c.rp # 0 /\ Dest(c, rule) # {c.rp} THEN [c EXCEPT !.rp = 0] ELSE c

\* A responder's establishment by a message on path id after its flight went to the paths sent. The paths were proven
\* only if the flight went to one path alone: the message that establishes answers it, so whoever sent it received
\* there. That path is validated and becomes the active one. Else nothing is validated and the session goes to the
\* path the message came on (its paths are challenged; not this model's). Rule "active" (the rule before): the active
\* path is validated; rule "loose" (a broken variant): the message's path is validated whatever the flight did.
REst(c, id, rule, sent) ==
    LET here == Find(c.t, id)
        one == Cardinality(sent) = 1
        p == IF one THEN Find(c.t, CHOOSE x \in sent : TRUE) ELSE 0
        c0 == [c EXCEPT !.hs = "done", !.fan = {}]
    IN CASE rule = "active" -> [c0 EXCEPT !.t[c.act].v = TRUE, !.ev = [fan |-> sent, val |-> {c.t[c.act].id}]]
         [] rule = "loose" -> [c0 EXCEPT !.act = here, !.t[here].v = TRUE, !.ev = [fan |-> sent, val |-> {id}]]
         [] p # 0 -> [c0 EXCEPT !.act = p, !.t[p].v = TRUE, !.ev = [fan |-> sent, val |-> {c.t[p].id}]]
         [] OTHER -> [c0 EXCEPT !.act = here, !.ev = [fan |-> sent, val |-> {}]]

\* A responder's handshake datagram on path id (handle_inner): a path it does not hold is learnt while it is in its
\* handshake or holds none (else the handshake packet is NoPath), by LearnR; a path given up leaves fan and asked. m is
\* what its message completes: "part" nothing; "first" the first message, the first time or the same again (the
\* responder owes its flight to that path: under rule "active" only the active path gets it); "finish" a Finish that
\* authenticated (its flight went out before); "resume" a resumption Hello whose binder verified, the session's first
\* message: the session is established and no path is validated, since no flight went out before it and anyone who
\* saw the Hello can send a copy of it from any source: the Reply's path is recorded and the dialer's first 1-RTT packet
\* proves it (Confirm), unless the Reply leaves on several paths (ReplyLeft). rv: the rule before that fix, a
\* resumption Hello validates the active path.
RRx(c, id, m, rv, rule) ==
    LET empty == \A i \in 1..NP : c.t[i].id = 0
        l == IF Find(c.t, id) = 0 /\ (empty \/ c.hs # "done")
             THEN LearnR(c.t, c.act, IF rule = "active" THEN {} ELSE c.fan, id) ELSE [t |-> c.t, i |-> Find(c.t, id)]
        c1 == [c EXCEPT !.t = l.t, !.fan = @ \cap HeldIds(l.t), !.asked = @ \cap HeldIds(l.t)]
    IN IF c1.hs = "done" \/ l.i = 0 \/ c1.t[c1.act].id = 0 THEN c1
       ELSE CASE m = "first" -> [c1 EXCEPT !.asked = @ \cup {id}, !.fan = IF rule = "active" THEN @ ELSE @ \cup {id}]
              [] m = "finish" /\ c1.asked # {} -> REst(c1, id, rule, Targets(c1, rule))
              [] m = "resume" /\ c1.asked = {} ->
                    IF rv THEN [c1 EXCEPT !.hs = "done", !.t[c1.act].v = TRUE, !.ev = [fan |-> {}, val |-> {c1.t[c1.act].id}]]
                    ELSE ReplyLeft([c1 EXCEPT !.hs = "done", !.ev = [fan |-> {}, val |-> {}], !.rp = c1.t[c1.act].id,
                                              !.fan = IF rule = "active" THEN @ ELSE @ \cup {id}], rule)
              [] OTHER -> c1

\* A resumed responder re-sends its Reply until it is confirmed, on the paths it is owed on (ReplyLeft)
Resend(c, rule) == ReplyLeft(c, rule)

\* A packet that authenticated after the establishment (k = "app" under the 1-RTT keys, on any path; "early" under the
\* 0-RTT keys). The 1-RTT keys of a resumption mix the responder's fresh share, sent only in its Reply, so the first
\* such packet proves the dialer received the Reply and validates the path it went to (recv.rs, the confirmation
\* point, which also ends the fan-out). The 0-RTT keys come from the ticket and the Hello alone, which any copy of the
\* Hello opens: they prove nothing.
Confirm(c, k) ==
    IF k = "app" /\ c.hs = "done" /\ c.rp # 0
    THEN LET i == Find(c.t, c.rp) IN IF i = 0 THEN [c EXCEPT !.rp = 0, !.fan = {}] ELSE [c EXCEPT !.t[i].v = TRUE, !.rp = 0, !.fan = {}]
    ELSE IF k = "app" /\ c.hs = "done" THEN [c EXCEPT !.fan = {}]
    ELSE c
=============================================================================
