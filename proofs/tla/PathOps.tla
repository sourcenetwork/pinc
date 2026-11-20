------------------------------- MODULE PathOps -------------------------------
(***************************************************************************)
(* The path table of pinc-transport conn/path.rs and what a connection's  *)
(* datagram input does to it (conn/recv.rs handle_inner, on_handshake,     *)
(* process_payload; conn/drive.rs follow_reply), call for call.            *)
(* ReplyPath.tla checks the operators over every interleaving and every    *)
(* input; TraceReplyPath.tla replays the recorded runs of the real code.   *)
(*                                                                         *)
(* A table t is NP slots: Empty, or the path's id (from 1), whether it     *)
(* is validated (v) and its kind (k): "d" a direct path, "r" one through a *)
(* relay. A relay path is born validated and nothing ever validates one    *)
(* again, so a relay slot always holds v (TypeOK pins it); a path learnt   *)
(* by receiving on it is direct and unvalidated.                           *)
(* act is the slot of the active path. Learn is                            *)
(* new_path_slot as learn_path calls it, the one rule of both roles for a  *)
(* path the connection learns by receiving on it: the slot of the path if *)
(* it is held already, else the first empty slot, else the first          *)
(* unvalidated path that is not the active one is given up, else no path  *)
(* is added. Place is that rule without the look-up, the rule before the   *)
(* correction that followed #399: it adds a path it already holds again.  *)
(*                                                                         *)
(* A connection c: t and act; hs, the handshake ("wait": the first flight  *)
(* is out, "key": a Reply waits for the key host, "done": established);   *)
(* rf, reply_from (the path of the last message the handshake took, 0 for  *)
(* none); pend, the path of the Reply that waits for the key host (0 for   *)
(* none), a ghost the properties read, not a field of the code; smp, the   *)
(* round trip estimate has a sample; hd, the handshake_dropped count.      *)
(*                                                                         *)
(* What a dialing side's handshake packet completes (Kinds), as its        *)
(* machine answers it: "none" no message (a fragment of one, or no         *)
(* handshake packet), "bad" a message that fails authentication (counted), *)
(* "other" one refused for another reason, "rej" a reject with the right  *)
(* echo (taken; nothing authenticated), "pend" a Reply that passed its     *)
(* first checks (the key host decides), "auth" a resume Reply, or a late  *)
(* one, that authenticated (the session is established at once). A Reply  *)
(* or a reject that arrives while a Reply waits for the key host is        *)
(* refused (UnexpectedMessage).                                            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NP,
          Direct \* TRUE: the rule since #598, a relay path the session leaves stays validated; FALSE: the rule before,
                 \* which took the validity of the path the session left whatever its kind

Empty == [id |-> 0, v |-> FALSE, k |-> "d"]
Kinds == {"none", "bad", "other", "rej", "pend", "auth"}

\* the least element of a set of slots, 0 for none
First(S) == IF S = {} THEN 0 ELSE CHOOSE i \in S : \A j \in S : i <= j

\* Paths::find: the first slot that holds the path id, 0 for none
Find(t, id) == First({i \in 1..NP : t[i].id = id})

\* new_path_slot: the first empty slot, else the first unvalidated path that is not the active one, 0 for none
Slot(t, act) ==
    LET free == {i \in 1..NP : t[i].id = 0}
    IN IF free # {} THEN First(free) ELSE First({i \in 1..NP : t[i].id # 0 /\ i # act /\ ~t[i].v})

\* the path id joins at Slot, direct and unvalidated, whether it is held or not (the rule before the correction); i = 0
\* when the table has no room
Place(t, act, id) ==
    LET i == Slot(t, act)
    IN IF i = 0 THEN [t |-> t, i |-> 0] ELSE [t |-> [t EXCEPT ![i] = [id |-> id, v |-> FALSE, k |-> "d"]], i |-> i]

\* learn_path (new_path_slot): the slot of a path already held, its state untouched, else Place
Learn(t, act, id) == IF Find(t, id) # 0 THEN [t |-> t, i |-> Find(t, id)] ELSE Place(t, act, id)

\* add_path with what the endpoint knows of the path (a held one stays as it is): a relay's is born validated;
\* i = 0 is TooMany
AddPath(t, act, id, k) ==
    LET l == Learn(t, act, id)
    IN IF l.i = 0 \/ Find(t, id) # 0 THEN l
       ELSE [l EXCEPT !.t = [l.t EXCEPT ![l.i] = [id |-> id, v |-> (k = "r"), k |-> k]]]

\* remove_path: r is "ok", "unknown" or "active" (the active path is not removed)
RemovePath(t, act, id) ==
    LET i == Find(t, id)
    IN IF i = 0 THEN [t |-> t, r |-> "unknown"]
       ELSE IF i = act THEN [t |-> t, r |-> "active"]
       ELSE [t |-> [t EXCEPT ![i] = Empty], r |-> "ok"]

\* follow_reply: the reply's path is learnt (found when it is held); the session moves to it, which is validated, and
\* the path it leaves is no longer validated unless it is a relay's: a relay path is born validated and nothing ever
\* validates one again (#598), so taking its validity away there loses the path for good. With no room for it the
\* session stays on its path.
FollowReply(c) ==
    LET id == c.rf
        l == Learn(c.t, c.act, id)
        c0 == [c EXCEPT !.rf = 0]
    IN IF id = 0 \/ l.i = 0 THEN c0
       ELSE IF l.i = c.act THEN [c0 EXCEPT !.t = l.t]
       ELSE [c0 EXCEPT !.t = [l.t EXCEPT ![c.act].v = (Direct /\ c.t[c.act].k = "r"), ![l.i].v = TRUE], !.act = l.i]

\* pump at the establishment: follow_reply, and the round trip sample feed took if the first flight went unrepeated (s)
Establish(c, s) == FollowReply([c EXCEPT !.hs = "done", !.pend = 0, !.smp = @ \/ s])

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
=============================================================================
