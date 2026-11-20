----------------------------- MODULE PathMoveOps -----------------------------
(***************************************************************************)
(* Path validation and migration of a connection, call for call, as        *)
(* pinc-transport conn/path.rs and the path part of conn/recv.rs do them   *)
(* once the session is established (the handshake's path rules are         *)
(* PathOps.tla's, checked by ReplyPath.tla; the lookup and the slot a new  *)
(* path takes are PathOps' Find and Slot, reused here). PathMove.tla       *)
(* checks the operators over every interleaving; TracePathMove.tla        *)
(* replays the recorded runs of the real code.                             *)
(*                                                                         *)
(* A slot p (Path): id (0 empty), k the kind ("d" direct, "r" relayed:     *)
(* the path runs through a node that carries the relay role), six (IPv6),  *)
(* v validated, ch the outstanding challenge (0 none), sent the table of   *)
(* the CH challenges kept (0 empty) and nx the next place in it            *)
(* (sent_next + 1), sc send_challenge, pr probes_left > 0, rj rejoin, gone,*)
(* hd what the clock says of last_rx ("never": 0, "fresh": heard within    *)
(* 15 s, "stale": silent for more than 15 s), r its round trip (ns).       *)
(* Ghosts the properties read: o the challenges that left on the slot,     *)
(* ps those pushed since its table was last cleared, lf the path was left  *)
(* while gone.                                                             *)
(* A connection c: t (NP slots), act the active slot, srtt the smoothed   *)
(* round trip (-1 before a sample), hi the last challenge token drawn     *)
(* (tokens are 1, 2, ... in drawing order: the random draw never repeats,  *)
(* an ideal primitive); ghosts mv (what moved the active path in this      *)
(* step) and dg (a choice moved off a usable direct path for a round-trip *)
(* gain of GAIN or less, the documented rule restated by T11).            *)
(*                                                                         *)
(* Time is not a number here: what the code reads of it is an input of the *)
(* step (hd, a probe due, the floor of a re-join, a challenge recent       *)
(* enough). rn says whether the random draw of a challenge succeeded       *)
(* (set_challenge changes nothing when it fails). Not modelled: the        *)
(* cadence of the probes (gaps, counts: pr only says whether one is left), *)
(* the amplification budget (Amp.tla), the datagram size (Mtu.tla).        *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS NP, CH, GAIN, PEN, BONUS

PO == INSTANCE PathOps

New(id, k, six, hd) ==
    [id |-> id, k |-> k, six |-> six, v |-> (k = "r"), ch |-> 0, sent |-> [x \in 1..CH |-> 0], nx |-> 1,
     sc |-> FALSE, pr |-> FALSE, rj |-> FALSE, gone |-> FALSE, hd |-> hd, r |-> 0, o |-> {}, ps |-> {}, lf |-> FALSE]
None == New(0, "d", FALSE, "never")

Max2(a, b) == IF a >= b THEN a ELSE b
\* the largest element of a set of slots, 0 for none
Last(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : y <= x

\* Path::cost: the round trip, plus one second for a relayed path, minus 3 ms for IPv6 (saturating)
Cost(p) == LET x == p.r + (IF p.k = "r" THEN PEN ELSE 0) IN IF p.six THEN Max2(0, x - BONUS) ELSE x
\* best_path's filter: validated, and not a direct path silent for 15 s (last_rx 0 reads as silent)
Usable(p) == p.id # 0 /\ p.v /\ (p.k = "r" \/ p.hd = "fresh")
\* best_path: the least (cost, slot) among the usable paths, 0 for none
Best(t) ==
    LET U == {x \in 1..NP : Usable(t[x])}
    IN IF U = {} THEN 0
       ELSE CHOOSE x \in U : \A y \in U : Cost(t[x]) < Cost(t[y]) \/ (Cost(t[x]) = Cost(t[y]) /\ x <= y)
Relays(t) == {x \in 1..NP : t[x].id # 0 /\ t[x].k = "r"}
\* the relayed paths relay_fallback may take: validated and not gone (fix T6)
Fallbacks(t) == {x \in Relays(t) : t[x].v /\ ~t[x].gone}

\* switch_active: the path left takes the smoothed round trip if there is a sample; m is the ghost of why
Switch(c, i, m) ==
    IF i = c.act \/ c.t[i].id = 0 THEN c
    ELSE [c EXCEPT !.t[c.act].r = IF c.srtt >= 0 /\ c.t[c.act].id # 0 THEN c.srtt ELSE @, !.act = i, !.mv = m]
\* follow_active: nothing restarts
Follow(c, i) == IF i = c.act \/ c.t[i].id = 0 THEN c ELSE [c EXCEPT !.act = i, !.mv = "follow"]
\* forget_gone: every gone path but the active one is dropped
ForgetGone(c) == [c EXCEPT !.t = [x \in 1..NP |-> IF x # c.act /\ c.t[x].id # 0 /\ c.t[x].gone THEN None ELSE c.t[x]]]

\* choose_path: to the best path at once from no path, a gone one or a relayed one, else when its round trip (not its
\* cost) is lower by more than GAIN; dg records a move off a usable direct path whose round-trip gain is GAIN or less
Choose(c) ==
    LET b == Best(c.t)
        cur == c.t[c.act]
    IN IF b = 0 THEN c
       ELSE IF cur.id = 0 \/ cur.gone \/ cur.k = "r" \/ c.t[b].r + GAIN < cur.r
            THEN LET d == ForgetGone(Switch(c, b, "choose"))
                 IN IF b # c.act /\ Usable(cur) /\ ~cur.gone /\ cur.k = "d" /\ cur.r - c.t[b].r <= GAIN
                    THEN [d EXCEPT !.dg = TRUE] ELSE d
            ELSE c

\* active_open_to_move (fix T4): the active path is left for any better path at once: none, gone or relayed
OpenToMove(c) == c.t[c.act].id = 0 \/ c.t[c.act].gone \/ c.t[c.act].k = "r"

\* relay_fallback: to the validated relayed path of the highest slot that is not gone (fix T6)
Fallback(c) == IF Fallbacks(c.t) = {} THEN c ELSE Switch(c, Last(Fallbacks(c.t)), "fallback")

\* push_challenge, set_challenge, queue_challenge, start_punch, is_challenge
Push(p, tok) == [p EXCEPT !.ch = tok, !.sent[p.nx] = tok, !.nx = (p.nx % CH) + 1, !.ps = @ \cup {tok}]
SetChal(c, i, rn) == IF ~rn \/ c.t[i].id = 0 THEN c ELSE [c EXCEPT !.hi = @ + 1, !.t[i] = Push(@, c.hi + 1)]
QueueChal(c, i, rn) ==
    IF c.t[i].id = 0 THEN c ELSE LET d == SetChal(c, i, rn) IN [d EXCEPT !.t[i].sc = (d.t[i].ch # 0)]
StartPunch(c, i, rn) ==
    IF c.t[i].id = 0 THEN c ELSE LET d == SetChal(c, i, rn) IN [d EXCEPT !.t[i].pr = TRUE, !.t[i].rj = FALSE]
IsChal(p, tok) == tok > 0 /\ \E x \in 1..CH : p.sent[x] = tok
\* what an answer (or path_returned) does to the slot: the table cleared, validated, no probe left, not rejoining
Clear(p, r) ==
    [p EXCEPT !.sent = [x \in 1..CH |-> 0], !.ch = 0, !.sc = FALSE, !.v = TRUE, !.pr = FALSE, !.rj = FALSE,
              !.r = r, !.ps = {}]

\* on_path_response: an answer to any challenge in the table validates the slot it arrived on, then choose_path; a
\* gone path is never validated again (fix T6)
OnResp(c, i, tok, r) ==
    IF c.t[i].id = 0 \/ c.t[i].gone \/ ~IsChal(c.t[i], tok) THEN c ELSE Choose([c EXCEPT !.t[i] = Clear(@, r)])

\* a packet that opened on slot i: last_rx = now
Heard(c, i) == IF i = 0 THEN c ELSE [c EXCEPT !.t[i].hd = "fresh"]

\* learn_path (new_path_slot): the slot of a held path, else a new direct, unvalidated path heard now in PathOps'
\* Slot; i = 0 when there is no room (Drop::NoPath)
Learn(c, id) ==
    LET f == PO!Find(c.t, id)
        s == PO!Slot(c.t, c.act)
    IN IF f # 0 THEN [c |-> c, i |-> f]
       ELSE IF s = 0 THEN [c |-> c, i |-> 0]
       ELSE [c |-> [c EXCEPT !.t[s] = New(id, "d", FALSE, "fresh")], i |-> s]

\* take_info (fix T7): a held path takes the kind the endpoint names; a relayed one neither validated nor gone is
\* validated, as every relayed path is (nothing for a slot no longer held)
TakeInfo(c, f, k, six) ==
    LET d == [c EXCEPT !.t[f].k = k, !.t[f].six = six]
    IN IF c.t[f].id = 0 THEN c
       ELSE IF k = "r" /\ ~d.t[f].v /\ ~d.t[f].gone THEN [d EXCEPT !.t[f].v = TRUE] ELSE d
\* the new-path part of add_path in slot s: never heard (last_rx 0), a relayed one validated, a direct one punched
\* (its challenge drawn, not yet queued)
Fresh(c, s, id, k, six, rn) ==
    LET d == [c EXCEPT !.t[s] = New(id, k, six, "never")] IN IF k = "d" THEN StartPunch(d, s, rn) ELSE d
\* add_path: a held path takes the info (TakeInfo); a held gone path starts over as a new one (fix T6); a new one
\* takes a slot (Fresh); then choose_path when the active path is gone (fix T4)
AddPath(c, id, k, six, rn) ==
    LET f == PO!Find(c.t, id)
        s == PO!Slot(c.t, c.act)
        Mv(d) == IF d.t[d.act].id = 0 \/ d.t[d.act].gone THEN Choose(d) ELSE d
    IN IF f # 0 THEN [c |-> Mv(IF c.t[f].gone THEN Fresh(c, f, id, k, six, rn) ELSE TakeInfo(c, f, k, six)), r |-> "ok"]
       ELSE IF s = 0 THEN [c |-> c, r |-> "toomany"]
       ELSE [c |-> Mv(Fresh(c, s, id, k, six, rn)), r |-> "ok"]

\* rebind_path: the slot keeps all it knows under the new id
Rebind(c, old, new) ==
    LET f == PO!Find(c.t, old)
    IN IF f = 0 THEN [c |-> c, r |-> "unknown"]
       ELSE IF PO!Find(c.t, new) # 0 THEN [c |-> c, r |-> "exists"]
       ELSE [c |-> [c EXCEPT !.t[f].id = new], r |-> "ok"]

\* remove_path
Remove(c, id) ==
    LET f == PO!Find(c.t, id)
    IN IF f = 0 THEN [c |-> c, r |-> "unknown"]
       ELSE IF f = c.act THEN [c |-> c, r |-> "active"]
       ELSE [c |-> [c EXCEPT !.t[f] = None], r |-> "ok"]

\* path_lost: gone and unvalidated, and nothing left armed on it (no probe, re-join or challenge), choose_path,
\* forget_gone
Lost(c, id) ==
    LET f == PO!Find(c.t, id)
    IN IF f = 0 THEN [c |-> c, r |-> "unknown"]
       ELSE [c |-> ForgetGone(Choose([c EXCEPT !.t[f].gone = TRUE, !.t[f].v = FALSE, !.t[f].pr = FALSE,
                                               !.t[f].rj = FALSE, !.t[f].sc = FALSE])), r |-> "ok"]

\* set_active
SetActive(c, id) ==
    LET f == PO!Find(c.t, id)
    IN IF f = 0 THEN [c |-> c, r |-> "unknown"]
       ELSE IF ~c.t[f].v THEN [c |-> c, r |-> "notvalidated"]
       ELSE [c |-> Switch(c, f, "set"), r |-> "ok"]

\* set_path_info (the interface size is not modelled: the test keeps it fixed): only when the info differs; choose_path
\* if the active path is open to a move (OpenToMove, fix T4); then take_info (TakeInfo, fix T7)
SetInfo(c, id, k, six) ==
    LET f == PO!Find(c.t, id)
    IN IF f = 0 \/ (c.t[f].k = k /\ c.t[f].six = six) THEN c
       ELSE LET d == [c EXCEPT !.t[f].k = k, !.t[f].six = six]
                e == IF OpenToMove(d) THEN Choose(d) ELSE d
            IN TakeInfo(e, f, k, six)

\* A packet with a PATH_CHALLENGE on path id (process_payload, on_frame, challenge_back). cb: the node is not declared
\* thin and the session moved application data within 20 s.
Chal(c, id, cb, rn) ==
    LET l == Learn(c, id)
        d == Heard(l.c, l.i)
    IN IF l.i = 0 THEN c
       ELSE IF cb /\ (d.t[d.act].id = 0 \/ d.t[d.act].k = "r") /\ d.t[l.i].k = "d" /\ ~d.t[l.i].v /\ d.t[l.i].ch = 0
            THEN QueueChal(d, l.i, rn) ELSE d

\* A packet with a PATH_RESPONSE answering tok on path id
Resp(c, id, tok, r) == LET l == Learn(c, id) IN IF l.i = 0 THEN c ELSE OnResp(Heard(l.c, l.i), l.i, tok, r)

\* A packet with STREAM or DATAGRAM data (wake: or a WAKE) on path id (process_payload, follow_peer). hi: its number
\* is not below the largest received. fresh: the node is declared thin and the path's challenge was drawn within
\* max(1 s, 2 x the node's round trip).
Data(c, id, hi, wake, fresh, rn) ==
    LET l == Learn(c, id)
        d == Heard(l.c, l.i)
        p == d.t[l.i]
        a == d.t[d.act]
        q == IF p.k = "d" /\ ~p.v /\ ~(fresh /\ p.ch # 0) THEN QueueChal(d, l.i, rn) ELSE d
    IN IF l.i = 0 THEN c
       ELSE IF ~hi \/ l.i = d.act \/ p.gone THEN d                                  \* fix T6: a gone path is not followed
       ELSE IF a.id = 0 \/ a.k = "r" \/ p.k = "d" \/ wake THEN Follow(q, l.i) ELSE q

\* time passes: a heard path goes silent for more than 15 s
Silence(c, x) == [c EXCEPT !.t[x].hd = "stale"]

\* path_returned: only a path held, not gone (fix T6), rejoining and not validated; validated with the given round
\* trip, heard now
Returned(c, id, r) ==
    LET f == PO!Find(c.t, id)
    IN IF f = 0 \/ c.t[f].gone \/ ~c.t[f].rj \/ c.t[f].v THEN [c |-> c, ok |-> FALSE]
       ELSE [c |-> Choose([c EXCEPT !.t[f] = [Clear(@, r) EXCEPT !.hd = "fresh"]]), ok |-> TRUE]

\* probe
Probe(c, id, rn) ==
    LET f == PO!Find(c.t, id)
    IN IF f = 0 THEN [c |-> c, r |-> "unknown"] ELSE [c |-> QueueChal(c, f, rn), r |-> "ok"]

\* punch_known: every direct path, not validated, not gone, with no probe left, is punched, in slot order
PunchDue(p) == p.id # 0 /\ p.k = "d" /\ ~p.v /\ ~p.gone /\ ~p.pr
RECURSIVE PunchFrom(_, _, _)
PunchFrom(c, x, rn) == IF x > NP THEN c ELSE PunchFrom(IF PunchDue(c.t[x]) THEN StartPunch(c, x, rn) ELSE c, x + 1, rn)
PunchKnown(c, rn) == PunchFrom(c, 1, rn)

\* on_path_timers, first half: idle_out for each validated direct path heard once and silent for more than 15 s, in
\* slot order (a thin session with no probe left re-challenges it, rejoining with one probe), the active one falling
\* back to a relayed path; then choose_path if the active path is open to a move (none, gone or relayed: fix T4)
IdleDue(p) == p.id # 0 /\ p.v /\ p.k = "d" /\ p.hd = "stale"
IdleOut(c, x, thin, rn) ==
    LET d == [c EXCEPT !.t[x].v = FALSE]
        e == IF thin /\ ~d.t[x].pr
             THEN LET y == SetChal(d, x, rn) IN [y EXCEPT !.t[x].rj = TRUE, !.t[x].pr = TRUE]
             ELSE d
    IN IF x = e.act THEN Fallback(e) ELSE e
RECURSIVE IdleFrom(_, _, _, _)
IdleFrom(c, x, thin, rn) ==
    IF x > NP THEN c ELSE IdleFrom(IF IdleDue(c.t[x]) THEN IdleOut(c, x, thin, rn) ELSE c, x + 1, thin, rn)
Timers(c, thin, rn) ==
    LET d == IdleFrom(c, 1, thin, rn)
    IN IF OpenToMove(d) THEN Choose(d) ELSE d

\* on_path_timers, second half: fire_probe for each unvalidated path with a probe left that is due (F), in slot order.
\* A thin session's re-join waiting for its floor (W) sends nothing; otherwise the challenge is queued and a probe
\* spent (L: it was the last), a thin direct re-join being re-armed with one.
FireDue(p) == p.id # 0 /\ ~p.v /\ p.pr
Fire(c, x, wait, last, thin) ==
    LET p == c.t[x]
    IN IF p.rj /\ thin /\ wait THEN c
       ELSE [c EXCEPT !.t[x].pr = (~last \/ (p.rj /\ p.k = "d" /\ thin)), !.t[x].sc = (p.ch # 0)]
RECURSIVE FireFrom(_, _, _, _, _, _)
FireFrom(c, x, F, W, L, thin) ==
    IF x > NP THEN c
    ELSE FireFrom(IF x \in F /\ FireDue(c.t[x]) THEN Fire(c, x, x \in W, x \in L, thin) ELSE c, x + 1, F, W, L, thin)

\* fail_over (three probe timeouts in a row or more): only an active direct path; a validated one is no longer
\* validated and a re-join is set up unless one is running (a challenge drawn, not yet queued); validated or not
\* (fix T5), the connection falls back to a relayed path (Fallback)
FailOver(c, rn) ==
    LET p == c.t[c.act]
        d == [c EXCEPT !.t[c.act].v = FALSE]
        e == IF p.rj /\ p.pr THEN d ELSE SetChal([d EXCEPT !.t[c.act].pr = TRUE, !.t[c.act].rj = TRUE], c.act, rn)
    IN IF p.id = 0 \/ p.k # "d" THEN c ELSE Fallback(IF p.v THEN e ELSE c)

\* fill_path in a packet that is sealed: the queued challenge leaves on slot x
Send(c, x) == [c EXCEPT !.t[x].o = @ \cup {c.t[x].ch}, !.t[x].sc = FALSE]

\* ghosts kept across a step from connection a to b: lf, the slot's path was left while gone (it is not the active
\* one, or it was left before and is still the same path)
Mark(a, b) ==
    [b EXCEPT !.t = [x \in 1..NP |-> [b.t[x] EXCEPT !.lf = (b.t[x].id # 0 /\ b.t[x].gone
                                        /\ (x # b.act \/ (a.t[x].lf /\ a.t[x].id = b.t[x].id)))]]]
\* the slots that hold a validated direct path after a step and did not before it
NewDirect(a, b) ==
    {x \in 1..NP : b.t[x].id # 0 /\ b.t[x].k = "d" /\ b.t[x].v /\ ~(a.t[x].id # 0 /\ a.t[x].k = "d" /\ a.t[x].v)}
=============================================================================
