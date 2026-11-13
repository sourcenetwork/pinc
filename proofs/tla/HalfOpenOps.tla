---------------------------- MODULE HalfOpenOps -----------------------------
(***************************************************************************)
(* The half-open bookkeeping of the vinc-core endpoint, step for step: the *)
(* admission of a first flight (rx.rs unrouted, accept), the end of the    *)
(* unauthenticated phase (events.rs on_established), the release of a slot *)
(* (endpoint.rs free_slot), the deadline a session holds (timers.rs settle) *)
(* and the timer loop (timers.rs handle_timeout, run_timer). HalfOpen.tla  *)
(* checks them over every interleaving at small sizes; TraceHalfOpen.tla   *)
(* replays the recorded calls of the real endpoint.                        *)
(*                                                                         *)
(* The state e: slots (a function from the slot numbers, each Free or a    *)
(* session [created, unauth, counted, dl]: when it was made, whether its   *)
(* peer is still unauthenticated, whether it counts against the cap, and   *)
(* the deadline it holds in the heap, NoDl for none) and count, the        *)
(* endpoint's counter of counted sessions. A message type is its first     *)
(* byte: 1 a full Initial, 2 a short Initial, 6 a resumption Hello.        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

NoDl == -1
Free == [use |-> FALSE, created |-> 0, unauth |-> FALSE, counted |-> FALSE, dl |-> NoDl]
Table0(k) == [j \in 0..(k - 1) |-> Free]
Min2(a, b) == IF a <= b THEN a ELSE b
MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y

\* unrouted: the size floor of each first message type; any other type starts nothing
First(kind) == kind \in {1, 2, 6}
Floor(kind, full, short) == CASE kind = 1 -> full [] kind = 2 -> short [] OTHER -> 0
\* admitted: the datagram meets the floor, and fewer than max sessions are counted unless the Hello's ticket opens
\* (resume: the Hello is whole in its first packet, names a registered protocol and an unused ticket that opens)
Admit(count, kind, len, resume, max, full, short) ==
    len >= Floor(kind, full, short) /\ (resume \/ count < max)

\* accept: the slot becomes an unauthenticated session made now, counted unless it resumes
Make(e, j, now, resume) ==
    [slots |-> [e.slots EXCEPT ![j] = [use |-> TRUE, created |-> now, unauth |-> TRUE,
                                       counted |-> ~resume, dl |-> NoDl]],
     count |-> IF resume THEN e.count ELSE e.count + 1]
\* a dial of this node (commands.rs connect): a session that is neither unauthenticated nor counted
Dial(e, j, now) ==
    [e EXCEPT !.slots[j] = [use |-> TRUE, created |-> now, unauth |-> FALSE, counted |-> FALSE, dl |-> NoDl]]
\* on_established: the peer is authenticated; a counted session leaves the count
Establish(e, j) ==
    [slots |-> [e.slots EXCEPT ![j].unauth = FALSE, ![j].counted = FALSE],
     count |-> IF e.slots[j].counted THEN e.count - 1 ELSE e.count]
\* free_slot: the slot is free again; a counted session leaves the count (saturating in the code, never below 0 here)
Release(e, j) ==
    [slots |-> [e.slots EXCEPT ![j] = Free],
     count |-> IF e.slots[j].counted THEN e.count - 1 ELSE e.count]

\* the end of an unauthenticated session's life, and run_timer's test for it
End(s, life) == s.created + life
Expired(s, now, life) == s.use /\ s.unauth /\ now >= End(s, life)
\* settle: the session's deadline is the earliest of its own d and, while it is unauthenticated, the end of its life
Settle(e, j, d, life) ==
    [e EXCEPT !.slots[j].dl = IF e.slots[j].unauth THEN Min2(d, End(e.slots[j], life)) ELSE d]
\* poll_timeout: the earliest deadline in the heap, none while the event queue is stalled
Dls(sl) == {sl[j].dl : j \in {x \in DOMAIN sl : sl[x].dl # NoDl}}
Poll(sl, stalled) == IF stalled \/ Dls(sl) = {} THEN NoDl ELSE MinOf(Dls(sl))
CountOf(sl) == Cardinality({j \in DOMAIN sl : sl[j].counted})

\* handle_timeout: pop the earliest due deadline (the lower slot on a tie), at most k times, stopping when the event
\* queue stalls (after cut pops); run_timer frees an expired session (expiry at now >= End, or past it when strict),
\* else the connection's own timer runs: d is its next deadline, Gone when the connection ended (settle frees it); a
\* deadline not after now is moved to now + 1
Gone == -2
Due(sl, now) == {j \in DOMAIN sl : sl[j].dl # NoDl /\ sl[j].dl <= now}
Pop(sl, now) == CHOOSE j \in Due(sl, now) :
                    \A x \in Due(sl, now) : sl[j].dl < sl[x].dl \/ (sl[j].dl = sl[x].dl /\ j <= x)
ExpiredAt(s, now, life, strict) == IF strict THEN s.use /\ s.unauth /\ now > End(s, life) ELSE Expired(s, now, life)
RunTimer(e, j, now, d, life, strict) ==
    IF ExpiredAt(e.slots[j], now, life, strict) \/ d = Gone THEN Release(e, j)
    ELSE LET e1 == Settle(e, j, d, life)
         IN IF e1.slots[j].dl <= now THEN [e1 EXCEPT !.slots[j].dl = now + 1] ELSE e1
RECURSIVE Loop(_, _, _, _, _, _, _)
Loop(e, now, ds, life, strict, fuel, cut) ==
    IF fuel = 0 \/ cut = 0 \/ Due(e.slots, now) = {} THEN e
    ELSE LET j == Pop(e.slots, now)
         IN Loop(RunTimer([e EXCEPT !.slots[j].dl = NoDl], j, now, ds[j], life, strict),
                 now, ds, life, strict, fuel - 1, cut - 1)
=============================================================================
