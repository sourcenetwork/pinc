---------------------------- MODULE NodeEventQueue ----------------------------
(***************************************************************************)
(* The node's bounded queue of application events: pinc-node io.rs         *)
(* `EventQueue` and the rule of event.rs, with the operators of            *)
(* NodeEventQueueOps.tla.                                                  *)
(*                                                                         *)
(* Three kinds of step, in any order:                                      *)
(*  - PushA: a layer emits an event (`push`, unconditionally, as the       *)
(*    layers do);                                                          *)
(*  - TakeA: the node loop asks `can_take` and, when it may, takes an      *)
(*    endpoint event if the endpoint has one (events.rs; through `extend`, *)
(*    which is `push`);                                                    *)
(*  - PopA: the host reads an event (`pop`, node.rs `poll_event`).         *)
(* Every event gets the next id, so an id is its arrival order; at most    *)
(* PUSHES events arrive.                                                   *)
(*                                                                         *)
(* The history variables restate the documented rules independently:      *)
(* drops counts the events dropped since the last Lost was delivered       *)
(* (capped one above LMAX), stopped whether the node's last check said     *)
(* stop, layered whether a layer pushed, keptDrop whether an event the     *)
(* application cannot recover was dropped. A step whose result breaks a   *)
(* rule adds the rule's name to bad, and an invariant per rule says bad    *)
(* never holds it.                                                         *)
(*                                                                         *)
(* Checked (the documentation of io.rs and event.rs):                      *)
(*  - Bounded: the queue never holds more than CAP events;                 *)
(*  - Ordered: one ordered queue (events stay in arrival order);           *)
(*  - DropRule: below CAP nothing is dropped; at CAP exactly one event of  *)
(*    the queued ones and the new one is dropped, the rest keep their      *)
(*    order, and the dropped one is recoverable unless none is;            *)
(*  - LostCount: every drop is counted (saturating at LMAX) until the      *)
(*    count is delivered;                                                  *)
(*  - PopRight: the count is delivered as Lost before the next event, then *)
(*    reset; otherwise the oldest event is delivered and removed;          *)
(*  - EmptyRight: `is_empty` exactly when a read would deliver nothing;    *)
(*  - TakeRight, ResumeRight: no endpoint event from HIGH queued events    *)
(*    until the queue is back to LOW;                                      *)
(*  - RoomForEndpoint: endpoint events alone never fill the queue (the     *)
(*    node takes them only while it has room), so nothing is dropped.      *)
(* Witnesses: NodeEventQueue_w_kept (an event the application cannot      *)
(* recover is dropped when nothing recoverable is queued),                 *)
(* NodeEventQueue_w_sat (the count of lost events saturates),              *)
(* NodeEventQueue_w_stop (the node stops taking endpoint events).          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS CAP, HIGH, LOW, LMAX, PUSHES
VARIABLES s, next, drops, stopped, layered, keptDrop, bad
vars == <<s, next, drops, stopped, layered, keptDrop, bad>>

INSTANCE NodeEventQueueOps

IMin(a, b) == IF a < b THEN a ELSE b

\* the drop rule stated on the result t of pushing e on s0: the names of the rules t breaks
PushExp(s0, e, t) ==
    LET all == Append(s0.q, e)
        removedOK(k) == t.q = RemoveAt(all, k) /\ (all[k].lossy \/ \A j \in 1..Len(all) : ~all[j].lossy)
    IN IF Len(s0.q) >= CAP
       THEN IF \E k \in 1..Len(all) : removedOK(k) THEN {} ELSE {"drop"}
       ELSE IF t.q = all THEN {} ELSE {"drop"}

\* push e (or nothing, for NoEv) on s1, with the history and the rules broken (extra, and the drop rule)
Step(s1, e, extra) ==
    LET pushed == e # NoEv
        full == pushed /\ Len(s1.q) >= CAP
        t == IF pushed THEN Push(s1, e) ELSE s1
    IN /\ s' = t
       /\ next' = IF pushed THEN next + 1 ELSE next
       /\ drops' = IF full THEN IMin(drops + 1, LMAX + 1) ELSE drops
       /\ keptDrop' = (keptDrop \/ (full /\ ~e.lossy /\ FirstLossy(s1.q, 1) = 0))
       /\ bad' = bad \cup extra \cup (IF pushed THEN PushExp(s1, e, t) ELSE {})

PushA(l) == /\ next < PUSHES
            /\ Step(s, [id |-> next + 1, lossy |-> l], {})
            /\ layered' = TRUE
            /\ UNCHANGED stopped

TakeA(has, l) ==
    LET c == CanTake(s)
        want == ~(Len(s.q) >= HIGH \/ (stopped /\ Len(s.q) > LOW))
    IN /\ has => next < PUSHES
       /\ Step(c.s, IF c.ok /\ has THEN [id |-> next + 1, lossy |-> l] ELSE NoEv,
               IF c.ok = want THEN {} ELSE {"take"})
       /\ stopped' = ~c.ok
       /\ UNCHANGED layered

PopA ==
    LET r == Pop(s)
        want == IF drops > 0 THEN r.ev.k = "lost" /\ r.ev.count = IMin(drops, LMAX) /\ r.s.q = s.q
                ELSE IF s.q = <<>> THEN r.ev.k = "none" /\ r.s.q = s.q
                ELSE /\ r.ev.k = "event" /\ r.ev.e = s.q[1]
                     /\ Len(r.s.q) = Len(s.q) - 1
                     /\ \A j \in 1..Len(r.s.q) : r.s.q[j] = s.q[j + 1]
    IN /\ s' = r.s
       /\ drops' = 0
       /\ bad' = bad \cup (IF want THEN {} ELSE {"pop"}) \cup (IF IsEmpty(s) = (r.ev.k = "none") THEN {} ELSE {"empty"})
       /\ UNCHANGED <<next, stopped, layered, keptDrop>>

Init == /\ s = Q0 /\ next = 0 /\ drops = 0 /\ stopped = FALSE
        /\ layered = FALSE /\ keptDrop = FALSE /\ bad = {}

Next == \/ \E l \in BOOLEAN : PushA(l) \/ TakeA(TRUE, l)
        \/ TakeA(FALSE, FALSE)
        \/ PopA

Spec == Init /\ [][Next]_vars

Bounded == Len(s.q) <= CAP
Ordered == \A j \in 1..(Len(s.q) - 1) : s.q[j].id < s.q[j + 1].id
LostCount == s.lost = IMin(drops, LMAX)
DropRule == "drop" \notin bad
PopRight == "pop" \notin bad
EmptyRight == "empty" \notin bad
TakeRight == "take" \notin bad
ResumeRight == Resumable(s) = (stopped /\ Len(s.q) <= LOW)
RoomForEndpoint == ~layered => Len(s.q) <= HIGH /\ drops = 0

\* reachability witnesses
NoKeptDrop == ~keptDrop
\* more events were dropped than the count can say: the count saturated
NoLostSat == drops <= LMAX
NoStop == ~s.held
=============================================================================
