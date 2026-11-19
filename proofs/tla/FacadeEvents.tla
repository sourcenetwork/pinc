------------------------------ MODULE FacadeEvents ------------------------------
(***************************************************************************)
(* The bounded buffer of topic events the facade keeps for the host:       *)
(* crates/pinc/src/engine/topics.rs (`EVENTS` = 1024, `push_event`,        *)
(* `poll_event`, `on_node_event` for `NodeEvent::Lost`), with the          *)
(* operators of FacadeEventsOps.tla. Events are numbered in the order they *)
(* are pushed; the node may also report events it dropped itself (counts   *)
(* in NODELOST); the host polls; the endpoint stops.                       *)
(*                                                                         *)
(* owed is the true number of drops not yet reported (the queue's and the  *)
(* node's, unsaturated); dropped the queue's drops so far; outN and        *)
(* lastOut the events delivered and the last one.                          *)
(*                                                                         *)
(* Checked, from the docs of event.rs (lines 3-4: "When it is full the     *)
(* newest is dropped and counted, and the count comes out as Event::Lost   *)
(* before the next event, so a gap never reads as silence"), topics.rs     *)
(* (line 7: "the event queue holds at most EVENTS events and counts what   *)
(* it drops") and `poll_event` ("None once the endpoint stopped and the    *)
(* queue is empty, else a wait"):                                          *)
(*  - Bounded: at most CAP events queued;                                  *)
(*  - InOrder: events come out in the order pushed, each once;             *)
(*  - Conserved: every event pushed is delivered, queued or dropped;       *)
(*  - CountExact: the count reported is the number of drops (below the     *)
(*    saturation of the u32);                                              *)
(*  - NewestDropped: a push to a full queue leaves the queue as it was;    *)
(*  - GapFirst: while drops are owed, no event is delivered (the count     *)
(*    comes first);                                                        *)
(*  - EndOnlyStopped: a poll ends (None) only when stopped, empty and with *)
(*    no count, and waits only when not stopped, empty and with no count.  *)
(* Witnesses: FacadeEvents_full (NeverDropped fails: the queue fills and   *)
(* drops), FacadeEvents_sat (TOP = 1: CountExact fails, the u32 count      *)
(* saturates; in the code after 2^32 - 1 drops between two polls).         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS CAP, TOP, MAXSTEPS, NODELOST
ASSUME CAP \in Nat \ {0} /\ TOP \in 1..65535 /\ MAXSTEPS \in Nat /\ NODELOST \subseteq 1..65535

O == INSTANCE FacadeEventsOps WITH TOPW <- <<TOP, 0, 0, 0, 0>>
Wd(k) == <<k, 0, 0, 0, 0>>

VARIABLES s, owed, nid, dropped, outN, lastOut, steps
vars == <<s, owed, nid, dropped, outN, lastOut, steps>>

Init == /\ s = O!Empty /\ owed = 0 /\ nid = 1 /\ dropped = 0 /\ outN = 0 /\ lastOut = 0 /\ steps = 0

\* a topic event for the host (push_event of any kind)
Push == /\ s' = O!Enq(s, nid)
        /\ nid' = nid + 1
        /\ dropped' = dropped + (IF O!Full(s) THEN 1 ELSE 0)
        /\ owed' = owed + (IF O!Full(s) THEN 1 ELSE 0)
        /\ UNCHANGED <<outN, lastOut>>
\* the node reports c events it dropped
NodeLostA == \E c \in NODELOST :
        /\ s' = O!NodeLost(s, Wd(c)) /\ owed' = owed + c
        /\ UNCHANGED <<nid, dropped, outN, lastOut>>
\* the host polls
Poll == LET p == O!PollOf(s)
        IN /\ s' = p.s
           /\ owed' = IF p.r = "lost" THEN 0 ELSE owed
           /\ outN' = outN + (IF p.r = "event" THEN 1 ELSE 0)
           /\ lastOut' = IF p.r = "event" THEN p.e ELSE lastOut
           /\ UNCHANGED <<nid, dropped>>
StopA == ~s.stopped /\ s' = O!Stop(s) /\ UNCHANGED <<owed, nid, dropped, outN, lastOut>>

Next == steps < MAXSTEPS /\ steps' = steps + 1 /\ (Push \/ NodeLostA \/ Poll \/ StopA)
Spec == Init /\ [][Next]_vars

Bounded == Len(s.q) <= CAP
InOrder == \A k \in 1..Len(s.q) : s.q[k] > lastOut /\ (k > 1 => s.q[k] > s.q[k - 1])
Conserved == nid - 1 = outN + Len(s.q) + dropped
CountExact == O!Val(s.lost) = owed
NewestDropped == [][nid' = nid + 1 /\ O!Full(s) => s'.q = s.q]_vars
GapFirst == [][owed > 0 => outN' = outN]_vars
EndOnlyStopped == LET r == O!PollOf(s).r
                  IN /\ r = "none" => (s.stopped /\ s.q = <<>> /\ s.lost = O!Zero)
                     /\ r = "wait" => (~s.stopped /\ s.q = <<>> /\ s.lost = O!Zero)

\* witnesses
NeverDropped == dropped = 0
=============================================================================
