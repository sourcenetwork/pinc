------------------------- MODULE NodeEventQueueOps -------------------------
(***************************************************************************)
(* The node's bounded queue of application events, pinc-node io.rs         *)
(* `EventQueue` (with the rule of event.rs), step for step: `push` (Push), *)
(* `pop` (Pop), `can_take` (CanTake), `resumable` (Resumable), `is_empty`  *)
(* (IsEmpty). An event is [id |-> n, lossy |-> b]: lossy is `lossy` of     *)
(* io.rs, an endpoint event the application can recover by reading state  *)
(* (StreamReadable, StreamWritable, OpenReady); id only names the event.   *)
(* CAP, HIGH and LOW are EVENT_CAP, EVENT_HIGH and EVENT_LOW; the count of *)
(* lost events saturates at LMAX (u32::MAX in the code).                   *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS CAP, HIGH, LOW, LMAX

Q0 == [q |-> <<>>, lost |-> 0, held |-> FALSE]

\* the index of the first recoverable event from k on, 0 when there is none
RECURSIVE FirstLossy(_, _)
FirstLossy(q, k) == IF k > Len(q) THEN 0 ELSE IF q[k].lossy THEN k ELSE FirstLossy(q, k + 1)

\* q.iter().position(lossy).unwrap_or(0), as an index from 1
Victim(q) == LET k == FirstLossy(q, 1) IN IF k = 0 THEN 1 ELSE k

RemoveAt(q, k) == SubSeq(q, 1, k - 1) \o SubSeq(q, k + 1, Len(q))

SatLost(n) == IF n < LMAX THEN n + 1 ELSE LMAX

\* push: a full queue counts a loss, drops a new recoverable event, else drops the oldest recoverable one (the
\* oldest event when none is) and appends
Push(s, e) ==
    IF Len(s.q) >= CAP
    THEN IF e.lossy THEN [s EXCEPT !.lost = SatLost(@)]
         ELSE [s EXCEPT !.lost = SatLost(@), !.q = Append(RemoveAt(@, Victim(@)), e)]
    ELSE [s EXCEPT !.q = Append(@, e)]

NoEv == [id |-> 0, lossy |-> FALSE]

\* pop: the count of lost events first (and reset), else the oldest event; ev.k is "lost", "event" or "none"
Pop(s) ==
    IF s.lost > 0 THEN [s |-> [s EXCEPT !.lost = 0], ev |-> [k |-> "lost", count |-> s.lost, e |-> NoEv]]
    ELSE IF s.q = <<>> THEN [s |-> s, ev |-> [k |-> "none", count |-> 0, e |-> NoEv]]
    ELSE [s |-> [s EXCEPT !.q = Tail(@)], ev |-> [k |-> "event", count |-> 0, e |-> Head(s.q)]]

\* can_take: stop at HIGH queued events, resume at LOW
CanTake(s) ==
    LET h == IF s.held THEN Len(s.q) > LOW ELSE Len(s.q) >= HIGH
    IN [s |-> [s EXCEPT !.held = h], ok |-> ~h]

Resumable(s) == s.held /\ Len(s.q) <= LOW

IsEmpty(s) == s.q = <<>> /\ s.lost = 0
=============================================================================
