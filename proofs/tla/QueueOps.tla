------------------------------ MODULE QueueOps ------------------------------
(***************************************************************************)
(* The operations of vinc-core queue.rs (EventRing), step for step: the    *)
(* bounded ring of events waiting for the host. Queue.tla checks them over *)
(* every interleaving at small sizes; TraceQueue.tla replays the recorded  *)
(* calls of the real code.                                                 *)
(*                                                                         *)
(* The state r is the ring as the code has it: cells (a function from the  *)
(* places 0..cap-1 to an event or None), head (the place of the oldest     *)
(* event), len (how many are queued), ll (how many of them the application *)
(* can recover by reading state), and the counters dropped and lost. An    *)
(* event is <<id, lossy, sess, closed>>: its place in the order of pushes, *)
(* whether the application can recover it, the session it names (0 for     *)
(* none) and whether it is that session's Closed. The code's split of the  *)
(* places into a base and four rows of K is an addressing of 0..cap-1 (the *)
(* Lean theorem place_inj), so the model has one array.                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

None == <<>>
Ring0(cap) == [cells |-> [p \in 0..cap-1 |-> None], head |-> 0, len |-> 0,
               ll |-> 0, dropped |-> 0, lost |-> 0]

At(r, cap, i) == (r.head + i) % cap
Get(r, cap, i) == r.cells[At(r, cap, i)]
Lossy(e) == e # None /\ e[2]

\* the queued events, oldest first
Window(r, cap) == [i \in 1..r.len |-> Get(r, cap, i - 1)]

\* the place, counting from the oldest, of the oldest recoverable event, or -1: the code's `find` from i
RECURSIVE VictimFrom(_, _, _)
VictimFrom(r, cap, i) ==
    IF i >= r.len THEN -1 ELSE IF Lossy(Get(r, cap, i)) THEN i ELSE VictimFrom(r, cap, i + 1)
Victim(r, cap) == VictimFrom(r, cap, 0)

\* the eviction loop of the code: for i in (0..v).rev() { place i+1 <- place i }
RECURSIVE ShiftLoop(_, _, _, _)
ShiftLoop(c, head, cap, k) ==
    IF k = 0 THEN c
    ELSE ShiftLoop([c EXCEPT ![(head + k) % cap] = c[(head + k - 1) % cap]], head, cap, k - 1)

\* what that loop leaves, place by place (Queue.tla's ShiftRight checks it equals the loop, at every victim of every
\* reachable ring; the Lean theorem shift_spec proves it for any size): the places 1..v counting from the head
\* take the event of the place before, the others keep theirs
Shift(c, head, cap, v) ==
    [p \in DOMAIN c |->
        IF (p - head + cap) % cap \in 1..v THEN c[(p - 1 + cap) % cap] ELSE c[p]]

Put(r, cap, ev) ==
    [r EXCEPT !.cells[(r.head + r.len) % cap] = ev, !.len = @ + 1,
              !.ll = @ + IF ev[2] THEN 1 ELSE 0]

\* a full queue gives up one event: the oldest recoverable one, else (counted as lost) the oldest.
\* headFirst is the wrong rule of a witness config: always the oldest.
Evict(r, cap, headFirst) ==
    LET v0 == IF headFirst THEN -1 ELSE Victim(r, cap)
        v == IF v0 < 0 THEN 0 ELSE v0
    IN [r EXCEPT !.cells = Shift(r.cells, r.head, cap, v), !.head = (r.head + 1) % cap,
                 !.len = @ - 1,
                 !.ll = IF Lossy(Get(r, cap, v)) THEN @ - 1 ELSE @,
                 !.lost = IF v0 < 0 THEN @ + 1 ELSE @]

\* push: a full queue counts a drop; it drops the new event if that is recoverable, else gives up one queued
Push(r, cap, ev, headFirst) ==
    IF r.len = cap
    THEN LET r1 == [r EXCEPT !.dropped = @ + 1]
         IN IF ev[2] THEN r1 ELSE Put(Evict(r1, cap, headFirst), cap, ev)
    ELSE Put(r, cap, ev)

Pop(r, cap) ==
    IF r.len = 0 THEN [out |-> None, r |-> r]
    ELSE LET e == r.cells[r.head]
         IN [out |-> e,
             r |-> [r EXCEPT !.cells[r.head] = None, !.head = (r.head + 1) % cap, !.len = @ - 1,
                             !.ll = IF Lossy(e) THEN @ - 1 ELSE @]]

\* the compaction loop of purge: event i is taken out of its place and, if it stays, written at place kept
RECURSIVE PurgeGo(_, _, _, _, _, _, _, _)
PurgeGo(c, head, cap, s, n, i, kept, ll) ==
    IF n = 0 THEN [c |-> c, kept |-> kept, ll |-> ll]
    ELSE LET from == (head + i) % cap
             to == (head + kept) % cap
             ev == c[from]
         IN IF ev = None THEN PurgeGo(c, head, cap, s, n - 1, i + 1, kept, ll)
            ELSE LET c1 == [c EXCEPT ![from] = None]
                 IN IF ev[3] = s /\ ~ev[4]
                    THEN PurgeGo(c1, head, cap, s, n - 1, i + 1, kept, IF ev[2] THEN ll - 1 ELSE ll)
                    ELSE PurgeGo([c1 EXCEPT ![to] = ev], head, cap, s, n - 1, i + 1, kept + 1, ll)

\* purge: the queued events that name the session, but its Closed, are dropped; the others keep their order
Purge(r, cap, s) ==
    LET x == PurgeGo(r.cells, r.head, cap, s, r.len, 0, 0, r.ll)
    IN [r EXCEPT !.cells = x.c, !.len = x.kept, !.ll = x.ll]

\* stalled: the unrecoverable events queued leave less than the headroom h
Stalled(r, cap, h) == r.len - r.ll + h > cap
=============================================================================
