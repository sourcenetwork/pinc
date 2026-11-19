------------------------------ MODULE HeldOps -------------------------------
(***************************************************************************)
(* The operations of pinc-core slot.rs (Held), step for step: the          *)
(* application events of a session that wait for its access check. The     *)
(* ring, its cells, head and length, and the loop that closes the gap an   *)
(* eviction leaves are those of QueueOps.tla (the event queue's ring), and *)
(* so are Put, Evict and Pop; the two differences are here: a recoverable  *)
(* event that repeats one held (the same kind and stream) merges into it,  *)
(* and a full ring with nothing recoverable in it refuses the new event    *)
(* and counts it, where the event queue gives up its oldest.               *)
(*                                                                         *)
(* An event is <<id, lossy, <<kind, stream>>, error>>: its place in the    *)
(* order of pushes (0 where a trace does not know it), whether the         *)
(* application can recover it (the kinds readable, writable and open       *)
(* ready, 1, 2 and 6), its kind and stream, and its error code. The code's *)
(* kinds are OPENED 0, READABLE 1, WRITABLE 2, RESET 3, DATAGRAM 4,        *)
(* STOPPED 5, OPEN_READY 6. The field ll of the ring is a ghost here: the  *)
(* code scans for recoverable events instead.                              *)
(***************************************************************************)
EXTENDS QueueOps

Ev(id, kind, stream, error) == <<id, kind \in {1, 2, 6}, <<kind, stream>>, error>>

\* a recoverable event that repeats a held one (the same kind and stream) is not held again
HMerges(r, cap, ev) == ev[2] /\ \E i \in 0..r.len - 1 : Get(r, cap, i)[3] = ev[3]

\* the ring holds nothing it may drop and has no room
HStalled(r, cap) == r.len = cap /\ Victim(r, cap) < 0

\* push: a repeat merges; a full ring gives up its oldest recoverable event, or, holding none, refuses the new
\* event; both count a drop. evictHead is the wrong rule of a witness config: a full ring with nothing recoverable
\* gives up its oldest event, as the event queue does.
HPush(r, cap, ev, evictHead) ==
    IF HMerges(r, cap, ev) THEN r
    ELSE IF r.len = cap
         THEN IF Victim(r, cap) < 0 /\ ~evictHead
              THEN [r EXCEPT !.dropped = @ + 1]
              ELSE Put(Evict([r EXCEPT !.dropped = @ + 1], cap, FALSE), cap, ev)
         ELSE Put(r, cap, ev)
=============================================================================
