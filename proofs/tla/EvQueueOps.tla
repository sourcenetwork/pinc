----------------------------- MODULE EvQueueOps -----------------------------
(***************************************************************************)
(* The operations of pinc-transport conn/event.rs (EvQueue: `push`,        *)
(* `pop`, `find`, `remove`), step for step, on the lazy table of           *)
(* LazyOps.tla that holds its places (`Lazy<Option<Ev>, QUEUE>`, blank     *)
(* None). EvQueue.tla checks them over every interleaving at small sizes;  *)
(* TraceEvQueue.tla replays the recorded calls of the real code at its     *)
(* size (640 places with `alloc`).                                         *)
(*                                                                         *)
(* The state q is the queue as the code has it: w (the written prefix of   *)
(* the places), head, len and lost. An event is <<kind, key, payload>>:    *)
(* the kind of `Ev`, the stream or path it names (0 for a kind that names  *)
(* none) and what else it carries (an error code, a length, the resumed    *)
(* flag), which `same_as` does not look at. None is <<>>.                  *)
(*   rd Readable, wr Writable, or OpenReady, dg Datagram, ex Extension:    *)
(*      the notifications the application recovers by polling (`lossy`);  *)
(*   op Opened, rs Reset, st Stopped (by stream), pv PathValidated, pf     *)
(*      PathFailed (by path), kr KeyRequest, cn Connected, tk Tickets, ry  *)
(*      Ready, as PeerAsleep, aw PeerAwake, wu WakeUnanswered, cl Closed,  *)
(*      xu ExtensionUndeliverable: the ones it cannot recover.             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
INSTANCE LazyOps

None == <<>>
LossyK == {"rd", "wr", "or", "dg", "ex"}
\* the kinds `push` queues without looking for a repeat
NoFindK == {"dg", "ex", "xu"}
\* `same_as`: the same kind and the same stream or path, or the same kind for the kinds that name none;
\* never for dg, ex and xu
KeyedK == {"op", "rs", "st", "rd", "wr", "pv", "pf"}
SingleK == {"kr", "cn", "or", "as", "aw", "wu", "tk", "ry", "cl"}
Lossy(e) == e # None /\ e[1] \in LossyK
Unrec(e) == e # None /\ ~Lossy(e)
SameAs(e, f) == e[1] = f[1] /\ ((e[1] \in KeyedK /\ e[2] = f[2]) \/ e[1] \in SingleK)

Q0 == [w |-> LNew, head |-> 0, len |-> 0, lost |-> 0]
Slot(q, cap, i) == (q.head + i) % cap
\* `items.get(slot(i)).copied().flatten()`
Get(q, cap, i) == LGet(q.w, cap, None, Slot(q, cap, i)).v
\* the queued events, oldest first
Window(q, cap) == [j \in 1..q.len |-> Get(q, cap, j - 1)]

\* `find`: whether a queued event is the same as ev
Find(q, cap, ev) == \E j \in 0..(q.len - 1) : Get(q, cap, j) # None /\ SameAs(Get(q, cap, j), ev)

\* the place, counting from the oldest, of the oldest event the application can recover, or -1
RECURSIVE VictimFrom(_, _, _)
VictimFrom(q, cap, i) == IF i >= q.len THEN -1 ELSE IF Lossy(Get(q, cap, i)) THEN i ELSE VictimFrom(q, cap, i + 1)

\* the loop of `remove`: for k in (0..i).rev() { place k+1 <- place k }, through `get` and `get_mut`
RECURSIVE MoveUp(_, _, _, _)
MoveUp(w, head, cap, k) ==
    IF k < 0 THEN w
    ELSE MoveUp(LSetMut(w, cap, None, (head + k + 1) % cap, LGet(w, cap, None, (head + k) % cap).v).w,
                head, cap, k - 1)
Remove(q, cap, i) ==
    [q EXCEPT !.w = MoveUp(q.w, q.head, cap, i - 1),
              !.head = IF q.len = 1 THEN 0 ELSE (q.head + 1) % cap,
              !.len = q.len - 1]

\* the tail of `push`: the event into place slot(len) through `get_mut`
Put(q, cap, ev) ==
    LET r == LSetMut(q.w, cap, None, Slot(q, cap, q.len), ev)
    IN IF r.ok THEN [q EXCEPT !.w = r.w, !.len = q.len + 1] ELSE q

\* `push`: a repeat is not queued; a full queue drops a recoverable event offered to it, else gives up its oldest
\* recoverable event, else counts the event lost
Push(q, cap, ev) ==
    IF ev[1] \notin NoFindK /\ Find(q, cap, ev) THEN q
    ELSE IF q.len = cap
         THEN IF Lossy(ev) THEN q
              ELSE LET v == VictimFrom(q, cap, 0)
                   IN IF v < 0 THEN [q EXCEPT !.lost = q.lost + 1]
                      ELSE Put(Remove(q, cap, v), cap, ev)
         ELSE Put(q, cap, ev)

\* `pop`: the event at the head, taken out of its written place
Pop(q, cap) ==
    IF q.len = 0 THEN [out |-> None, q |-> q]
    ELSE LET t == LTake(q.w, q.head, None)
         IN [out |-> t.v,
             q |-> [q EXCEPT !.w = t.w, !.head = IF q.len = 1 THEN 0 ELSE (q.head + 1) % cap,
                             !.len = q.len - 1]]

\* `queue_fits(streams, paths)` with FIXED_EVENTS = 8 + EXT_SLOTS + EXT_QUEUED = 32 (fix T3; 16 before it)
QueueFits(s, p, cap) == 3 * s + 2 * p + 32 <= cap
=============================================================================
