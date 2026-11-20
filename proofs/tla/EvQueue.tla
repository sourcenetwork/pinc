------------------------------- MODULE EvQueue -------------------------------
(***************************************************************************)
(* The connection's event queue, pinc-transport conn/event.rs (EvQueue     *)
(* over Lazy, EvQueueOps.tla), over every sequence of pushes of the events *)
(* in KINDS x KEYS and pops, at a small number of places (QUEUE).          *)
(*                                                                         *)
(* aq and alost are the queue the doc of EvQueue describes, as a sequence: *)
(* a repeat of an event the application learns nothing more from is not   *)
(* queued; when the queue is full a recoverable notification is dropped    *)
(* first (one offered to it, else the oldest one queued); an event that    *)
(* cannot be recovered is counted in `lost` when nothing can give way.     *)
(* owed counts the unrecoverable events accepted (not repeats) and not yet *)
(* popped.                                                                 *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - RingIsQueue: the ring read from its head (with the shifting of       *)
(*    `remove` and the head reset when the last event leaves) is that      *)
(*    queue, and counts the same losses;                                   *)
(*  - QueuedWritten: every queued place was written and holds an event,    *)
(*    so `pop` (through `written_mut`) never comes back empty while events *)
(*    are queued; TypeOK: len <= QUEUE and the written prefix never passes *)
(*    QUEUE (the reserved room of Lazy);                                   *)
(*  - NoRepeat: no two queued events are the same;                         *)
(*  - Accounted: every accepted unrecoverable event is queued, was given   *)
(*    to the application, or is counted in `lost`; nothing else vanishes;  *)
(*  - LostOnlyFull: `lost` grows only when the queue is full and holds no  *)
(*    recoverable event;                                                   *)
(*  - NoLost (EvQueue_fits): with QUEUE equal to the number of distinct    *)
(*    unrecoverable events the callers can raise (the premise of           *)
(*    `queue_fits`), nothing is lost.                                      *)
(* XU is the most undeliverable-extension events (xu, never matched as a   *)
(* repeat) the callers raise while unread: with fix T3 FIXED_EVENTS counts *)
(* one per extension slot and one per frame of the extension send queue (8 *)
(* + 16), which conn/send.rs `hold_queued_extension` raises besides the 8  *)
(* of `shed_extensions`. EvQueue_over gives the callers two such events    *)
(* with a queue that counts both: nothing is lost. Before T3 the queue     *)
(* counted one (QUEUE 3) and TLC found a lost event (the finding).         *)
(* The ASSUME checks the sizes event.rs states for the two builds.         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS QUEUE, KINDS, KEYS, XU, LMAX
ASSUME QUEUE >= 1
VARIABLES q, aq, alost, owed
vars == <<q, aq, alost, owed>>

INSTANCE EvQueueOps

\* event.rs: "sized for a session of 200 stream slots" with `alloc` (640 places), "a session of up to 72 slots" in
\* 256 places without it (77 before fix T3); both with the 4 paths of a connection
ASSUME QueueFits(200, 4, 640) /\ QueueFits(72, 4, 256) /\ ~QueueFits(73, 4, 256)

Events == {<<k, IF k \in KeyedK THEN s ELSE 0, 0>> : k \in KINDS, s \in KEYS}
XuIn(sq) == Cardinality({j \in 1..Len(sq) : sq[j][1] = "xu"})
UnrecIn(sq) == Cardinality({j \in 1..Len(sq) : Unrec(sq[j])})
Repeat(sq, ev) == ev[1] \notin NoFindK /\ \E j \in 1..Len(sq) : SameAs(sq[j], ev)

\* the documented rule on the sequence
FirstLossy(sq) == CHOOSE j \in 1..Len(sq) : Lossy(sq[j]) /\ \A m \in 1..(j - 1) : ~Lossy(sq[m])
Without(sq, j) == SubSeq(sq, 1, j - 1) \o SubSeq(sq, j + 1, Len(sq))
APush(sq, l, ev) ==
    IF Repeat(sq, ev) THEN [s |-> sq, l |-> l]
    ELSE IF Len(sq) < QUEUE THEN [s |-> Append(sq, ev), l |-> l]
    ELSE IF Lossy(ev) THEN [s |-> sq, l |-> l]
    ELSE IF \E j \in 1..Len(sq) : Lossy(sq[j]) THEN [s |-> Append(Without(sq, FirstLossy(sq)), ev), l |-> l]
    ELSE [s |-> sq, l |-> l + 1]

Init == q = Q0 /\ aq = <<>> /\ alost = 0 /\ owed = 0

PushStep == \E ev \in Events :
    /\ (ev[1] = "xu" => XuIn(aq) < XU)
    /\ q' = Push(q, QUEUE, ev)
    /\ LET a == APush(aq, alost, ev) IN aq' = a.s /\ alost' = a.l
    /\ owed' = owed + (IF Unrec(ev) /\ ~Repeat(aq, ev) THEN 1 ELSE 0)
PopStep == LET p == Pop(q, QUEUE)
           IN /\ q' = p.q
              /\ aq' = IF aq = <<>> THEN aq ELSE Tail(aq)
              /\ alost' = alost
              /\ owed' = owed - (IF Unrec(p.out) THEN 1 ELSE 0)
Next == PushStep \/ PopStep
Spec == Init /\ [][Next]_vars

Bound == q.lost <= LMAX

TypeOK == /\ q.len \in 0..QUEUE /\ q.head \in 0..(QUEUE - 1) /\ Len(q.w) <= QUEUE
          /\ q.lost \in Nat
RingIsQueue == Window(q, QUEUE) = aq /\ q.lost = alost
QueuedWritten == \A j \in 0..(q.len - 1) : Slot(q, QUEUE, j) < Len(q.w) /\ Get(q, QUEUE, j) # None
NoRepeat == \A j, m \in 1..Len(aq) : (j # m /\ aq[j][1] \notin NoFindK) => ~SameAs(aq[j], aq[m])
Accounted == owed = UnrecIn(aq) + q.lost
LostOnlyFull == [][q'.lost > q.lost =>
                     (q.len = QUEUE /\ \A j \in 0..(q.len - 1) : ~Lossy(Get(q, QUEUE, j)))]_vars
NoLost == q.lost = 0
=============================================================================
