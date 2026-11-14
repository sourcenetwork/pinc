----------------------------- MODULE StandbyOps -----------------------------
(***************************************************************************)
(* The operations of crates/vinc/src/standby.rs (Standby), step for step:  *)
(* the slab of tickets of the facade futures that wait, and the queue of   *)
(* those waiting for the driving role. FacadeStandby.tla checks them over  *)
(* every sequence of calls, stale and forged tickets included;             *)
(* FacadeTurn.tla runs them inside the drive's turn; TraceFacadeStandby.tla *)
(* replays the recorded calls of the real code.                            *)
(*                                                                         *)
(* The state s: slots (the code's Vec; the slot of index i, counted from 0 *)
(* as the code does, is slots[i + 1]), each [gen, waker, queued, live]     *)
(* with waker 0 for none and the number of a waker otherwise; free (the    *)
(* code's Vec used as a stack: push appends, pop takes the last); queue    *)
(* (the VecDeque of tickets, front first). A ticket is <<idx, gen>>. gens  *)
(* is the number of generations, 2^32 in the code (u32 wrapping_add).      *)
(* ReleaseKeep is release before the fix of #419, for the witnesses.       *)
(* Every call that can wake returns w, the wakers woken in the order the   *)
(* code wakes them.                                                        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

Sb0 == [slots |-> <<>>, free |-> <<>>, queue |-> <<>>]
NewSlot == [gen |-> 0, waker |-> 0, queued |-> FALSE, live |-> TRUE]

Has(s, i) == i >= 0 /\ i < Len(s.slots)
Slot(s, i) == s.slots[i + 1]
\* slot(): the slot of the ticket, if it is live and has the ticket's generation
Valid(s, t) == Has(s, t[1]) /\ Slot(s, t[1]).live /\ Slot(s, t[1]).gen = t[2]
Pop(q) == SubSeq(q, 1, Len(q) - 1)

\* alloc: the slot on top of the free stack, live again with its generation; else (no free slot, or a popped index
\* past the end, which the code then drops) a new slot at the end, of generation 0
Alloc(s) ==
    IF s.free # <<>> /\ Has(s, s.free[Len(s.free)])
    THEN LET i == s.free[Len(s.free)]
         IN [t |-> <<i, Slot(s, i).gen>>,
             s |-> [s EXCEPT !.free = Pop(@), !.slots[i + 1].live = TRUE]]
    ELSE [t |-> <<Len(s.slots), 0>>,
          s |-> [s EXCEPT !.free = IF @ = <<>> THEN @ ELSE Pop(@), !.slots = Append(@, NewSlot)]]

\* the entries of the queue whose ticket names a live slot of its generation, in order (drop_stale keeps these)
LiveEntries(s) == SelectSeq(s.queue, LAMBDA t : Valid(s, t))

\* arm: keep the waker; unless the slot is queued, queue the ticket at the back, first dropping the stale entries when
\* the queue holds twice as many entries as the slab has slots
Arm(s, t, w) ==
    IF ~Valid(s, t) THEN s
    ELSE IF Slot(s, t[1]).queued THEN [s EXCEPT !.slots[t[1] + 1].waker = w]
    ELSE [s EXCEPT !.slots[t[1] + 1].waker = w, !.slots[t[1] + 1].queued = TRUE,
                   !.queue = Append(IF Len(@) >= 2 * Len(s.slots) THEN LiveEntries(s) ELSE @, t)]

\* notify: take the waker of the ticket's slot and wake it
Notify(s, t) ==
    IF Valid(s, t) /\ Slot(s, t[1]).waker # 0
    THEN [w |-> <<Slot(s, t[1]).waker>>, s |-> [s EXCEPT !.slots[t[1] + 1].waker = 0]]
    ELSE [w |-> <<>>, s |-> s]

\* baton: pop the queue from the front; an entry whose ticket is stale is dropped and its slot left as it is; the slot
\* of a live one is no longer queued, and the first live one with a waker gives it up and is woken, and the loop ends
RECURSIVE Baton(_)
Baton(s) ==
    IF s.queue = <<>> THEN [w |-> <<>>, s |-> s]
    ELSE LET t == Head(s.queue)
             s1 == [s EXCEPT !.queue = Tail(@)]
         IN IF ~Valid(s, t) THEN Baton(s1)
            ELSE LET s2 == [s1 EXCEPT !.slots[t[1] + 1].queued = FALSE]
                 IN IF Slot(s, t[1]).waker # 0
                    THEN [w |-> <<Slot(s, t[1]).waker>>, s |-> [s2 EXCEPT !.slots[t[1] + 1].waker = 0]]
                    ELSE Baton(s2)

\* notify_all: every live slot with a waker gives it up and is woken, in the order of the slots
Armed(s, k) == s.slots[k].live /\ s.slots[k].waker # 0
NotifyAll(s) ==
    LET ks == SelectSeq([k \in 1..Len(s.slots) |-> k], LAMBDA k : Armed(s, k))
    IN [w |-> [j \in 1..Len(ks) |-> s.slots[ks[j]].waker],
        s |-> [s EXCEPT !.slots = [k \in 1..Len(s.slots) |->
                   IF Armed(s, k) THEN [s.slots[k] EXCEPT !.waker = 0] ELSE s.slots[k]]]]

\* release before the fix of #419: the slot is no longer live nor queued, its generation moves on (wrapping), its waker
\* is dropped, and it goes on the free stack; the entry of the ticket stays in the queue, stale, until the baton or a
\* compaction drops it
ReleaseKeep(s, t, gens) ==
    IF ~Valid(s, t) THEN s
    ELSE [s EXCEPT !.slots[t[1] + 1].live = FALSE, !.slots[t[1] + 1].gen = (@ + 1) % gens,
                   !.slots[t[1] + 1].waker = 0, !.slots[t[1] + 1].queued = FALSE, !.free = Append(@, t[1])]
\* release: as above, and the release that brings the slot's generation round (from gens - 1 to 0) drops every stale
\* entry of the queue (drop_stale, after the slot is released), so no entry of an earlier round outlives it
Release(s, t, gens) ==
    LET r == ReleaseKeep(s, t, gens)
    IN IF Valid(s, t) /\ Slot(s, t[1]).gen = gens - 1 THEN [r EXCEPT !.queue = LiveEntries(r)] ELSE r

Range(q) == {q[k] : k \in DOMAIN q}
Distinct(q) == \A j, k \in DOMAIN q : q[j] = q[k] => j = k
Lives(s) == {i \in 0..Len(s.slots) - 1 : Slot(s, i).live}

\* The queue's own invariants. Every entry names a slot of the slab, and a queued slot is live with the entry of its
\* ticket in the queue (QueueLive). While no stale entry names a live slot again, which Release keeps (the rule before
\* #419, ReleaseKeep, does not): the slot of every live entry is queued, no ticket has two live entries, and the queue
\* holds at most twice as many entries as the slab has slots (QueueExact).
QueueLive(s) == /\ \A k \in DOMAIN s.queue : Has(s, s.queue[k][1])
                /\ \A i \in 0..Len(s.slots) - 1 :
                       Slot(s, i).queued => Slot(s, i).live /\ <<i, Slot(s, i).gen>> \in Range(s.queue)
QueueExact(s) == /\ \A k \in DOMAIN s.queue : Valid(s, s.queue[k]) => Slot(s, s.queue[k][1]).queued
                 /\ Distinct(LiveEntries(s))
                 /\ Len(s.queue) <= 2 * Len(s.slots)

\* The documented order of the baton, kept beside the slab: the tickets waiting for the driving role, in the order they
\* were queued. arm appends a live ticket that is not in it; release takes its ticket out; the baton offers the role to
\* the first ticket whose slot is armed, and that one and every one before it leave the order (all, when none is
\* armed). OrderWoken is what the documented order says the baton wakes.
ArmedT(s, t) == Valid(s, t) /\ Slot(s, t[1]).waker # 0
OrderHits(s, o) == {k \in DOMAIN o : ArmedT(s, o[k])}
OrderFirst(s, o) == CHOOSE k \in OrderHits(s, o) : \A j \in OrderHits(s, o) : k <= j
OrderArm(s, t, o) == IF Valid(s, t) /\ t \notin Range(o) THEN Append(o, t) ELSE o
OrderRelease(s, t, o) == IF Valid(s, t) THEN SelectSeq(o, LAMBDA u : u # t) ELSE o
OrderBaton(s, o) == IF OrderHits(s, o) = {} THEN <<>> ELSE SubSeq(o, OrderFirst(s, o) + 1, Len(o))
OrderWoken(s, o) == IF OrderHits(s, o) = {} THEN <<>> ELSE <<Slot(s, o[OrderFirst(s, o)][1]).waker>>
=============================================================================
