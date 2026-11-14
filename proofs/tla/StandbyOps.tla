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
(* (the VecDeque, front first). A ticket is <<idx, gen>>. gens is the      *)
(* number of generations, 2^32 in the code (u32 wrapping_add). Every call  *)
(* that can wake returns w, the wakers woken in the order the code wakes   *)
(* them.                                                                   *)
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

\* arm: keep the waker, and queue the slot unless it is queued already
Arm(s, t, w) ==
    IF ~Valid(s, t) THEN s
    ELSE IF Slot(s, t[1]).queued THEN [s EXCEPT !.slots[t[1] + 1].waker = w]
    ELSE [s EXCEPT !.slots[t[1] + 1].waker = w, !.slots[t[1] + 1].queued = TRUE, !.queue = Append(@, t[1])]

\* notify: take the waker of the ticket's slot and wake it
Notify(s, t) ==
    IF Valid(s, t) /\ Slot(s, t[1]).waker # 0
    THEN [w |-> <<Slot(s, t[1]).waker>>, s |-> [s EXCEPT !.slots[t[1] + 1].waker = 0]]
    ELSE [w |-> <<>>, s |-> s]

\* baton: pop the queue from the front; each popped slot is no longer queued; the first one that is live and has a
\* waker gives it up and is woken, and the loop ends
RECURSIVE Baton(_)
Baton(s) ==
    IF s.queue = <<>> THEN [w |-> <<>>, s |-> s]
    ELSE LET i == Head(s.queue)
             s1 == [s EXCEPT !.queue = Tail(@)]
         IN IF ~Has(s, i) THEN Baton(s1)
            ELSE LET s2 == [s1 EXCEPT !.slots[i + 1].queued = FALSE]
                 IN IF Slot(s, i).live /\ Slot(s, i).waker # 0
                    THEN [w |-> <<Slot(s, i).waker>>, s |-> [s2 EXCEPT !.slots[i + 1].waker = 0]]
                    ELSE Baton(s2)

\* notify_all: every live slot with a waker gives it up and is woken, in the order of the slots
Armed(s, k) == s.slots[k].live /\ s.slots[k].waker # 0
NotifyAll(s) ==
    LET ks == SelectSeq([k \in 1..Len(s.slots) |-> k], LAMBDA k : Armed(s, k))
    IN [w |-> [j \in 1..Len(ks) |-> s.slots[ks[j]].waker],
        s |-> [s EXCEPT !.slots = [k \in 1..Len(s.slots) |->
                   IF Armed(s, k) THEN [s.slots[k] EXCEPT !.waker = 0] ELSE s.slots[k]]]]

\* release: the slot is no longer live, its generation moves on (wrapping), its waker is dropped, and it goes on the
\* free stack; the queue is left as it is
Release(s, t, gens) ==
    IF ~Valid(s, t) THEN s
    ELSE [s EXCEPT !.slots[t[1] + 1].live = FALSE, !.slots[t[1] + 1].gen = (@ + 1) % gens,
                   !.slots[t[1] + 1].waker = 0, !.free = Append(@, t[1])]

Range(q) == {q[k] : k \in DOMAIN q}
Distinct(q) == \A j, k \in DOMAIN q : q[j] = q[k] => j = k
Lives(s) == {i \in 0..Len(s.slots) - 1 : Slot(s, i).live}
=============================================================================
