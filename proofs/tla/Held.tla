-------------------------------- MODULE Held --------------------------------
(***************************************************************************)
(* The held ring of a session (vinc-core slot.rs Held): the application    *)
(* events waiting for the access check. Every interleaving of push and pop *)
(* at small sizes (HeldOps.tla has the operators; the ring is the event    *)
(* queue's, QueueOps.tla).                                                 *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the ring never grows: at most CAP events, every queued place holds   *)
(*    an event (Bounded);                                                  *)
(*  - events leave in the order they entered: the held events have         *)
(*    increasing places in the order of pushes, all after the last one     *)
(*    popped (Fifo);                                                       *)
(*  - every drop is counted: pushes = pops + merged + dropped + held       *)
(*    (Balance); and every unrecoverable event pushed is popped, held or   *)
(*    refused (BalanceUnrec): an unrecoverable event is never evicted;     *)
(*  - the rule of a push, read off the held sequence and not the cells     *)
(*    (PushRule): a recoverable event that repeats a held one (the same    *)
(*    kind and stream) changes nothing and counts nothing; otherwise onto  *)
(*    a ring with room it appends; onto a full ring it counts a drop and   *)
(*    gives up the oldest recoverable event and appends, or, holding none, *)
(*    refuses the new event (PopRule: a pop gives the oldest);             *)
(*  - an event is refused only by a ring that is stalled, full of events   *)
(*    the application cannot recover (RefusalNeedsStall), so a push made   *)
(*    while the ring is not stalled holds an unrecoverable event           *)
(*    (GuardedHolds), the endpoint's rule;                                 *)
(*  - the recoverable events held have distinct kind and stream            *)
(*    (Distinct).                                                          *)
(* Witnesses: Held_head gives up the oldest event of a stalled ring, as    *)
(* the event queue does (PushRule and BalanceUnrec fail); Held_refuse,     *)
(* Held_merge and Held_evict are reachability witnesses: a refusal, a      *)
(* merge and an eviction happen.                                           *)
(* Lean counterpart: proofs/lean/Vinc/CoreHeld*.lean.                      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS CAP, PMAX, CL, EVICT_HEAD
VARIABLES r, pushes, pops, merged, pushesU, popsU, refusedU, nextId, lastPop, act, arg
vars == <<r, pushes, pops, merged, pushesU, popsU, refusedU, nextId, lastPop, act, arg>>

INSTANCE HeldOps

Init == /\ r = Ring0(CAP)
        /\ pushes = 0 /\ pops = 0 /\ merged = 0 /\ pushesU = 0 /\ popsU = 0 /\ refusedU = 0
        /\ nextId = 1 /\ lastPop = 0 /\ act = "init" /\ arg = None

\* the events the runs push, by number: readable of stream 1 or 2, writable of stream 1, a stream reset (cannot be
\* recovered), a stream opened
Mk(id, c) == CASE c = 1 -> Ev(id, 1, 1, 0)
                [] c = 2 -> Ev(id, 1, 2, 0)
                [] c = 3 -> Ev(id, 2, 1, 0)
                [] c = 4 -> Ev(id, 3, 1, 7)
                [] c = 5 -> Ev(id, 0, 1, 0)
Unrec(e) == IF e[2] THEN 0 ELSE 1
Q == Window(r, CAP)

PushStep == \E c \in CL :
    LET ev == Mk(nextId, c)
        merges == HMerges(r, CAP, ev)
        refuses == ~merges /\ r.len = CAP /\ Victim(r, CAP) < 0
    IN /\ r' = HPush(r, CAP, ev, EVICT_HEAD)
       /\ pushes' = pushes + 1 /\ pushesU' = pushesU + Unrec(ev) /\ nextId' = nextId + 1
       /\ merged' = IF merges THEN merged + 1 ELSE merged
       /\ refusedU' = IF refuses THEN refusedU + Unrec(ev) ELSE refusedU
       /\ act' = "push" /\ arg' = ev
       /\ UNCHANGED <<pops, popsU, lastPop>>

PopStep ==
    LET x == Pop(r, CAP)
    IN /\ r' = x.r
       /\ pops' = IF x.out = None THEN pops ELSE pops + 1
       /\ popsU' = IF x.out = None THEN popsU ELSE popsU + Unrec(x.out)
       /\ lastPop' = IF x.out = None THEN lastPop ELSE x.out[1]
       /\ act' = "pop" /\ arg' = None
       /\ UNCHANGED <<pushes, merged, pushesU, refusedU, nextId>>

Next == PushStep \/ PopStep
Spec == Init /\ [][Next]_vars
Bound == nextId <= PMAX

CountLossy(q) == Len(SelectSeq(q, LAMBDA e : e[2]))

Bounded == /\ r.len \in 0..CAP /\ r.head \in 0..CAP - 1
           /\ \A i \in 0..r.len - 1 : Get(r, CAP, i) # None
Fifo == /\ \A i, j \in 1..Len(Q) : i < j => Q[i][1] < Q[j][1]
        /\ \A i \in 1..Len(Q) : lastPop < Q[i][1]
Balance == pushes = pops + merged + r.dropped + r.len
BalanceUnrec == pushesU = popsU + (r.len - CountLossy(Q)) + refusedU
Distinct == \A i, j \in 1..Len(Q) : (i < j /\ Q[i][2] /\ Q[j][2]) => Q[i][3] # Q[j][3]
Inv == Bounded /\ Fifo /\ Balance /\ BalanceUnrec /\ Distinct /\ (r.ll = CountLossy(Q))

Without(q, i) == SubSeq(q, 1, i - 1) \o SubSeq(q, i + 1, Len(q))
FirstLossy(q) ==
    LET m == {i \in 1..Len(q) : q[i][2]}
    IN IF m = {} THEN 0 ELSE CHOOSE i \in m : \A j \in m : i <= j
Repeats(q, ev) == ev[2] /\ \E i \in 1..Len(q) : q[i][3] = ev[3]

\* the rule of a push, from the held sequences
PushRuleA ==
    act' = "push" =>
        LET ev == arg'
        IN IF Repeats(Q, ev)
           THEN Window(r', CAP) = Q /\ r'.dropped = r.dropped
           ELSE IF Len(Q) < CAP
                THEN Window(r', CAP) = Append(Q, ev) /\ r'.dropped = r.dropped
                ELSE /\ r'.dropped = r.dropped + 1
                     /\ IF FirstLossy(Q) # 0
                        THEN Window(r', CAP) = Append(Without(Q, FirstLossy(Q)), ev)
                        ELSE Window(r', CAP) = Q
PopRuleA == act' = "pop" =>
    IF Len(Q) = 0 THEN Window(r', CAP) = Q ELSE Window(r', CAP) = Tail(Q)
\* an event is refused only by a ring that is full of events the application cannot recover
RefusalNeedsStallA == (act' = "push" /\ ~Repeats(Q, arg') /\ Window(r', CAP) = Q) =>
    (Len(Q) = CAP /\ CountLossy(Q) = 0)
\* a push made while the ring is not stalled holds an unrecoverable event
GuardedHoldsA == (act' = "push" /\ ~arg'[2] /\ ~HStalled(r, CAP)) =>
    \E i \in 1..Len(Window(r', CAP)) : Window(r', CAP)[i][1] = arg'[1]
PushRule == [][PushRuleA]_vars
PopRule == [][PopRuleA]_vars
RefusalNeedsStall == [][RefusalNeedsStallA]_vars
GuardedHolds == [][GuardedHoldsA]_vars

\* reachability witnesses: a refusal, a merge and an eviction happen
NoRefuse == [][~(act' = "push" /\ ~Repeats(Q, arg') /\ Len(Q) = CAP /\ CountLossy(Q) = 0)]_vars
NoMerge == [][~(act' = "push" /\ Repeats(Q, arg'))]_vars
NoEvict == [][~(act' = "push" /\ ~Repeats(Q, arg') /\ Len(Q) = CAP /\ CountLossy(Q) > 0)]_vars
=============================================================================
