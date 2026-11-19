------------------------------- MODULE Queue --------------------------------
(***************************************************************************)
(* The endpoint's bounded event queue (pinc-core queue.rs), over every     *)
(* interleaving of push, pop, purge and a burst of pushes, at small sizes  *)
(* (QueueOps.tla has the operators, a ring of cells with a head, as the    *)
(* code has it).                                                           *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the ring never grows: at most CAP events, the head a place of the    *)
(*    ring, every queued place holds an event (Bounded);                   *)
(*  - ll is the number of queued events the application can recover        *)
(*    (LossyLen);                                                          *)
(*  - events leave in the order they entered: the queued events have       *)
(*    increasing places in the order of pushes, all after the last one     *)
(*    popped (Fifo);                                                       *)
(*  - every drop is counted: pushes = pops + purged + dropped + queued     *)
(*    (Balance), and every loss: the unrecoverable pushes are the          *)
(*    unrecoverable pops, plus those a purge took, plus those queued, plus *)
(*    lost (BalanceUnrec);                                                 *)
(*  - the rule of a push, read off the queued sequence and not the cells   *)
(*    (PushRule): a push onto a queue that is not full appends; onto a     *)
(*    full one it counts a drop and drops the new event if that is         *)
(*    recoverable, else gives up the oldest recoverable queued event, or,  *)
(*    when none is recoverable, the oldest (counted as lost), and appends; *)
(*    a pop gives the oldest (PopRule); a purge keeps the other events in  *)
(*    their order and drops those that name the session but its Closed     *)
(*    (PurgeRule);                                                         *)
(*  - an unrecoverable event is evicted only if the queue holds nothing    *)
(*    recoverable (NoEvictUnrec);                                          *)
(*  - the headroom: from a queue that is not stalled, a burst that pushes  *)
(*    at most H unrecoverable events, and any recoverable ones, does not   *)
(*    change lost (BurstKeeps).                                            *)
(* Witnesses: Queue_over lets a burst push H + 1 unrecoverable events      *)
(* (BurstKeeps fails); Queue_head evicts the oldest event always, not the  *)
(* oldest recoverable one (PushRule fails); Queue_lost and Queue_drop are  *)
(* reachability witnesses: a loss and a drop happen.                       *)
(* Lean counterpart: proofs/lean/Pinc/CoreQueue*.lean.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS CAP, H, HB, PMAX, BL, CL, PS, HEAD_FIRST
VARIABLES r, pushes, pops, purged, pushesU, popsU, purgedU, nextId, lastPop, act, arg
vars == <<r, pushes, pops, purged, pushesU, popsU, purgedU, nextId, lastPop, act, arg>>

INSTANCE QueueOps

Init == /\ r = Ring0(CAP)
        /\ pushes = 0 /\ pops = 0 /\ purged = 0 /\ pushesU = 0 /\ popsU = 0 /\ purgedU = 0
        /\ nextId = 1 /\ lastPop = 0 /\ act = "init" /\ arg = None

Unrec(e) == IF e[2] THEN 0 ELSE 1
\* the kinds of event the runs push, by number: recoverable for session 1 or 2, unrecoverable for session 1 or
\* for none, and the Closed of session 1
Cls(c) == CASE c = 1 -> <<TRUE, 1, FALSE>>
            [] c = 2 -> <<TRUE, 2, FALSE>>
            [] c = 3 -> <<FALSE, 1, FALSE>>
            [] c = 4 -> <<FALSE, 0, FALSE>>
            [] c = 5 -> <<FALSE, 1, TRUE>>
Mk(id, c) == <<id, Cls(c)[1], Cls(c)[2], Cls(c)[3]>>
Q == Window(r, CAP)
Stale(e, s) == e[3] = s /\ ~e[4]

RECURSIVE PushAll(_, _)
PushAll(x, evs) == IF evs = <<>> THEN x ELSE PushAll(Push(x, CAP, Head(evs), HEAD_FIRST), Tail(evs))
RECURSIVE UnrecIn(_)
UnrecIn(evs) == IF evs = <<>> THEN 0 ELSE Unrec(Head(evs)) + UnrecIn(Tail(evs))

PushStep == \E c \in CL :
    LET ev == Mk(nextId, c)
    IN /\ r' = Push(r, CAP, ev, HEAD_FIRST)
       /\ pushes' = pushes + 1 /\ pushesU' = pushesU + Unrec(ev) /\ nextId' = nextId + 1
       /\ act' = "push" /\ arg' = ev
       /\ UNCHANGED <<pops, purged, popsU, purgedU, lastPop>>

PopStep ==
    LET x == Pop(r, CAP)
    IN /\ r' = x.r
       /\ pops' = IF x.out = None THEN pops ELSE pops + 1
       /\ popsU' = IF x.out = None THEN popsU ELSE popsU + Unrec(x.out)
       /\ lastPop' = IF x.out = None THEN lastPop ELSE x.out[1]
       /\ act' = "pop" /\ arg' = None
       /\ UNCHANGED <<pushes, purged, pushesU, purgedU, nextId>>

PurgeStep == \E s \in PS :
    LET gone == SelectSeq(Q, LAMBDA e : Stale(e, s))
    IN /\ r' = Purge(r, CAP, s)
       /\ purged' = purged + Len(gone)
       /\ purgedU' = purgedU + Len(SelectSeq(gone, LAMBDA e : ~e[2]))
       /\ act' = "purge" /\ arg' = s
       /\ UNCHANGED <<pushes, pops, pushesU, popsU, nextId, lastPop>>

\* one step the endpoint takes without checking the queue again: several pushes after a check that it is not
\* stalled, at most HB of them unrecoverable
BurstStep == \E n \in 1..BL : \E cs \in [1..n -> CL] :
    LET evs == [i \in 1..n |-> Mk(nextId + i - 1, cs[i])]
    IN /\ ~Stalled(r, CAP, H)
       /\ UnrecIn(evs) <= HB
       /\ r' = PushAll(r, evs)
       /\ pushes' = pushes + n /\ pushesU' = pushesU + UnrecIn(evs) /\ nextId' = nextId + n
       /\ act' = "burst" /\ arg' = None
       /\ UNCHANGED <<pops, purged, popsU, purgedU, lastPop>>

Next == PushStep \/ PopStep \/ PurgeStep \/ BurstStep
Spec == Init /\ [][Next]_vars
Bound == nextId <= PMAX

CountLossy(q) == Len(SelectSeq(q, LAMBDA e : e[2]))

Bounded == /\ r.len \in 0..CAP /\ r.head \in 0..CAP - 1
           /\ \A i \in 0..r.len - 1 : Get(r, CAP, i) # None
LossyLen == r.ll = CountLossy(Q)
Fifo == /\ \A i, j \in 1..Len(Q) : i < j => Q[i][1] < Q[j][1]
        /\ \A i \in 1..Len(Q) : lastPop < Q[i][1]
Balance == pushes = pops + purged + r.dropped + r.len
BalanceUnrec == pushesU = popsU + purgedU + (r.len - r.ll) + r.lost
\* the closed form of the eviction's shift is the code's loop, for every victim
ShiftRight == \A v \in 0..CAP - 1 : Shift(r.cells, r.head, CAP, v) = ShiftLoop(r.cells, r.head, CAP, v)
Inv == Bounded /\ LossyLen /\ Fifo /\ Balance /\ BalanceUnrec /\ ShiftRight

Without(q, i) == SubSeq(q, 1, i - 1) \o SubSeq(q, i + 1, Len(q))
FirstLossy(q) ==
    LET m == {i \in 1..Len(q) : q[i][2]}
    IN IF m = {} THEN 0 ELSE CHOOSE i \in m : \A j \in m : i <= j

\* the rule of a push, from the queued sequences
PushRuleA ==
    act' = "push" =>
        LET ev == arg'
        IN IF Len(Q) < CAP
           THEN /\ Window(r', CAP) = Append(Q, ev) /\ r'.dropped = r.dropped /\ r'.lost = r.lost
           ELSE /\ r'.dropped = r.dropped + 1
                /\ IF ev[2]
                   THEN Window(r', CAP) = Q /\ r'.lost = r.lost
                   ELSE IF FirstLossy(Q) # 0
                        THEN Window(r', CAP) = Append(Without(Q, FirstLossy(Q)), ev) /\ r'.lost = r.lost
                        ELSE Window(r', CAP) = Append(Tail(Q), ev) /\ r'.lost = r.lost + 1
PopRuleA == act' = "pop" =>
    IF Len(Q) = 0 THEN Window(r', CAP) = Q ELSE Window(r', CAP) = Tail(Q)
PurgeRuleA == act' = "purge" =>
    /\ Window(r', CAP) = SelectSeq(Q, LAMBDA e : ~Stale(e, arg'))
    /\ r'.dropped = r.dropped /\ r'.lost = r.lost
\* an unrecoverable event leaves a push only when the queue holds nothing recoverable
NoEvictUnrecA == act' = "push" =>
    \A i \in 1..Len(Q) :
        (~Q[i][2] /\ \A j \in 1..Len(Window(r', CAP)) : Window(r', CAP)[j][1] # Q[i][1])
            => (CountLossy(Q) = 0 /\ Len(Q) = CAP /\ i = 1)
BurstKeepsA == act' = "burst" => r'.lost = r.lost
PushRule == [][PushRuleA]_vars
PopRule == [][PopRuleA]_vars
PurgeRule == [][PurgeRuleA]_vars
NoEvictUnrec == [][NoEvictUnrecA]_vars
BurstKeeps == [][BurstKeepsA]_vars

\* reachability witnesses: each is a property TLC must violate (a loss, a drop, an eviction of an event that is not
\* the first queued, the head going round the ring, a purge that drops something, a burst from a queue holding
\* exactly CAP - H unrecoverable events)
NoLost == r.lost = 0
NoDrop == r.dropped = 0
NoDeepEvict == [][~(act' = "push" /\ Len(Q) = CAP /\ ~arg'[2] /\ FirstLossy(Q) > 1)]_vars
NoWrap == [][r'.head >= r.head]_vars
NoPurgeDrop == [][~(act' = "purge" /\ r'.len < r.len)]_vars
NoBurstEdge == [][~(act' = "burst" /\ r.len - r.ll = CAP - H)]_vars
=============================================================================
