---------------------------- MODULE FacadeStandby ----------------------------
(***************************************************************************)
(* The slab of tickets of the facade's waiting futures and the queue of    *)
(* candidates for the driving role (crates/pinc/src/standby.rs), over      *)
(* every sequence of alloc, arm, notify, baton, notify_all and release, at *)
(* small sizes, with every ticket ever handed out (stale ones included)    *)
(* and a forged one (StandbyOps.tla has the operators). At most LIVE       *)
(* tickets are held at once and AMAX are handed out in all; W are the      *)
(* wakers; GENS generations stand for the code's 2^32, so a slot's         *)
(* generation goes round within the bound. Beside the slab the model keeps *)
(* ord, the documented order: the tickets waiting for the role in the      *)
(* order they were queued, and wrapped, set once alloc hands out a ticket  *)
(* that a stale entry of the queue still names (its slot was released a    *)
(* multiple of GENS times since the entry was queued, so the entry names a *)
(* live slot again).                                                       *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - wrapped is never set (NoRevive): the release that brings a slot's    *)
(*    generation round drops every stale entry of the queue (the fix of    *)
(*    #419), so no entry of an earlier round names the slot's next ticket, *)
(*    whatever the calls (a slot released unarmed included); and it could  *)
(*    be set only after a slot was released GENS times (WrapCost);         *)
(*  - every entry of the queue names a slot of the slab, and a queued slot *)
(*    is live with the entry of its ticket in the queue; the slot of every *)
(*    live entry is queued, no ticket has two live entries, and the queue  *)
(*    holds at most twice as many entries as the slab has slots            *)
(*    (QueueOnce);                                                         *)
(*  - the live entries of the queue are the documented order: a ticket     *)
(*    that reuses a released slot queues behind the tickets already        *)
(*    waiting (QueueOrder);                                                *)
(*  - a slot keeps a waker only while it is live and queued (WakerQueued); *)
(*  - the free stack holds each slot at most once, exactly the slots that  *)
(*    are not live (FreeExact);                                            *)
(*  - the slab is as long as the most tickets held at once (SlabBound);    *)
(*  - a released ticket names a live slot again only after its slot was    *)
(*    released a multiple of GENS times (DeadStay);                        *)
(*  - an arm, notify or release with a ticket that does not name a live    *)
(*    slot of its generation changes nothing and wakes nothing; a release  *)
(*    that acts leaves its ticket dead (StaleRight);                       *)
(*  - alloc hands out a live ticket: the slot on top of the free stack, or *)
(*    a new one at the end only when every slot is live (AllocRight);      *)
(*  - notify wakes the ticket's waker if it is armed and nothing else;     *)
(*    notify_all wakes exactly the armed live slots, each once, in slot    *)
(*    order (WakeRight);                                                   *)
(*  - the baton, as the code has it: it wakes the waker of the first entry *)
(*    of the queue whose ticket is live and armed, and every entry up to   *)
(*    it leaves the queue; with none, the queue empties and nothing is     *)
(*    woken; the slot of every live entry it popped is no longer queued    *)
(*    and no other slot's mark changes; whenever a slot is armed, exactly  *)
(*    one waker is woken (BatonRight);                                     *)
(*  - the baton wakes the oldest armed ticket of the documented order      *)
(*    (BatonOldest).                                                       *)
(* Witnesses: FacadeStandby_oldest runs the code before the fix of #311    *)
(* (OLD: release leaves the slot queued and its entry in the queue, and    *)
(* the baton takes an entry by its slot whatever the generation, so a      *)
(* ticket that reuses a queued slot keeps the released ticket's place):    *)
(* BatonOldest fails. FacadeStandby_wrapkeep runs the release before the   *)
(* fix of #419 (DROP = FALSE: the stale entries stay queued at the wrap)   *)
(* with GENS = 2: a stale entry names a live slot again after its slot was *)
(* released twice, and the queue is no longer exact (QueueStrict fails);   *)
(* FacadeStandby_wrap is the same run with the fix, where QueueStrict      *)
(* holds. FacadeStandby_nogen has one generation: a stale ticket names the *)
(* slot of a later future (NoStaleHit fails).                              *)
(* Lean counterpart: proofs/lean/Pinc/FacadeStandby*.lean.                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS LIVE, AMAX, W, GENS, OLD,
          DROP   \* the release of the code (TRUE) or the release before the fix of #419 (FALSE)
VARIABLES sb, issued, allocs, hw, rels, dead, ord, wrapped, rStale, rAlloc, rWake, rBaton, oldest
vars == <<sb, issued, allocs, hw, rels, dead, ord, wrapped, rStale, rAlloc, rWake, rBaton, oldest>>

INSTANCE StandbyOps

Init == /\ sb = Sb0 /\ issued = {} /\ allocs = 0 /\ hw = 0 /\ rels = [i \in 0..LIVE - 1 |-> 0] /\ dead = {}
        /\ ord = <<>> /\ wrapped = FALSE
        /\ rStale = TRUE /\ rAlloc = TRUE /\ rWake = TRUE /\ rBaton = TRUE /\ oldest = TRUE

\* a forged ticket: a slot past every one the slab can have
FORGED == <<LIVE + 4, 0>>
Tickets == issued \cup {FORGED}
ArmedSlot(s, i) == Slot(s, i).live /\ Slot(s, i).waker # 0
Ghost == <<rels, dead>>

\* The code before the fix of #311, for the witness: release leaves the slot queued and its entry in the queue, arm
\* queues the ticket only when the slot is not queued (and compacts nothing: the queue never held a slot twice), and
\* the baton takes each entry by its slot, whatever the generation.
ArmOld(s, t, w) ==
    IF ~Valid(s, t) THEN s
    ELSE IF Slot(s, t[1]).queued THEN [s EXCEPT !.slots[t[1] + 1].waker = w]
    ELSE [s EXCEPT !.slots[t[1] + 1].waker = w, !.slots[t[1] + 1].queued = TRUE, !.queue = Append(@, t)]
RECURSIVE BatonOld(_)
BatonOld(s) ==
    IF s.queue = <<>> THEN [w |-> <<>>, s |-> s]
    ELSE LET i == Head(s.queue)[1]
             s1 == [s EXCEPT !.queue = Tail(@)]
         IN IF ~Has(s, i) THEN BatonOld(s1)
            ELSE LET s2 == [s1 EXCEPT !.slots[i + 1].queued = FALSE]
                 IN IF Slot(s, i).live /\ Slot(s, i).waker # 0
                    THEN [w |-> <<Slot(s, i).waker>>, s |-> [s2 EXCEPT !.slots[i + 1].waker = 0]]
                    ELSE BatonOld(s2)
ReleaseOld(s, t) ==
    IF ~Valid(s, t) THEN s
    ELSE [s EXCEPT !.slots[t[1] + 1].live = FALSE, !.slots[t[1] + 1].gen = (@ + 1) % GENS,
                   !.slots[t[1] + 1].waker = 0, !.free = Append(@, t[1])]
DoArm(s, t, w) == IF OLD THEN ArmOld(s, t, w) ELSE Arm(s, t, w)
DoBaton(s) == IF OLD THEN BatonOld(s) ELSE Baton(s)
DoRelease(s, t) == IF OLD THEN ReleaseOld(s, t) ELSE IF DROP THEN Release(s, t, GENS) ELSE ReleaseKeep(s, t, GENS)

AllocA ==
    LET x == Alloc(sb)
        full == Lives(sb) = 0..Len(sb.slots) - 1
    IN /\ Cardinality(Lives(sb)) < LIVE /\ allocs < AMAX
       /\ sb' = x.s /\ issued' = issued \cup {x.t} /\ allocs' = allocs + 1
       /\ hw' = IF Cardinality(Lives(sb')) > hw THEN Cardinality(Lives(sb')) ELSE hw
       \* a stale entry of the queue that names the ticket handed out names a live slot again
       /\ wrapped' = (wrapped \/ x.t \in Range(sb.queue))
       /\ rAlloc' = (rAlloc /\ Valid(sb', x.t) /\ ~Valid(sb, x.t)
                     /\ IF sb.free # <<>> THEN x.t[1] = sb.free[Len(sb.free)] /\ Len(sb'.slots) = Len(sb.slots)
                        ELSE full /\ x.t = <<Len(sb.slots), 0>> /\ Len(sb'.slots) = Len(sb.slots) + 1)
       /\ UNCHANGED <<rels, dead, ord, rStale, rWake, rBaton, oldest>>

ArmA == \E t \in Tickets, w \in W :
    /\ sb' = DoArm(sb, t, w)
    /\ ord' = OrderArm(sb, t, ord)
    /\ rStale' = (rStale /\ (~Valid(sb, t) => sb' = sb))
    /\ rWake' = (rWake /\ (Valid(sb, t) => Slot(sb', t[1]).waker = w /\ Slot(sb', t[1]).queued))
    /\ UNCHANGED <<issued, allocs, hw, rels, dead, wrapped, rAlloc, rBaton, oldest>>

NotifyA == \E t \in Tickets :
    LET x == Notify(sb, t)
    IN /\ sb' = x.s
       /\ rStale' = (rStale /\ (~Valid(sb, t) => sb' = sb /\ x.w = <<>>))
       /\ rWake' = (rWake /\ x.w = IF Valid(sb, t) /\ Slot(sb, t[1]).waker # 0 THEN <<Slot(sb, t[1]).waker>> ELSE <<>>)
       /\ UNCHANGED <<issued, allocs, hw, rels, dead, ord, wrapped, rAlloc, rBaton, oldest>>

NotifyAllA ==
    LET x == NotifyAll(sb)
        ks == {i \in 0..Len(sb.slots) - 1 : ArmedSlot(sb, i)}
        \* the armed slots in increasing order
        sorted == [j \in 1..Cardinality(ks) |-> CHOOSE i \in ks : Cardinality({k \in ks : k < i}) = j - 1]
    IN /\ sb' = x.s
       /\ rWake' = (/\ rWake
                    /\ x.w = [j \in 1..Cardinality(ks) |-> Slot(sb, sorted[j]).waker]
                    /\ (\A i \in ks : Slot(sb', i).waker = 0)
                    /\ (\A i \in 0..Len(sb.slots) - 1 : i \notin ks => Slot(sb', i) = Slot(sb, i)))
       /\ UNCHANGED <<issued, allocs, hw, rels, dead, ord, wrapped, rStale, rAlloc, rBaton, oldest>>

BatonA ==
    LET x == DoBaton(sb)
        q == sb.queue
        n == Len(q) - Len(x.s.queue)
        hits == {k \in DOMAIN q : ArmedT(sb, q[k])}
        first == CHOOSE k \in hits : \A j \in hits : k <= j
        \* the slots of the live entries the baton popped
        offered == {q[k][1] : k \in {j \in 1..n : Valid(sb, q[j])}}
    IN /\ sb' = x.s
       /\ ord' = OrderBaton(sb, ord)
       /\ rBaton' = (/\ rBaton
                     /\ IF hits = {} THEN x.w = <<>> /\ x.s.queue = <<>>
                        ELSE /\ n = first /\ x.s.queue = SubSeq(q, first + 1, Len(q))
                             /\ x.w = <<Slot(sb, q[first][1]).waker>> /\ Slot(x.s, q[first][1]).waker = 0
                     /\ \A i \in 0..Len(sb.slots) - 1 :
                            IF i \in offered THEN ~Slot(x.s, i).queued ELSE Slot(x.s, i).queued = Slot(sb, i).queued
                     /\ ((\E i \in 0..Len(sb.slots) - 1 : Slot(sb, i).waker # 0) => Len(x.w) = 1))
       /\ oldest' = (oldest /\ x.w = OrderWoken(sb, ord))
       /\ UNCHANGED <<issued, allocs, hw, rels, dead, wrapped, rStale, rAlloc, rWake>>

ReleaseA == \E t \in Tickets :
    /\ sb' = DoRelease(sb, t)
    /\ IF Valid(sb, t)
       THEN /\ rels' = [rels EXCEPT ![t[1]] = @ + 1]
            /\ dead' = dead \cup {<<t[1], t[2], rels'[t[1]]>>}
       ELSE UNCHANGED <<rels, dead>>
    /\ ord' = OrderRelease(sb, t, ord)
    /\ rStale' = (rStale /\ ~Valid(sb', t) /\ (~Valid(sb, t) => sb' = sb))
    /\ UNCHANGED <<issued, allocs, hw, wrapped, rAlloc, rWake, rBaton, oldest>>

Next == AllocA \/ ArmA \/ NotifyA \/ NotifyAllA \/ BatonA \/ ReleaseA
Spec == Init /\ [][Next]_vars

NoRevive == ~wrapped
QueueOnce == QueueLive(sb) /\ QueueExact(sb)
QueueOrder == LiveEntries(sb) = ord
WrapCost == wrapped => \E i \in 0..LIVE - 1 : rels[i] >= GENS
WakerQueued == \A i \in 0..Len(sb.slots) - 1 : Slot(sb, i).waker # 0 => Slot(sb, i).live /\ Slot(sb, i).queued
FreeExact == /\ Distinct(sb.free)
             /\ Range(sb.free) = {i \in 0..Len(sb.slots) - 1 : ~Slot(sb, i).live}
             /\ Len(sb.slots) = Cardinality(Lives(sb)) + Len(sb.free)
SlabBound == Len(sb.slots) = hw
GenRange == \A i \in 0..Len(sb.slots) - 1 : Slot(sb, i).gen \in 0..GENS - 1
DeadStay == \A d \in dead : Valid(sb, <<d[1], d[2]>>) => (rels[d[1]] - d[3] + 1) % GENS = 0
StaleRight == rStale
AllocRight == rAlloc
WakeRight == rWake
BatonRight == rBaton
BatonOldest == oldest
Inv == NoRevive /\ QueueOnce /\ QueueOrder /\ WrapCost /\ WakerQueued /\ FreeExact /\ SlabBound /\ GenRange
       /\ DeadStay /\ StaleRight /\ AllocRight /\ WakeRight /\ BatonRight /\ BatonOldest

\* the witnesses: the queue exact and in the documented order (a stale entry that names a live slot again, which the
\* release before #419 lets happen, breaks it), and a stale ticket that names a later future's slot
QueueStrict == QueueExact(sb) /\ LiveEntries(sb) = ord
NoStaleHit == \A d \in dead : ~Valid(sb, <<d[1], d[2]>>)
=============================================================================
