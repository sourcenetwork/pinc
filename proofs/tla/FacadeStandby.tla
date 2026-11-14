---------------------------- MODULE FacadeStandby ----------------------------
(***************************************************************************)
(* The slab of tickets of the facade's waiting futures and the queue of    *)
(* candidates for the driving role (crates/vinc/src/standby.rs), over      *)
(* every sequence of alloc, arm, notify, baton, notify_all and release, at *)
(* small sizes, with every ticket ever handed out (stale ones included)    *)
(* and a forged one (StandbyOps.tla has the operators). At most LIVE       *)
(* tickets are held at once and AMAX are handed out in all; W are the      *)
(* wakers.                                                                 *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the queue holds each slot at most once, exactly the slots marked     *)
(*    queued, so it never outgrows the slab (QueueOnce);                   *)
(*  - a slot keeps a waker only while it is live and queued (WakerQueued); *)
(*  - the free stack holds each slot at most once, exactly the slots that  *)
(*    are not live (FreeExact);                                            *)
(*  - the slab is as long as the most tickets held at once (SlabBound);    *)
(*  - a released ticket names a live slot again only after its slot was    *)
(*    released a multiple of GENS times (2^32 in the code) (DeadStay);     *)
(*  - an arm, notify or release with a ticket that does not name a live    *)
(*    slot of its generation changes nothing and wakes nothing; a release  *)
(*    that acts leaves its ticket dead (StaleRight);                       *)
(*  - alloc hands out a live ticket: the slot on top of the free stack, or *)
(*    a new one at the end only when every slot is live (AllocRight);      *)
(*  - notify wakes the ticket's waker if it is armed and nothing else;     *)
(*    notify_all wakes exactly the armed live slots, each once, in slot    *)
(*    order (WakeRight);                                                   *)
(*  - the baton's order, as the code has it: it wakes the waker of the     *)
(*    first slot in the queue that is live and armed, and every entry up   *)
(*    to it leaves the queue; with none, the queue empties and nothing is  *)
(*    woken; whenever a slot is armed, exactly one waker is woken          *)
(*    (BatonRight).                                                        *)
(* The queue is of slots, not tickets: release leaves a queued slot in the *)
(* queue, and a later ticket of the same slot keeps that place (#311).     *)
(* The witness FacadeStandby_oldest checks the documented "the baton wakes *)
(* the oldest armed ticket" (BatonOldest, against armo, the order in which *)
(* the tickets now armed were first armed) and must fail. The witness      *)
(* FacadeStandby_nogen has one generation: a stale ticket names the slot   *)
(* of a later future (NoStaleHit fails).                                   *)
(* Lean counterpart: proofs/lean/Vinc/FacadeStandby*.lean.                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS LIVE, AMAX, W, GENS
VARIABLES sb, issued, allocs, hw, rels, dead, armo, rStale, rAlloc, rWake, rBaton, oldest
vars == <<sb, issued, allocs, hw, rels, dead, armo, rStale, rAlloc, rWake, rBaton, oldest>>

INSTANCE StandbyOps

Init == /\ sb = Sb0 /\ issued = {} /\ allocs = 0 /\ hw = 0 /\ rels = [i \in 0..LIVE - 1 |-> 0] /\ dead = {}
        /\ armo = <<>> /\ rStale = TRUE /\ rAlloc = TRUE /\ rWake = TRUE /\ rBaton = TRUE /\ oldest = TRUE

\* a forged ticket: a slot past every one the slab can have
FORGED == <<LIVE + 4, 0>>
Tickets == issued \cup {FORGED}
Without(q, i) == SelectSeq(q, LAMBDA j : j # i)
ArmedSlot(s, i) == Slot(s, i).live /\ Slot(s, i).waker # 0
Ghost == <<rels, dead>>

AllocA ==
    LET x == Alloc(sb)
        full == Lives(sb) = 0..Len(sb.slots) - 1
    IN /\ Cardinality(Lives(sb)) < LIVE /\ allocs < AMAX
       /\ sb' = x.s /\ issued' = issued \cup {x.t} /\ allocs' = allocs + 1
       /\ hw' = IF Cardinality(Lives(sb')) > hw THEN Cardinality(Lives(sb')) ELSE hw
       /\ rAlloc' = (rAlloc /\ Valid(sb', x.t) /\ ~Valid(sb, x.t)
                     /\ IF sb.free # <<>> THEN x.t[1] = sb.free[Len(sb.free)] /\ Len(sb'.slots) = Len(sb.slots)
                        ELSE full /\ x.t = <<Len(sb.slots), 0>> /\ Len(sb'.slots) = Len(sb.slots) + 1)
       /\ UNCHANGED <<rels, dead, armo, rStale, rWake, rBaton, oldest>>

ArmA == \E t \in Tickets, w \in W :
    /\ sb' = Arm(sb, t, w)
    /\ armo' = IF Valid(sb, t) /\ t[1] \notin Range(armo) THEN Append(armo, t[1]) ELSE armo
    /\ rStale' = (rStale /\ (~Valid(sb, t) => sb' = sb))
    /\ rWake' = (rWake /\ (Valid(sb, t) => Slot(sb', t[1]).waker = w /\ Slot(sb', t[1]).queued))
    /\ UNCHANGED <<issued, allocs, hw, rels, dead, rAlloc, rBaton, oldest>>

NotifyA == \E t \in Tickets :
    LET x == Notify(sb, t)
    IN /\ sb' = x.s
       /\ rStale' = (rStale /\ (~Valid(sb, t) => sb' = sb /\ x.w = <<>>))
       /\ rWake' = (rWake /\ x.w = IF Valid(sb, t) /\ Slot(sb, t[1]).waker # 0 THEN <<Slot(sb, t[1]).waker>> ELSE <<>>)
       /\ UNCHANGED <<issued, allocs, hw, rels, dead, armo, rAlloc, rBaton, oldest>>

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
       /\ UNCHANGED <<issued, allocs, hw, rels, dead, armo, rStale, rAlloc, rBaton, oldest>>

BatonA ==
    LET x == Baton(sb)
        q == sb.queue
        n == Len(q) - Len(x.s.queue)
        hits == {k \in DOMAIN q : Has(sb, q[k]) /\ ArmedSlot(sb, q[k])}
        first == CHOOSE k \in hits : \A j \in hits : k <= j
        popped == Range(SubSeq(q, 1, n))
        \* the doc's order: the first of the tickets now armed in the order they were first armed
        cands == SelectSeq(armo, LAMBDA i : Has(sb, i) /\ ArmedSlot(sb, i))
    IN /\ sb' = x.s
       /\ armo' = SelectSeq(armo, LAMBDA i : i \notin popped)
       /\ rBaton' = (rBaton
                     /\ IF hits = {} THEN x.w = <<>> /\ x.s.queue = <<>>
                        ELSE /\ n = first /\ x.s.queue = SubSeq(q, first + 1, Len(q))
                             /\ x.w = <<Slot(sb, q[first]).waker>> /\ Slot(x.s, q[first]).waker = 0
                     /\ (\A i \in popped : (Has(sb, i) => ~Slot(x.s, i).queued))
                     /\ ((\E i \in 0..Len(sb.slots) - 1 : Slot(sb, i).waker # 0) => Len(x.w) = 1))
       /\ oldest' = (oldest /\ (x.w = <<>> \/ (cands # <<>> /\ q[n] = cands[1])))
       /\ UNCHANGED <<issued, allocs, hw, rels, dead, rStale, rAlloc, rWake>>

ReleaseA == \E t \in Tickets :
    /\ sb' = Release(sb, t, GENS)
    /\ IF Valid(sb, t)
       THEN /\ rels' = [rels EXCEPT ![t[1]] = @ + 1]
            /\ dead' = dead \cup {<<t[1], t[2], rels'[t[1]]>>}
            /\ armo' = Without(armo, t[1])
       ELSE UNCHANGED <<rels, dead, armo>>
    /\ rStale' = (rStale /\ ~Valid(sb', t) /\ (~Valid(sb, t) => sb' = sb))
    /\ UNCHANGED <<issued, allocs, hw, rAlloc, rWake, rBaton, oldest>>

Next == AllocA \/ ArmA \/ NotifyA \/ NotifyAllA \/ BatonA \/ ReleaseA
Spec == Init /\ [][Next]_vars

QueueOnce == /\ Distinct(sb.queue)
             /\ \A k \in DOMAIN sb.queue : Has(sb, sb.queue[k])
             /\ \A i \in 0..Len(sb.slots) - 1 : Slot(sb, i).queued <=> i \in Range(sb.queue)
             /\ Len(sb.queue) <= Len(sb.slots)
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
Inv == QueueOnce /\ WakerQueued /\ FreeExact /\ SlabBound /\ GenRange /\ DeadStay
       /\ StaleRight /\ AllocRight /\ WakeRight /\ BatonRight

\* the witnesses: the documented order of the baton (#311), and a stale ticket that names a later future's slot
BatonOldest == oldest
NoStaleHit == \A d \in dead : ~Valid(sb, <<d[1], d[2]>>)
=============================================================================
