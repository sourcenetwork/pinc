------------------------------ MODULE FacadeTurn ------------------------------
(***************************************************************************)
(* The drive's turn (crates/pinc/src/drive.rs: Shared::run_as and the      *)
(* guard Turn with its Drop) over the slab of standby.rs (StandbyOps.tla): *)
(* how the futures of the facade take, hold and hand on the driving role,  *)
(* and what the driver reads from the host. The futures F are numbered     *)
(* from 1; a future's waker is its number.                                 *)
(*                                                                         *)
(* A future is off (not started, or ended), run (woken: the executor will  *)
(* poll it), wait (its poll returned Pending) or flush (it is sending what *)
(* the endpoint wants sent, after an Io step or before it returns). One    *)
(* poll (PollIo, PollDone, PollWait) is one call of the poll function of   *)
(* run_as, done in one borrow of the core except the host's I/O, which     *)
(* only the driver touches:                                                *)
(*  - PollIo: the core served something, or the attempt queued packets, so *)
(*    the future flushes and polls again; nothing is registered;           *)
(*  - PollDone: the attempt finished; the future flushes and returns,      *)
(*    which drops its guard;                                               *)
(*  - PollWait: the attempt waits; the future's ticket (allocated at its   *)
(*    first wait) is armed with its waker, and it takes the role if it may *)
(*    (ROLE: only OWNER, the future of Endpoint::run, may) and the flag is *)
(*    free. A driver then reads what the host has ready, at most DRAIN     *)
(*    datagrams, handing each to the core, and ends in Io (flush, then     *)
(*    poll again) if anything moved, else in Pending.                      *)
(* Drop is the guard's Drop, when the future returns or the host drops it: *)
(* a driver clears the flag; the ticket is released; a driver, or (PASS)   *)
(* any future that ends while the flag is free, passes the baton. The      *)
(* environment notifies tickets (an event for a wait, kick, wake_driver),  *)
(* wakes every armed ticket (an event the endpoint dropped), delivers      *)
(* datagrams and fires the driver's sleep.                                 *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - at most one future holds the role, exactly when the flag is set; the *)
(*    core's driver ticket is its ticket; with ROLE only OWNER drives      *)
(*    (OneDriver);                                                         *)
(*  - a future holds a ticket only while it runs, every ticket held names  *)
(*    a live slot of its generation (no stale ticket is ever used), no two *)
(*    futures share a slot, and the live slots are exactly the slots held, *)
(*    so each is released once, by the future that took it (TicketsLive); *)
(*  - a slot keeps only its holder's waker, and a waiting future's waker   *)
(*    is kept (WakerOwner, WaitArmed);                                     *)
(*  - the slab's own invariants (QueueOnce: StandbyOps' QueueLive and      *)
(*    QueueExact, so the live entries of the queue are exactly the tickets *)
(*    of the queued slots, once each, and the queue holds at most twice as *)
(*    many entries as the slab has slots; WakerQueued, FreeExact,          *)
(*    SlabBound: the slab is as long as the most futures that held a       *)
(*    ticket at once). A slot's generation goes round within the bound,    *)
(*    and the release that brings it round drops every stale entry (the    *)
(*    fix of #419), so the stale entry of its old ticket is gone before    *)
(*    the slot is taken at that generation again: FacadeTurn_wrap (GENS =  *)
(*    5, more than twice the slab, where a compaction drops it first) and  *)
(*    FacadeTurn_wrapfew (GENS = 3, not more than twice the slab);         *)
(*  - every datagram the host delivered is either still with the host or   *)
(*    was handed to the core, exactly once and in order (FedExact), and a  *)
(*    poll reads at most DRAIN (DrainBound);                               *)
(*  - while the flag is free and a future that may drive waits, some       *)
(*    future that may drive and holds a ticket is running or flushing      *)
(*    (RoleOffered): the role is never left with nobody to take it;        *)
(*  - under fairness (the host's executor polls every woken future, an     *)
(*    attempt does not end in Io forever, a flush finishes), a free role   *)
(*    with a future waiting is taken, or nobody waits any more (RoleTaken, *)
(*    FacadeTurn_live).                                                    *)
(* Witnesses: FacadeTurn_nopass (a future that ends while the flag is free *)
(* does not pass the baton on: the one it was offered to is dropped and a  *)
(* waiting future is stranded, RoleOffered fails); FacadeTurn_drain (a     *)
(* poll stops at DRAIN with datagrams still waiting at the host);          *)
(* FacadeTurn_wrapkeep (the release before the fix of #419, DROP = FALSE,  *)
(* with GENS = 3: a slot is taken at the generation of a stale entry       *)
(* before the queue is long enough to compact it, and QueueOnce fails).    *)
(* Assumed of the host (#246 (c)): its executor polls every woken future;  *)
(* a dropped receive future loses no datagram; sleep(at) does not finish   *)
(* before at; every future runs on the thread that built the endpoint, so  *)
(* a poll is one step and no borrow of the core is held across an await.   *)
(* Lean counterpart: proofs/lean/Pinc/FacadeTurn.lean.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS F, OWNER, ROLE, DRAIN, DMAX, STARTS, GENS, PASS,
          DROP   \* the release of the code (TRUE) or the release before the fix of #419 (FALSE)
VARIABLES sb, st, tk, drv, flag, driver, sock, fed, arrived, starts, done, took, hw
vars == <<sb, st, tk, drv, flag, driver, sock, fed, arrived, starts, done, took, hw>>

INSTANCE StandbyOps

NoTicket == <<>>
CanDrive(f) == ~ROLE \/ f = OWNER
Rel(s, t) == IF DROP THEN Release(s, t, GENS) ELSE ReleaseKeep(s, t, GENS)
Max(a, b) == IF a > b THEN a ELSE b

Init == /\ sb = Sb0 /\ st = [f \in F |-> "off"] /\ tk = [f \in F |-> NoTicket] /\ drv = [f \in F |-> FALSE]
        /\ flag = FALSE /\ driver = NoTicket /\ sock = <<>> /\ fed = <<>> /\ arrived = 0
        /\ starts = [f \in F |-> 0] /\ done = [f \in F |-> FALSE] /\ took = 0 /\ hw = 0

\* the wakers ws are woken: a future that waits is polled again; one running or flushing already stays as it is
Wake(s, ws) == [f \in F |-> IF s[f] = "wait" /\ f \in Range(ws) THEN "run" ELSE s[f]]
\* the driver's own host futures (its receive, its sleep) wake it
HostWoken(s) == [f \in F |-> IF drv[f] /\ s[f] = "wait" THEN "run" ELSE s[f]]

\* the burst: up to drain turns of the loop, each taking one datagram the host has ready, stopping at the first that
\* is not
RECURSIVE Burst(_, _, _)
Burst(n, ready, drain) == IF n = drain \/ ready = 0 THEN 0 ELSE 1 + Burst(n + 1, ready - 1, drain)

Start(f) ==
    /\ st[f] = "off" /\ starts[f] < STARTS
    /\ st' = [st EXCEPT ![f] = "run"] /\ starts' = [starts EXCEPT ![f] = @ + 1] /\ done' = [done EXCEPT ![f] = FALSE]
    /\ took' = 0
    /\ UNCHANGED <<sb, tk, drv, flag, driver, sock, fed, arrived, hw>>

PollIo(f) ==
    /\ st[f] = "run" /\ st' = [st EXCEPT ![f] = "flush"] /\ took' = 0
    /\ UNCHANGED <<sb, tk, drv, flag, driver, sock, fed, arrived, starts, done, hw>>

PollDone(f) ==
    /\ st[f] = "run" /\ st' = [st EXCEPT ![f] = "flush"] /\ done' = [done EXCEPT ![f] = TRUE] /\ took' = 0
    /\ UNCHANGED <<sb, tk, drv, flag, driver, sock, fed, arrived, starts, hw>>

PollWait(f) ==
    /\ st[f] = "run"
    /\ LET a == IF tk[f] = NoTicket THEN Alloc(sb) ELSE [t |-> tk[f], s |-> sb]
           s1 == Arm(a.s, a.t, f)
           take == ~drv[f] /\ CanDrive(f) /\ ~flag
           driving == drv[f] \/ take
       IN /\ sb' = s1
          /\ tk' = [tk EXCEPT ![f] = a.t]
          /\ drv' = [drv EXCEPT ![f] = driving]
          /\ flag' = (flag \/ take)
          /\ driver' = IF take THEN a.t ELSE driver
          /\ hw' = Max(hw, Cardinality(Lives(s1)))
          /\ IF ~driving
             THEN /\ st' = [st EXCEPT ![f] = "wait"] /\ took' = 0
                  /\ UNCHANGED <<sock, fed>>
             ELSE \E ready \in 0..Len(sock), moved \in BOOLEAN :
                    LET k == Burst(0, ready, DRAIN)
                    IN /\ fed' = fed \o SubSeq(sock, 1, k)
                       /\ sock' = SubSeq(sock, k + 1, Len(sock))
                       /\ took' = k
                       /\ st' = [st EXCEPT ![f] = IF k > 0 \/ moved THEN "flush" ELSE "wait"]
    /\ UNCHANGED <<arrived, starts, done>>

\* the guard's Drop
Ended(f) ==
    IF tk[f] = NoTicket
    THEN /\ st' = [st EXCEPT ![f] = "off"]
         /\ UNCHANGED <<sb, tk, drv, flag, driver>>
    ELSE LET flag1 == IF drv[f] THEN FALSE ELSE flag
             s1 == Rel(sb, tk[f])
             b == IF drv[f] \/ (PASS /\ ~flag1) THEN Baton(s1) ELSE [w |-> <<>>, s |-> s1]
         IN /\ sb' = b.s /\ flag' = flag1
            /\ driver' = IF drv[f] THEN NoTicket ELSE driver
            /\ st' = [Wake(st, b.w) EXCEPT ![f] = "off"]
            /\ tk' = [tk EXCEPT ![f] = NoTicket]
            /\ drv' = [drv EXCEPT ![f] = FALSE]

\* the flush ends: the future polls again, or returns
Flush(f) ==
    /\ st[f] = "flush"
    /\ IF done[f] THEN Ended(f) ELSE st' = [st EXCEPT ![f] = "run"] /\ UNCHANGED <<sb, tk, drv, flag, driver>>
    /\ took' = 0
    /\ UNCHANGED <<sock, fed, arrived, starts, done, hw>>

\* the host drops the future
Drop(f) ==
    /\ st[f] \in {"run", "wait", "flush"} /\ Ended(f) /\ took' = 0
    /\ UNCHANGED <<sock, fed, arrived, starts, done, hw>>

NotifyE(f) ==
    /\ tk[f] # NoTicket
    /\ LET x == Notify(sb, tk[f]) IN sb' = x.s /\ st' = Wake(st, x.w)
    /\ took' = 0
    /\ UNCHANGED <<tk, drv, flag, driver, sock, fed, arrived, starts, done, hw>>

NotifyAllE ==
    /\ LET x == NotifyAll(sb) IN sb' = x.s /\ st' = Wake(st, x.w)
    /\ took' = 0
    /\ UNCHANGED <<tk, drv, flag, driver, sock, fed, arrived, starts, done, hw>>

Arrive ==
    /\ arrived < DMAX /\ arrived' = arrived + 1 /\ sock' = Append(sock, arrived + 1) /\ st' = HostWoken(st)
    /\ took' = 0
    /\ UNCHANGED <<sb, tk, drv, flag, driver, fed, starts, done, hw>>

HostWake ==
    /\ st' = HostWoken(st) /\ st' # st /\ took' = 0
    /\ UNCHANGED <<sb, tk, drv, flag, driver, sock, fed, arrived, starts, done, hw>>

Next == \/ \E f \in F : Start(f) \/ PollIo(f) \/ PollDone(f) \/ PollWait(f) \/ Flush(f) \/ Drop(f) \/ NotifyE(f)
        \/ NotifyAllE \/ Arrive \/ HostWake
Spec == Init /\ [][Next]_vars
Fairness == \A f \in F : SF_vars(PollWait(f) \/ PollDone(f)) /\ WF_vars(Flush(f))
LSpec == Spec /\ Fairness

Held == {f \in F : tk[f] # NoTicket}
OneDriver == /\ \A f, g \in F : drv[f] /\ drv[g] => f = g
             /\ flag <=> \E f \in F : drv[f]
             /\ \A f \in F : drv[f] => CanDrive(f) /\ tk[f] # NoTicket /\ driver = tk[f]
             /\ ~flag => driver = NoTicket
TicketsLive == /\ \A f \in F : st[f] = "off" => tk[f] = NoTicket /\ ~drv[f]
               /\ \A f \in Held : Valid(sb, tk[f])
               /\ \A f, g \in Held : tk[f][1] = tk[g][1] => f = g
               /\ Lives(sb) = {tk[f][1] : f \in Held}
WakerOwner == \A i \in 0..Len(sb.slots) - 1 :
                  Slot(sb, i).waker # 0 => Slot(sb, i).waker \in Held /\ tk[Slot(sb, i).waker][1] = i
WaitArmed == \A f \in F : st[f] = "wait" => f \in Held /\ Slot(sb, tk[f][1]).waker = f
QueueOnce == QueueLive(sb) /\ QueueExact(sb)
WakerQueued == \A i \in 0..Len(sb.slots) - 1 : Slot(sb, i).waker # 0 => Slot(sb, i).live /\ Slot(sb, i).queued
FreeExact == /\ Distinct(sb.free)
             /\ Range(sb.free) = {i \in 0..Len(sb.slots) - 1 : ~Slot(sb, i).live}
SlabBound == Len(sb.slots) = hw
FedExact == fed \o sock = [j \in 1..arrived |-> j]
DrainBound == took <= DRAIN
WaitAny == \E f \in F : st[f] = "wait" /\ CanDrive(f)
RoleOffered == (~flag /\ WaitAny) => \E g \in Held : st[g] \in {"run", "flush"} /\ CanDrive(g)
Inv == OneDriver /\ TicketsLive /\ WakerOwner /\ WaitArmed /\ QueueOnce /\ WakerQueued /\ FreeExact /\ SlabBound
       /\ FedExact /\ DrainBound /\ RoleOffered

RoleTaken == (~flag /\ WaitAny) ~> (flag \/ ~WaitAny)

\* a reachability witness: a poll stops at DRAIN with datagrams still at the host
NotCut == ~(took = DRAIN /\ sock # <<>>)
=============================================================================
