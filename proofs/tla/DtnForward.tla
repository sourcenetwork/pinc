------------------------------ MODULE DtnForward ------------------------------
(***************************************************************************)
(* One node of vinc-dtn forward.rs: binary spray-and-wait with a copy      *)
(* budget and link-aware retransmission timers. The operators are those of *)
(* DtnForwardOps.tla (Forwarder::step and poll, step for step); this spec *)
(* drives them with every input at every time and adds ghost variables     *)
(* that the code does not have, only to state the properties:              *)
(*   rcv[id]  the copies the node received with the Hold of id (0 if none) *)
(*   gs[i]    the number of sends of the transfer in slot i                *)
(*   gone     the ids released as delivered or expired                     *)
(*   lab      what the last action was                                     *)
(*                                                                         *)
(* Checked (invariants and action properties, every config):               *)
(*  - Balance: copies held + copies handed = copies received, for every    *)
(*    held bundle (copies are conserved, never duplicated; a repeated hold *)
(*    changes nothing, so the extra copies are lost, never added);         *)
(*    a held bundle keeps at least one copy; copies held never grow except *)
(*    at the first Hold; handed copies are never taken back (given and     *)
(*    peer of a transfer never change).                                    *)
(*  - Spray: a send to a non-destination hands exactly copies / 2 (the    *)
(*    holder keeps the rest, at least one), a send to the destination is a *)
(*    delivery with 0 copies; one transfer per (bundle, peer).             *)
(*  - Timers: the time charged to a running timer is exactly the elapsed   *)
(*    time when its link was up and 0 when it was down (the link state of *)
(*    the step before the input); time never runs backwards.              *)
(*  - Expiry: a delivered or expired bundle is released first, whatever   *)
(*    the links, and only such a bundle (or a Forget) leaves the table.   *)
(*  - Give-up: a transfer is sent max(1, MaxSends) times in all at most,   *)
(*    and gives up only then, with its timer out and its link up.        *)
(*  - Quiet: when poll has nothing to do, every bundle held with the      *)
(*    destination's link up has a transfer to it or the transfer table is *)
(*    full (the exact condition under which the destination is not served *)
(*    at once).                                                           *)
(* Liveness (config DtnForward_live): with room in the tables and the     *)
(* destination's link up, the delivery send happens.                      *)
(* Witness (config DtnForward_rehold): a bundle released as delivered can  *)
(* be held again with fresh copies, so a late duplicate of the hold        *)
(* re-creates copies the budget already counted (see DtnForwardNet).      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS B, L, T, Retry, MaxSends, NI, NP, MaxTime, CopyVals, ExpVals, Live

VARIABLES f, rcv, gs, gone, lab
vars == <<f, rcv, gs, gone, lab>>
View == <<f, rcv, gs>>
ViewG == <<f, rcv, gs, gone>>

F == INSTANCE DtnForwardOps

Ids == 1..NI
Peers == 1..NP

Inputs == {[k |-> "tick"]}
    \cup [k : {"hold"}, id : Ids, dest : Peers, exp : ExpVals, copies : CopyVals \cup {0}]
    \cup [k : {"up", "down"}, peer : Peers]
    \cup [k : {"ack"}, peer : Peers, id : Ids]
    \cup [k : {"forget"}, id : Ids]

Init == /\ f = F!New(0)
        /\ rcv = [i \in Ids |-> 0]
        /\ gs = [i \in 1..T |-> 0]
        /\ gone = {}
        /\ lab = [t |-> "init"]

GsAfter(g, act, old) ==
    [i \in 1..T |-> IF ~g.ts[i].full THEN 0
                    ELSE IF act.k = "send" /\ act.slot = i THEN (IF act.retr THEN old[i] + 1 ELSE 1) ELSE old[i]]

StepA == \E now \in 0..MaxTime, inp \in Inputs :
    LET r == F!Step(f, now, inp) IN
    /\ (Live = 0 \/ inp.k \in {"tick", "up"} \/ (inp.k = "hold" /\ inp.dest = NP))
    /\ f' = r.f
    /\ rcv' = IF inp.k = "hold" /\ r.err = "ok" THEN [rcv EXCEPT ![inp.id] = inp.copies]
              ELSE IF inp.k = "forget" /\ r.err = "ok" THEN [rcv EXCEPT ![inp.id] = 0] ELSE rcv
    /\ gs' = GsAfter(r.f, F!NoAct, gs)
    /\ gone' = gone
    /\ lab' = [t |-> "step", now |-> now, inp |-> inp, err |-> r.err]

PollA == LET r == F!Poll(f) IN
    /\ (r.f # f \/ r.act.k # "none")
    /\ f' = r.f
    /\ rcv' = IF r.act.k = "release" THEN [rcv EXCEPT ![r.act.bundle] = 0] ELSE rcv
    /\ gs' = GsAfter(r.f, r.act, gs)
    /\ gone' = IF r.act.k = "release" THEN gone \cup {r.act.bundle} ELSE gone
    /\ lab' = [t |-> "poll", act |-> r.act]

Next == StepA \/ PollA
Spec == Init /\ [][Next]_vars
LiveSpec == Spec /\ WF_vars(PollA)

\* ------------------------------ invariants ---------------------------------
Wf == /\ \A i \in 1..B : f.bs[i].full => f.bs[i].copies >= 1
      /\ \A i, j \in 1..B : (i # j /\ f.bs[i].full /\ f.bs[j].full) => f.bs[i].id # f.bs[j].id
      /\ \A i, j \in 1..L : (i # j /\ f.ls[i].full /\ f.ls[j].full) => f.ls[i].peer # f.ls[j].peer
      /\ \A i, j \in 1..T : (i # j /\ f.ts[i].full /\ f.ts[j].full) =>
             (f.ts[i].bundle # f.ts[j].bundle \/ f.ts[i].peer # f.ts[j].peer)
      /\ \A i \in 1..T : f.ts[i].full =>
             /\ F!HasB(f, f.ts[i].bundle)
             /\ LET bu == f.bs[F!MinOf(F!BIdx(f, f.ts[i].bundle))] IN
                  IF f.ts[i].deliver THEN f.ts[i].given = 0 /\ f.ts[i].peer = bu.dest
                  ELSE f.ts[i].given >= 1 /\ f.ts[i].peer # bu.dest
\* transfers are only created by poll_spray, whose bundle exists: "transfers reference live bundles" is in Wf

Balance == \A id \in Ids : IF F!HasB(f, id) THEN F!CopiesHeld(f, id) + F!Handed(f, id) = rcv[id]
                           ELSE rcv[id] = 0 /\ F!Handed(f, id) = 0

KeepsOne == \A i \in 1..B : f.bs[i].full => f.bs[i].copies >= 1

SendsExact == \A i \in 1..T : f.ts[i].full =>
                  /\ f.ts[i].sends = gs[i]
                  /\ gs[i] >= 1 /\ gs[i] <= F!Max2(1, MaxSends)
                  /\ (f.ts[i].ph = "gaveup" => gs[i] = F!Max2(1, MaxSends))
                  /\ (f.ts[i].ph = "sent" => f.ts[i].rem <= Retry)

\* ------------------------------ action properties --------------------------
SameTransfer(i) == /\ f.ts[i].full /\ f'.ts[i].full
                   /\ f'.ts[i].bundle = f.ts[i].bundle /\ f'.ts[i].peer = f.ts[i].peer

Kept == \A i \in 1..T : SameTransfer(i) =>
            /\ f'.ts[i].given = f.ts[i].given /\ f'.ts[i].deliver = f.ts[i].deliver
            /\ (f.ts[i].ph = "acked" => f'.ts[i].ph = "acked")
            /\ (f.ts[i].ph = "gaveup" => f'.ts[i].ph \in {"gaveup", "acked"})
            /\ f'.ts[i].sends >= f.ts[i].sends

HeldNeverGrows == \A id \in Ids : F!HasB(f, id) => F!CopiesHeld(f', id) <= F!CopiesHeld(f, id)

\* an id leaves the table only by Forget or as a delivered / expired release
LeavesOnlyDone == \A id \in Ids : (F!HasB(f, id) /\ ~F!HasB(f', id)) =>
    \/ (lab'.t = "step" /\ lab'.inp.k = "forget" /\ lab'.err = "ok")
    \/ (lab'.t = "poll" /\ lab'.act.k = "release" /\ lab'.act.bundle = id
        /\ \E i \in F!BIdx(f, id) : f.bs[i].delivered \/ f.bs[i].exp <= f.now)

TimeMonotone == f'.now = IF lab'.t = "step" THEN F!Max2(f.now, lab'.now) ELSE f.now

\* the time charged to a running timer: the elapsed time if its link was up, nothing if it was down
TimersExact == (lab'.t = "step") => \A i \in 1..T :
    (SameTransfer(i) /\ f.ts[i].ph = "sent" /\ f'.ts[i].ph = "sent") =>
        f'.ts[i].rem = IF F!Up(f, f.ts[i].peer) THEN F!Mon(f.ts[i].rem, F!Mon(lab'.now, f.now)) ELSE f.ts[i].rem

TimersFrozenDown == (lab'.t = "step") => \A i \in 1..T :
    (SameTransfer(i) /\ f.ts[i].ph = "sent" /\ ~F!Up(f, f.ts[i].peer)) => f'.ts[i].rem = f.ts[i].rem

PollActs == (lab'.t = "poll") =>
    LET a == lab'.act IN
    /\ (F!DoneSet(f) # {} => a.k = "release")
    /\ (a.k = "release" => F!DoneSet(f) # {})
    /\ (a.k = "send" /\ a.retr =>
          /\ F!DoneSet(f) = {}
          /\ f.ts[a.slot].ph = "sent" /\ f.ts[a.slot].rem = 0 /\ F!Up(f, a.peer) /\ f.ts[a.slot].sends < MaxSends
          /\ a.copies = f.ts[a.slot].given /\ f'.ts[a.slot].rem = Retry
          /\ f'.bs = f.bs)
    /\ (a.k = "send" /\ ~a.retr =>
          /\ F!DoneSet(f) = {} /\ F!RetrSet(f) = {}
          /\ F!Up(f, a.peer) /\ F!TIdx(f, a.bundle, a.peer) = {} /\ F!TIdx(f', a.bundle, a.peer) # {}
          /\ LET bu == f.bs[F!MinOf(F!BIdx(f, a.bundle))] IN
               IF a.peer = bu.dest
               THEN a.copies = 0 /\ F!CopiesHeld(f', a.bundle) = bu.copies
               ELSE a.copies = bu.copies \div 2 /\ a.copies >= 1
                    /\ F!CopiesHeld(f', a.bundle) = bu.copies - a.copies /\ F!CopiesHeld(f', a.bundle) >= 1)
    /\ (a.k = "none" => f'.bs = f.bs)

\* the destination is served unless the transfer table is full; nothing else is left to do when poll is quiet
QuietSound == (lab'.t = "poll" /\ lab'.act.k = "none") =>
    \A li \in 1..L, bi \in 1..B :
        (f'.ls[li].full /\ f'.ls[li].up /\ f'.bs[bi].full) =>
            \/ F!TIdx(f', f'.bs[bi].id, f'.ls[li].peer) # {}
            \/ F!FreeT(f') = {}
            \/ (f'.ls[li].peer # f'.bs[bi].dest /\ f'.bs[bi].copies \div 2 = 0)

\* a transfer gives up only with the timer out, the link up and the sends used
GiveUpOnly == \A i \in 1..T : (SameTransfer(i) /\ f.ts[i].ph = "sent" /\ f'.ts[i].ph = "gaveup") =>
    f.ts[i].rem = 0 /\ F!Up(f, f.ts[i].peer) /\ f.ts[i].sends >= MaxSends

\* a refused step input leaves exactly the advanced state: in particular a repeated hold adds nothing
RefusedKeeps == (lab'.t = "step" /\ lab'.err # "ok") => f' = F!Advance(f, lab'.now)

A_QuietSound == [][QuietSound]_vars
A_Kept == [][Kept]_vars
A_HeldNeverGrows == [][HeldNeverGrows]_vars
A_LeavesOnlyDone == [][LeavesOnlyDone]_vars
A_TimeMonotone == [][TimeMonotone]_vars
A_TimersExact == [][TimersExact]_vars
A_TimersFrozenDown == [][TimersFrozenDown]_vars
A_PollActs == [][PollActs]_vars
A_GiveUpOnly == [][GiveUpOnly]_vars
A_RefusedKeeps == [][RefusedKeeps]_vars

\* ------------------------------ the witness --------------------------------
\* NoReHold is violated: a bundle released as delivered or expired is held again with fresh copies
A_NoReHold == [][(lab'.t = "step" /\ lab'.inp.k = "hold" /\ lab'.err = "ok") => ~(lab'.inp.id \in gone)]_vars

\* ------------------------------ liveness ------------------------------------
\* with the destination's link up and a free transfer slot, a held bundle gets its delivery send
DestOf(id) == f.bs[F!MinOf(F!BIdx(f, id))].dest
Ready(id) == F!HasB(f, id) /\ F!DoneSet(f) = {} /\ F!Up(f, DestOf(id)) /\ F!TIdx(f, id, DestOf(id)) = {}
Served == \A id \in Ids : [](Ready(id) => <>(F!TIdx(f, id, DestOf(id)) # {} \/ ~F!HasB(f, id)))
=============================================================================
