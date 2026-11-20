------------------------------ MODULE ConnectDuty ------------------------------
(***************************************************************************)
(* Model check of the beacon schedule: pinc-connect local.rs, Duty (new,   *)
(* restart, set_mailbox, poll, deadline), over every interleaving of polls *)
(* at clock steps in STEPS (a step back included), restarts at the clock   *)
(* values in RS and mailbox changes, on a clock of 0..T units of one       *)
(* second (the code's BURST_GAP is 1 s, BURST 5 s, STEADY_GAP 60 s; T     *)
(* reaches two steady beacons after a burst that starts at 0, at 64 and    *)
(* 124; RS bounds the restarts because the schedule depends only on the    *)
(* clock relative to the last one, and every restart time would multiply   *)
(* the states). TOP is the clock's maximum (u64::MAX), -1 when             *)
(* the clock never reaches it (ConnectDutyOps.tla has the time scale).     *)
(* The count `sent` is reset to 0 after each step to keep the state space  *)
(* small; the trace checks it.                                             *)
(*                                                                         *)
(* Checked (the module doc of local.rs: "at most BURST / BURST_GAP beacons *)
(* in a burst and one per STEADY_GAP after it", "not at all in the steady  *)
(* phase while a mailbox serves the node"; the doc of poll: "returns true  *)
(* once per release and schedules the next"):                             *)
(*  - BurstBound (state): at most BURST / BURST_GAP = 5 releases in the    *)
(*    burst since the last start or restart;                               *)
(*  - BurstGap (step): releases at least BURST_GAP apart;                  *)
(*  - SteadyGap (step): two releases after the burst at least STEADY_GAP   *)
(*    apart;                                                               *)
(*  - QuietWithMailbox (step): no release after the burst while a mailbox  *)
(*    serves the node;                                                     *)
(*  - Rearm (step): after a release the deadline is later than now, or     *)
(*    there is none (Never: the next one is past the clock's end).         *)
(* Witnesses: ConnectDuty_w_burst violates BurstNotFull (a burst of 5 is   *)
(* reached, so the bound is tight); ConnectDuty_sat (TOP = T: the clock    *)
(* reaches u64::MAX) checks Rearm at the clock's end: a release there      *)
(* leaves no deadline, so it is the last (C1; before it the deadline       *)
(* saturated to now and every poll released).                              *)
(***************************************************************************)
EXTENDS Integers, ConnectDutyOps

CONSTANTS UNIT, TOP, T, STEPS, RS
\* a config file takes no negative number: the configs substitute these
NoTop == -1
DutySteps == {-1, 0, 1, 4, 60}

VARIABLES c, d, nb, ls, lr, ev
vars == <<c, d, nb, ls, lr, ev>>

Clamp(t) == IF t < 0 THEN 0 ELSE IF t > T THEN T ELSE t

Init == /\ c = 0 /\ d = DutyNew(0) /\ nb = 0 /\ ls = -1 /\ lr = -1
        /\ ev = [r |-> FALSE, burst |-> FALSE]

Poll(step) ==
    LET now == Clamp(c + step)
        r == DutyPoll(UNIT, TOP, d, now)
    IN /\ c' = now
       /\ d' = [r.d EXCEPT !.sent = 0]
       /\ nb' = IF r.r /\ r.burst THEN nb + 1 ELSE nb
       /\ ls' = IF r.r /\ ~r.burst THEN now ELSE ls
       /\ lr' = IF r.r THEN now ELSE lr
       /\ ev' = [r |-> r.r, burst |-> r.burst]

Restart == /\ c \in RS
           /\ d' = DutyRestart(d, c)
           /\ nb' = 0 /\ ls' = -1 /\ lr' = -1
           /\ ev' = [r |-> FALSE, burst |-> FALSE]
           /\ UNCHANGED c

Mailbox(v) == /\ d' = DutyMailbox(d, v)
              /\ ev' = [r |-> FALSE, burst |-> FALSE]
              /\ UNCHANGED <<c, nb, ls, lr>>

Next == (\E s \in STEPS : Poll(s)) \/ Restart \/ (\E v \in BOOLEAN : Mailbox(v))
Spec == Init /\ [][Next]_vars

\* only a poll that released sets r
Released == ev'.r

BurstBound == nb <= BU(UNIT) \div BG(UNIT)
BurstGap == [][(Released /\ lr >= 0) => c' - lr >= BG(UNIT)]_vars
SteadyGap == [][(Released /\ ~ev'.burst /\ ls >= 0) => c' - ls >= ST(UNIT)]_vars
QuietWithMailbox == [][(Released /\ ~ev'.burst) => ~d.mb]_vars
Rearm == [][Released => d'.nx = Never \/ d'.nx > c']_vars

\* the reachability witness: a full burst
BurstNotFull == nb < BU(UNIT) \div BG(UNIT)
=============================================================================
