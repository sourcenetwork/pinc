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
(* The probe timer of the client (client/timers.rs, next_probe, an Option  *)
(* since code commit a7f24632) rides on the same polls: the node starts    *)
(* with a probe due at its start (conn.rs 466); a poll at or after it      *)
(* fires it and arms the next HOME_RETRY_NS (2 s) on without a home or     *)
(* RECORD_REPUBLISH_NS / 30 (60 s) on with one, either at any poll         *)
(* (timers.rs 102-127); a restart is resume (10 ms on, timers.rs 198) or   *)
(* link_changed (NETCHECK_DELAY, 50 ms on, 218), each just before          *)
(* duty.restart. Every one is deadline_after: a deadline at the clock's    *)
(* last instant is kept, one past it is none. On this clock of whole       *)
(* units 10 and 50 ms round up to one unit, which fires at the same polls  *)
(* and is none at the same instants. next_deadline is modelled for a node  *)
(* with relays (without one the probe is not one of its terms) and         *)
(* beacons on. PROBE turns the probe on: without it the probe has no       *)
(* deadline and the state space is that of the beacons alone; its rule     *)
(* only matters at the clock's maximum, where ConnectDuty_sat turns it on. *)
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
(*    there is none (Never: the next one is past the clock's end);         *)
(*  - ProbeRearm (step): after the probe fired its next deadline is later  *)
(*    than now, or there is none;                                          *)
(*  - DeadlineCovers (state): next_deadline (timers.rs 17-37, the probe    *)
(*    and the beacon terms) is some time no later than every armed one,    *)
(*    a probe or beacon deadline at the clock's last instant included.     *)
(* Witnesses: ConnectDuty_w_burst violates BurstNotFull (a burst of 5 is   *)
(* reached, so the bound is tight); ConnectDuty_sat (TOP = T: the clock    *)
(* reaches u64::MAX) checks Rearm at the clock's end: a release there      *)
(* leaves no deadline, so it is the last (C1; before it the deadline       *)
(* saturated to now and every poll released). ConnectDuty_w_probetop       *)
(* violates ProbeNotAtTop: a probe deadline at the clock's last instant    *)
(* is armed and kept, not dropped.                                         *)
(***************************************************************************)
EXTENDS Integers, ConnectDutyOps

CONSTANTS UNIT, TOP, T, STEPS, RS, PROBE
\* a config file takes no negative number: the configs substitute these
NoTop == -1
DutySteps == {-1, 0, 1, 4, 60}

VARIABLES c, d, nb, ls, lr, ev, pr
vars == <<c, d, nb, ls, lr, ev, pr>>

Clamp(t) == IF t < 0 THEN 0 ELSE IF t > T THEN T ELSE t

CeilDiv(a, b) == (a + b - 1) \div b
\* the probe's next gap after it fired: HOME_RETRY_NS without a home, RECORD_REPUBLISH_NS / 30 with one
ProbeGaps == {2 * UNIT, ST(UNIT)}
\* the probe's gap at a restart: resume's 10 ms and link_changed's NETCHECK_DELAY of 50 ms, rounded up to the clock
RestartGaps == {CeilDiv(UNIT, 100), CeilDiv(UNIT, 20)}

Init == /\ c = 0 /\ d = DutyNew(0) /\ nb = 0 /\ ls = -1 /\ lr = -1
        /\ ev = [r |-> FALSE, burst |-> FALSE, p |-> FALSE] /\ pr = IF PROBE THEN 0 ELSE Never

Poll(step) ==
    LET now == Clamp(c + step)
        r == DutyPoll(UNIT, TOP, d, now)
        fired == pr # Never /\ now >= pr
    IN /\ c' = now
       /\ d' = [r.d EXCEPT !.sent = 0]
       /\ nb' = IF r.r /\ r.burst THEN nb + 1 ELSE nb
       /\ ls' = IF r.r /\ ~r.burst THEN now ELSE ls
       /\ lr' = IF r.r THEN now ELSE lr
       /\ ev' = [r |-> r.r, burst |-> r.burst, p |-> fired]
       /\ pr' \in IF fired THEN {ChkAdd(TOP, now, g) : g \in ProbeGaps} ELSE {pr}

Restart == /\ c \in RS
           /\ d' = DutyRestart(d, c)
           /\ nb' = 0 /\ ls' = -1 /\ lr' = -1
           /\ ev' = [r |-> FALSE, burst |-> FALSE, p |-> FALSE]
           /\ IF PROBE THEN \E g \in RestartGaps : pr' = ChkAdd(TOP, c, g) ELSE pr' = pr
           /\ UNCHANGED c

Mailbox(v) == /\ d' = DutyMailbox(d, v)
              /\ ev' = [r |-> FALSE, burst |-> FALSE, p |-> FALSE]
              /\ UNCHANGED <<c, nb, ls, lr, pr>>

Next == (\E s \in STEPS : Poll(s)) \/ Restart \/ (\E v \in BOOLEAN : Mailbox(v))
Spec == Init /\ [][Next]_vars

\* only a poll that released sets r
Released == ev'.r

BurstBound == nb <= BU(UNIT) \div BG(UNIT)
BurstGap == [][(Released /\ lr >= 0) => c' - lr >= BG(UNIT)]_vars
SteadyGap == [][(Released /\ ~ev'.burst /\ ls >= 0) => c' - ls >= ST(UNIT)]_vars
QuietWithMailbox == [][(Released /\ ~ev'.burst) => ~d.mb]_vars
Rearm == [][Released => d'.nx = Never \/ d'.nx > c']_vars
ProbeRearm == [][ev'.p => pr' = Never \/ pr' > c']_vars

\* next_deadline as the code folds it: none, then the soonest of each term that is some
Soonest(t, x) == IF x = Never THEN t ELSE IF t = Never \/ x < t THEN x ELSE t
NextDeadline == Soonest(Soonest(Never, pr), d.nx)
DeadlineCovers == \A x \in {pr, d.nx} : x # Never => NextDeadline # Never /\ NextDeadline <= x

\* the reachability witness: a full burst
BurstNotFull == nb < BU(UNIT) \div BG(UNIT)
\* the reachability witness: a probe deadline at the clock's last instant is armed
ProbeNotAtTop == pr # TOP
=============================================================================
