----------------------------- MODULE ConnectDutyOps -----------------------------
(***************************************************************************)
(* The beacon schedule and the radio adapter of local discovery            *)
(* (pinc-connect local.rs, Duty and Radio) as pure operators. ConnectDuty  *)
(* and ConnectRadio (the model checks) and TraceConnectDuty (the trace     *)
(* validation) use them.                                                   *)
(*                                                                         *)
(* Time. The code counts nanoseconds in a u64 and saturates at u64::MAX.   *)
(* Here a time t stands for origin + t * unit nanoseconds, where every     *)
(* constant of the schedule is a whole number of units (BURST_GAP = 1 s,   *)
(* BURST = 5 s, STEADY_GAP = 60 s): u is the unit in the code's units of a *)
(* second (1 in the model checks, 1000 in the trace, which counts          *)
(* milliseconds). top is the t at which origin + t * unit is u64::MAX, or  *)
(* -1 when no time of the run comes near it; then every saturating         *)
(* addition is the plain one. Comparisons and differences of times are     *)
(* the same in t as in nanoseconds. The radio counts in nanoseconds        *)
(* (unit 1), and maxu stands for u64::MAX in its products.                 *)
(*                                                                         *)
(* Deadlines follow the clock rule of the decided fix (pinc-transport      *)
(* `deadline_after`, a checked add): a deadline past the clock's last      *)
(* instant is Never (the code's None), which never fires; top itself is a  *)
(* valid deadline. Products and differences still saturate.                *)
(***************************************************************************)
EXTENDS Integers

BG(u) == u          \* BURST_GAP
BU(u) == 5 * u      \* BURST
ST(u) == 60 * u     \* STEADY_GAP

\* a deadline that is not there (Option::None): below every time, so it is tested before any compare
Never == -1
\* deadline_after(a, b) = a.checked_add(b): Never past the clock's last instant
ChkAdd(top, a, b) == IF top >= 0 /\ a + b > top THEN Never ELSE a + b
SatSub(a, b) == IF a < b THEN 0 ELSE a - b
SatMul(maxu, a, b) == IF a * b > maxu THEN maxu ELSE a * b

(* Duty::new *)
DutyNew(now) == [b |-> now, nx |-> now, sent |-> 0, mb |-> FALSE]
(* Duty::restart *)
DutyRestart(d, now) == [d EXCEPT !.b = now, !.nx = now]
(* Duty::set_mailbox *)
DutyMailbox(d, v) == [d EXCEPT !.mb = v]

(* Duty::poll: r the answer, burst whether `now` was in the burst *)
DutyPoll(u, top, d, now) ==
    IF d.nx = Never \/ now < d.nx THEN [d |-> d, r |-> FALSE, burst |-> FALSE]
    ELSE LET inb == SatSub(now, d.b) < BU(u)
         IN IF ~inb /\ d.mb THEN [d |-> [d EXCEPT !.nx = ChkAdd(top, now, ST(u))], r |-> FALSE, burst |-> FALSE]
            ELSE LET after == ChkAdd(top, now, BG(u))
                 IN [d |-> [d EXCEPT !.sent = d.sent + 1,
                                     !.nx = IF after # Never /\ SatSub(after, d.b) < BU(u) THEN after
                                             ELSE ChkAdd(top, now, ST(u))],
                     r |-> TRUE, burst |-> inb]

(* Radio::new: ready_at 0, below every time of the run *)
RadioNew(mtu, nspb, duty) == [mtu |-> mtu, nspb |-> nspb, duty |-> duty, ready |-> 0]

(* Radio::admit: r the answer; off the off time it charged and exact the off time without saturation *)
RadioAdmit(top, maxu, rd, now, len) ==
    IF len > rd.mtu \/ rd.ready = Never \/ now < rd.ready \/ rd.duty = 0 THEN [rd |-> rd, r |-> FALSE, exact |-> 0]
    ELSE LET air == SatMul(maxu, len, rd.nspb)
             off == SatMul(maxu, air, 1000) \div rd.duty
         IN [rd |-> [rd EXCEPT !.ready = ChkAdd(top, now, off)], r |-> TRUE, exact |-> (len * rd.nspb * 1000) \div rd.duty]
=============================================================================
