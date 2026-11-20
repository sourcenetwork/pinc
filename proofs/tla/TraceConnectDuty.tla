-------------------------- MODULE TraceConnectDuty --------------------------
(***************************************************************************)
(* Trace validation of the beacon schedule and the radio adapter of local  *)
(* discovery: pinc-connect local.rs, Duty and Radio.                       *)
(*                                                                         *)
(* The Rust test tests/trace_connect_duty.rs runs real schedules and       *)
(* radios with seeded calls. A schedule: polls on time, early, late, at    *)
(* the edges of the burst and of the steady gap, with the clock stepping   *)
(* back; restarts in the burst and after it; the mailbox on and off; runs  *)
(* whose clock starts near u64::MAX so that the deadline saturates. It     *)
(* records each call with its time in milliseconds after the run's origin  *)
(* (`top` the time of u64::MAX, -1 when the run stays far from it), the    *)
(* answer, and the deadline and count after it. A radio: frames that fit   *)
(* and do not, admissions before, at and after the off time, duty 0 and    *)
(* over 1000, runs near u64::MAX; each admission with its time in          *)
(* nanoseconds after the origin, its length and the answer. Every call     *)
(* must be the step of ConnectDutyOps.tla (DutyPoll at unit 1000,          *)
(* DutyRestart, DutyMailbox, RadioAdmit), with the same deadline and count *)
(* for a schedule and the same answer for a radio. The test keeps every    *)
(* product len * ns_per_byte * 1000 and every time below 2^31 (TLC's       *)
(* integers), so MAXU, which stands for u64::MAX, is never reached here.   *)
(*                                                                         *)
(* A deadline the code holds as None (past the clock's end, fix C1) is     *)
(* written as -1, the model's Never.                                       *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds connect_duty.ndjson.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, ConnectDutyOps, TraceEnd

VARIABLES i, d, dtop, rd, rtop
vars == <<i, d, dtop, rd, rtop>>

MS == 1000
MAXU == 2147483647

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_duty.ndjson")
Ev0 == Trace[i]

DutyAfter == d'.nx = Ev0.next /\ d'.sent = Ev0.sent

DNew == /\ Ev0.op = "new" /\ d' = DutyNew(Ev0.at) /\ dtop' = Ev0.top
DPoll == LET r == DutyPoll(MS, dtop, d, Ev0.at)
         IN /\ Ev0.op = "poll" /\ r.r = Ev0.r /\ d' = r.d /\ UNCHANGED dtop
DRestart == /\ Ev0.op = "restart" /\ d' = DutyRestart(d, Ev0.at) /\ UNCHANGED dtop
DMailbox == /\ Ev0.op = "mailbox" /\ d' = DutyMailbox(d, Ev0.v) /\ UNCHANGED dtop
DutyEv == /\ Ev0.t = "duty"
          /\ (DNew \/ DPoll \/ DRestart \/ DMailbox)
          /\ DutyAfter
          /\ UNCHANGED <<rd, rtop>>

RNew == /\ Ev0.op = "new" /\ rd' = RadioNew(Ev0.mtu, Ev0.nspb, Ev0.duty) /\ rtop' = Ev0.top
RAdmit == LET r == RadioAdmit(rtop, MAXU, rd, Ev0.at, Ev0.len)
          IN /\ Ev0.op = "admit" /\ r.r = Ev0.r /\ rd' = r.rd /\ UNCHANGED rtop
RadioEv == /\ Ev0.t = "radio"
           /\ (RNew \/ RAdmit)
           /\ UNCHANGED <<d, dtop>>

Init == i = 1 /\ d = DutyNew(0) /\ dtop = -1 /\ rd = RadioNew(0, 0, 0) /\ rtop = -1
Step == /\ i <= Len(Trace)
        /\ (DutyEv \/ RadioEv)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
(* A recorded call that is not the model's step leaves no successor: TLC reports the deadlock at that event. *)
TraceSpec == Init /\ [][TNext]_vars
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
