-------------------------- MODULE FacadeRoleClockOps --------------------------
(***************************************************************************)
(* The relay clock of an Endpoint that carries the relay role, step for   *)
(* step: crates/pinc/src/endpoint.rs assemble (the wall clock is asked     *)
(* once; zero refuses the role; the offset is wall - T0, saturating),      *)
(* drive.rs now() (T0 plus the time since the endpoint started),           *)
(* drive/role_io.rs relay_now (the endpoint clock plus the offset,         *)
(* saturating), role_serve (the relay's deadline taken back to the         *)
(* endpoint clock, saturating) and role_task (restore at the relay clock), *)
(* and pinc-connect relay/mod.rs restore_held (a kept packet older than    *)
(* the mailbox age is refused). FacadeRoleClock.tla checks them;           *)
(* TraceFacadeRoleClock.tla replays a test on the real code.               *)
(*                                                                         *)
(* Times are in one unit; MAX stands for u64::MAX.                         *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS T0,  \* the endpoint clock's origin (drive.rs T0)
          MAX, \* the largest clock value
          AGE  \* Limits.mailbox_max_age_ns

Min(a, b) == IF a < b THEN a ELSE b
SatSub(a, b) == IF a > b THEN a - b ELSE 0
SatAdd(a, b) == Min(a + b, MAX)

\* assemble: the offset of the relay clock from the endpoint clock, for a wall clock w (refused when w = 0)
Offset(w) == SatSub(w, T0)
\* the endpoint clock after el units, and the relay clock
EpNow(el) == SatAdd(T0, el)
RelayNow(off, el) == SatAdd(EpNow(el), off)
\* role_serve: the endpoint deadline of a relay deadline d
EpDeadline(d, off) == SatSub(d, off)
\* restore_held: the kept packets (by arrival time) a restore at relay clock t takes
Taken(kept, t) == {a \in kept : SatSub(t, a) < AGE}
=============================================================================
