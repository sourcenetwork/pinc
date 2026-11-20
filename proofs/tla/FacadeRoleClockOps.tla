-------------------------- MODULE FacadeRoleClockOps --------------------------
(***************************************************************************)
(* The relay clock of an Endpoint that carries the relay role, step for    *)
(* step: crates/pinc/src/endpoint.rs assemble (the wall clock is asked     *)
(* once; zero refuses the role; the role's clock origin is the wall clock  *)
(* itself), drive.rs now() (T0 plus the time since the endpoint started),  *)
(* role_clock (the origin plus the endpoint clock past T0, saturating),    *)
(* endpoint_clock (a relay deadline taken back to the endpoint clock, T0   *)
(* plus its time past the origin, saturating), drive/role_io.rs role_task  *)
(* (restore at the relay clock), and pinc-connect relay/mod.rs             *)
(* restore_held (a kept packet older than the mailbox age is refused).     *)
(* FacadeRoleClock.tla checks them; TraceFacadeRoleClock.tla replays a     *)
(* test on the real code.                                                  *)
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

\* assemble: the origin of the relay clock for a wall clock w (refused when w = 0)
Origin(w) == w
\* the endpoint clock after el units, and the relay clock (drive.rs role_clock)
EpNow(el) == SatAdd(T0, el)
RoleClock(org, now) == SatAdd(org, SatSub(now, T0))
RelayNow(org, el) == RoleClock(org, EpNow(el))
\* role_serve: the endpoint deadline of a relay deadline d (drive.rs endpoint_clock)
EpDeadline(d, org) == SatAdd(T0, SatSub(d, org))
\* restore_held: the kept packets (by arrival time) a restore at relay clock t takes
Taken(kept, t) == {a \in kept : SatSub(t, a) < AGE}
=============================================================================
