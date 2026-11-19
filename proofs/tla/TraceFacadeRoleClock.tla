------------------------- MODULE TraceFacadeRoleClock -------------------------
(***************************************************************************)
(* Trace validation of the relay clock of an Endpoint that carries the     *)
(* relay role: endpoint.rs assemble, drive.rs now(), drive/role_io.rs      *)
(* relay_now and role_task, over the real Endpoint.                        *)
(*                                                                         *)
(* The Rust test tests/trace_facade_role_clock.rs builds Endpoints on a    *)
(* platform whose wall clock it sets and whose monotonic clock it moves by *)
(* hand, with a store that keeps one member's packets at chosen arrival   *)
(* times. For each wall clock: whether the build is refused; then runs of  *)
(* the endpoint at chosen times since the start, each until its restore    *)
(* is done, with the count of packets the role's mailbox took so far       *)
(* (Stats.mailbox.stored). Each count must be the one the operators of     *)
(* FacadeRoleClockOps.tla give at the relay clock of that run.             *)
(*                                                                         *)
(* Times are milliseconds; the test's times are whole milliseconds, so the *)
(* code's comparisons in nanoseconds have the same answers. Needs the TLA+ *)
(* CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the directory that *)
(* holds role-clock.ndjson.                                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils
CONSTANTS T0, MAX, AGE
VARIABLES i, ok, off, kept, stored
vars == <<i, ok, off, kept, stored>>
INSTANCE FacadeRoleClockOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/role-clock.ndjson")
E == Trace[i]
Rng(f) == {f[j] : j \in DOMAIN f}

\* a new endpoint: built unless the wall clock is unknown
BuildEv == /\ E.op = "build"
           /\ E.ok = (E.w # 0)
           /\ ok' = E.ok /\ off' = Offset(E.w) /\ kept' = Rng(E.kept) /\ stored' = 0

\* a run at el since the start restores the store: the mailbox takes the packets live at the relay clock
RunEv == /\ E.op = "run" /\ ok
         /\ stored' = stored + Cardinality(Taken(kept, RelayNow(off, E.el)))
         /\ E.stored = stored'
         /\ UNCHANGED <<ok, off, kept>>

EndEv == E.op = "end" /\ UNCHANGED <<ok, off, kept, stored>>

Init == i = 1 /\ ok = FALSE /\ off = 0 /\ kept = {} /\ stored = 0
Step == /\ i <= Len(Trace)
        /\ \/ BuildEv \/ RunEv \/ EndEv
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == stored >= 0
=============================================================================
