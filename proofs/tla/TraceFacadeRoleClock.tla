------------------------- MODULE TraceFacadeRoleClock -------------------------
(***************************************************************************)
(* Trace validation of the relay clock of an Endpoint that carries the     *)
(* relay role: endpoint.rs assemble, drive.rs now(), drive/role_io.rs      *)
(* relay_now and role_task, over the real Endpoint.                        *)
(*                                                                         *)
(* The Rust test tests/trace_facade_role_clock.rs builds Endpoints on a    *)
(* platform whose wall clock it sets and whose monotonic clock it moves by *)
(* hand, with a store that keeps one member's packets at chosen arrival    *)
(* times. For each wall clock: whether the build is refused; then runs of  *)
(* the endpoint at chosen times since the start, each until its role is    *)
(* serving, with the count of packets the role's mailbox took so far       *)
(* (Stats.mailbox.stored) and the store's loads. Each count must be the    *)
(* one the operators of FacadeRoleClockOps.tla give at the relay clock of  *)
(* that run; a later run of the same endpoint loads and restores nothing   *)
(* (Role::restored).                                                       *)
(*                                                                         *)
(* Times are milliseconds; the test's times are whole milliseconds, so the *)
(* code's comparisons in nanoseconds have the same answers. Needs the TLA+ *)
(* CommunityModules (Json, IOUtils) and PINC_TRACE_DIR, the directory that *)
(* holds role-clock.ndjson.                                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd
CONSTANTS T0, MAX, AGE
VARIABLES i, ok, org, kept, stored, done
vars == <<i, ok, org, kept, stored, done>>
INSTANCE FacadeRoleClockOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/role-clock.ndjson")
E == Trace[i]
Rng(f) == {f[j] : j \in DOMAIN f}

\* a new endpoint: built unless the wall clock is unknown
BuildEv == /\ E.op = "build"
           /\ E.ok = (E.w # 0)
           /\ ok' = E.ok /\ org' = Origin(E.w) /\ kept' = Rng(E.kept) /\ stored' = 0 /\ done' = FALSE

\* the first run at el since the start restores the store: the mailbox takes the packets live at the relay clock; a
\* later run takes nothing and does not load
RunEv == /\ E.op = "run" /\ ok
         /\ stored' = IF done THEN stored ELSE stored + Cardinality(Taken(kept, RelayNow(org, E.el)))
         /\ E.stored = stored' /\ E.loads = 1
         /\ done' = TRUE
         /\ UNCHANGED <<ok, org, kept>>

EndEv == E.op = "end" /\ UNCHANGED <<ok, org, kept, stored, done>>

Init == i = 1 /\ ok = FALSE /\ org = 0 /\ kept = {} /\ stored = 0 /\ done = FALSE
Step == /\ i <= Len(Trace)
        /\ \/ BuildEv \/ RunEv \/ EndEv
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

Inv == stored >= 0
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
