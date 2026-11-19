---------------------------- MODULE FacadeRoleClock ----------------------------
(***************************************************************************)
(* The relay clock of an Endpoint that carries the relay role, and what    *)
(* runs before the role's store is restored: endpoint.rs assemble,         *)
(* drive.rs run_as (role_task made per run, datagrams held back until the  *)
(* role is ready, the flush that hands outgoing datagrams to the role's    *)
(* carriers and sends the role's own), drive/role_io.rs (relay_now,        *)
(* role_serve, role_carries, role_outgoing, role_task, RoleEnd), role.rs   *)
(* (the Role contract: the relay clock is nanoseconds since the Unix       *)
(* epoch; a role is driven by one run at a time and ends when it ends).    *)
(* The operators are in FacadeRoleClockOps.tla.                            *)
(*                                                                         *)
(* The networks. Only an ordinary node carries the role inside an          *)
(* Endpoint; in a network of ordinary nodes only, these nodes are its      *)
(* relays. A node deployed from the relay binary runs the role with        *)
(* Relay::run on its own clock, the host's wall clock, which this model    *)
(* does not cover; in a mixed network the two kinds keep records and       *)
(* mailboxes by the same rules, so an Endpoint whose relay clock is not    *)
(* the wall clock keeps a packet for a different time than the binary      *)
(* next to it (see ClockIsWall). A relay binary restarted with the same    *)
(* identity, records on disk, TCP or WebSocket carriers and an older       *)
(* library is outside this model: none of it reads the Endpoint's clock.   *)
(*                                                                         *)
(* The wall clock is read once, when the endpoint is built: 0 (unknown),   *)
(* before T0, at T0, after it, near MAX. The endpoint clock moves on by    *)
(* Advance. A run restores the store (KEPT: arrival times of the packets   *)
(* kept), then is ready; the flush of a run's driver runs at any time.     *)
(*                                                                         *)
(* Checked: WallKnown (the role is built only with a wall clock),          *)
(* ClockIsWall (role.rs: the relay clock is the wall clock), DeadlineExact *)
(* (the endpoint wakes no later than the relay's deadline, and exactly at  *)
(* it when it is past the offset), NothingBeforeReady (role_io.rs: nothing *)
(* runs until the role's records are restored), RestoredOnce (each kept    *)
(* packet is restored once).                                               *)
(***************************************************************************)
EXTENDS FacadeRoleClockOps

CONSTANTS WALLS,  \* the wall clocks the platform may give
          DMAX,   \* the most time the endpoint runs
          DUES,   \* the deadlines the relay may ask for (relay clock)
          KEPT,   \* the arrival times of the packets in the store
          MAXRUN  \* the most runs of one endpoint

VARIABLES st,     \* "new", "refused", "built"
          wall, off, el,
          run,    \* runs started
          phase,  \* "idle" (no run), "loading", "ready"
          got,    \* how often each kept packet was restored
          early,  \* the role was handed work before it was ready
          ed      \* [d, e]: the last relay deadline and the endpoint deadline it became
vars == <<st, wall, off, el, run, phase, got, early, ed>>

Init == /\ st = "new" /\ wall = 0 /\ off = 0 /\ el = 0 /\ run = 0 /\ phase = "idle"
        /\ got = [a \in KEPT |-> 0] /\ early = FALSE /\ ed = [d |-> 0, e |-> 0]

Build(w) ==
    /\ st = "new"
    /\ wall' = w
    /\ IF w = 0 THEN st' = "refused" /\ off' = 0 ELSE st' = "built" /\ off' = Offset(w)
    /\ UNCHANGED <<el, run, phase, got, early, ed>>

StartRun ==
    /\ st = "built" /\ phase = "idle" /\ run < MAXRUN
    /\ phase' = "loading" /\ run' = run + 1
    /\ UNCHANGED <<st, wall, off, el, got, early, ed>>

Restore ==
    /\ phase = "loading"
    /\ LET t == RelayNow(off, el) IN got' = [a \in KEPT |-> IF a \in Taken(KEPT, t) THEN got[a] + 1 ELSE got[a]]
    /\ phase' = "ready"
    /\ UNCHANGED <<st, wall, off, el, run, early, ed>>

\* the driver's flush: the endpoint's datagrams to members go to the role's carriers, the role's own leave
Flush ==
    /\ phase # "idle"
    /\ early' = (early \/ phase = "loading")
    /\ UNCHANGED <<st, wall, off, el, run, phase, got, ed>>

\* role_serve: only when ready; the relay's next deadline joins the endpoint's
Serve(d) ==
    /\ phase = "ready"
    /\ ed' = [d |-> d, e |-> EpDeadline(d, off)]
    /\ UNCHANGED <<st, wall, off, el, run, phase, got, early>>

Advance ==
    /\ st = "built" /\ el < DMAX
    /\ el' = el + 1
    /\ UNCHANGED <<st, wall, off, run, phase, got, early, ed>>

\* the run ends however it ends (RoleEnd): not ready, carriers dropped
End ==
    /\ phase # "idle"
    /\ phase' = "idle"
    /\ UNCHANGED <<st, wall, off, el, run, got, early, ed>>

Next == \/ \E w \in WALLS : Build(w)
        \/ StartRun \/ Restore \/ Flush \/ Advance \/ End
        \/ \E d \in DUES : Serve(d)

Spec == Init /\ [][Next]_vars

TypeOK == /\ st \in {"new", "refused", "built"}
          /\ phase \in {"idle", "loading", "ready"}
          /\ el \in 0..DMAX
          /\ off \in 0..MAX

WallKnown == st = "built" => wall # 0

ClockIsWall == st = "built" => RelayNow(off, el) = SatAdd(wall, el)

DeadlineExact == /\ SatAdd(ed.e, off) >= ed.d
                 /\ ed.d >= off => ed.e + off = ed.d

NothingBeforeReady == ~early

RestoredOnce == \A a \in KEPT : got[a] <= 1

\* witnesses: each must be violated
NoRefused == st # "refused"
NoRestored == \A a \in KEPT : got[a] = 0
=============================================================================
