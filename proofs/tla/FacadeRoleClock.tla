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
(* mailboxes by the same rules, and ClockIsWall makes an Endpoint keep a   *)
(* packet for the same time as the binary next to it, whatever wall clock  *)
(* it was built with. A relay binary restarted with the same               *)
(* identity, records on disk, TCP or WebSocket carriers and an older       *)
(* library is outside this model: none of it reads the Endpoint's clock.   *)
(*                                                                         *)
(* The wall clock is read once, when the endpoint is built: 0 (unknown),   *)
(* after 0 and before T0, at T0, after it, near MAX. The endpoint clock    *)
(* moves on by Advance. A run's role_task restores the store (KEPT: the    *)
(* arrival times of the packets kept) unless an earlier run restored it    *)
(* (Role::restored), then sets role_ready; RoleEnd clears it. The          *)
(* flush of a run's driver runs at any time: before role_ready it takes a  *)
(* datagram for a member and drops it, counted (Role::lost), and sends     *)
(* nothing of the role's own.                                              *)
(*                                                                         *)
(* Checked: WallKnown (the role is built only with a wall clock),          *)
(* ClockIsWall (role.rs: the relay clock is the wall clock, for every      *)
(* wall clock, below T0 too), DeadlineExact (the endpoint wakes no later   *)
(* than the relay's deadline, exactly at it when the endpoint clock can    *)
(* name it, and at once for one before the origin), NothingBeforeReady     *)
(* (role_io.rs: nothing runs until the role's records are restored),       *)
(* RestoredOnce (each kept packet is restored once, over two runs).        *)
(* Witnesses: _w_refused (NoRefused), _w_restored (NoRestored), _w_lost    *)
(* (NoLost: a flush before the restore drops a datagram, counted).         *)
(***************************************************************************)
EXTENDS FacadeRoleClockOps

CONSTANTS WALLS,  \* the wall clocks the platform may give
          DMAX,   \* the most time the endpoint runs
          DUES,   \* the deadlines the relay may ask for (relay clock)
          KEPT,   \* the arrival times of the packets in the store
          MAXRUN  \* the most runs of one endpoint

VARIABLES st,     \* "new", "refused", "built"
          wall, org, el,
          run,    \* runs started
          phase,  \* "idle" (no run), "loading", "ready"
          rdy,    \* role_ready
          rst,    \* the role was restored (Role::restored)
          got,    \* how often each kept packet was restored
          early,  \* the role was handed work before it was restored
          lost,   \* a datagram was taken and dropped before role_ready (Role::lost counts it)
          ed      \* [on, d, e]: the last relay deadline and the endpoint deadline it became
vars == <<st, wall, org, el, run, phase, rdy, rst, got, early, lost, ed>>

Init == /\ st = "new" /\ wall = 0 /\ org = 0 /\ el = 0 /\ run = 0 /\ phase = "idle" /\ rdy = FALSE /\ rst = FALSE
        /\ got = [a \in KEPT |-> 0] /\ early = FALSE /\ lost = FALSE /\ ed = [on |-> FALSE, d |-> 0, e |-> 0]

Build(w) ==
    /\ st = "new"
    /\ wall' = w
    /\ IF w = 0 THEN st' = "refused" /\ org' = 0 ELSE st' = "built" /\ org' = Origin(w)
    /\ UNCHANGED <<el, run, phase, rdy, rst, got, early, lost, ed>>

\* role_task's first poll: role_ready cleared
StartRun ==
    /\ st = "built" /\ phase = "idle" /\ run < MAXRUN
    /\ phase' = "loading" /\ run' = run + 1 /\ rdy' = FALSE
    /\ UNCHANGED <<st, wall, org, el, rst, got, early, lost, ed>>

\* load and restore at the relay clock, skipped when an earlier run restored the role; then role_ready
Restore ==
    /\ phase = "loading"
    /\ LET t == RelayNow(org, el)
       IN got' = IF rst THEN got ELSE [a \in KEPT |-> IF a \in Taken(KEPT, t) THEN got[a] + 1 ELSE got[a]]
    /\ phase' = "ready" /\ rdy' = TRUE /\ rst' = TRUE
    /\ UNCHANGED <<st, wall, org, el, run, early, lost, ed>>

\* the driver's flush: with role_ready the endpoint's datagrams to members go to the role's carriers and the role's
\* own leave; without it a datagram for a member is taken and dropped, counted, and the role sends nothing
Flush ==
    /\ phase # "idle"
    /\ early' = (early \/ (rdy /\ phase # "ready"))
    /\ lost' = (lost \/ ~rdy)
    /\ UNCHANGED <<st, wall, org, el, run, phase, rdy, rst, got, ed>>

\* role_serve: only with role_ready; the relay's next deadline joins the endpoint's
Serve(d) ==
    /\ rdy
    /\ ed' = [on |-> TRUE, d |-> d, e |-> EpDeadline(d, org)]
    /\ UNCHANGED <<st, wall, org, el, run, phase, rdy, rst, got, early, lost>>

Advance ==
    /\ st = "built" /\ el < DMAX
    /\ el' = el + 1
    /\ UNCHANGED <<st, wall, org, run, phase, rdy, rst, got, early, lost, ed>>

\* the run ends however it ends (RoleEnd): role_ready cleared, carriers dropped
End ==
    /\ phase # "idle"
    /\ phase' = "idle" /\ rdy' = FALSE
    /\ UNCHANGED <<st, wall, org, el, run, rst, got, early, lost, ed>>

Next == \/ \E w \in WALLS : Build(w)
        \/ StartRun \/ Restore \/ Flush \/ Advance \/ End
        \/ \E d \in DUES : Serve(d)

Spec == Init /\ [][Next]_vars

TypeOK == /\ st \in {"new", "refused", "built"}
          /\ phase \in {"idle", "loading", "ready"}
          /\ el \in 0..DMAX
          /\ org \in 0..MAX

WallKnown == st = "built" => wall # 0

ClockIsWall == st = "built" => RelayNow(org, el) = SatAdd(wall, el)

\* the relay clock at the endpoint deadline: never past the relay's deadline (when it is at or after the origin), equal
\* to it when the endpoint clock reaches that far, and the first instant for a deadline before the origin
DeadlineExact == ed.on => /\ ed.d >= org => RoleClock(org, ed.e) <= ed.d
                          /\ ed.d >= org /\ T0 + (ed.d - org) <= MAX => RoleClock(org, ed.e) = ed.d
                          /\ ed.d < org => ed.e = T0

NothingBeforeReady == ~early

RestoredOnce == \A a \in KEPT : got[a] <= 1

\* witnesses: each must be violated
NoRefused == st # "refused"
NoRestored == \A a \in KEPT : got[a] = 0
NoLost == ~lost
=============================================================================
