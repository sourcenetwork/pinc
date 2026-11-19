------------------------------- MODULE Settle --------------------------------
(***************************************************************************)
(* The keepalive plan as the endpoint applies it: pinc-core timers.rs      *)
(* settle_core, for one connected session that is not closing.             *)
(*                                                                         *)
(* After every input that touches a session the endpoint settles it; a     *)
(* connected session gets the plan of keepalive.rs (Inputs::plan, the      *)
(* operator Plan of KeepaliveOps.tla on u64 nanosecond words), and when    *)
(* the plan differs from the one it holds it stores it and hands the       *)
(* connection the interval ping_at - last_tx (saturating), or none while   *)
(* the keepalive is handed to the layer above (SetPulse). The connection   *)
(* sends a PING once that long passed without sending anything             *)
(* (Connection::set_keepalive; its timer is last_sent + interval).         *)
(*                                                                         *)
(* Every call that moves an input settles at once, at the same time, as    *)
(* the code does: a datagram sent (poll_transmit: note_sent sets last_tx,  *)
(* then settle_core), one received (deliver sets last_rx, then settle), an *)
(* acknowledgement that empties the flight, application data (Write sets   *)
(* last_app), a timer, and SetPulse (which also clears the stored ping, so *)
(* the next settle applies again). The role, the side and whether the      *)
(* active path is direct are fixed per behaviour; the end of the quiet     *)
(* period after a resume is the constant QU. Times are whole seconds.      *)
(*                                                                         *)
(* Properties (the documentation of settle_core, set_keepalive and         *)
(* SetPulse):                                                              *)
(*  - Applied: outside a pulse, the interval the connection holds, counted *)
(*    from the last send, ends at the plan's ping (and there is none when  *)
(*    the plan has no ping): the plan is the one applied;                  *)
(*  - PulseOff: while the keepalive is handed to the layer above the       *)
(*    connection holds no interval (the endpoint sends no PING itself).    *)
(* Configs: Settle.cfg, every role, side and path kind but a quiet dialing *)
(* session on a direct path, no quiet period; Settle_watch.cfg (a quiet    *)
(* dialing session on a direct path) and Settle_held.cfg (a quiet period)  *)
(* are findings: the plan's ping stays the same while the last send moves, *)
(* so the stored interval is not applied again and the connection's PING   *)
(* falls later than the plan; TLC must find Applied violated there.        *)
(***************************************************************************)
EXTENDS Integers, FiniteSets
CONSTANTS TIMES, ROLES, DIALERS, DIRECTS, WATCH, QU
VARIABLES kind, now, tx, rx, app, flight, pulse, plan, applied
vars == <<kind, now, tx, rx, app, flight, pulse, plan, applied>>

INSTANCE KeepaliveOps

Kinds == {r \in [role : ROLES, dialer : DIALERS, direct : DIRECTS] : (Quiet(r) /\ r.dialer /\ r.direct) = WATCH}

In(t, tx1, rx1, app1, fl1) ==
    [role |-> kind.role, dialer |-> kind.dialer, direct |-> kind.direct, now |-> Sc(t), tx |-> Sc(tx1),
     rx |-> Sc(rx1), app |-> Sc(app1), qu |-> Sc(QU), flight |-> fl1]

\* the interval settle_core hands the connection for plan p
Interval(p, tx1, pl1) == IF pl1 \/ ~p.ping.some THEN None ELSE Some(N!SatSub(p.ping.v, Sc(tx1)))

\* settle at t with these inputs, the plan held being plan0
Settled(t, tx1, rx1, app1, fl1, pl1, plan0) ==
    LET p == Plan(In(t, tx1, rx1, app1, fl1))
    IN /\ now' = t /\ tx' = tx1 /\ rx' = rx1 /\ app' = app1 /\ flight' = fl1 /\ pulse' = pl1
       /\ plan' = p
       /\ applied' = IF p = plan0 THEN applied ELSE Interval(p, tx1, pl1)
       /\ UNCHANGED kind

Init == /\ kind \in Kinds
        /\ now = 0 /\ tx = 0 /\ rx = 0 /\ app = 0 /\ flight = FALSE /\ pulse = FALSE
        /\ plan = [ping |-> None, review |-> None]
        /\ applied = None

Timer(t) == Settled(t, tx, rx, app, flight, pulse, plan)
SendData(t) == Settled(t, t, rx, app, TRUE, pulse, plan)
SendAck(t) == Settled(t, t, rx, app, flight, pulse, plan)
Recv(t) == Settled(t, tx, t, app, flight, pulse, plan)
Acked(t) == Settled(t, tx, t, app, FALSE, pulse, plan)
AppData(t) == Settled(t, tx, rx, t, flight, pulse, plan)
SetPulse(t, on) == Settled(t, tx, rx, app, flight, on, [plan EXCEPT !.ping = None])

Next == \E t \in TIMES :
            /\ t >= now
            /\ \/ Timer(t)
               \/ SendData(t)
               \/ SendAck(t)
               \/ Recv(t)
               \/ Acked(t)
               \/ AppData(t)
               \/ \E on \in BOOLEAN : SetPulse(t, on)
Spec == Init /\ [][Next]_vars

Applied == ~pulse => applied = Interval(plan, tx, FALSE)
PulseOff == pulse => applied = None
Inv == Applied /\ PulseOff
=============================================================================
