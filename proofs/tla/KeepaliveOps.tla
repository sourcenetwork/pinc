---------------------------- MODULE KeepaliveOps ----------------------------
(***************************************************************************)
(* The keepalive schedule of vinc-core keepalive.rs (Inputs::plan and      *)
(* standby_due), step for step, on the u64 nanosecond words of Nanos.tla   *)
(* (a time is five 16-bit limbs; saturating_add saturates). Keepalive.tla  *)
(* checks the properties over boundary inputs; TraceKeepalive.tla replays  *)
(* the recorded calls of the real code.                                    *)
(*                                                                         *)
(* An input x is the record [role, dialer, direct, now, tx, rx, app, qu,   *)
(* flight]: the role ("hub", "member" or "other"), whether this side       *)
(* dialed, whether the active path is direct, the clock, the last send,    *)
(* the last receive on the active path, the last application data, the end *)
(* of the quiet period after a resume, whether packets are in flight. An   *)
(* optional time is [some, v]. The plan is [ping, review].                 *)
(*                                                                         *)
(* PlanWith(x, acc, qurev) is the code when acc = 70 (the accepting side's *)
(* idle interval in seconds) and actrev = TRUE (the close of the 20 s     *)
(* window of the standby paths is a review moment); other values are the   *)
(* deliberate bugs of the witness configs. Plan(x) is the code.            *)
(* Lean counterpart: proofs/lean/Vinc/CoreKeepalive*.lean.                 *)
(***************************************************************************)
EXTENDS Integers

N == INSTANCE Nanos

Sc(n) == N!Sec(n)
PathKeep == Sc(5)
ActiveKeep == Sc(20)
IdleDrop == Sc(90)
DirectSilence == Sc(14)
HoldWindow == Sc(120)
\* the idle timeout of a connection (vinc-transport conn/config.rs IDLE_TIMEOUT)
IdleTimeout == Sc(75)

None == [some |-> FALSE, v |-> N!Zero]
Some(v) == [some |-> TRUE, v |-> v]

Quiet(x) == x.role # "other"
IdleKeepWith(x, acc) == IF Quiet(x) THEN (IF x.dialer THEN Sc(60) ELSE Sc(acc)) ELSE Sc(40)
IdleKeep(x) == IdleKeepWith(x, 70)

\* the Option::map_or(t, |c| c.min(t)) of `earliest`
Earliest(p, t) == Some(IF p.some THEN N!Min(p.v, t) ELSE t)
After(x, t) == N!Max(t, x.now)
\* map(|p| p.max(n))
MapMax(n, p) == IF p.some THEN Some(N!Max(p.v, n)) ELSE None

StandbyDue(now, ptx, app) ==
    LET due == N!Max(N!SatAdd(ptx, PathKeep), now)
    IN IF N!Lt(due, N!SatAdd(app, ActiveKeep)) THEN Some(due) ELSE None

\* a moment the answer can change by itself counts only after now
Change(now, r, t) == IF N!Lt(now, t) THEN Earliest(r, t) ELSE r

IdleDueWith(x, acc) == After(x, N!SatAdd(x.tx, IdleKeepWith(x, acc)))
IdleDue(x) == IdleDueWith(x, 70)
Watch(x) == Quiet(x) /\ x.dialer /\ x.direct
DirectDue(x) == After(x, N!SatAdd(N!Max(x.rx, x.tx), DirectSilence))
Held(x) == N!Lt(x.now, x.qu) /\ ~x.flight

PlanWith(x, acc, actrev) ==
    LET sb == StandbyDue(x.now, x.tx, x.app)
        p1 == IF sb.some THEN Earliest(None, sb.v) ELSE None
        r1 == IF actrev THEN Change(x.now, None, N!SatAdd(x.app, ActiveKeep)) ELSE None
        idle == IdleDueWith(x, acc)
        p2 == IF Quiet(x) \/ N!Lt(idle, N!SatAdd(x.app, IdleDrop)) THEN Earliest(p1, idle) ELSE p1
        r2 == IF ~Quiet(x) THEN Change(x.now, r1, N!SatAdd(x.app, IdleDrop)) ELSE r1
        dd == DirectDue(x)
        p3 == IF Watch(x) /\ N!Lt(dd, N!SatAdd(x.app, HoldWindow)) THEN Earliest(p2, dd) ELSE p2
        r3 == IF Watch(x) THEN Change(x.now, r2, N!SatAdd(x.app, HoldWindow)) ELSE r2
        p4 == IF Held(x) THEN MapMax(x.qu, p3) ELSE p3
        r4 == IF Held(x) THEN Change(x.now, r3, x.qu) ELSE r3
    IN [ping |-> p4, review |-> r4]

Plan(x) == PlanWith(x, 70, TRUE)
=============================================================================
