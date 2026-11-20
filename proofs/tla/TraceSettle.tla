----------------------------- MODULE TraceSettle -----------------------------
(***************************************************************************)
(* Trace validation of the settle step of a connected session: pinc-core   *)
(* timers.rs settle_core, as Settle.tla models it.                         *)
(*                                                                         *)
(* The Rust test tests/trace_settle.rs runs pairs of real endpoints (every *)
(* role, both sides, application data, silence, pulses handed to the layer *)
(* above, a resume's quiet period) and records, for every settle of a      *)
(* connected session that is not closing, what it read and decided (the   *)
(* probe SettleRecord). A u64 is four 16-bit limbs; an absent time is [].  *)
(* For each record, in order:                                              *)
(*  - PlanOK: the plan is Plan of KeepaliveOps.tla on the inputs read;     *)
(*  - AppliedOK: at every settle (fix C4) the interval handed to the       *)
(*    connection is the plan's ping less the last send (none in a pulse or *)
(*    without a ping), so the PING falls at the plan's ping (Applied and   *)
(*    PulseOff of Settle.tla); the probe records it in every record.       *)
(*  - DeadlineOK: the deadline set in the heap is the earliest of the      *)
(*    connection's own timer (read after the hand-over, fix C4), the       *)
(*    review moment, the ping in a pulse when                              *)
(*    it is later than now, the earliest standby ping, the access recheck  *)
(*    and, unauthenticated, the end of the session's life (timers.rs);     *)
(*  - DueOK: a ping is reported due in a pulse once it is at or before now.*)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds core/settle.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd
VARIABLES i, applied
vars == <<i, applied>>
INSTANCE KeepaliveOps
U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/core/settle.ndjson")
Lm(l) == U!FromLimbs(l)
Op(l) == IF l = <<>> THEN None ELSE Some(Lm(l))
MinOp(a, b) == IF ~b.some THEN a ELSE IF ~a.some THEN b ELSE Some(N!Min(a.v, b.v))

In(ev) == [role |-> ev.role, dialer |-> ev.dialer, direct |-> ev.direct, now |-> Lm(ev.now), tx |-> Lm(ev.tx),
           rx |-> Lm(ev.rx), app |-> Lm(ev.app), qu |-> Lm(ev.qu), flight |-> ev.flight]

\* the interval the plan p asks of the connection
Interval(ev, p) == IF ev.pulse \/ ~p.ping.some THEN None ELSE Some(N!SatSub(p.ping.v, Lm(ev.tx)))
\* the interval the connection of session sid holds: the last one handed to it, none before the first
Holds(sid) == IF sid \in DOMAIN applied THEN applied[sid] ELSE None

PlanOK(ev, p) == p.ping = Op(ev.ping) /\ p.review = Op(ev.review)

AppliedOK(ev, p) ==
    Op(ev.interval) = Interval(ev, p)  \* fix C4: the interval is handed over at every settle

DeadlineOK(ev, p) ==
    LET later == IF ev.pulse /\ p.ping.some /\ N!Lt(Lm(ev.now), p.ping.v) THEN p.ping ELSE None
        d == MinOp(MinOp(MinOp(MinOp(MinOp(Some(Lm(ev.own)), p.review), later), Op(ev.standby)), Op(ev.acp)),
                   Op(ev.end))
    IN Op(ev.deadline) = d

DueOK(ev, p) == ev.due = (ev.pulse /\ p.ping.some /\ N!Le(p.ping.v, Lm(ev.now)))

EventOK(ev) ==
    LET p == Plan(In(ev))
    IN PlanOK(ev, p) /\ AppliedOK(ev, p) /\ DeadlineOK(ev, p) /\ DueOK(ev, p)

Init == i = 1 /\ applied = [s \in {} |-> None]
Step == /\ i <= Len(Trace)
        /\ Trace[i].t = "settle"
        /\ EventOK(Trace[i])
        /\ i' = i + 1
        /\ applied' = [s \in DOMAIN applied \cup {Trace[i].sid} |->
                          IF s = Trace[i].sid THEN Op(Trace[i].interval) ELSE applied[s]]
Finished == i > Len(Trace) /\ UNCHANGED vars
Next == Step \/ Finished
TraceSpec == Init /\ [][Next]_vars
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
