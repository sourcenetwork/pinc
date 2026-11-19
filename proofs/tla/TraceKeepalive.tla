---------------------------- MODULE TraceKeepalive ----------------------------
(***************************************************************************)
(* Trace validation of the keepalive schedule: pinc-core keepalive.rs.     *)
(*                                                                         *)
(* The Rust test tests/trace_keepalive.rs runs the real Inputs::plan and   *)
(* standby_due on seeded inputs and on inputs one nanosecond either side   *)
(* of every constant of the schedule, with times up to u64::MAX. A u64 is  *)
(* four 16-bit limbs; an absent time is []. Every recorded ping and review *)
(* moment must be the ones PlanWith of KeepaliveOps.tla computes (acc 70,  *)
(* the window close a review moment: the code), and every recorded         *)
(* standby due the operator StandbyDue.                                    *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds keepalive.ndjson.     *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLE i
vars == <<i>>
INSTANCE KeepaliveOps
U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/keepalive.ndjson")
Lm(l) == U!FromLimbs(l)
Op(l) == IF l = <<>> THEN None ELSE Some(Lm(l))

PlanOK(ev) ==
    LET x == [role |-> ev.role, dialer |-> ev.dialer, direct |-> ev.direct, now |-> Lm(ev.now), tx |-> Lm(ev.tx),
              rx |-> Lm(ev.rx), app |-> Lm(ev.app), qu |-> Lm(ev.qu), flight |-> ev.flight]
        q == Plan(x)
    IN q.ping = Op(ev.ping) /\ q.review = Op(ev.review)

StandbyOK(ev) == StandbyDue(Lm(ev.now), Lm(ev.tx), Lm(ev.app)) = Op(ev.due)

EventOK(ev) == IF ev.op = "plan" THEN PlanOK(ev) ELSE StandbyOK(ev)

Init == i = 1
Step == /\ i <= Len(Trace) /\ Trace[i].t = "cka" /\ EventOK(Trace[i]) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
Next == Step \/ Finished
TraceSpec == Init /\ [][Next]_vars
=============================================================================
