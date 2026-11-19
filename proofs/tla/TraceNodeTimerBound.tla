------------------------- MODULE TraceNodeTimerBound -------------------------
(***************************************************************************)
(* Trace validation of the bound on the node's timer, pinc-node timers.rs. *)
(*                                                                         *)
(* The Rust test tests/trace_node_timer_bound.rs drives the real `Bound`   *)
(* (through the probe `timers_probe::TimerProbe`, built with the cargo     *)
(* feature `trace`) with seeded timer calls over all nine deadlines: ones  *)
(* that move, ones that name the time of the call, ones that stay due,     *)
(* none, at times that step forward, stand still, step back and sit at the *)
(* top of the u64 range; between the calls it asks the answer for earliest *)
(* deadlines below, at and above the held time, and the counters. Every   *)
(* call must be the step of Check, Answer and Total of                     *)
(* NodeTimerBoundOps.tla, whose properties TLC checks in                   *)
(* NodeTimerBound.cfg. Times are four 16-bit limbs; an absent time is [].  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds timer_bound.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, Nanos
CONSTANTS N, TICK, CMAX
VARIABLES i, st
vars == <<i, st>>
INSTANCE NodeTimerBoundOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/timer_bound.ndjson")
Ev0 == Trace[i]
L(x) == U!FromLimbs(x)
\* an Option<Nanos>: [] or four limbs
O(x) == IF x = <<>> THEN Nil ELSE <<L(x)>>

\* the code's TIMER_TICK (1 ms); the counters cannot reach u64::MAX in a trace, so CMAX is the largest TLC integer
TraceTick == Millis(1)

InitEv == /\ Ev0.op = "init" /\ Ev0.n = N /\ L(Ev0.tick) = TICK /\ st' = Bound0(N)
CheckEv == LET r == Check(st, L(Ev0.now), [k \in 1..N |-> O(Ev0.dues[k])])
           IN /\ Ev0.op = "check" /\ Len(Ev0.dues) = N
              /\ st' = r.st
              /\ \A k \in 1..N : r.first[k] = Ev0.first[k]
              /\ O(Ev0.held) = r.st.held
              /\ \A k \in 1..N : r.st.stats[k] = Ev0.stats[k]
AnswerEv == /\ Ev0.op = "answer" /\ Answer(st, O(Ev0.due)) = O(Ev0.r) /\ st' = st
StatsEv == /\ Ev0.op = "stats" /\ Total(st) = Ev0.total
           /\ \A k \in 1..N : st.stats[k] = Ev0.stuck[k]
           /\ st' = st

Init == i = 1 /\ st = Bound0(N)
Step == /\ i <= Len(Trace) /\ Ev0.t = "tb"
        /\ (InitEv \/ CheckEv \/ AnswerEv \/ StatsEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the held time is set exactly while the last call left a deadline stuck, and a tick after it
Inv == st.held # Nil => st.last # Nil /\ st.held = <<SatAdd(st.last[1], TICK)>>
=============================================================================
