---------------------------- MODULE NodeTimerBound ----------------------------
(***************************************************************************)
(* The bound on the node's timer: pinc-node timers.rs (`Bound`,            *)
(* `Bound::answer`, `Node::bound_timer`, `TimerStats`), with the operators *)
(* of NodeTimerBoundOps.tla.                                               *)
(*                                                                         *)
(* A step is one timer call at any time of TIMES (forward, standing still, *)
(* backward, at the top of the u64 range) with any deadline, or none, for  *)
(* each of N timers: what the layers name is not constrained, so a layer   *)
(* that moves its deadline, one that names the time of the call, one that  *)
(* keeps a deadline that does not move and one with none are all steps.    *)
(* What the node answers between two timer calls is checked for every      *)
(* earliest deadline the layers could name then (the invariants quantify   *)
(* over it), which covers every other call that moves a deadline.          *)
(*                                                                         *)
(* The history variables restate the documented rule independently of the *)
(* code's `left` and `last`: prev is the previous timer call and the       *)
(* deadlines it saw; a deadline is stuck at a call when the previous call  *)
(* saw it due, and this call sees it due at a time no later than the      *)
(* previous call. cnt counts the stuck calls of each timer (capped one     *)
(* above CMAX), recs the trace records (capped at 2).                      *)
(*                                                                         *)
(* Checked (the invariants of timers.rs):                                  *)
(*  - HeldBound: a deadline left due by two timer calls in a row, and due  *)
(*    at the time of the first, is answered no earlier than one tick after *)
(*    the second, for every time below the top of the clock's range;      *)
(*  - Unmoved: when the last call left nothing stuck the node answers its  *)
(*    layers' earliest deadline unchanged;                                 *)
(*  - AtMostTick: the node answers a deadline exactly when its layers name *)
(*    one, and at most one tick after the last timer call when later than *)
(*    theirs (the layers are served at most one tick late);                *)
(*  - Counted, TotalOK: each timer counts the calls that did not move its  *)
(*    deadline (saturating), the total is their saturating sum;            *)
(*  - RecordedOnce: a timer is recorded in the trace once, the first time. *)
(* Counted and RecordedOnce with cnt all 0 are the documented "a node whose *)
(* layers move their deadlines counts nothing, records nothing".           *)
(* Witnesses: NodeTimerBound_w_top (the held time saturates at u64::MAX:   *)
(* the top of the range the bound excepts is reached), NodeTimerBound_w_sat *)
(* (a counter reaches its saturation).                                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Nanos
CONSTANTS N, TIMES, CMAX, TICK
VARIABLES st, prev, cnt, recs, lastStuck
vars == <<st, prev, cnt, recs, lastStuck>>

INSTANCE NodeTimerBoundOps

Ids == 1..N
Opts == {Nil} \cup {<<t>> : t \in TIMES}
IMin(a, b) == IF a < b THEN a ELSE b

\* the model's domains: the edges of the u64 range, a tick of one nanosecond (so u64::MAX - 1 plus a tick fits and u64::MAX does not)
TimesDef == {Zero, One, U!Sub(U!Max64, One), U!Max64}
TickDef == One

\* the documented rule, from the history alone
SpecStuck(now, d, i) ==
    /\ prev.has
    /\ prev.d[i] # Nil /\ Le(prev.d[i][1], prev.t)
    /\ d[i] # Nil /\ Le(d[i][1], now) /\ Le(d[i][1], prev.t)

Init == /\ st = Bound0(N)
        /\ prev = [has |-> FALSE, t |-> Zero, d |-> [i \in Ids |-> Nil]]
        /\ cnt = [i \in Ids |-> 0]
        /\ recs = [i \in Ids |-> 0]
        /\ lastStuck = FALSE

Next == \E now \in TIMES, d \in [Ids -> Opts] :
    LET r == Check(st, now, d)
        ss == {i \in Ids : SpecStuck(now, d, i)}
    IN /\ st' = r.st
       /\ prev' = [has |-> TRUE, t |-> now, d |-> d]
       /\ cnt' = [i \in Ids |-> IF i \in ss THEN IMin(cnt[i] + 1, CMAX + 1) ELSE cnt[i]]
       /\ recs' = [i \in Ids |-> IF r.first[i] THEN IMin(recs[i] + 1, 2) ELSE recs[i]]
       /\ lastStuck' = (ss # {})

Spec == Init /\ [][Next]_vars

HeldBound ==
    lastStuck /\ U!Fits(U!Add(prev.t, TICK)) =>
        \A due \in Opts : due = Nil \/ Le(U!Add(prev.t, TICK), Answer(st, due)[1])

Unmoved == ~lastStuck => \A due \in Opts : Answer(st, due) = due

AtMostTick ==
    \A due \in Opts :
        /\ (Answer(st, due) = Nil) = (due = Nil)
        /\ due # Nil => Le(due[1], Answer(st, due)[1])
        /\ due # Nil /\ lastStuck => Le(Answer(st, due)[1], Max(due[1], SatAdd(prev.t, TICK)))

Counted == \A i \in Ids : st.stats[i] = IMin(cnt[i], CMAX)

RECURSIVE SumTo(_, _)
SumTo(f, k) == IF k = 0 THEN 0 ELSE SumTo(f, k - 1) + f[k]
TotalOK == Total(st) = IMin(SumTo([i \in Ids |-> IMin(cnt[i], CMAX)], N), CMAX)

RecordedOnce == \A i \in Ids : recs[i] = IF cnt[i] > 0 THEN 1 ELSE 0

\* reachability witnesses
NoTopHold == st.held # <<U!Max64>>
NoSat == \A i \in Ids : st.stats[i] < CMAX
=============================================================================
