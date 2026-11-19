------------------------- MODULE NodeTimerBoundOps -------------------------
(***************************************************************************)
(* The bound on the node's timer, pinc-node timers.rs, step for step: the  *)
(* state `Bound` (held, last, left, stats), `Bound::answer` (Answer), the  *)
(* check the node makes as the last step of a timer call (Check, the loop  *)
(* of `bound_timer`, with `first` the deadlines the call records in the    *)
(* trace) and `TimerStats::total` (Total). Times are the Nanos words of    *)
(* Nanos.tla; an Option is <<>> or <<w>>. The stuck counters are native    *)
(* integers that saturate at CMAX (u64::MAX in the code, which no model    *)
(* reaches: a model sets a small CMAX so the saturation is reached).       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Nanos
CONSTANTS TICK, CMAX

Nil == <<>>

Bound0(n) == [last |-> Nil, held |-> Nil, left |-> [i \in 1..n |-> FALSE], stats |-> [i \in 1..n |-> 0]]

\* Bound::answer: the layers' earliest deadline, no earlier than the held time
Answer(st, due) == IF due # Nil /\ st.held # Nil THEN <<Max(due[1], st.held[1])>> ELSE due

\* due.filter(|d| *d <= now)
DueAt(d, now) == IF d # Nil /\ Le(d[1], now) THEN d ELSE Nil

\* left due by the last timer call, which ran at last, and left due again at a time no later than last
StuckAt(st, now, dues, i) ==
    /\ st.left[i]
    /\ st.last # Nil
    /\ LET d == DueAt(dues[i], now) IN d # Nil /\ Le(d[1], st.last[1])

SatInc(n) == IF n < CMAX THEN n + 1 ELSE CMAX

\* bound_timer(now) with the deadlines dues (the endpoint's, then each layer's): the new state, and for each
\* deadline whether the call records it in the trace (stuck for the first time)
Check(st, now, dues) ==
    LET ids == DOMAIN st.left
        s(i) == StuckAt(st, now, dues, i)
    IN [st |-> [last |-> <<now>>,
                held |-> IF \E i \in ids : s(i) THEN <<SatAdd(now, TICK)>> ELSE Nil,
                left |-> [i \in ids |-> DueAt(dues[i], now) # Nil],
                stats |-> [i \in ids |-> IF s(i) THEN SatInc(st.stats[i]) ELSE st.stats[i]]],
        first |-> [i \in ids |-> s(i) /\ st.stats[i] = 0]]

\* TimerStats::total: a saturating fold over the counters in order
RECURSIVE TotalTo(_, _)
TotalTo(f, k) == IF k = 0 THEN 0 ELSE LET r == TotalTo(f, k - 1) IN IF r + f[k] < CMAX THEN r + f[k] ELSE CMAX
Total(st) == TotalTo(st.stats, Cardinality(DOMAIN st.stats))
=============================================================================
