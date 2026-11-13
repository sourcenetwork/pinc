------------------------------ MODULE TraceHeld ------------------------------
(***************************************************************************)
(* Trace validation of the held ring of a session: vinc-core slot.rs       *)
(* (Held).                                                                 *)
(*                                                                         *)
(* The Rust test tests/trace_held.rs drives real rings (built with the     *)
(* cargo feature `trace`) with seeded calls: events of every kind for a    *)
(* few streams, pops and the release of everything, in mixes that keep the *)
(* ring short, fill it with events the application can recover or cannot,  *)
(* push on into the full ring (the oldest recoverable event goes, or the   *)
(* new event is refused) and take the head round it. Every call must be    *)
(* the step the operators of HeldOps.tla compute, with the result the code *)
(* returned; the head, length, drop count and stall flag recorded must be  *)
(* the model's, and so must the held events whenever the record carries    *)
(* them (at most 16 held, and then every 29th call and the end of the run).*)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds held.ndjson.          *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils
VARIABLES i, r, cap
vars == <<i, r, cap>>
INSTANCE HeldOps

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/held.ndjson")
Ev0 == Trace[i]

\* an event as the test records it: its kind, stream and error
HView(e) == <<e[3][1], e[3][2], e[4]>>

Same(x, v, c) ==
    /\ x.head = v.head /\ x.len = v.len /\ x.dropped = v.dropped
    /\ HStalled(x, c) = v.stalled
    /\ v.full => [k \in 1..x.len |-> HView(Window(x, c)[k])] = v.q

\* the release of everything: pops until the ring is empty
RECURSIVE ClearGo(_, _)
ClearGo(x, c) == IF x.len = 0 THEN x ELSE ClearGo(Pop(x, c).r, c)

InitEv == /\ Ev0.op = "init" /\ cap' = Ev0.n /\ r' = Ring0(Ev0.n) /\ Same(r', Ev0.v, Ev0.n)
PushEv == /\ Ev0.op = "push"
          /\ r' = HPush(r, cap, Ev(0, Ev0.ev[1], Ev0.ev[2], Ev0.ev[3]), FALSE)
          /\ Same(r', Ev0.v, cap) /\ UNCHANGED cap
PopEv == LET x == Pop(r, cap)
         IN /\ Ev0.op = "pop" /\ (IF x.out = None THEN <<>> ELSE HView(x.out)) = Ev0.out
            /\ r' = x.r /\ Same(r', Ev0.v, cap) /\ UNCHANGED cap
ClearEv == /\ Ev0.op = "clear" /\ r' = ClearGo(r, cap) /\ Same(r', Ev0.v, cap) /\ UNCHANGED cap
EndEv == /\ Ev0.op = "end" /\ r' = r /\ Same(r', Ev0.v, cap) /\ UNCHANGED cap

Init == i = 1 /\ r = Ring0(1) /\ cap = 1
Step == /\ i <= Len(Trace) /\ Ev0.t = "coh"
        /\ (InitEv \/ PushEv \/ PopEv \/ ClearEv \/ EndEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the ring never grows
Inv == r.len \in 0..cap
=============================================================================
