---------------------------- MODULE TraceValuesTime ----------------------------
(***************************************************************************)
(* Trace validation of the time rules of the value fetch (vinc-values      *)
(* fetch/recv.rs and fetch/stall.rs).                                      *)
(*                                                                         *)
(* The Rust test tests/trace_values_time.rs runs the real Fetch in the     *)
(* deterministic multi-provider simulation (silent, slow and lying         *)
(* providers, deadlines, ranges that start in the middle of a granule,     *)
(* seeded random worlds) and records, for every step of the simulation     *)
(* (one queued event or one on_timeout call), the time state of the fetch  *)
(* before and after, the records and events it emitted in order, and the   *)
(* answers of the sessions. Each recorded step must be a step of the       *)
(* operators of ValuesTimeOps.tla:                                         *)
(*  - an event step is, in this order, BYTE_LIVE (when the stream bytes    *)
(*    arrived: the last byte time is now), ARK_PACE (when a frame          *)
(*    completed: the last frame time is now), then for every recorded      *)
(*    record in order a group verified (Verify: store, capture or          *)
(*    announce, hold check, completion check), an eviction, or a store     *)
(*    refusal, and optionally the completion check of a stream end;        *)
(*  - a run of steps in which only stream bytes arrived is one line (bs):   *)
(*    BYTE_LIVE at the first time, then the largest gap and the last time; *)
(*  - a timer step is OnTimeout with the waits w (STALL_RTT) and lv        *)
(*    (STALL_LIVE) that the test computed from the sessions: the stall     *)
(*    block, the head block, the steal re-check, the deadline.             *)
(* The state after the step, and the records and events it emitted, must   *)
(* be exactly what the operators compute: the same wait, the same last      *)
(* frame and byte times, the same held granule, release cause, redial      *)
(* waits and failure reason. The time of the first request, the steal      *)
(* timer and the retry timers are armed by code outside these rules; they  *)
(* are taken from the record, allowing only the values the code can arm    *)
(* (treq: the step's time once; tw: the step's time plus 1 s once spent),  *)
(* and poll_timeout must be the minimum of the timers the model holds,     *)
(* or a retry time below it. The start of a run must report what           *)
(* StartOutcome says. The wanted groups are the group-aligned pieces of    *)
(* the wanted spans; the model's verified set is the groups the store held *)
(* at the start plus the groups the trace verified.                        *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds values_time.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES i, m, c
vars == <<i, m, c>>

OP == INSTANCE ValuesTimeOps
U == INSTANCE U64

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/values_time.ndjson")

W(l) == U!FromLimbs(l)
G(p) == [off |-> p[1], len |-> p[2]]
GSet(ps) == {G(ps[k]) : k \in 1..Len(ps)}
HeadOf(st) == IF st.head.h THEN OP!Held(G(<<st.head.off, st.head.len>>), W(st.head.t0)) ELSE OP!NoHead

(* the model's atoms for the recorded ones: lengths are checked apart *)
Key(a) == IF a[1] \in {"ver", "held", "rd"} THEN <<a[1], a[2]>>
          ELSE IF a[1] = "redial" THEN <<"redial", W(a[2]), W(a[3])>>
          ELSE a
Keys(rs) == [k \in 1..Len(rs) |-> Key(rs[k])]
LenOk(s, rs) == \A k \in 1..Len(rs) :
                  rs[k][1] \in {"ver", "rd"} => \E g \in s.sto : g.off = rs[k][2] /\ g.len = rs[k][3]

(* the model's state agrees with the recorded one *)
Same(s, st) == /\ s.run = st.run /\ s.sw = W(st.sw) /\ s.lastp = W(st.lastp) /\ s.lastb = W(st.lastb)
               /\ s.head = HeadOf(st) /\ s.rel = st.rel /\ s.nv = st.nv

(* poll_timeout is the minimum of the timers the model holds, or a retry time (not visible) below it *)
PollOk(cf, s, st) ==
    LET mp == OP!Poll(cf, s)
    IN IF ~st.poll.p THEN ~mp.p
       ELSE ~mp.p \/ U!Le(W(st.poll.v), mp.v)

Init == i = 1 /\ m = OP!Init({}, 0) /\ c = [none |-> TRUE]

(* ---- the start of a run ---- *)
Begin ==
    /\ Trace[i].t = "vtrun"
    /\ LET L == Trace[i]
           cf == [o0 |-> L.o0, wg |-> GSet(L.wg), hasdl |-> L.hasdl, dl |-> W(L.dl), striped |-> L.striped,
                  hb |-> L.hb, nvl |-> L.nvl]
           sto == GSet(L.sto)
           out == OP!StartOutcome(L.len, L.er, cf.wg \subseteq sto, L.np)
           m0 == OP!Init(sto, L.np)
           run == out = "running"
       IN /\ L.post.run = run
          /\ W(L.post.sw) = m0.sw /\ W(L.post.lastp) = OP!Z /\ W(L.post.lastb) = OP!Z /\ W(L.post.tw) = OP!Z
          /\ ~L.post.head.h /\ ~L.post.rel /\ L.post.nv = 0
          /\ L.tr = (IF out = "BadRoot" THEN <<<<"fail", "BadRoot">>>>
                     ELSE IF out = "complete" THEN <<<<"done">>>>
                     ELSE IF out = "NoProvider" THEN <<<<"fail", "NoProvider">>>>
                     ELSE <<>>)
          /\ m' = [m0 EXCEPT !.run = run, !.treq = W(L.post.treq)]
          /\ c' = cf
    /\ i' = i + 1

(* ---- the recorded records an event step consumes, in order ---- *)
RECURSIVE Fold(_, _, _, _, _)
Fold(cf, s, now, rs, k) ==
    IF k > Len(rs) THEN s
    ELSE LET a == rs[k]
             s2 == IF a[1] = "ver" THEN OP!Verify(cf, s, now, G(<<a[2], a[3]>>))
                   ELSE IF a[1] = "liar" THEN OP!Evict(s, now, FALSE)
                   ELSE IF a[1] = "fail" /\ a[2] = "Store" THEN OP!Fail(s, "Store")
                   ELSE s
         IN Fold(cf, s2, now, rs, k + 1)

\* the Evict operator emits its own "liar" and "fail" records, and Fail its own: the fold must not repeat a recorded
\* "fail" that Evict produced, so only a Store refusal is an input
EvStep(L) ==
    LET now == W(L.now)
        post == L.post
        s0 == [m EXCEPT !.ev = <<>>]
        s1 == IF W(post.lastb) = now THEN OP!ByteLive(s0, now) ELSE s0
        s2 == IF W(post.lastp) = now THEN OP!Arrival(s1, now) ELSE s1
        s3 == Fold(c, s2, now, L.tr, 1)
    IN \E endc \in BOOLEAN :
         LET s4 == IF endc /\ s3.run THEN OP!CheckDone(c, s3, now) ELSE s3
         IN /\ Same(m, L.pre)
            /\ Same(s4, post)
            /\ s4.ev = Keys(L.tr)
            /\ LenOk(s4, L.tr)
            /\ W(post.treq) = m.treq \/ (m.treq = OP!Z /\ W(post.treq) = now)
            /\ W(post.tw) = m.tw \/ (U!Le(m.tw, now) /\ W(post.tw) = OP!SAdd(now, OP!StealHalf))
            /\ PollOk(c, [s4 EXCEPT !.tw = W(post.tw)], post)
            /\ m' = [s4 EXCEPT !.treq = W(post.treq), !.tw = W(post.tw), !.ev = <<>>]

ToStep(L) ==
    LET now == W(L.now)
        post == L.post
        s0 == [m EXCEPT !.ev = <<>>]
    IN \E rearm \in BOOLEAN :
         LET s4 == OP!OnTimeout(c, s0, now, W(L.w), W(L.lv), rearm, OP!Z)
         IN /\ Same(m, L.pre)
            /\ Same(s4, post)
            /\ s4.ev = Keys(L.tr)
            /\ LenOk(s4, L.tr)
            /\ W(post.treq) = m.treq \/ (m.treq = OP!Z /\ W(post.treq) = now)
            /\ W(post.tw) = s4.tw
            /\ PollOk(c, [s4 EXCEPT !.treq = W(post.treq)], post)
            /\ m' = [s4 EXCEPT !.treq = W(post.treq), !.ev = <<>>]

(* consecutive steps in which only stream bytes arrived, written as one line: BYTE_LIVE at the first time, then, as the
   fold of BYTE_LIVE over the later times keeps the largest of its gaps (Lean: byteLive_run), the largest gap and the
   last time *)
BsStep(L) ==
    LET s1 == OP!ByteLive([m EXCEPT !.ev = <<>>], W(L.t1))
        s2 == IF L.n > 1
              THEN [s1 EXCEPT !.sw = OP!Mx(s1.sw, OP!Mn(OP!ByteCap, OP!SMul3(W(L.mg)))), !.lastb = W(L.tn)]
              ELSE s1
    IN /\ Same(m, L.pre)
       /\ Same(s2, L.post)
       /\ PollOk(c, s2, L.post)
       /\ m' = s2

Step ==
    /\ Trace[i].t = "vt"
    /\ IF Trace[i].k = "ev" THEN EvStep(Trace[i]) ELSE IF Trace[i].k = "bs" THEN BsStep(Trace[i]) ELSE ToStep(Trace[i])
    /\ UNCHANGED c
    /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (Begin \/ Step)) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of the operators of ValuesTimeOps.tla
TraceAccepted == <>(i = Len(Trace) + 1)
=============================================================================
