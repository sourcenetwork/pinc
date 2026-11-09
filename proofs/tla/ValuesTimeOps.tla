---------------------------- MODULE ValuesTimeOps ----------------------------
(***************************************************************************)
(* The time rules of the value fetch (vinc-values fetch/recv.rs and        *)
(* fetch/stall.rs), written step for step on the machine integers of       *)
(* U64.tla, with no variables: ValuesTime.tla model checks them over all   *)
(* inputs of a small world, TraceValuesTime.tla compares the recorded      *)
(* behaviour of the real Fetch with the same operators.                    *)
(*                                                                         *)
(* A time is a u64 word of U64.tla (nanoseconds); a saturating operation   *)
(* of the code is SAdd, SSub, SMul2, SMul3, SMul4 (exact: a repeated       *)
(* saturating add is the saturating product). A byte offset or length is a *)
(* plain integer (the code adds them without saturation; they are bounded  *)
(* by the value length, far below 2^31 in the checked worlds).             *)
(*                                                                         *)
(* The configuration `c` of a fetch: c.o0 the first request offset,        *)
(* c.wg the set of groups wanted (each a record [off, len]), c.dl the      *)
(* deadline word or c.hasdl = FALSE, c.striped, c.we the end of the wanted  *)
(* ranges in delivery order (the end of the last one asked), c.hb =        *)
(* HOLD_B, c.nvl = HOLD_NV. The state `s` holds the fields of `Fetch` the rules read or    *)
(* write: run, sw, lastp, lastb, treq, tw, rt (0 = none), head (NoHead or  *)
(* [h, g, t0] with the held group g), rel, nv, sto (the verified groups),  *)
(* trusted, and ev, the records and events the last operator emitted, in   *)
(* order: <<"ver", off>>, <<"held", off>>, <<"rel", off, why>>, <<"rd",    *)
(* off>>, <<"done">>, <<"fail", reason>>, <<"redial", wait, next>>.        *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/ValuesTime.lean (the same functions  *)
(* on natural numbers with saturation), proved in ValuesTimeHold, -Inv,    *)
(* -Bound, -Stall and -Deadline.                                           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64

Z == U!Zero

(* ---- saturating time arithmetic ---- *)
SAdd(a, b) == LET r == U!Add(a, b) IN IF U!Fits(r) THEN r ELSE U!Max64
SSub(a, b) == IF U!Lt(a, b) THEN Z ELSE U!Sub(a, b)
SMul2(a) == SAdd(a, a)
SMul3(a) == SAdd(SAdd(a, a), a)
SMul4(a) == SMul2(SMul2(a))
Mn(a, b) == U!Min(a, b)
Mx(a, b) == U!Max(a, b)

(* ---- the constants of knobs.rs, in nanoseconds ---- *)
NsOne == <<51712, 15258, 0, 0, 0>>
MsOne == <<16960, 15, 0, 0, 0>>
RECURSIVE MulK(_, _)
MulK(a, k) == IF k = 0 THEN Z
              ELSE IF k % 2 = 0 THEN LET h == MulK(a, k \div 2) IN SAdd(h, h)
              ELSE SAdd(a, MulK(a, k - 1))
Secs(k) == MulK(NsOne, k)
Millis(k) == MulK(MsOne, k)

HoldMax == Secs(2)
StallWait == Secs(4)
StallCap == Secs(16)
ArkCap == Secs(40)
ByteCap == Secs(60)
RttCap == Secs(60)
SlowRtt == Millis(250)
LiveCap == Secs(90)
StealHalf == Secs(1)
OpenRetry == Millis(200)

NoHead == [h |-> FALSE]
Skip == [off |-> -1, len |-> 0]    \* a frame skipped as already stored
Held(g, t0) == [h |-> TRUE, g |-> g, t0 |-> t0]

Init(sto, trusted) ==
    [run |-> TRUE, sw |-> StallWait, lastp |-> Z, lastb |-> Z, treq |-> Z, tw |-> Z, rt |-> Z,
     head |-> NoHead, rel |-> FALSE, nv |-> 0, sto |-> sto, trusted |-> trusted, ev |-> <<>>]

(* ---- the verified set: the groups, and the run of verified bytes that starts at e ---- *)
RECURSIVE Chain(_, _)
Chain(sto, e) ==
    IF \E g \in sto : g.off = e
    THEN LET g == CHOOSE g \in sto : g.off = e IN g.len + Chain(sto, e + g.len)
    ELSE 0

RECURSIVE SumLen(_)
SumLen(S) == IF S = {} THEN 0 ELSE LET g == CHOOSE g \in S : TRUE IN g.len + SumLen(S \ {g})

WantedDone(c, s) == c.wg \subseteq s.sto

Emit(s, es) == [s EXCEPT !.ev = s.ev \o es]

(* ---- HEAD_HOLD (recv.rs) ---- *)
HoldWhy(c, s, h, t, force) ==
    LET e == h.g.off + h.g.len
        b == Chain(s.sto, e)
    IN IF force # "none" THEN force
       ELSE IF b >= c.hb THEN "buffered"
       ELSE IF e + b >= c.we THEN "tail"
       ELSE IF s.nv >= c.nvl THEN "granules"
       ELSE IF ~U!Lt(t, SAdd(h.t0, HoldMax)) THEN "timeout"
       ELSE "none"

HoldCheck(c, s, t, force) ==
    IF ~s.head.h THEN s
    ELSE LET why == HoldWhy(c, s, s.head, t, force)
         IN IF why = "none" THEN s
            ELSE [Emit(s, <<<<"rel", s.head.g.off, why>>, <<"rd", s.head.g.off>>>>) EXCEPT !.head = NoHead, !.rel = TRUE]

CheckDone(c, s, t) ==
    LET s1 == HoldCheck(c, s, t, "none")
    IN IF WantedDone(c, s1)
       THEN LET s2 == HoldCheck(c, s1, t, "done") IN [Emit(s2, <<<<"done">>>>) EXCEPT !.run = FALSE]
       ELSE s1

(* group_verified for a group whose bytes are written and committed *)
GroupVerified(c, s, t, g) ==
    LET s0 == Emit(s, <<<<"ver", g.off>>>>)
        capture == ~s0.rel /\ g.off <= c.o0 /\ c.o0 < g.off + g.len
        s1 == IF capture
              THEN [Emit(s0, <<<<"held", g.off>>>>) EXCEPT
                       !.head = Held(g, IF s0.head.h THEN s0.head.t0 ELSE t), !.nv = 0]
              ELSE LET s2 == Emit(s0, <<<<"rd", g.off>>>>)
                   IN IF s2.head.h THEN HoldCheck(c, [s2 EXCEPT !.nv = s2.nv + 1], t, "none") ELSE s2
    IN CheckDone(c, s1, t)

(* store_group then group_verified; a group another stream already stored (the race of two streams on one group) is
   neither written nor announced again: only its Verified record and the completion check run *)
Verify(c, s, t, g) ==
    IF g \in s.sto THEN CheckDone(c, Emit(s, <<<<"ver", g.off>>>>), t)
    ELSE GroupVerified(c, [s EXCEPT !.sto = s.sto \cup {g}], t, g)

Fail(s, r) == [Emit(s, <<<<"fail", r>>>>) EXCEPT !.run = FALSE]

(* ---- STALL_REDIAL (recv.rs arrival and on_readable, stall.rs) ---- *)
Arrival(s, t) ==
    LET gap3 == SMul3(SSub(t, s.lastp))
    IN [s EXCEPT !.sw = IF s.lastp # Z /\ U!Lt(s.sw, gap3) THEN Mn(ArkCap, gap3) ELSE s.sw, !.lastp = t]

ByteLive(s, t) ==
    [s EXCEPT !.sw = IF s.lastb # Z THEN Mx(s.sw, Mn(ByteCap, SMul3(SSub(t, s.lastb))))
                     ELSE IF s.treq # Z THEN Mx(s.sw, Mn(ByteCap, SMul2(SSub(t, s.treq))))
                     ELSE s.sw,
              !.lastb = t]

(* the stall timer counts from the later of the last frame, the last bytes and the first request, and runs once a
   request was sent (stall_base) *)
Lp(s) == Mx(s.lastp, s.treq)
Base(s) == Mx(Mx(s.lastp, s.lastb), s.treq)
Due(s, t) == s.treq # Z /\ U!Le(SAdd(Base(s), s.sw), t)
RttWait(s, t, w) == U!Lt(s.sw, w) /\ U!Lt(t, SAdd(Lp(s), w))
NextSw(sw) == Mn(SMul2(sw), StallCap)

(* the first block of on_timeout; w = stall_rtt, lv = stall_live as the session reports them *)
StallStep(s, t, w, lv) ==
    IF ~Due(s, t) THEN s
    ELSE IF RttWait(s, t, w) THEN [s EXCEPT !.sw = w]
    ELSE IF lv # Z THEN [s EXCEPT !.sw = SAdd(SSub(t, Lp(s)), lv)]
    ELSE [Emit(s, <<<<"redial", s.sw, NextSw(s.sw)>>>>) EXCEPT !.lastp = t, !.sw = NextSw(s.sw)]

Late(c, t) == c.hasdl /\ U!Lt(c.dl, t)

(* poll_timeout: the minimum of the armed timers, [p |-> FALSE] if there is none *)
Timers(c, s) ==
    LET a == IF s.treq # Z THEN {SAdd(Base(s), s.sw)} ELSE {}
        b == IF s.head.h THEN {SAdd(s.head.t0, HoldMax)} ELSE {}
        d == IF s.tw # Z THEN {s.tw} ELSE {}
        e == IF c.hasdl THEN {SAdd(c.dl, U!One)} ELSE {}
        f == IF s.rt # Z THEN {s.rt} ELSE {}
    IN a \cup b \cup d \cup e \cup f
Poll(c, s) ==
    IF ~s.run THEN [p |-> FALSE]
    ELSE LET T == Timers(c, s)
         IN IF T = {} THEN [p |-> FALSE] ELSE [p |-> TRUE, v |-> CHOOSE m \in T : \A x \in T : U!Le(m, x)]

(* on_timeout: the stall block (skipped past the deadline), the head block, the steal re-check, the deadline, the
   retries; rearm = the re-check armed the steal timer again, rtn = the retry timer after the due retries *)
OnTimeout(c, s, t, w, lv, rearm, rtn) ==
    IF ~s.run THEN s
    ELSE LET late == Late(c, t)
             s1 == IF late THEN s ELSE StallStep(s, t, w, lv)
             s2 == IF s1.head.h THEN CheckDone(c, HoldCheck(c, s1, t, "none"), t) ELSE s1
         IN IF ~s2.run THEN s2
            ELSE LET s3 == IF ~late /\ c.striped /\ s2.tw # Z /\ U!Le(s2.tw, t)
                           THEN [s2 EXCEPT !.tw = IF rearm THEN SAdd(t, StealHalf) ELSE Z] ELSE s2
                 IN IF late THEN Fail(s3, "Deadline")
                    ELSE IF s3.rt # Z /\ U!Le(s3.rt, t) THEN [s3 EXCEPT !.rt = rtn] ELSE s3

(* ---- the other inputs ---- *)
FrameIn(c, s, t, byte, g) ==
    LET s1 == IF byte THEN ByteLive(s, t) ELSE s
        s2 == Arrival(s1, t)
    IN IF g = Skip THEN s2 ELSE Verify(c, s2, t, g)
FrameStoreFail(s, t, byte) == Fail(Arrival(IF byte THEN ByteLive(s, t) ELSE s, t), "Store")
Evict(s, t, byte) ==
    LET s1 == IF byte THEN ByteLive(s, t) ELSE s
        s2 == Emit(s1, <<<<"liar">>>>)
    IN IF s1.trusted <= 1 THEN Fail([s2 EXCEPT !.trusted = 0], "Lied") ELSE [s2 EXCEPT !.trusted = s1.trusted - 1]

(* what Fetch::start reports: the bad root first, then nothing missing, then no provider; else the fetch runs *)
StartOutcome(len, er, wantDone, np) ==
    IF len = 0 /\ ~er THEN "BadRoot"
    ELSE IF wantDone THEN "complete"
    ELSE IF np = 0 THEN "NoProvider"
    ELSE "running"
=============================================================================
