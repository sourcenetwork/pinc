----------------------------- MODULE RecoveryOps ------------------------------
(***************************************************************************)
(* The operations of vinc-transport recovery/engine.rs, ack.rs, loss.rs,   *)
(* pto.rs, sent.rs and rtt.rs (loss recovery), step for step. Recovery.tla *)
(* checks them over every interleaving at small sizes; TraceRecovery.tla   *)
(* replays the recorded calls of the real code through the same operators. *)
(*                                                                         *)
(* One operator per public call of Recovery: Send (on_packet_sent),        *)
(* Untracked (on_packet_untracked), Ack (on_ack_received), Timeout         *)
(* (on_timeout), Flush (flush_in_flight), SwitchPath, FollowPath, SetKind  *)
(* (set_path_kind), SeedRtt, Activity (note_peer_activity), Asleep, Down,  *)
(* NodeRtt, HsRtt. The state R holds the sent ring, the byte accounts, the *)
(* round-trip estimate, the probe timer, the paths and the reorder lens.   *)
(* The congestion controller and the pacer are not in the state (they are  *)
(* the subject of CubicOps.tla); the model records only what recovery      *)
(* decides for them (the packets lost, the window saved by the first probe *)
(* timeout, restored by an acknowledgement of that packet).                *)
(*                                                                         *)
(* Time. The code counts nanoseconds in u64; TLC integers are 32 bits, so  *)
(* the sums and products of the code are the saturating operators SAdd,    *)
(* SMul, SSub below, saturating at TOP. TOP stands for u64::MAX: a value   *)
(* that reaches it is above every time of every checked run (the model     *)
(* checker bounds its clock, the trace test keeps every time below 2^31    *)
(* ns), so a comparison with a saturated value has the answer the code     *)
(* gives. A TLC run that would overflow a 32-bit integer stops with an     *)
(* error instead of wrapping. The constants MS and SEC scale the time:     *)
(* TLC runs them small, the trace runs the real 10^6 and 10^9.             *)
(*                                                                         *)
(* Not modelled: a packet number above 2^62 - 1 (the model never produces  *)
(* one, the code answers PacketNumberOutOfRange), the cwnd and ssthresh    *)
(* values of the saved window (only the packet that saved them), the       *)
(* limited_at stamp (it feeds the pacer and the window resume only).       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N, MS, SEC, MP, TOP, MAXG, LATEN

Mx(a, b) == IF a > b THEN a ELSE b
Mn(a, b) == IF a < b THEN a ELSE b
SAdd(a, b) == IF a > TOP - b THEN TOP ELSE a + b
SSub(a, b) == IF a > b THEN a - b ELSE 0
SMul(a, b) == IF a = 0 \/ b = 0 THEN 0 ELSE IF a > TOP \div b THEN TOP ELSE a * b
Mul9d8(a) == SAdd(SMul(a \div 8, 9), (9 * (a % 8)) \div 8)     \* exactly a * 9 / 8

IRTT == SMul(MS, 333)
AD == SMul(MS, 25)               \* the receiver's delay allowed for
LONG == SMul(MS, 250)
OLDX == SMul(MS, 50)
RELAYMIN == (SEC \div 2) * 3
GRET == SMul(SEC, 2)             \* GHOST_RETENTION
GSCAN == SMul(MS, 25)
LATESAMPLE == SMul(SEC, 4)
PTOCAP == SMul(SEC, 2)
SLOWSRTT == SMul(LONG, 4)
GIVEUPSLOW == SMul(SEC, 20)

(* ---- the states ---- *)
NoNew == <<-1, 0, 0>>
S0 == [ap |-> 0, ab |-> 0, lap |-> 0, lp |-> 0, lb |-> 0]

Init0 == [ring |-> <<>>, ls |-> -1, la |-> -1, sent |-> 0, acked |-> 0, lost |-> 0, inf |-> 0, infp |-> 0,
          lt |-> -1, pc |-> 0, lp |-> 0, asleep |-> FALSE, down |-> FALSE, hrd |-> 0, clock |-> 0, tgr |-> 0, lrtt |-> 0,
          rtt |-> [lat |-> -1, sm |-> IRTT, var |-> IRTT \div 2, mn |-> -1, has |-> FALSE],
          rel |-> [p \in 0..(MP - 1) |-> FALSE], prtt |-> [p \in 0..(MP - 1) |-> 0], act |-> 0, flip |-> -1,
          late |-> <<>>, saved |-> -1, reo |-> [p \in 0..(MP - 1) |-> [ext |-> 0, seen |-> -1]], gs |-> 0, lat |-> 0]

(* ---- the round-trip estimate (rtt.rs) ---- *)
RttUpdate(e, x) ==
    LET e1 == [e EXCEPT !.lat = x, !.mn = IF e.mn < 0 THEN x ELSE Mn(e.mn, x)]
        diff == IF e.sm > x THEN e.sm - x ELSE x - e.sm
    IN IF ~e.has THEN [e1 EXCEPT !.has = TRUE, !.sm = x, !.var = x \div 2]
       ELSE [e1 EXCEPT !.var = (3 * (e.var \div 4)) + (SAdd(3 * (e.var % 4), diff) \div 4),
                       !.sm = SAdd(7 * (e.sm \div 8), (SAdd(7 * (e.sm % 8), x) \div 8))]
RttSeed(e, x) == IF e.has THEN e ELSE [e EXCEPT !.has = TRUE, !.sm = Mx(x, MS), !.var = Mx(x, MS) \div 2]
IsLongRtt(mn) == mn >= 0 /\ mn >= LONG

(* ---- the sent ring (sent.rs); slot: pn time size path rep probe fr st at ---- *)
\* st: 0 in flight, 1 declared lost (a ghost), 2 done
RECURSIVE Trim(_, _)
Trim(ring, now) ==
    IF ring = <<>> THEN ring
    ELSE LET h == Head(ring)
         IN IF h.st = 2 \/ (h.st = 1 /\ SAdd(h.at, GRET) < now) THEN Trim(Tail(ring), now) ELSE ring
HasRoom(ring) == Len(ring) < N \/ (Len(ring) > 0 /\ Head(ring).st # 0)
Push(ring, slot) ==
    IF Len(ring) = N
    THEN IF Head(ring).st = 0 THEN [ok |-> FALSE, ring |-> ring] ELSE [ok |-> TRUE, ring |-> Append(Tail(ring), slot)]
    ELSE [ok |-> TRUE, ring |-> Append(ring, slot)]
LowerBound(ring, pn) == Cardinality({i \in DOMAIN ring : ring[i].pn < pn}) + 1
HasGhost(ring) == \E i \in DOMAIN ring : ring[i].st = 1
Ghosts(ring) == Cardinality({i \in DOMAIN ring : ring[i].st = 1})
LimitGhosts(ring) ==
    LET ex == Mx(0, Ghosts(ring) - MAXG)
    IN [i \in DOMAIN ring |->
          IF ring[i].st = 1 /\ Cardinality({j \in 1..i : ring[j].st = 1}) <= ex THEN [ring[i] EXCEPT !.st = 2] ELSE ring[i]]
FirstIF(ring) == IF \E i \in DOMAIN ring : ring[i].st = 0 THEN CHOOSE i \in DOMAIN ring : ring[i].st = 0 /\ \A j \in 1..(i - 1) : ring[j].st # 0 ELSE 0
NewestIFTime(ring) ==
    IF \E i \in DOMAIN ring : ring[i].st = 0
    THEN ring[CHOOSE i \in DOMAIN ring : ring[i].st = 0 /\ \A j \in (i + 1)..Len(ring) : ring[j].st # 0].time
    ELSE -1
IsGhostData(f) == f     \* a frame is recorded as TRUE when it is stream data with bytes and no end
AnyGhost(fr) == \E k \in DOMAIN fr : fr[k]
DataFrames(fr) == SelectSeq(fr, LAMBDA f : f)
IsRelay(R, p) == p < MP /\ R.rel[p]

(* ---- events and results ---- *)
Ev(k, pn, size, fr, f1, f2) == [k |-> k, pn |-> pn, size |-> size, fr |-> fr, f1 |-> f1, f2 |-> f2]

(* ---- the reorder lens (loss.rs) ---- *)
ReoHold(R) == Mx(SMul(SEC, 2), SMul(R.rtt.sm, 16))
ReoExtent(R, p, now) ==
    LET q == R.reo[p]
    IN IF q.seen >= 0 /\ SSub(now, q.seen) < ReoHold(R) THEN q.ext ELSE -1
NoteOvertaken(R, now, pn, time, p) ==
    IF R.la < 0 \/ SAdd(pn, 3) > R.la \/ p # R.act \/ IsRelay(R, p) THEN R
    ELSE LET spread == SSub(R.lat, time)
             kept == Mx(0, ReoExtent(R, p, now))
         IN [R EXCEPT !.reo[p] = [ext |-> Mx(kept, spread), seen |-> now]]

(* ---- late sends (engine.rs LateSends) ---- *)
LateInsert(ls, pn, time) ==
    LET base == IF Len(ls) = LATEN
                THEN LET m == CHOOSE i \in DOMAIN ls : \A j \in DOMAIN ls : ls[i][1] <= ls[j][1]
                     IN SubSeq(ls, 1, m - 1) \o SubSeq(ls, m + 1, Len(ls))
                ELSE ls
    IN Append(base, <<pn, time>>)
LateHas(ls, pn) == \E i \in DOMAIN ls : ls[i][1] = pn
LateTime(ls, pn) == IF LateHas(ls, pn) THEN ls[CHOOSE i \in DOMAIN ls : ls[i][1] = pn][2] ELSE -1
LateTake(ls, pn) ==
    IF LateHas(ls, pn)
    THEN LET m == CHOOSE i \in DOMAIN ls : ls[i][1] = pn IN SubSeq(ls, 1, m - 1) \o SubSeq(ls, m + 1, Len(ls))
    ELSE ls

(* ---- losing a packet (lose_at, settle_losses) ---- *)
\* Y: [r, ev, s, nl]; nl is the send time of the newest loss that counts, -1 for none
LoseAt(Y, i, now) ==
    LET R == Y.r
        sl == R.ring[i]
        counts == ~sl.rep /\ ~sl.probe
        ghost == counts /\ AnyGhost(sl.fr)
        R1 == [R EXCEPT !.ring[i].st = IF ghost THEN 1 ELSE 2, !.ring[i].at = IF ghost THEN now ELSE sl.at,
                        !.inf = R.inf - sl.size, !.lost = R.lost + sl.size, !.infp = R.infp - 1,
                        !.late = IF counts THEN LateInsert(R.late, sl.pn, sl.time) ELSE R.late]
    IN [r |-> R1, ev |-> Append(Y.ev, Ev("lost", sl.pn, sl.size, sl.fr, counts, sl.probe)),
        s |-> [Y.s EXCEPT !.lp = Y.s.lp + 1, !.lb = Y.s.lb + sl.size],
        nl |-> IF counts THEN Mx(Y.nl, sl.time) ELSE Y.nl]
Settle(Y) == IF Y.s.lp > 0 THEN [Y EXCEPT !.r.ring = LimitGhosts(Y.r.ring)] ELSE Y

(* ---- loss detection (loss.rs detect_lost) ---- *)
LossRtt(R) == IF R.rtt.has THEN Mx(IF R.rtt.lat < 0 THEN 0 ELSE R.rtt.lat, R.rtt.sm) ELSE IRTT
LossDelay(R) == Mx(Mul9d8(LossRtt(R)), MS)
\* the verdict of one packet: [lost |-> by count, thr |-> the age threshold]
Verdict(R, sl, largest, now) ==
    LET rtt == LossRtt(R)
        delay == LossDelay(R)
        p == sl.path
    IN IF p # R.act
       THEN LET widest == Mx(rtt, R.prtt[p])
                d2 == SAdd(SMul(widest, 4), OLDX)
            IN [lost |-> FALSE, thr |-> IF R.rel[p] THEN Mx(d2, RELAYMIN) ELSE d2]
       ELSE IF R.rel[p] /\ R.flip >= 0 /\ sl.time <= R.flip
       THEN [lost |-> FALSE, thr |-> Mx(SAdd(SMul(rtt, 4), OLDX), RELAYMIN)]
       ELSE IF R.rel[p]
       THEN [lost |-> FALSE, thr |-> SAdd(Mx(SMul(rtt, 2), delay), OLDX)]
       ELSE IF ReoExtent(R, p, now) >= 0
       THEN [lost |-> FALSE,
             thr |-> Mn(Mx(delay, SAdd(rtt, SMul(ReoExtent(R, p, now), 2))), SMul(rtt, 4))]
       ELSE [lost |-> largest >= SAdd(sl.pn, 3), thr |-> delay]

RECURSIVE DetectLoop(_, _, _, _)
DetectLoop(Y, i, now, largest) ==
    IF i > Len(Y.r.ring) \/ Y.r.ring[i].pn > largest THEN Y
    ELSE LET sl == Y.r.ring[i] IN
         IF sl.st # 0 THEN DetectLoop(Y, i + 1, now, largest)
         ELSE LET v == Verdict(Y.r, sl, largest, now)
                  due == SAdd(sl.time, v.thr)
              IN IF ~(v.lost \/ now >= due)
                 THEN DetectLoop([Y EXCEPT !.r.lt = IF Y.r.lt < 0 THEN due ELSE Mn(Y.r.lt, due)], i + 1, now, largest)
                 ELSE DetectLoop(LoseAt(Y, i, now), i + 1, now, largest)

\* Y in, Y out (the summary and events accumulate)
Detect(Y, now, largest) == Settle(DetectLoop([Y EXCEPT !.r.lt = -1], 1, now, largest))

(* ---- the probe timer (pto.rs) ---- *)
Node(R) == Mx(R.tgr, R.lrtt)
PtoSeed(R) == Mx(IRTT, SMul(Node(R), 2))
PtoSrtt(R) == IF R.rtt.has THEN R.rtt.sm ELSE PtoSeed(R)
PtoSlow(R) == IsLongRtt(R.rtt.mn) \/ PtoSrtt(R) >= SLOWSRTT
PtoWide(R) == Mx(PTOCAP, SMul(PtoSrtt(R), 2))
PtoDur(R) ==
    LET srtt == PtoSrtt(R)
        var == IF R.rtt.has THEN R.rtt.var ELSE PtoSeed(R) \div 2
        base == SAdd(SAdd(srtt, Mx(SMul(var, 4), MS)), AD)
        shifted == Mn(SMul(base, 2 ^ Mn(R.pc, 6)), SMul(PtoWide(R), 4))
    IN Mn(shifted, IF PtoSlow(R) THEN PtoWide(R) ELSE PTOCAP)
PtoDeadline(R) ==
    LET nw == NewestIFTime(R.ring) IN IF nw < 0 THEN -1 ELSE SAdd(Mx(nw, R.lp), PtoDur(R))
NextTimeout(R) ==
    LET pd == PtoDeadline(R)
    IN IF R.lt < 0 THEN pd ELSE IF pd < 0 THEN R.lt ELSE Mn(R.lt, pd)

IsThin(R) == IF ~R.rtt.has THEN TRUE
             ELSE Mx(Mx(Node(R), Mx(R.rtt.mn, 0)), R.rtt.sm \div 2) >= LONG
Health(R, now) ==
    LET slow == IsLongRtt(R.rtt.mn) \/ IsThin(R)
        srtt == IF R.rtt.has THEN R.rtt.sm ELSE 0
        need == Mx(IF slow THEN GIVEUPSLOW ELSE 0, SMul(srtt, 8))
    IN IF R.pc >= 10 /\ SSub(now, R.hrd) >= need THEN "Dead" ELSE IF R.pc >= 3 THEN "Degraded" ELSE "Healthy"

DeclareOldest(Y, now) ==
    LET i == FirstIF(Y.r.ring)
    IN IF i = 0 THEN Y
       ELSE LET Y1 == IF Y.r.pc = 1 THEN [Y EXCEPT !.r.saved = Y.r.ring[i].pn] ELSE Y
            IN Settle(LoseAt(Y1, i, now))

\* the result of a call that returns a summary: [r, ev, s, err, ping]
Res(R, ev, s, err, ping) == [r |-> R, ev |-> ev, s |-> s, err |-> err, ping |-> ping]

Timeout(R, now) ==
    LET R0 == [R EXCEPT !.clock = Mx(R.clock, now)]
        Y0 == [r |-> R0, ev |-> <<>>, s |-> S0, nl |-> -1]
        Y1 == IF R0.lt >= 0 /\ now >= R0.lt /\ R0.la >= 0 THEN Detect(Y0, now, R0.la) ELSE Y0
        R1 == Y1.r
        d == PtoDeadline(R1)
    IN IF d < 0 \/ now < d THEN Res(R1, Y1.ev, Y1.s, "ok", FALSE)
       ELSE IF R1.asleep THEN Res([R1 EXCEPT !.lp = now], Y1.ev, Y1.s, "ok", FALSE)
       ELSE LET R2 == [R1 EXCEPT !.pc = IF R1.down THEN R1.pc ELSE R1.pc + 1, !.lp = now]
                Y2 == [Y1 EXCEPT !.r = R2]
            IN IF Health(R2, now) = "Dead" THEN Res(R2, Y1.ev, Y1.s, "ok", FALSE)
               ELSE LET Y3 == DeclareOldest(Y2, now) IN Res(Y3.r, Y3.ev, Y3.s, "ok", TRUE)

(* ---- flush_in_flight ---- *)
RECURSIVE FlushLoop(_, _, _)
FlushLoop(Y, i, now) ==
    IF i > Len(Y.r.ring) THEN Y
    ELSE LET sl == Y.r.ring[i] IN
         IF sl.st # 0 THEN FlushLoop(Y, i + 1, now)
         ELSE LET R1 == [Y.r EXCEPT !.ring[i].st = 1, !.ring[i].at = now, !.inf = Y.r.inf - sl.size,
                                    !.lost = Y.r.lost + sl.size, !.infp = Y.r.infp - 1]
              IN FlushLoop([r |-> R1, ev |-> Append(Y.ev, Ev("lost", sl.pn, sl.size, sl.fr, ~sl.rep /\ ~sl.probe, sl.probe)),
                            s |-> [Y.s EXCEPT !.lp = Y.s.lp + 1, !.lb = Y.s.lb + sl.size], nl |-> -1], i + 1, now)
Flush(R, now) ==
    LET Y == FlushLoop([r |-> [R EXCEPT !.clock = Mx(R.clock, now)], ev |-> <<>>, s |-> S0, nl |-> -1], 1, now)
    IN Res([Y.r EXCEPT !.lt = -1, !.pc = 0, !.lp = 0, !.saved = -1], Y.ev, Y.s, "ok", FALSE)

(* ---- sending ---- *)
\* p: [pn, time, size, path, rep, probe, fr]
Send(R, p) ==
    IF R.ls >= 0 /\ p.pn <= R.ls THEN Res(R, <<>>, S0, "PacketNumberNotIncreasing", FALSE)
    ELSE IF p.path >= MP THEN Res(R, <<>>, S0, "PathOutOfRange", FALSE)
    ELSE LET R1 == [R EXCEPT !.clock = Mx(R.clock, p.time), !.ring = Trim(R.ring, p.time)]
             pu == Push(R1.ring, [pn |-> p.pn, time |-> p.time, size |-> p.size, path |-> p.path, rep |-> p.rep,
                                  probe |-> p.probe, fr |-> p.fr, st |-> 0, at |-> 0])
         IN IF ~pu.ok THEN Res(R1, <<>>, S0, "RingFull", FALSE)
            ELSE Res([R1 EXCEPT !.ring = pu.ring, !.ls = p.pn, !.sent = R1.sent + p.size, !.inf = R1.inf + p.size,
                                !.infp = R1.infp + 1], <<>>, S0, "ok", FALSE)
Untracked(R, pn) ==
    IF R.ls >= 0 /\ pn <= R.ls THEN Res(R, <<>>, S0, "PacketNumberNotIncreasing", FALSE)
    ELSE Res([R EXCEPT !.ls = pn], <<>>, S0, "ok", FALSE)

(* ---- acknowledgements (ack.rs) ---- *)
\* X: [r, ev, s, fl, nw, gh, err]; nw = <<pn, time, path>>
RECURSIVE AckRing(_, _, _, _)
AckRing(X, now, i, b) ==
    IF i > Len(X.r.ring) \/ X.r.ring[i].pn > b THEN X
    ELSE LET sl == X.r.ring[i] IN
         IF sl.st = 2 THEN AckRing(X, now, i + 1, b)
         ELSE IF sl.st = 1 /\ ~X.gh THEN AckRing(X, now, i + 1, b)
         ELSE IF sl.st = 1 /\ SSub(now, sl.at) > GRET THEN AckRing([X EXCEPT !.r.ring[i].st = 2], now, i + 1, b)
         ELSE
           LET late == sl.st = 1
               R1 == NoteOvertaken([X.r EXCEPT !.ring[i].st = 2], now, sl.pn, sl.time, sl.path)
           IN IF late
              THEN AckRing([X EXCEPT !.r = [R1 EXCEPT !.lost = R1.lost - sl.size, !.acked = R1.acked + sl.size],
                                     !.s.lap = X.s.lap + 1,
                                     !.ev = Append(X.ev, Ev("late", sl.pn, 0, DataFrames(sl.fr), FALSE, FALSE))],
                           now, i + 1, b)
              ELSE AckRing([X EXCEPT !.r = [R1 EXCEPT !.inf = R1.inf - sl.size, !.acked = R1.acked + sl.size,
                                                      !.infp = R1.infp - 1],
                                     !.s.ap = X.s.ap + 1, !.s.ab = X.s.ab + sl.size,
                                     !.ev = Append(X.ev, Ev("acked", sl.pn, sl.size, sl.fr, sl.probe, sl.rep)),
                                     !.nw = IF X.nw[1] < 0 \/ sl.pn > X.nw[1] THEN <<sl.pn, sl.time, sl.path>> ELSE X.nw],
                           now, i + 1, b)

RECURSIVE AckRanges(_, _, _, _)
AckRanges(X, now, rgs, k) ==
    IF k > Len(rgs) \/ X.err # "ok" THEN X
    ELSE LET a == rgs[k][1]
             b == rgs[k][2]
         IN IF a > b THEN [X EXCEPT !.err = "InvalidAckRange"]
            ELSE IF X.r.ls < 0 \/ b > X.r.ls THEN [X EXCEPT !.err = "AckOfUnsentPacket"]
            ELSE LET X1 == [X EXCEPT !.fl = Mx(X.fl, b),
                                     !.r.saved = IF X.r.saved >= a /\ X.r.saved <= b THEN -1 ELSE X.r.saved]
                 IN AckRanges(AckRing(X1, now, LowerBound(X1.r.ring, a), b), now, rgs, k + 1)

\* rgs: a sequence of <<start, end>>, largest first
Ack(R, now, rgs) ==
    LET R0 == [R EXCEPT !.clock = Mx(R.clock, now)]
        gh == SSub(now, R0.gs) >= GSCAN /\ HasGhost(R0.ring)
        R1 == IF gh THEN [R0 EXCEPT !.gs = now] ELSE R0
        X == AckRanges([r |-> R1, ev |-> <<>>, s |-> S0, fl |-> -1, nw |-> NoNew, gh |-> gh, err |-> "ok"], now, rgs, 1)
    IN IF X.err # "ok" THEN Res(X.r, X.ev, X.s, X.err, FALSE)
       ELSE IF X.fl < 0 THEN Res([X.r EXCEPT !.hrd = Mx(X.r.hrd, now)], X.ev, X.s, "ok", FALSE)
       ELSE
         LET R2 == [X.r EXCEPT !.hrd = Mx(X.r.hrd, now), !.la = Mx(X.r.la, X.fl)]
             lst == LateTime(R2.late, X.fl)
             R3 == [R2 EXCEPT !.late = LateTake(R2.late, X.fl)]
             seeded == lst >= 0 /\ X.nw[1] # X.fl /\ ~R3.rtt.has
             nw == IF seeded THEN <<X.fl, Mx(lst, SSub(now, LATESAMPLE)), R3.act>> ELSE X.nw
             R4 == IF seeded THEN [R3 EXCEPT !.pc = 0] ELSE R3
         IN IF nw[1] < 0 THEN Res([R4 EXCEPT !.ring = Trim(R4.ring, now)], X.ev, X.s, "ok", FALSE)
            ELSE
              LET sample == SSub(now, nw[2])
                  e2 == RttUpdate(R4.rtt, sample)
                  R5 == IF nw[1] = X.fl
                        THEN [R4 EXCEPT !.lat = nw[2], !.rtt = e2, !.tgr = Mx(e2.sm, R4.tgr - (R4.tgr \div 32)),
                                        !.prtt[nw[3]] = e2.sm]
                        ELSE R4
                  Y == Detect([r |-> [R5 EXCEPT !.pc = 0], ev |-> X.ev, s |-> X.s, nl |-> -1], now, X.fl)
              IN Res([Y.r EXCEPT !.ring = Trim(Y.r.ring, now)], Y.ev, Y.s, "ok", FALSE)

(* ---- configuration calls ---- *)
SwitchPath(R, p) ==
    IF p >= MP THEN [r |-> R, restarted |-> FALSE, err |-> "PathOutOfRange"]
    ELSE IF p = R.act THEN [r |-> R, restarted |-> FALSE, err |-> "ok"]
    ELSE IF R.rel[R.act] /\ R.rel[p] THEN [r |-> [R EXCEPT !.act = p], restarted |-> FALSE, err |-> "ok"]
    ELSE [r |-> [R EXCEPT !.act = p, !.flip = R.clock], restarted |-> TRUE, err |-> "ok"]
FollowPath(R, p) ==
    IF p >= MP THEN [r |-> R, err |-> "PathOutOfRange"]
    ELSE IF p # R.act THEN [r |-> [R EXCEPT !.act = p, !.flip = R.clock], err |-> "ok"]
    ELSE [r |-> R, err |-> "ok"]
SetKind(R, p, relay) == IF p >= MP THEN [r |-> R, err |-> "PathOutOfRange"] ELSE [r |-> [R EXCEPT !.rel[p] = relay], err |-> "ok"]
SeedRtt(R, x) == [R EXCEPT !.rtt = RttSeed(R.rtt, x)]
Activity(R, now) == [R EXCEPT !.hrd = Mx(R.hrd, now), !.clock = Mx(R.clock, now)]
Asleep(R, b) == [R EXCEPT !.asleep = b]
Down(R, b) == [R EXCEPT !.down = b]
NodeRtt(R, x) == [R EXCEPT !.tgr = x]
HsRtt(R, x) == [R EXCEPT !.lrtt = x]

(* ---- tail repair (tail.rs) ---- *)
TailNew == [burst |-> 0, cand |-> -1]
TailPacket(t, pn, plain, inel) ==
    LET b1 == Mn(t.burst + 1, 2)
        b2 == IF inel THEN 2 ELSE b1
    IN IF b2 > 1 THEN [burst |-> b2, cand |-> -1]
       ELSE [burst |-> b2, cand |-> IF plain THEN pn ELSE t.cand]
TailDrain(t) == [t |-> TailNew, c |-> t.cand]

(* ---- the facts every state satisfies ---- *)
SumSizes(ring, st) == LET F[i \in 0..Len(ring)] == IF i = 0 THEN 0 ELSE F[i - 1] + IF ring[i].st = st THEN ring[i].size ELSE 0 IN F[Len(ring)]
CountSt(ring, st) == Cardinality({i \in DOMAIN ring : ring[i].st = st})
=============================================================================
