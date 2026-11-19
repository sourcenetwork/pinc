------------------------------- MODULE CcOps --------------------------------
(***************************************************************************)
(* The operations of pinc-transport recovery/cubic.rs, round_exit.rs,      *)
(* delivery.rs and pacer.rs (congestion control and pacing), call for     *)
(* call. Cc.tla checks them over every interleaving at small sizes;        *)
(* TraceCc.tla replays the recorded calls of the real code through the    *)
(* same operators.                                                        *)
(*                                                                         *)
(* Numbers. TLC integers are 32 bits, so a product the code forms in u64   *)
(* or u128 is formed here with the saturating operators SAdd, SMul at TOP  *)
(* (which stands for u64::MAX: a value that reaches it is above every      *)
(* value of every checked run) or with MulDiv, the exact floor(a * m / d)  *)
(* of three numbers computed by long multiplication without ever forming   *)
(* the product (the domain: d at most 2^30, m at most 2^30). A TLC run that *)
(* would overflow a 32-bit integer stops with an error instead of          *)
(* wrapping. MAXC is the model's window cap: TLC cannot hold the code's    *)
(* 2^40, so the checked runs keep every window far below it and the cap    *)
(* is tested at a small MAXC by Cc.tla; the Lean model has the real one.   *)
(*                                                                         *)
(* The cubic term of congestion avoidance is a bounded step here: the     *)
(* origin K (an integer cube root of a 74-bit radicand) and the target    *)
(* W_max + 4 mss d^3 / 1e10 are not computed (TLC has no integers wide    *)
(* enough); an acknowledgement in congestion avoidance relates the state  *)
(* before and after by what the code guarantees of the step (AckRel): the  *)
(* window never falls, stays within the cap, ends at least at the Reno    *)
(* estimate, which is exact up to the window the step reached (between    *)
(* the window before and the window after). The Lean replay (TraceCc.lean) *)
(* computes the whole step at full width.                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MS, SEC, TOP, MAXC, MINC, INITC, BETALIM, MINMSS, MAXMSS, MINSAMP, EXITCW, GFAST, GMID, U32MAX, IRTT, BURST

Mx(a, b) == IF a > b THEN a ELSE b
Mn(a, b) == IF a < b THEN a ELSE b
SAdd(a, b) == IF a > TOP - b THEN TOP ELSE a + b
SMul(a, b) == IF a = 0 \/ b = 0 THEN 0 ELSE IF a > TOP \div b THEN TOP ELSE a * b
SSub(a, b) == IF a > b THEN a - b ELSE 0

FASTRTT == 2 * MS
SLOWRTT == 250 * MS

(* ---- exact floor(a * m / d) without the product (d in 1 .. 2^30, m < 2^30) ---- *)
RECURSIVE BitsOf(_, _)
BitsOf(v, acc) == IF v = 0 THEN acc ELSE BitsOf(v \div 2, <<v % 2>> \o acc)
\* bits is msb first; the pair is (quotient, remainder) of the prefix times ra by d
RECURSIVE Horner(_, _, _, _)
Horner(bits, ra, d, qr) ==
    IF bits = <<>> THEN qr
    ELSE LET q2 == IF 2 * qr[2] >= d THEN 2 * qr[1] + 1 ELSE 2 * qr[1]
             r2 == IF 2 * qr[2] >= d THEN 2 * qr[2] - d ELSE 2 * qr[2]
             q3 == IF Head(bits) = 1 /\ r2 + ra >= d THEN q2 + 1 ELSE q2
             r3 == IF Head(bits) = 1 THEN (IF r2 + ra >= d THEN r2 + ra - d ELSE r2 + ra) ELSE r2
         IN Horner(Tail(bits), ra, d, <<q3, r3>>)
MulDiv(a, m, d) == (m * (a \div d)) + Horner(BitsOf(m, <<>>), a % d, d, <<0, 0>>)[1]

(* ---- the states ---- *)
\* the controller; none is -1; ss = TOP is a threshold not set (u64::MAX)
Cc0 == [cwnd |-> INITC, ss |-> TOP, wmax |-> 0, west |-> 0, k |-> 0, epoch |-> -1, rec |-> -1, streak |-> 0,
        rend |-> 0, ref |-> -1, rmin |-> -1, samp |-> 0, pst |-> -1, pby |-> 0, rate |-> 0, slack |-> GMID]
Pc0 == [tokens |-> BURST, next |-> 0, start |-> 0]

(* ---- the slow-start exit detector ---- *)
OnSample(x, s) == [x EXCEPT !.rmin = IF x.rmin < 0 THEN s ELSE Mn(x.rmin, s), !.samp = Mn(x.samp + 1, U32MAX)]

\* round_exit.on_ack: the new detector fields and whether slow start ends
ReOnAck(x, la, np, cw) ==
    LET reset == x.rend <= la
        ref1 == IF reset /\ x.samp >= MINSAMP /\ x.rmin >= 0 THEN x.rmin ELSE x.ref
        rmin1 == IF reset THEN -1 ELSE x.rmin
        samp1 == IF reset THEN 0 ELSE x.samp
        rend1 == IF reset THEN np ELSE x.rend
        ex == ref1 >= 0 /\ rmin1 >= 0 /\ samp1 >= MINSAMP /\ cw >= EXITCW
              /\ rmin1 > SAdd(ref1, Mx(4 * MS, Mn(ref1 \div 8, 16 * MS)))
    IN [x |-> [x EXCEPT !.ref = ref1, !.rmin = rmin1, !.samp = samp1, !.rend = rend1], ex |-> ex]

(* ---- the delivery-rate probe ---- *)
ProbeOnAcked(x, now, bytes, m) ==
    LET st == IF x.pst < 0 THEN now ELSE x.pst
        b == SAdd(x.pby, bytes)
        el == SSub(now, st)
    IN IF el = 0 \/ el < m THEN [x EXCEPT !.pst = st, !.pby = b]
       ELSE [x EXCEPT !.pst = now, !.pby = 0, !.rate = Mx(Mn(MulDiv(b, SEC, el), TOP), x.rate - (x.rate \div 8))]

(* ---- the rate gate ---- *)
GateCap(x, m) ==
    IF x.rate = 0 THEN -1
    ELSE LET bdp == Mn(MulDiv(x.rate, m, SEC), TOP)
             slack == IF m < FASTRTT THEN GFAST ELSE IF m >= SLOWRTT THEN 0 ELSE x.slack
             floor == IF m < FASTRTT THEN INITC ELSE IF m >= SLOWRTT THEN MINC ELSE INITC
         IN Mn(Mx(SAdd(SMul(bdp, 2), slack), floor), MAXC)
ApplyGate(x, m) ==
    LET cap == GateCap(x, m)
    IN IF cap >= 0 /\ cap < x.cwnd THEN [x EXCEPT !.cwnd = cap, !.ss = Mn(x.ss, cap)] ELSE x

(* ---- an acknowledgement ---- *)
\* a = [now, acked, la, np, srtt, mn, mss]; srtt and mn are -1 for none
FeedProbe(x, a) == IF a.mn > 0 THEN ProbeOnAcked(x, a.now, a.acked, a.mn) ELSE x
Decay(x, a) ==
    LET srtt == IF a.srtt < 0 THEN IRTT ELSE a.srtt
    IN IF x.streak # 0 /\ x.rec >= 0 /\ SMul(4, srtt) < SSub(a.now, x.rec) THEN [x EXCEPT !.streak = 0] ELSE x
InSlowStart(x) == x.cwnd < x.ss
GateInPlay(a) == a.mn >= 0 /\ ~(a.mn >= FASTRTT /\ a.mn < SLOWRTT)

\* slow start: every acknowledged byte, and the exit detector
GrowSS(x, a) ==
    LET cw == Mn(SAdd(x.cwnd, a.acked), MAXC)
        r == ReOnAck(x, a.la, a.np, cw)
    IN [r.x EXCEPT !.cwnd = cw, !.ss = IF r.ex THEN cw ELSE x.ss]

Reno(mss, acked, cw) == MulDiv(53 * mss, acked, 100 * cw)

\* congestion avoidance relates the state before (x, already decayed) and after (y): the bounded step
CaRel(x, a, y) ==
    LET mss == Mx(MINMSS, Mn(a.mss, MAXMSS))
        ws0 == IF x.epoch < 0 THEN x.cwnd ELSE x.west
        lo == Mn(SAdd(ws0, Reno(mss, a.acked, y.cwnd)), MAXC)
        hi == Mn(SAdd(ws0, Reno(mss, a.acked, x.cwnd)), MAXC)
    IN /\ y.epoch = (IF x.epoch < 0 THEN a.now ELSE x.epoch)
       /\ (x.epoch >= 0 => y.k = x.k)
       /\ (x.epoch < 0 /\ x.cwnd >= x.wmax => y.k = 0)
       /\ y.cwnd >= x.cwnd /\ y.cwnd <= MAXC /\ y.cwnd >= y.west
       /\ y.west >= lo /\ y.west <= hi
       /\ (y.cwnd > y.west => y.west = lo)
       /\ y.ss = x.ss /\ y.wmax = x.wmax /\ y.rec = x.rec /\ y.streak = x.streak
       /\ y.rend = x.rend /\ y.ref = x.ref /\ y.rmin = x.rmin /\ y.samp = x.samp
       /\ y.pst = x.pst /\ y.pby = x.pby /\ y.rate = x.rate /\ y.slack = x.slack

\* the acknowledgement relation: y is a state the code can reach from x by the acknowledgement a
AckRel(x, a, y) ==
    LET x1 == Decay(FeedProbe(x, a), a)
    IN IF InSlowStart(x1)
       THEN y = (IF GateInPlay(a) THEN ApplyGate(GrowSS(x1, a), a.mn) ELSE GrowSS(x1, a))
       ELSE ~GateInPlay(a) /\ CaRel(x1, a, y)

(* ---- the other calls ---- *)
\* on_loss: the new state and whether the window was reduced
InEpisode(x, newest) == x.rec >= 0 /\ newest <= x.rec
Filtered(x, lat, mn) == lat >= 0 /\ mn >= 0 /\ lat <= SAdd(mn, Mx(4 * MS, mn \div 8)) /\ x.streak < 4
Mul9d10(c) == 9 * (c \div 10) + (9 * (c % 10)) \div 10
MulFrac(c, n, d) == n * (c \div d) + (n * (c % d)) \div d
Loss(x, now, newest, lat, mn) ==
    IF InEpisode(x, newest) THEN [x |-> x, r |-> FALSE]
    ELSE IF Filtered(x, lat, mn)
         THEN LET cw == Mx(Mul9d10(x.cwnd), MINC)
                  y == [x EXCEPT !.rec = now, !.streak = x.streak + 1, !.cwnd = cw]
              IN [x |-> IF x.ss # TOP THEN [y EXCEPT !.ss = Mn(x.ss, cw), !.west = Mn(x.west, cw)] ELSE y, r |-> TRUE]
         ELSE LET cw == Mx(IF x.cwnd < BETALIM THEN MulFrac(x.cwnd, 85, 100) ELSE MulFrac(x.cwnd, 7, 10), MINC)
              IN [x |-> [x EXCEPT !.rec = now, !.streak = 0, !.wmax = x.cwnd, !.cwnd = cw, !.ss = cw, !.epoch = -1, !.west = cw],
                  r |-> TRUE]
NewPath(x, now, np) ==
    [x EXCEPT !.cwnd = INITC, !.ss = TOP, !.epoch = -1, !.rend = np, !.ref = -1, !.rmin = -1, !.samp = 0, !.streak = 0,
              !.rec = IF x.rec < 0 \/ x.rec < now THEN now ELSE x.rec]
Restore(x, cw, ss) ==
    IF x.cwnd < cw THEN [x EXCEPT !.cwnd = Mn(cw, MAXC), !.ss = Mx(x.ss, ss), !.west = Mx(x.west, Mn(cw, MAXC))] ELSE x
Resume(x, mn) == IF mn >= 0 THEN ApplyGate(x, mn) ELSE x
SetSlack(x, b) == [x EXCEPT !.slack = Mn(b, MAXC)]

(* ---- the pacer ---- *)
Gap(mtu, srtt, cwnd) == Mn(MulDiv(srtt, 4 * Mn(mtu, MAXMSS), 5 * Mx(cwnd, 1)), TOP)
\* on_sent: start is the time of the first packet of the burst; the last packet of a burst sets the release, ten
\* gaps after it, or one tick after it when the window does not limit the sender (lim is FALSE) and the burst took
\* at least ten gaps already. The release only moves forward.
StartAt(p, now) == IF p.tokens = BURST THEN now ELSE p.start
Span(mtu, srtt, cwnd) == SMul(Gap(mtu, srtt, cwnd), BURST)
Slow(p, now, mtu, srtt, cwnd, lim) == ~lim /\ Mx(now - StartAt(p, now), 0) >= Span(mtu, srtt, cwnd)
OnSent(p, now, mtu, srtt, cwnd, lim) ==
    IF p.tokens > 1 THEN [p EXCEPT !.tokens = p.tokens - 1, !.start = StartAt(p, now)]
    ELSE [tokens |-> BURST,
          next |-> Mx(p.next, SAdd(now, IF Slow(p, now, mtu, srtt, cwnd, lim) THEN 1 ELSE Span(mtu, srtt, cwnd))),
          start |-> StartAt(p, now)]
NextRelease(p, now) == IF p.next > now THEN p.next ELSE now
=============================================================================
