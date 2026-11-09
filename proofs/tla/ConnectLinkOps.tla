---------------------------- MODULE ConnectLinkOps ----------------------------
(***************************************************************************)
(* The client carrier state machine of vinc-connect/src/client/link.rs as   *)
(* pure operators: each takes the link L, the shared state S, a clock       *)
(* reading and the context c, and returns the new link, the new shared      *)
(* state and what the host must do.                                         *)
(*                                                                         *)
(* Time is in microseconds (TLC integers are 32 bits wide; the code counts  *)
(* nanoseconds and every rule constant is a whole number of microseconds,   *)
(* and the traces use readings that are whole milliseconds, so every        *)
(* division of the code is exact). saturating_sub is SatSub; a plain `-`    *)
(* of the code is Sub, which stops TLC with an error when it would          *)
(* underflow. The shared "unset" values are -1 (keep_fail, defer_until).    *)
(* Lean counterpart: Vinc/ConnectLink.lean, ConnectLinkThm.lean.            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

SEC == 1000000
RETRYMIN == SEC
RETRYMAX == 2 * SEC
DIALMIN == 8 * SEC
DIALRTTS == 8
DIALCAP == 30 * SEC
HOMEKEEP == 30 * SEC
RELAYKEEP == 65 * SEC
KEEPMEM == 600 * SEC
CHECKMIN == 3 * SEC
CHECKRTTS == 3
KEEPFLOOR == 15 * SEC
LEASEFLOOR == 15 * SEC
DEFER == 600000

Max(a, b) == IF a > b THEN a ELSE b
Min(a, b) == IF a < b THEN a ELSE b
SatSub(a, b) == IF a < b THEN 0 ELSE a - b
Sub(a, b) == IF a < b THEN Assert(FALSE, "u64 subtraction underflows") ELSE a - b

DialWait(rtt) == LET w == rtt * DIALRTTS
                     w2 == IF w > DIALMIN THEN w ELSE DIALMIN
                 IN IF w2 > DIALCAP THEN DIALCAP ELSE w2
CheckWait(rtt) == LET w == rtt * CHECKRTTS IN IF w > CHECKMIN THEN w ELSE CHECKMIN
LeaseKeep(hi) == LET a == (hi * 7) \div 8
                     b == (LEASEFLOOR + hi) \div 2
                     m == IF a < b THEN a ELSE b
                 IN IF m > LEASEFLOOR THEN m ELSE LEASEFLOOR

NewLink == [st |-> "down", retry |-> RETRYMIN, at |-> 0, ds |-> 0, chk |-> 0, ride |-> FALSE, gap |-> 0,
            lrx |-> 0, hlt |-> 0, defer |-> FALSE, was |-> FALSE]
NewShared == [phone |-> FALSE, kfail |-> -1, lhi |-> 0, klearn |-> FALSE, kiv |-> 0, restarted |-> FALSE, du |-> -1]

R(L, S, a) == [L |-> L, S |-> S, act |-> a]

WantDial(L, S, now, c) ==
    IF L.st # "down" THEN R(L, S, "none")
    ELSE LET S1 == IF S.restarted /\ S.du < 0 THEN [S EXCEPT !.du = now + DEFER] ELSE S
             untl == S1.du
         IN IF S.restarted /\ ~c.queued /\ c.home /\ now < untl
            THEN R([L EXCEPT !.at = Max(L.at, untl), !.defer = TRUE], S1, "none")
            ELSE LET L1 == IF S.restarted /\ c.queued /\ L.defer THEN [L EXCEPT !.defer = FALSE, !.at = Min(L.at, now)] ELSE L
                 IN IF L1.at <= now /\ (c.queued \/ c.home)
                    THEN R([L1 EXCEPT !.st = "dialing", !.ds = now], S1, "dial")
                    ELSE R(L1, S1, "none")

Opened(L, now) == [was |-> L.was, L |-> [L EXCEPT !.st = "open", !.retry = RETRYMIN, !.chk = 0, !.ride = FALSE,
                                          !.lrx = now, !.hlt = now, !.was = TRUE]]
Closed(L, now) == [L EXCEPT !.st = "down", !.at = now + L.retry, !.retry = Min(L.retry * 2, RETRYMAX), !.chk = 0]
Heard(L, now) == [L EXCEPT !.lrx = now, !.chk = 0]
Wrote(L, now) == [L EXCEPT !.hlt = now]
Reset(L, now) == [L EXCEPT !.st = "down", !.at = now, !.chk = 0, !.lrx = now]

Check(L, now, c, ridden) ==
    IF L.st # "open" \/ L.chk # 0 THEN [L |-> L, act |-> "none"]
    ELSE LET L1 == [L EXCEPT !.chk = now + CheckWait(c.rtt), !.ride = ridden] IN
         IF ridden THEN [L |-> L1, act |-> "none"]
         ELSE [L |-> [L1 EXCEPT !.gap = SatSub(now, L.hlt)], act |-> "ping"]

BeforeSend(L, S, now, c) ==
    IF L.st = "open" /\ S.lhi # 0 /\ ~c.udp /\ SatSub(now, L.hlt) >= S.lhi /\ SatSub(now, L.lrx) >= S.lhi
    THEN [L |-> Reset(L, now), act |-> "close"]
    ELSE [L |-> L, act |-> "none"]

Pulse(L, now, c) ==
    IF L.st # "open" THEN [L |-> L, p |-> "closed"]
    ELSE LET k == Check(L, now, c, FALSE) IN [L |-> k.L, p |-> IF k.act = "none" THEN "waiting" ELSE "ping"]

KeepAfter(S, now, c) ==
    LET base == IF c.home /\ (S.phone \/ (S.kfail >= 0 /\ SatSub(now, S.kfail) < KEEPMEM)) THEN HOMEKEEP ELSE RELAYKEEP
    IN IF S.kiv = 0 THEN base ELSE Min(base, S.kiv)

TickOpen(L, S, now, c) ==
    LET lease == S.lhi # 0 /\ ~c.udp IN
    IF L.chk # 0 /\ now >= L.chk
    THEN IF L.ride
         THEN LET k == Check([L EXCEPT !.chk = 0], now, c, FALSE) IN R(k.L, S, k.act)
         ELSE LET S1 == [S EXCEPT !.kfail = now]
                  silence == SatSub(now, L.lrx)
                  seen == IF S1.kiv = 0 THEN silence ELSE Min(S1.kiv, silence)
                  S2 == IF S1.klearn THEN [S1 EXCEPT !.kiv = Max(seen \div 2, KEEPFLOOR)] ELSE S1
                  S3 == IF ~c.udp /\ L.gap >= LEASEFLOOR
                        THEN [S2 EXCEPT !.lhi = IF S2.lhi = 0 THEN L.gap ELSE Min(S2.lhi, L.gap)] ELSE S2
              IN R(Reset(L, now), S3, "close")
    ELSE IF L.chk # 0 THEN R(L, S, "none")
    ELSE IF lease /\ (c.home \/ c.rides) /\ SatSub(now, L.hlt) >= LeaseKeep(S.lhi)
         THEN LET k == Check(L, now, c, FALSE) IN R(k.L, S, k.act)
    ELSE IF (c.home \/ c.rides) /\ SatSub(now, L.lrx) >= KeepAfter(S, now, c) THEN R(L, S, "check")
    ELSE R(L, S, "none")

Tick(L, S, now, c) ==
    CASE L.st = "dialing" ->
           IF SatSub(now, L.ds) > DialWait(c.rtt) THEN R([L EXCEPT !.st = "down", !.at = now], S, "close") ELSE R(L, S, "none")
      [] L.st = "down" -> WantDial(L, S, now, c)
      [] L.st = "open" -> TickOpen(L, S, now, c)

\* the first instant Tick can act, or -1 (the code's one nanosecond past the watchdog is rounded up to a microsecond)
NextDeadline(L, S, now, c) ==
    CASE L.st = "dialing" -> L.ds + DialWait(c.rtt) + 1
      [] L.st = "down" -> IF c.queued \/ c.home THEN (IF S.restarted /\ c.queued /\ L.defer THEN Min(L.at, now) ELSE L.at) ELSE -1
      [] L.st = "open" ->
           IF L.chk # 0 THEN L.chk
           ELSE IF ~(c.home \/ c.rides) THEN -1
           ELSE LET silent == L.lrx + KeepAfter(S, now, c) IN
                IF S.lhi # 0 /\ ~c.udp THEN Min(L.hlt + LeaseKeep(S.lhi), silent) ELSE silent
=============================================================================
