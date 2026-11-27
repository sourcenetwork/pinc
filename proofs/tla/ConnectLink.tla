------------------------------ MODULE ConnectLink ------------------------------
(***************************************************************************)
(* Model check of the client carrier state machine (ConnectLinkOps.tla)   *)
(* under a host that does what link.rs says it does with each answer:     *)
(*   dial   the stream opens (Opened) or the dial fails (Closed), any time *)
(*   close  the stream is closed; the link is Down                         *)
(*   ping   the PING is written (Wrote); the answer (Heard) may or may not *)
(*          come                                                           *)
(*   check  the host starts the check (Check) with the PING written or    *)
(*          ridden on a session packet                                     *)
(* Time moves by the steps of Steps (microseconds), up to Horizon; the    *)
(* context is a constant of the model.                                     *)
(*                                                                         *)
(*  RetryOk        the retry wait is 1 s or 2 s                            *)
(*  DeadlineOk     a tick one microsecond before the reported deadline    *)
(*                 does nothing (no deadline is late)                      *)
(*  FutureOk       when a tick does nothing, the next deadline is in the  *)
(*                 future (no busy loop)                                   *)
(*  OpenByOpened   a link becomes Open only by Opened                      *)
(*  LeaseMono      lease_hi never rises once set                           *)
(*  KivBound       a learned keepalive is at least 15 s and at most half  *)
(*                 of the one it replaces (or 15 s)                        *)
(*  FloorOk        the lease gap that is learned is at least 15 s         *)
(*  ActsAtDeadline the tick at the reported deadline (or now, if that is   *)
(*                 past) acts: a host that sleeps until the deadline is   *)
(*                 never woken for nothing (Progress let a tick that only *)
(*                 moved the state count, and the 90 s horizons never met *)
(*                 the end of the 600 s memory of a silent death)          *)
(* Witnesses (ConnectLink_w_*.cfg): the operators before the fix, put in  *)
(* place by a definition override, break ActsAtDeadline.                   *)
(* Liveness (Live configs, the host never answers a PING, time jumps to   *)
(* the next deadline and the tick is weakly fair):                          *)
(*  DownDials      a home carrier that is down dials                       *)
(*  DialResolves   a dial that is never answered is closed by the watchdog *)
(*  SilentOpenDies a home carrier that hears nothing is checked and reset  *)
(* Lean: Pinc/ConnectLinkThm.lean.                                         *)
(***************************************************************************)
EXTENDS ConnectLinkOps

CONSTANTS C, Steps, Horizon, S0, L0, Now0
VARIABLES L, S, now, last
vars == <<L, S, now, last>>

Init == /\ L = L0 /\ S = S0 /\ now = Now0 /\ last = "init"

Apply(r, tag) == /\ L' = r.L /\ S' = r.S /\ last' = tag /\ UNCHANGED now

\* the host answers an action of the link
React(r) ==
    CASE r.act = "check" ->
           \E ridden \in BOOLEAN :
              LET k == Check(r.L, now, C, ridden) IN
              /\ L' = (IF k.act = "ping" THEN Wrote(k.L, now) ELSE k.L) /\ S' = r.S /\ last' = "check" /\ UNCHANGED now
      [] r.act = "ping" -> /\ L' = Wrote(r.L, now) /\ S' = r.S /\ last' = "ping" /\ UNCHANGED now
      [] OTHER -> /\ L' = r.L /\ S' = r.S /\ last' = r.act /\ UNCHANGED now

DoTick == LET r == Tick(L, S, now, C) IN React(r)
DoWant == LET r == WantDial(L, S, now, C) IN Apply(r, "want")
DoOpened == /\ L.st = "dialing" /\ LET o == Opened(L, now) IN /\ L' = o.L /\ S' = S /\ last' = "opened" /\ UNCHANGED now
DoClosed == /\ L.st \in {"dialing", "open"} /\ L' = Closed(L, now) /\ S' = S /\ last' = "closed" /\ UNCHANGED now
DoHeard == /\ L.st = "open" /\ L' = Heard(L, now) /\ S' = S /\ last' = "heard" /\ UNCHANGED now
DoWrote == /\ L' = Wrote(L, now) /\ S' = S /\ last' = "wrote" /\ UNCHANGED now
DoBefore == LET b == BeforeSend(L, S, now, C) IN /\ L' = b.L /\ S' = S /\ last' = (IF b.act = "close" THEN "reset" ELSE "send") /\ UNCHANGED now
DoAdvance == \E d \in Steps : now + d <= Horizon /\ now' = now + d /\ UNCHANGED <<L, S>> /\ last' = "time"

Next == \/ DoTick \/ DoWant \/ DoOpened \/ DoClosed \/ DoHeard \/ DoWrote \/ DoBefore \/ DoAdvance

Spec == Init /\ [][Next]_vars

(* the cases the configs choose from *)
CHome == [home |-> TRUE, rtt |-> 0, udp |-> FALSE, rides |-> FALSE, queued |-> FALSE]
CHomeUdp == [home |-> TRUE, rtt |-> SEC, udp |-> TRUE, rides |-> FALSE, queued |-> FALSE]
CRides == [home |-> FALSE, rtt |-> 0, udp |-> FALSE, rides |-> TRUE, queued |-> FALSE]
CQueued == [home |-> TRUE, rtt |-> 0, udp |-> FALSE, rides |-> TRUE, queued |-> TRUE]
CHomeRides == [home |-> TRUE, rtt |-> 0, udp |-> FALSE, rides |-> TRUE, queued |-> FALSE]
S0Plain == NewShared
S0Learn == [NewShared EXCEPT !.klearn = TRUE]
S0Lease == [NewShared EXCEPT !.lhi = 20 * SEC, !.klearn = TRUE]
S0Phone == [NewShared EXCEPT !.phone = TRUE, !.klearn = TRUE, !.kiv = 40 * SEC]
\* a restart: the end of the defer is fixed when the shared state is built (the node starts at 0)
S0Restart == [NewShared EXCEPT !.restarted = TRUE, !.du = DEFER]
\* a silent death at 0, remembered up to and including 600 s
S0Memory == [NewShared EXCEPT !.kfail = 0]
StepsA == {SEC, 7 * SEC, 15 * SEC}
StepsC == {7 * SEC, 30 * SEC}
\* 16 s lets a check find a lease gap in [15 s, 20 s), below the 20 s of S0Lease, so the learned lease moves
StepsD == {10 * SEC, 16 * SEC, 25 * SEC}
StepsE == {600000, 3 * SEC}
StepsB == {SEC \div 2, 3 * SEC, 30 * SEC}
StepsF == {3 * SEC, 30 * SEC}
\* the quick profile of ConnectLink.cfg: the longer step of StepsC alone
StepsCQuick == {30 * SEC}
\* the quick profile of ConnectLink_ridesHome.cfg: the longer step of StepsF alone
StepsFQuick == {30 * SEC}
\* the quick profile of ConnectLink_rides.cfg: steps of 5 s and 30 s (time points every 5 s)
StepsBQuick == {5 * SEC, 30 * SEC}
LDown == NewLink
LDialing == [NewLink EXCEPT !.st = "dialing", !.ds = 0]
LOpen == [NewLink EXCEPT !.st = "open", !.lrx = 0, !.hlt = 0, !.was = TRUE]
\* open and heard at 580 s, 20 s before the memory of S0Memory ends: the check is due after the long interval
LOpenLate == [NewLink EXCEPT !.st = "open", !.lrx = 580 * SEC, !.hlt = 580 * SEC, !.was = TRUE]
StepsM == {10 * SEC, 30 * SEC}
\* the quick profile of ConnectLink_memory.cfg: steps of 20 s (580 s, 600 s, ...: the memory's last instant is met)
StepsMQuick == {20 * SEC}

RetryOk == L.retry \in {RETRYMIN, RETRYMAX}

DeadlineOk ==
    LET d == NextDeadline(L, S, now, C) IN d > now => Tick(L, S, d - 1, C).act = "none"

FutureOk ==
    LET r == Tick(L, S, now, C) IN
    r.act = "none" =>
        LET d == NextDeadline(r.L, r.S, now, C) IN d = -1 \/ d > now

OpenByOpened == [][L'.st = "open" => (L.st = "open" \/ last' = "opened")]_vars

LeaseMono == [][S.lhi # 0 => (S'.lhi # 0 /\ S'.lhi <= S.lhi)]_vars

KivBound == [][S'.kiv # S.kiv => (S'.kiv >= KEEPFLOOR /\ (S.kiv # 0 => S'.kiv <= Max(KEEPFLOOR, S.kiv \div 2)))]_vars

FloorOk == [][S'.lhi # S.lhi => (S'.lhi >= LEASEFLOOR /\ L.gap >= LEASEFLOOR)]_vars

\* Bounded response, the liveness of the machine (time is unbounded, so it is stated as a bound): whatever the instant a
\* link is looked at, it has a deadline within a fixed time, and the tick at the deadline acts or moves the state.
DownBound == (L.st = "down" /\ (C.home \/ C.queued)) => NextDeadline(L, S, now, C) <= now + RETRYMAX
DialBound == L.st = "dialing" => NextDeadline(L, S, now, C) <= now + DIALCAP + 1
OpenBound == (L.st = "open" /\ (C.home \/ C.rides)) => (NextDeadline(L, S, now, C) >= 0 /\ NextDeadline(L, S, now, C) <= now + RELAYKEEP)
Progress ==
    LET d == NextDeadline(L, S, now, C) IN
    d > now => LET r == Tick(L, S, d, C) IN (r.act # "none" \/ r.L # L \/ r.S # S)
\* Lean: tick_at_deadline_acts.
ActsAtDeadline ==
    LET d == NextDeadline(L, S, now, C) IN d >= 0 => Tick(L, S, Max(d, now), C).act # "none"

(* The witnesses: the operators as they were before the fix. *)
\* the first want_dial after a restart fixed the end of the defer (get_or_insert), so the tick at the reported deadline
\* only fixed it and did nothing
S0RestartLazy == [NewShared EXCEPT !.restarted = TRUE]
WantDialLazy(K, T, t, c) ==
    IF K.st # "down" THEN R(K, T, "none")
    ELSE LET T1 == IF T.restarted /\ T.du < 0 THEN [T EXCEPT !.du = t + DEFER] ELSE T
             untl == T1.du
         IN IF T.restarted /\ ~c.queued /\ c.home /\ t < untl
            THEN R([K EXCEPT !.at = Max(K.at, untl), !.defer = TRUE], T1, "none")
            ELSE LET K1 == IF T.restarted /\ c.queued /\ K.defer THEN [K EXCEPT !.defer = FALSE, !.at = Min(K.at, t)] ELSE K
                 IN IF K1.at <= t /\ (c.queued \/ c.home)
                    THEN R([K1 EXCEPT !.st = "dialing", !.ds = t], T1, "dial")
                    ELSE R(K1, T1, "none")
\* the silent-carrier check due with the interval of the call instant, which a memory ending before it lengthens
KeepDueAtCall(K, T, t, c) == K.lrx + KeepAfter(T, t, c)
=============================================================================
