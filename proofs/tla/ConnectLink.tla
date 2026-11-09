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
(* Liveness (Live configs, the host never answers a PING, time jumps to   *)
(* the next deadline and the tick is weakly fair):                          *)
(*  DownDials      a home carrier that is down dials                       *)
(*  DialResolves   a dial that is never answered is closed by the watchdog *)
(*  SilentOpenDies a home carrier that hears nothing is checked and reset  *)
(* Lean: Vinc/ConnectLinkThm.lean.                                         *)
(***************************************************************************)
EXTENDS ConnectLinkOps

CONSTANTS C, Steps, Horizon, S0, L0
VARIABLES L, S, now, last
vars == <<L, S, now, last>>

Init == /\ L = L0 /\ S = S0 /\ now = 0 /\ last = "init"

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
S0Plain == NewShared
S0Lease == [NewShared EXCEPT !.lhi = 20 * SEC, !.klearn = TRUE]
S0Phone == [NewShared EXCEPT !.phone = TRUE, !.klearn = TRUE, !.kiv = 40 * SEC]
S0Restart == [NewShared EXCEPT !.restarted = TRUE]
StepsA == {SEC, 7 * SEC, 15 * SEC}
StepsC == {7 * SEC, 30 * SEC}
StepsD == {10 * SEC, 25 * SEC}
StepsE == {600000, 3 * SEC}
StepsB == {SEC \div 2, 3 * SEC, 30 * SEC}
LDown == NewLink
LDialing == [NewLink EXCEPT !.st = "dialing", !.ds = 0]
LOpen == [NewLink EXCEPT !.st = "open", !.lrx = 0, !.hlt = 0, !.was = TRUE]

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
=============================================================================
