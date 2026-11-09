------------------------------- MODULE MtuOps -------------------------------
(***************************************************************************)
(* The operations of vinc-transport conn/mtu.rs (the Mtu state of one path),*)
(* call for call: probing the path datagram size, the floor, and the       *)
(* black-hole fallback. Mtu.tla checks them over every interleaving at     *)
(* small sizes; TraceMtu.tla replays the recorded calls of the real code.  *)
(*                                                                         *)
(* The state m: cur (the datagram size), infl (the probe in flight, -1 for *)
(* none), probed, jdone (the jumbo probe is done), retry (a lost probe     *)
(* waits until then), started, lbig, backed, pbig (packet numbers of       *)
(* full-size packets, -1 for none) and susp (the black-hole suspicion: the *)
(* packet and the time it is judged, <<-1, 0>> for none). The packet       *)
(* numbers of the full-size packets are inputs from the send and receive   *)
(* paths (SetBig).                                                         *)
(*                                                                         *)
(* Time is nanoseconds in a u64 in the code; the sums are the saturating   *)
(* SAdd at TOP (which stands for u64::MAX). REPROBE is 600 s in the code;  *)
(* the trace check, whose integers are 32 bits, runs it at TOP, so a lost   *)
(* probe waits for a path event there; Mtu.tla runs it small.              *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS TOP, MINMTU, PROBEMTU, JFLOOR, JMTU, REPROBE

Mn(a, b) == IF a < b THEN a ELSE b
SAdd(a, b) == IF a > TOP - b THEN TOP ELSE a + b

M0 == [cur |-> MINMTU, infl |-> -1, probed |-> FALSE, jdone |-> FALSE, retry |-> 0, started |-> FALSE,
       lbig |-> -1, backed |-> -1, pbig |-> -1, susp |-> <<-1, 0>>]

\* the next size to probe, -1 for none
Target(m, allowed, imtu, lowlat, now) ==
    IF ~allowed \/ ~m.started \/ m.infl >= 0 \/ m.retry > now THEN -1
    ELSE IF ~m.probed THEN (IF imtu >= PROBEMTU /\ m.cur < PROBEMTU THEN PROBEMTU ELSE -1)
    ELSE IF ~m.jdone /\ m.cur = PROBEMTU /\ lowlat /\ Mn(imtu, JMTU) > JFLOOR THEN Mn(imtu, JMTU)
    ELSE -1

ProbeSent(m, size) ==
    IF size = PROBEMTU /\ ~m.probed THEN [m EXCEPT !.infl = size, !.probed = TRUE]
    ELSE [m EXCEPT !.infl = size, !.jdone = TRUE]

\* a probe of size was acknowledged or echoed: the new state and the size if the datagram size rose (-1 otherwise)
Raise(m, size) ==
    LET m1 == IF m.infl = size THEN [m EXCEPT !.infl = -1] ELSE m
    IN IF size > m.cur THEN [m |-> [m1 EXCEPT !.cur = size], new |-> size] ELSE [m |-> m1, new |-> -1]

ProbeLost(m, size, now) ==
    LET m1 == IF m.infl = size THEN [m EXCEPT !.infl = -1] ELSE m
        m2 == [m1 EXCEPT !.retry = SAdd(now, REPROBE)]
    IN IF size > PROBEMTU THEN [m2 EXCEPT !.jdone = TRUE] ELSE m2

Event(m) == [m EXCEPT !.probed = FALSE, !.jdone = FALSE, !.retry = 0]

BlackHole(m, now, rtt) ==
    IF m.pbig < 0 THEN m
    ELSE IF m.cur <= MINMTU \/ (m.backed >= 0 /\ m.backed >= m.pbig) THEN m
    ELSE [m EXCEPT !.susp = <<m.pbig, SAdd(now, rtt)>>]

\* the suspicion settled: the new state and whether the path dropped to the minimum size
BlackHoleCheck(m, now) ==
    IF m.susp[1] < 0 THEN [m |-> m, dropped |-> FALSE]
    ELSE IF (m.backed >= 0 /\ m.backed >= m.susp[1]) \/ m.cur <= MINMTU
         THEN [m |-> [m EXCEPT !.susp = <<-1, 0>>], dropped |-> FALSE]
    ELSE IF now < m.susp[2] THEN [m |-> m, dropped |-> FALSE]
    ELSE [m |-> [m EXCEPT !.susp = <<-1, 0>>, !.cur = MINMTU, !.infl = -1, !.lbig = -1, !.pbig = -1,
                          !.retry = SAdd(now, REPROBE), !.probed = TRUE, !.jdone = TRUE],
          dropped |-> TRUE]

Start(m) == [m EXCEPT !.started = TRUE]
SetBig(m, lb, ba, pb) == [m EXCEPT !.lbig = lb, !.backed = ba, !.pbig = pb]
=============================================================================
