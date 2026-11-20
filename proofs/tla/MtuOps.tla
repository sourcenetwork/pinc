------------------------------- MODULE MtuOps -------------------------------
(***************************************************************************)
(* The operations of pinc-transport conn/mtu.rs (the Mtu state of one path),*)
(* call for call: probing the path datagram size, the floor, and the       *)
(* black-hole fallback. Mtu.tla checks them over every interleaving at     *)
(* small sizes; TraceMtu.tla replays the recorded calls of the real code.  *)
(*                                                                         *)
(* The state m: cur (the datagram size), infl (the probe in flight, its    *)
(* size and packet number, -1 for none), flushed (the probe a flush took,  *)
(* kept so its acknowledgement can still raise the path, -1 for none),     *)
(* probed, jdone (the jumbo probe is done), retry (a lost probe waits      *)
(* until then), started, lbig, backed, pbig (packet numbers of full-size   *)
(* packets, -1 for none) and susp (the black-hole suspicion: the packet    *)
(* and the time it is judged, <<-1, 0>> for none). The packet numbers of   *)
(* the full-size packets are inputs from the send and receive paths        *)
(* (SetBig).                                                               *)
(*                                                                         *)
(* Every outcome is pn-matched: an acknowledgement, a loss or a flush      *)
(* applies only when it names exactly the probe in flight there, and a     *)
(* flush's acknowledgement only when it names the probe the flush took. An *)
(* echo rises only when a probe of exactly that size is in flight and the  *)
(* path's ceiling can carry it; the ceiling is the caller's guard, so      *)
(* Raise itself is unguarded, as in the code.                              *)
(*                                                                         *)
(* Time is nanoseconds in a u64 in the code; the sums are the saturating   *)
(* SAdd at TOP (which stands for u64::MAX). REPROBE is 600 s in the code;  *)
(* the trace check, whose integers are 32 bits, runs it at TOP, so a lost  *)
(* probe waits for a path event there; Mtu.tla runs it small.              *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS TOP, MINMTU, PROBEMTU, JFLOOR, JMTU, REPROBE

Mn(a, b) == IF a < b THEN a ELSE b
SAdd(a, b) == IF a > TOP - b THEN TOP ELSE a + b

M0 == [cur |-> MINMTU, infl |-> -1, flushed |-> -1, probed |-> FALSE, jdone |-> FALSE, retry |-> 0,
       started |-> FALSE, lbig |-> -1, backed |-> -1, pbig |-> -1, susp |-> <<-1, 0>>]

\* the next size to probe, -1 for none
Target(m, allowed, imtu, lowlat, now) ==
    IF ~allowed \/ ~m.started \/ m.infl >= 0 \/ m.retry > now THEN -1
    ELSE IF ~m.probed THEN (IF imtu >= PROBEMTU /\ m.cur < PROBEMTU THEN PROBEMTU ELSE -1)
    ELSE IF ~m.jdone /\ m.cur = PROBEMTU /\ lowlat /\ Mn(imtu, JMTU) > JFLOOR THEN Mn(imtu, JMTU)
    ELSE -1

ProbeSent(m, size, pn) ==
    LET m1 == [m EXCEPT !.infl = <<size, pn>>, !.flushed = -1]
    IN IF size = PROBEMTU /\ ~m.probed THEN [m1 EXCEPT !.probed = TRUE]
       ELSE [m1 EXCEPT !.jdone = TRUE]

\* a probe of size was acknowledged or echoed: the new state and the size if the datagram size rose (-1 otherwise).
\* An echo arrives through the caller's guard (a probe of exactly that size in flight, the ceiling); an
\* acknowledgement of any other probe than the one in flight raises nothing.
Raise(m, size) ==
    LET m1 == IF m.infl >= 0 /\ m.infl[1] = size THEN [m EXCEPT !.infl = -1] ELSE m
    IN IF size > m.cur THEN [m |-> [m1 EXCEPT !.cur = size], new |-> size] ELSE [m |-> m1, new |-> -1]

\* the probe of size sent as pn was acknowledged: the new state and the size if the datagram size rose, -2 when
\* the acknowledgement names another probe than the one in flight (a refusal), -1 when it names it but does not
\* raise the size
Acked(m, size, pn) ==
    IF m.infl = <<size, pn>>
    THEN LET m1 == [m EXCEPT !.infl = -1]
         IN IF size > m.cur THEN [m |-> [m1 EXCEPT !.cur = size], new |-> size] ELSE [m |-> m1, new |-> -1]
    ELSE [m |-> m, new |-> -2]

\* the probe of size sent as pn was declared lost: the new state and whether the loss applied
ProbeLost(m, size, pn, now) ==
    IF m.infl = <<size, pn>>
    THEN LET m1 == [m EXCEPT !.infl = -1, !.retry = SAdd(now, REPROBE)]
         IN IF size > PROBEMTU THEN [m |-> [m1 EXCEPT !.jdone = TRUE], applied |-> TRUE]
                               ELSE [m |-> m1, applied |-> TRUE]
    ELSE [m |-> m, applied |-> FALSE]

\* a flush took the probe of size sent as pn: its size and packet number are kept for its acknowledgement, and
\* the probe is owed again at once. The flush of another probe is refused.
Flush(m, size, pn) ==
    IF m.infl = <<size, pn>>
    THEN [m |-> [m EXCEPT !.infl = -1, !.flushed = <<size, pn>>], applied |-> TRUE]
    ELSE [m |-> m, applied |-> FALSE]

\* the probe a flush took, sent as pn, was acknowledged after all: the new state and the size if it rose
FlushedAcked(m, pn) ==
    IF m.flushed >= 0 /\ m.flushed[2] = pn
    THEN LET size == m.flushed[1]
             m1 == [m EXCEPT !.flushed = -1]
         IN IF size > m.cur THEN [m |-> [m1 EXCEPT !.cur = size], new |-> size] ELSE [m |-> m1, new |-> -1]
    ELSE [m |-> m, new |-> -1]

Event(m) == [m EXCEPT !.probed = FALSE, !.jdone = FALSE, !.retry = 0]

BlackHole(m, now, rtt) ==
    IF m.pbig < 0 THEN m
    ELSE IF m.cur <= MINMTU \/ (m.backed >= 0 /\ m.backed >= m.pbig) THEN m
    ELSE [m EXCEPT !.susp = <<m.pbig, SAdd(now, rtt)>>]

\* the suspicion settled: the new state and whether the path dropped to the minimum size. The drop forgets the
\* mark of the probe a flush took: the path was condemned for carrying small packets only, and the stale
\* acknowledgement of its probe is no evidence against that.
BlackHoleCheck(m, now) ==
    IF m.susp[1] < 0 THEN [m |-> m, dropped |-> FALSE]
    ELSE IF (m.backed >= 0 /\ m.backed >= m.susp[1]) \/ m.cur <= MINMTU
         THEN [m |-> [m EXCEPT !.susp = <<-1, 0>>], dropped |-> FALSE]
    ELSE IF now < m.susp[2] THEN [m |-> m, dropped |-> FALSE]
    ELSE [m |-> [m EXCEPT !.susp = <<-1, 0>>, !.cur = MINMTU, !.infl = -1, !.flushed = -1, !.lbig = -1,
                          !.pbig = -1, !.retry = SAdd(now, REPROBE), !.probed = TRUE, !.jdone = TRUE],
          dropped |-> TRUE]

Start(m) == [m EXCEPT !.started = TRUE]
SetBig(m, lb, ba, pb) == [m EXCEPT !.lbig = lb, !.backed = ba, !.pbig = pb]
=============================================================================
