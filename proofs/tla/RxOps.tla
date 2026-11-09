------------------------------- MODULE RxOps --------------------------------
(***************************************************************************)
(* The operations of vinc-transport recovery/recv.rs (ReceivedPackets), *)
(* step for step: the bounded range set of received packet numbers, the   *)
(* duplicate test, the acknowledgement decision, the ranges to report and *)
(* the floor the peer's confirmations raise. Rx.tla checks them over every *)
(* interleaving at small sizes; TraceRx.tla replays the recorded calls of *)
(* the real code through the same operators.                              *)
(*                                                                        *)
(* The state x: items (the ranges [start, end), lowest first), cap (the    *)
(* const generic RANGES), floor, pending, due, every, mrtt (the two        *)
(* options as -1 for none), sent (our acknowledgement packets: number and  *)
(* the largest number each reported), conf (the peer's confirmations: time *)
(* and number) and cf (the floor they produced, -1 for none).              *)
(*                                                                        *)
(* Time is nanoseconds in a u64 in the code; TLC integers are 32 bits, so  *)
(* the sums are the saturating SAdd at TOP (TOP stands for u64::MAX: above *)
(* every time of every checked run). A packet number is below 2^62 in the  *)
(* code (MAXPN); the checked runs keep every number below 2^31. The u32    *)
(* counters (pending) saturate at U32MAX in the code and Lean; a checked   *)
(* run never has 2^31 packets awaiting an acknowledgement.                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MS, SEC, TOP, MAXPN, U32MAX, SENTN, CONFN, MAXACK

Mx(a, b) == IF a > b THEN a ELSE b
Mn(a, b) == IF a < b THEN a ELSE b
SAdd(a, b) == IF a > TOP - b THEN TOP ELSE a + b

LONG == 250 * MS
BASEDELAY == 25 * MS
HOLD == 2 * SEC
BULKB == 1000
BULKMIN == 2
IsLong(m) == m >= 0 /\ m >= LONG
\* max_ack_delay (rtt.rs)
Delay(m) == IF IsLong(m) THEN Mx(BASEDELAY, Mn(LONG, m \div 8)) ELSE BASEDELAY

Init0(cap) == [items |-> <<>>, cap |-> cap, floor |-> 0, pending |-> 0, due |-> -1, every |-> -1, mrtt |-> -1,
               sent |-> <<>>, conf |-> <<>>, cf |-> -1]

Largest(x) == IF x.items = <<>> THEN -1 ELSE x.items[Len(x.items)][2] - 1
Contains(x, pn) == pn < x.floor \/ \E k \in DOMAIN x.items : x.items[k][1] <= pn /\ pn < x.items[k][2]

\* the number of leading ranges that end below pn (partition_point)
RECURSIVE Part(_, _)
Part(it, pn) == IF it = <<>> \/ it[1][2] >= pn THEN 0 ELSE 1 + Part(Tail(it), pn)

Ins(it, at, iv) == SubSeq(it, 1, at) \o <<iv>> \o SubSeq(it, at + 1, Len(it))
Del(it, at) == SubSeq(it, 1, at - 1) \o SubSeq(it, at + 1, Len(it))
Put(it, at, iv) == [it EXCEPT ![at] = iv]

\* push_new: a fresh one-number range at the sorted position at (0-based); when full the lowest range is forgotten
PushNew(x, at, pn) ==
    IF Len(x.items) = x.cap
    THEN IF at = 0
         THEN [ok |-> FALSE, x |-> [x EXCEPT !.floor = Mx(x.floor, x.items[1][1])]]
         ELSE [ok |-> TRUE, x |-> [x EXCEPT !.floor = Mx(x.floor, x.items[1][2]),
                                            !.items = Ins(Del(x.items, 1), at - 1, <<pn, pn + 1>>)]]
    ELSE [ok |-> TRUE, x |-> [x EXCEPT !.items = Ins(x.items, at, <<pn, pn + 1>>)]]

\* insert: false when pn is a duplicate or too old
Insert(x, pn) ==
    IF pn < x.floor THEN [ok |-> FALSE, x |-> x]
    ELSE LET at == Part(x.items, pn)
         IN IF at >= Len(x.items) THEN PushNew(x, at, pn)
            ELSE LET iv == x.items[at + 1]
                 IN IF iv[1] <= pn /\ pn < iv[2] THEN [ok |-> FALSE, x |-> x]
                    ELSE IF iv[2] = pn
                         THEN IF at + 2 <= Len(x.items) /\ x.items[at + 2][1] = pn + 1
                              THEN [ok |-> TRUE, x |-> [x EXCEPT !.items =
                                        Del(Put(x.items, at + 1, <<iv[1], x.items[at + 2][2]>>), at + 2)]]
                              ELSE [ok |-> TRUE, x |-> [x EXCEPT !.items = Put(x.items, at + 1, <<iv[1], pn + 1>>)]]
                         ELSE IF iv[1] = pn + 1
                              THEN [ok |-> TRUE, x |-> [x EXCEPT !.items = Put(x.items, at + 1, <<pn, iv[2]>>)]]
                              ELSE PushNew(x, at, pn)

\* on_packet_received: p = [pn, now, elic, bytes]; the outcome is "New", "Duplicate" or the error
Receive(x, p) ==
    IF p.pn > MAXPN THEN [out |-> "PacketNumberOutOfRange", x |-> x]
    ELSE LET expected == IF x.items = <<>> THEN 0 ELSE Largest(x) + 1
             ins == Insert(x, p.pn)
             y == ins.x
         IN IF ~ins.ok THEN [out |-> "Duplicate", x |-> y]
            ELSE IF ~p.elic THEN [out |-> "New", x |-> y]
            ELSE LET gap == p.pn # expected
                     pend == Mn(y.pending + 1, U32MAX)
                     bulk == p.bytes >= BULKB /\ Largest(y) >= BULKMIN
                     e0 == IF y.every >= 0 THEN y.every ELSE IF bulk THEN 3 ELSE 2
                     ev == IF IsLong(y.mrtt) THEN Mx(e0, 4) ELSE e0
                     due2 == SAdd(p.now, Delay(y.mrtt))
                     d == IF pend >= ev \/ gap THEN p.now
                          ELSE IF y.due < 0 \/ y.due > due2 THEN due2 ELSE y.due
                 IN [out |-> "New", x |-> [y EXCEPT !.pending = pend, !.due = d]]

SetMinRtt(x, m) == [x EXCEPT !.mrtt = m]
SetEvery(x, e) == [x EXCEPT !.every = IF e < 0 THEN -1 ELSE Mx(e, 1)]

AckDeadline(x) == IF x.pending = 0 THEN -1 ELSE x.due
AckDue(x, now) == AckDeadline(x) >= 0 /\ AckDeadline(x) <= now

\* the confirmations at least 2 s old, oldest first
RECURSIVE Aged(_, _)
Aged(c, now) == IF c = <<>> \/ SAdd(c[1][1], HOLD) > now THEN <<>> ELSE <<c[1]>> \o Aged(Tail(c), now)
RECURSIVE MaxN(_, _)
MaxN(c, m) == IF c = <<>> THEN m ELSE MaxN(Tail(c), Mx(m, c[1][2]))
FloorAt(x, now) == MaxN(Aged(x.conf, now), x.cf)

\* ack_ranges: largest first, as inclusive pairs
AckRanges(x, now) ==
    LET n == Len(x.items)
        f == FloorAt(x, now)
        only == f >= 0 /\ n > 1 /\ x.items[n - 1][2] - 1 < f
        take == IF only THEN 1 ELSE Mn(n, MAXACK)
    IN [k \in 1..take |-> <<x.items[n - k + 1][1], x.items[n - k + 1][2] - 1>>]

\* on_ack_sent: an acknowledgement of everything received went out in our packet apn at now
AckSent(x, apn, now) ==
    IF x.items = <<>> THEN x
    ELSE LET ag == Aged(x.conf, now)
             k == Len(ag)
             y == [x EXCEPT !.pending = 0, !.due = -1, !.cf = MaxN(ag, x.cf), !.conf = SubSeq(x.conf, k + 1, Len(x.conf))]
             s0 == IF Len(y.sent) = SENTN THEN Tail(y.sent) ELSE y.sent
         IN [y EXCEPT !.sent = Append(s0, <<apn, Largest(x)>>)]

\* on_peer_ack: the peer acknowledged the inclusive ranges rgs
InRgs(rgs, pn) == \E k \in DOMAIN rgs : rgs[k][1] <= pn /\ pn <= rgs[k][2]
PeerAck(x, now, rgs) ==
    IF rgs = <<>> THEN x
    ELSE LET largest == MaxN(rgs, -1)
             hits == {k \in DOMAIN x.sent : x.sent[k][1] <= largest /\ InRgs(rgs, x.sent[k][1])}
         IN IF hits = {} THEN x
            ELSE LET best == CHOOSE m \in {x.sent[k][2] : k \in hits} : \A o \in {x.sent[k][2] : k \in hits} : o <= m
                     kept == SelectSeq(x.sent, LAMBDA e : e[1] > largest)
                     y == [x EXCEPT !.sent = kept]
                 IN IF Len(x.conf) < CONFN THEN [y EXCEPT !.conf = Append(x.conf, <<now, best>>)] ELSE y
=============================================================================
