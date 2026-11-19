--------------------------------- MODULE Rx ---------------------------------
(***************************************************************************)
(* Received packet ranges and acknowledgement thinning of pinc-transport   *)
(* recovery/recv.rs over every interleaving of the calls the connection    *)
(* makes on it, at small sizes (RxOps.tla has the operators).              *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the range set is exact: every packet number reported New is in       *)
(*    exactly one range or below the floor, no number that was not         *)
(*    received is in a range (Exact, Shape, Seen);                         *)
(*  - the set is bounded (at most cap ranges), sorted, disjoint and        *)
(*    merged, and the oldest range is the one forgotten when it is full:   *)
(*    the floor rises to its end and stays below every range kept          *)
(*    (Shape, FloorMonotone, DropsOldest);                                 *)
(*  - a packet is New only if it was not seen before and is not below the  *)
(*    floor (NewIsFresh);                                                  *)
(*  - an acknowledgement is due no later than the delay after the oldest   *)
(*    ack-eliciting packet it still owes (or at the clock, when that       *)
(*    point is behind it), and at once for a gap or when the count rule is *)
(*    met (DeadlineHonoured, DueNow);                                      *)
(*  - the ranges reported are the newest ranges, largest first, at most    *)
(*    MAXACK, or only the newest after a confirmation (ReportShape);       *)
(*  - the tables of our acknowledgements and of confirmations are bounded  *)
(*    (TablesBounded).                                                     *)
(* Lean counterpart: proofs/lean/Pinc/TransportRx*.lean.                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS MS, SEC, TOP, MAXPN, U32MAX, SENTN, CONFN, MAXACK, CAP, PN, HOR, KMAX
VARIABLES x, rcv, gdl, t, k, anext, lastnew, lastdue
vars == <<x, rcv, gdl, t, k, anext, lastnew, lastdue>>

INSTANCE RxOps

Init == x = Init0(CAP) /\ rcv = {} /\ gdl = -1 /\ t = 0 /\ k = 0 /\ anext = 0 /\ lastnew = TRUE /\ lastdue = TRUE

Rec == \E pn \in 0..PN, d \in {0, 30, 260}, kind \in 0..2 :
         LET el == (kind > 0)
             by == IF kind = 2 THEN 1000 ELSE 0
         IN
         /\ t + d <= HOR /\ t' = t + d
         /\ LET r == Receive(x, [pn |-> pn, now |-> t + d, elic |-> el, bytes |-> by])
                m == x.mrtt
            IN /\ x' = r.x
               /\ rcv' = IF r.out = "New" THEN rcv \cup {pn} ELSE rcv
               /\ lastnew' = (r.out = "New" => pn \notin rcv /\ pn >= x.floor)
               /\ lastdue' = (r.out = "New" /\ el => (r.x.pending >= 1 /\ r.x.due >= 0))
               /\ gdl' = IF r.out = "New" /\ el
                         THEN (IF gdl < 0 THEN SAdd(t + d, Delay(m)) ELSE Mn(gdl, SAdd(t + d, Delay(m))))
                         ELSE gdl
         /\ UNCHANGED <<anext>>
SetRtt == \E m \in {-1, 300} : x' = SetMinRtt(x, m) /\ UNCHANGED <<rcv, gdl, t, anext, lastnew, lastdue>>
SetEv == \E e \in {-1, 1, 4} : x' = SetEvery(x, e) /\ UNCHANGED <<rcv, gdl, t, anext, lastnew, lastdue>>
Ack == /\ x.items # <<>> /\ anext < 4
       /\ x' = AckSent(x, anext, t) /\ anext' = anext + 1 /\ gdl' = -1
       /\ UNCHANGED <<rcv, t, lastnew, lastdue>>
Peer == \E a \in 0..3, b \in 0..3 : a <= b /\ x' = PeerAck(x, t, <<<<a, b>>>>) /\ UNCHANGED <<rcv, gdl, t, anext, lastnew, lastdue>>
Tick == t + 100 <= HOR /\ t' = t + 100 /\ UNCHANGED <<x, rcv, gdl, anext, lastnew, lastdue>>

Next == (Rec \/ SetRtt \/ SetEv \/ Ack \/ Peer \/ Tick) /\ k' = k + 1
Spec == Init /\ [][Next]_vars
Bound == k <= KMAX

Covered == {pn \in 0..(PN + 1) : \E j \in DOMAIN x.items : x.items[j][1] <= pn /\ pn < x.items[j][2]}
Shape == /\ Len(x.items) <= x.cap
         /\ \A j \in DOMAIN x.items : x.items[j][1] < x.items[j][2]
         /\ \A j \in 1..(Len(x.items) - 1) : x.items[j][2] < x.items[j + 1][1]
         /\ (x.items # <<>> => x.floor <= x.items[1][1])
Exact == Covered = {pn \in rcv : pn >= x.floor}
Seen == \A pn \in rcv : Contains(x, pn)
NewIsFresh == lastnew
TablesBounded == Len(x.sent) <= SENTN /\ Len(x.conf) <= CONFN
\* the deadline is no later than the delay after the oldest packet owed, unless that point is behind the clock, and then it
\* is the time of the latest call (a later packet sets it to its own time)
DeadlineHonoured == x.pending > 0 => (x.due >= 0 /\ gdl >= 0 /\ x.due <= Mx(gdl, t))
DueNow == lastdue
ReportShape ==
    LET r == AckRanges(x, t) n == Len(x.items)
    IN /\ Len(r) <= MAXACK
       /\ (n > 0 => Len(r) >= 1 /\ r[1][2] = Largest(x))
       /\ \A j \in DOMAIN r : <<r[j][1], r[j][2] + 1>> = x.items[n - j + 1]
Inv == Shape /\ Exact /\ Seen /\ NewIsFresh /\ TablesBounded /\ DeadlineHonoured /\ DueNow /\ ReportShape

\* the floor never falls, and the ranges kept are the newest: a forgotten number is below every kept range
FloorMonotone == [][x'.floor >= x.floor]_vars
DropsOldest == [][x'.floor > x.floor => (x'.items # <<>> => x'.floor <= x'.items[1][1])]_vars
=============================================================================
