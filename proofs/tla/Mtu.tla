--------------------------------- MODULE Mtu ---------------------------------
(***************************************************************************)
(* Path MTU discovery of pinc-transport conn/mtu.rs over every interleaving *)
(* of the calls the connection makes, at small sizes (MtuOps.tla has the   *)
(* operators and the scaling).                                             *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the datagram size is never below the floor (Floor), rises only by    *)
(*    a probe the peer confirmed, and falls only by the black-hole        *)
(*    fallback, to the floor (RisesByRaise, FallsToFloor);                 *)
(*  - a probe is due only when discovery started, none is in flight and no *)
(*    lost probe still waits, and it is above the datagram size, so at     *)
(*    most one probe is in flight (TargetShape);                           *)
(*  - a lost probe is not tried again until a path event or REPROBE later  *)
(*    (LostWaits);                                                         *)
(*  - a black-hole suspicion exists only above the floor, and the          *)
(*    fallback leaves the floor, nothing in flight, the path marked        *)
(*    probed and the jumbo probe done (SuspectShape, DropShape).           *)
(* Lean counterpart: proofs/lean/Pinc/TransportMtu*.lean.                  *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS TOP, MINMTU, PROBEMTU, JFLOOR, JMTU, REPROBE, KMAX
VARIABLES m, t, k, lost, ev
vars == <<m, t, k, lost, ev>>

INSTANCE MtuOps

Init == m = M0 /\ t = 0 /\ k = 0 /\ lost = -1 /\ ev = [dropped |-> FALSE, raised |-> -1]

StartA == m' = Start(m) /\ UNCHANGED <<t, lost>> /\ ev' = [dropped |-> FALSE, raised |-> -1]
TickA == \E d \in {0, 3, 12} : t' = t + d /\ UNCHANGED <<m, lost, ev>>
SentA == \E allowed \in BOOLEAN, im \in {1200, 1500, 9000}, ll \in BOOLEAN :
           LET s == Target(m, allowed, im, ll, t)
           IN /\ s >= 0 /\ m' = ProbeSent(m, s) /\ UNCHANGED <<t, lost>> /\ ev' = [dropped |-> FALSE, raised |-> -1]
RaiseA == \E s \in {1452, 3000, 9000} :
            LET r == Raise(m, s) IN m' = r.m /\ ev' = [dropped |-> FALSE, raised |-> r.new] /\ UNCHANGED <<t, lost>>
LostA == \E s \in {1452, 9000} : m' = ProbeLost(m, s, t) /\ lost' = t /\ UNCHANGED <<t>> /\ ev' = [dropped |-> FALSE, raised |-> -1]
EventA == m' = Event(m) /\ lost' = -1 /\ UNCHANGED <<t>> /\ ev' = [dropped |-> FALSE, raised |-> -1]
BigA == \E lb \in {-1, 5}, ba \in {-1, 3, 6}, pb \in {-1, 5} :
          m' = SetBig(m, lb, ba, pb) /\ UNCHANGED <<t, lost>> /\ ev' = [dropped |-> FALSE, raised |-> -1]
BhA == \E rtt \in {0, 4} : m' = BlackHole(m, t, rtt) /\ UNCHANGED <<t, lost>> /\ ev' = [dropped |-> FALSE, raised |-> -1]
BhcA == LET r == BlackHoleCheck(m, t) IN m' = r.m /\ ev' = [dropped |-> r.dropped, raised |-> -1] /\ UNCHANGED <<t, lost>>

Next == (StartA \/ TickA \/ SentA \/ RaiseA \/ LostA \/ EventA \/ BigA \/ BhA \/ BhcA) /\ k' = k + 1
Spec == Init /\ [][Next]_vars
Bound == k <= KMAX

Floor == m.cur >= MINMTU
SuspectShape == m.susp[1] >= 0 => m.cur > MINMTU
LostWaits == lost >= 0 => m.retry >= SAdd(lost, REPROBE)
TargetShape == \A al \in BOOLEAN, im \in {1200, 1500, 9000}, ll \in BOOLEAN :
                 LET s == Target(m, al, im, ll, t)
                 IN s >= 0 => (al /\ m.started /\ m.infl = -1 /\ m.retry <= t /\ s > m.cur)
Inv == Floor /\ SuspectShape /\ LostWaits /\ TargetShape

RisesByRaise == [][m'.cur > m.cur => ev'.raised = m'.cur]_vars
FallsToFloor == [][m'.cur < m.cur => (ev'.dropped /\ m'.cur = MINMTU)]_vars
DropShape == [][ev'.dropped => (m'.cur = MINMTU /\ m'.infl = -1 /\ m'.probed /\ m'.jdone /\ m'.susp[1] < 0)]_vars
=============================================================================
