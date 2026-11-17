--------------------------------- MODULE Mtu ---------------------------------
(***************************************************************************)
(* Path MTU discovery of vinc-transport conn/mtu.rs over every interleaving *)
(* of the calls the connection makes, on two paths and at small sizes      *)
(* (MtuOps.tla has the operators and the scaling).                          *)
(*                                                                         *)
(* Each path has its own state. A probe that leaves on a path is recorded  *)
(* (outs, the packet records of loss recovery) with the path it left on    *)
(* and its identity (the step it left in, standing for its packet number); *)
(* its acknowledgement and its loss go to that path, whichever path is     *)
(* active when they arrive (ROUTE = "probe"), and are applied only while   *)
(* that probe is the one in flight there. A path can be replaced (a path   *)
(* removed and a new one taking its slot); the probes the old path left    *)
(* still come back and must touch the new one in no way. An echo arrives *)
(* on a path and is taken only if it is the size of the probe in flight   *)
(* on that path and no larger than the smaller of the jumbo size and what *)
(* the interface carries (BOUND = TRUE). Each slot keeps the packet       *)
(* numbers of the probes its current occupant sent (toks); a replacement  *)
(* empties it. The witnesses switch the rules off: ROUTE, BOUND, and MATCH *)
(* (a probe is matched by its size alone instead of by size and packet    *)
(* number).                                                               *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the datagram size of a path is never below the floor (Floor), rises  *)
(*    only by a probe the peer confirmed, and falls only by the black-hole *)
(*    fallback, to the floor, or by the path being replaced               *)
(*    (RisesByRaise, FallsToFloor);                                        *)
(*  - it rises only to a size a probe left on that path with (OwnRaise),   *)
(*    also across a replacement of the path;                               *)
(*  - an outcome (a raise, a lost mark, the wait after a loss, an echo) is *)
(*    applied to a slot only if its packet number is one the slot's        *)
(*    current occupant sent, so the probe of a path that is gone, still    *)
(*    in flight when a new path took the slot, changes the new path in no  *)
(*    way (AppliedOwnToken);                                               *)
(*  - the outcome of a probe is applied to the path the probe left on, and *)
(*    to no other (OutcomeOnProbePath);                                    *)
(*  - an echo raises a path only to a size within the bound (EchoBounded); *)
(*  - a probe is due only when discovery started, none is in flight and no *)
(*    lost probe still waits, and it is above the datagram size, so at     *)
(*    most one probe is in flight per path (TargetShape);                  *)
(*  - a lost probe is not tried again until a path event or REPROBE later  *)
(*    (LostWaits);                                                         *)
(*  - a black-hole suspicion exists only above the floor, and the          *)
(*    fallback leaves the floor, nothing in flight, the path marked        *)
(*    probed and the jumbo probe done (SuspectShape, DropShape).           *)
(* Lean counterpart: proofs/lean/Vinc/TransportMtu*.lean.                  *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS TOP, MINMTU, PROBEMTU, JFLOOR, JMTU, REPROBE, KMAX, ROUTE, BOUND, MATCH
VARIABLES ms, act, t, k, lost, sent, outs, toks, ev
vars == <<ms, act, t, k, lost, sent, outs, toks, ev>>

INSTANCE MtuOps

Paths == {1, 2}
\* the sizes a probe has: the main one, or the jumbo one at the largest size
Sizes == {PROBEMTU, JMTU}
\* what an event reports: dropped (the black-hole fallback), raised (the new size or -1), path (the path whose state
\* changed, 0 for none), replaced (the path a new path took the slot of, 0 for none), from (the path the probe of an outcome left on, 0 for none), via (how a size was confirmed),
\* im (the interface payload an echo was checked against), app (an outcome was applied to the path) and tok (the packet
\* number of the probe that outcome names)
NoEv == [dropped |-> FALSE, replaced |-> 0, raised |-> -1, path |-> 0, from |-> 0, via |-> "none", im |-> 0, app |-> FALSE,
         tok |-> -1]
EchoBoundOf(im) == IF BOUND THEN Ceil(im) ELSE TOP

Init == /\ ms = [p \in Paths |-> M0] /\ act = 1 /\ t = 0 /\ k = 0 /\ lost = [p \in Paths |-> -1]
        /\ sent = [p \in Paths |-> {}] /\ outs = [p \in Paths |-> {}] /\ toks = [p \in Paths |-> {}] /\ ev = NoEv

Put(p, m) == ms' = [ms EXCEPT ![p] = m]

StartA == \E p \in Paths : Put(p, Start(ms[p])) /\ UNCHANGED <<act, t, lost, sent, outs, toks>> /\ ev' = NoEv
TickA == \E d \in {0, 3, 12} : t' = t + d /\ UNCHANGED <<ms, act, lost, sent, outs, toks, ev>>
SwitchA == act' = 3 - act /\ UNCHANGED <<ms, t, lost, sent, outs, toks>> /\ ev' = NoEv
SentA == \E p \in Paths, allowed \in BOOLEAN, im \in {1200, 1500, 9000}, ll \in BOOLEAN :
           LET s == Target(ms[p], allowed, im, ll, t)
           IN /\ s >= 0 /\ Put(p, ProbeSent(ms[p], s, k))
              /\ sent' = [sent EXCEPT ![p] = @ \cup {s}] /\ outs' = [outs EXCEPT ![p] = @ \cup {<<s, k>>}]
              /\ toks' = [toks EXCEPT ![p] = @ \cup {k}]
              /\ UNCHANGED <<act, t, lost>> /\ ev' = NoEv
\* the path an outcome of a probe that left on path p is applied to
RouteOf(p) == IF ROUTE = "probe" THEN p ELSE act
\* the identity a probe is matched by: its packet number (the code's rule), or, in the witness, only its size (the slot's
\* own identity is put in its place)
MatchTok(m, tok) == IF MATCH = "token" THEN tok ELSE m.ptok
AckA == \E p \in Paths : \E e \in outs[p] :
          /\ LET q == RouteOf(p)
                 r == Raise(ms[q], e[1], MatchTok(ms[q], e[2]))
             IN /\ Put(q, r.m)
                /\ ev' = [NoEv EXCEPT !.raised = r.new, !.path = q, !.from = p, !.via = "ack",
                                      !.app = Holds(ms[q], e[1], MatchTok(ms[q], e[2])), !.tok = e[2]]
          /\ outs' = [outs EXCEPT ![p] = @ \ {e}] /\ UNCHANGED <<act, t, lost, sent, toks>>
EchoA == \E p \in Paths, s \in {PROBEMTU, 3000, JMTU, 65535}, im \in {1200, 1500, 9000} :
           LET r == Echo(ms[p], s, EchoBoundOf(im))
           IN /\ Put(p, r.m)
              /\ ev' = [NoEv EXCEPT !.raised = r.new, !.path = p, !.via = "echo", !.im = im,
                                    !.app = (ms[p].infl = s /\ s <= EchoBoundOf(im)), !.tok = ms[p].ptok]
              /\ UNCHANGED <<act, t, lost, sent, outs, toks>>
LostA == \E p \in Paths : \E e \in outs[p] :
           /\ LET q == RouteOf(p) IN
              /\ Put(q, ProbeLost(ms[q], e[1], MatchTok(ms[q], e[2]), t))
              /\ lost' = IF Holds(ms[q], e[1], MatchTok(ms[q], e[2])) THEN [lost EXCEPT ![q] = t] ELSE lost
              /\ ev' = [NoEv EXCEPT !.path = q, !.from = p, !.app = Holds(ms[q], e[1], MatchTok(ms[q], e[2])), !.tok = e[2]]
           /\ outs' = [outs EXCEPT ![p] = @ \ {e}] /\ UNCHANGED <<act, t, sent, toks>>
\* a path is removed and a new one takes its slot: a fresh state, nothing it sent, its discovery started; the probes the old
\* path left stay in outs and come back later
ReplaceA == \E p \in Paths : Put(p, Start(M0)) /\ sent' = [sent EXCEPT ![p] = {}] /\ lost' = [lost EXCEPT ![p] = -1]
                             /\ toks' = [toks EXCEPT ![p] = {}]
                             /\ ev' = [NoEv EXCEPT !.replaced = p] /\ UNCHANGED <<act, t, outs>>
EventA == \E p \in Paths : Put(p, Event(ms[p])) /\ lost' = [lost EXCEPT ![p] = -1]
                           /\ UNCHANGED <<act, t, sent, outs, toks>> /\ ev' = NoEv
BigA == \E p \in Paths, lb \in {-1, 5}, ba \in {-1, 3, 6}, pb \in {-1, 5} :
          Put(p, SetBig(ms[p], lb, ba, pb)) /\ UNCHANGED <<act, t, lost, sent, outs, toks>> /\ ev' = NoEv
BhA == \E p \in Paths, rtt \in {0, 4} :
         Put(p, BlackHole(ms[p], t, rtt)) /\ UNCHANGED <<act, t, lost, sent, outs, toks>> /\ ev' = NoEv
BhcA == \E p \in Paths :
          LET r == BlackHoleCheck(ms[p], t)
          IN Put(p, r.m) /\ ev' = [NoEv EXCEPT !.dropped = r.dropped, !.path = IF r.dropped THEN p ELSE 0]
             /\ UNCHANGED <<act, t, lost, sent, outs, toks>>

Next == (StartA \/ TickA \/ SwitchA \/ SentA \/ AckA \/ EchoA \/ LostA \/ ReplaceA \/ EventA \/ BigA \/ BhA \/ BhcA) /\ k' = k + 1
Spec == Init /\ [][Next]_vars
Bound == k <= KMAX

Floor == \A p \in Paths : ms[p].cur >= MINMTU
SuspectShape == \A p \in Paths : ms[p].susp[1] >= 0 => ms[p].cur > MINMTU
LostWaits == \A p \in Paths : lost[p] >= 0 => ms[p].retry >= SAdd(lost[p], REPROBE)
TargetShape == \A p \in Paths, al \in BOOLEAN, im \in {1200, 1500, 9000}, ll \in BOOLEAN :
                 LET s == Target(ms[p], al, im, ll, t)
                 IN s >= 0 => (al /\ ms[p].started /\ ms[p].infl = -1 /\ ms[p].retry <= t /\ s > ms[p].cur)
OwnRaise == \A p \in Paths : ms[p].cur = MINMTU \/ ms[p].cur \in sent[p]
\* an outcome is applied to a slot only if the probe it names was sent by the slot's current occupant: the probes of an
\* earlier occupant, still in flight when the slot was refilled, change nothing
AppliedOwnToken == ev.app => ev.tok \in toks[ev.path]
Inv == Floor /\ SuspectShape /\ LostWaits /\ TargetShape /\ OwnRaise /\ AppliedOwnToken

RisesByRaise == [][\A p \in Paths : ms'[p].cur > ms[p].cur => (ev'.raised = ms'[p].cur /\ ev'.path = p)]_vars
FallsToFloor == [][\A p \in Paths : ms'[p].cur < ms[p].cur =>
                     (ev'.replaced = p \/ (ev'.dropped /\ ev'.path = p /\ ms'[p].cur = MINMTU))]_vars
DropShape == [][ev'.dropped => (LET m1 == ms'[ev'.path]
                                IN m1.cur = MINMTU /\ m1.infl = -1 /\ m1.probed /\ m1.jdone /\ m1.susp[1] < 0)]_vars
OutcomeOnProbePath == [][ev'.from > 0 => ev'.path = ev'.from]_vars
EchoBounded == [][ev'.via = "echo" => ev'.raised <= Ceil(ev'.im)]_vars
=============================================================================
