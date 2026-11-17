------------------------------ MODULE Recovery ------------------------------
(***************************************************************************)
(* Loss recovery of vinc-transport (recovery/engine.rs, ack.rs, loss.rs,   *)
(* pto.rs, sent.rs, rtt.rs, tail.rs) over every interleaving of the calls  *)
(* the connection makes on it, at small sizes (RecoveryOps.tla has the     *)
(* operators and the scaling).                                             *)
(*                                                                         *)
(* Checked, per concern:                                                   *)
(*  - nothing acknowledged is ever lost or sent again as new data: a slot  *)
(*    that is done stays done (DoneStays), a packet number is sent once    *)
(*    and strictly above every earlier one, a packet is acknowledged,      *)
(*    declared lost and late-acknowledged at most once each, and never     *)
(*    declared lost after it was acknowledged (EventsOnce, EventsSound);   *)
(*  - the byte accounts balance: sent = acked + in flight + lost, the in   *)
(*    flight bytes and packets are the sums over the ring, the lost slots  *)
(*    are counted in lost (Acct);                                          *)
(*  - every packet that leaves the in-flight set is reported once, as lost *)
(*    with requeue unless it is a repair packet or an MTU probe (the data  *)
(*    of a lost packet is retransmitted), or acknowledged, so the stream   *)
(*    layer sees every frame come back (LostRequeues);                     *)
(*  - the probe timeout declares the oldest packet in flight lost, backs   *)
(*    off by one count per firing, not while the peer sleeps or the link   *)
(*    is down (a sleeping peer holds the probe timer and its back-off, not *)
(*    the time-threshold loss rule) (PtoOldest, PtoBackoff, DurMonotone,   *)
(*    DurCapped);                                                          *)
(*  - the ring never overflows and the room check guarantees progress: a   *)
(*    ring without room is full and its head is in flight, and the probe   *)
(*    that fires then frees it (RingShape, RoomProgress);                  *)
(*  - ghosts: a late acknowledgement of a lost packet acts on its stream   *)
(*    data frames only, once; at most MAXG ghosts remain after a loss      *)
(*    (GhostBound); the ghost look runs at most once per 25 ms;            *)
(*  - tail repair: a candidate exists only after a burst of exactly one    *)
(*    packet (TailShape).                                                  *)
(*  - a path that takes a slot: the round trip kept for a path comes from a *)
(*    packet its present occupant sent; an acknowledgement of a packet an  *)
(*    earlier occupant sent sets none (PathRttFresh; Recovery_forget_w is  *)
(*    the witness without the guard).                                      *)
(* Lean counterpart: proofs/lean/Vinc/TransportRecovery*.lean.             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS N, MS, SEC, MP, TOP, MAXG, LATEN, Guard, DELTAS, PNMAX, SIZES, HOR, OPS, KMAX, FLAGS, PMAX, FRN
VARIABLES R, ev, H, T, L, stepc
vars == <<R, ev, H, T, L, stepc>>

INSTANCE RecoveryOps

L0 == [op |-> "init", ping |-> FALSE, err |-> "ok", s |-> S0]
Init == R = Init0 /\ ev = <<>> /\ H = {} /\ T = TailNew /\ L = L0 /\ stepc = 0

Frs == IF FRN = 1 THEN {<<>>, <<TRUE>>} ELSE {<<>>, <<TRUE>>, <<FALSE, TRUE>>}
Rng == {<<a, b>> : a \in 0..PNMAX, b \in 0..PNMAX}
Ranges == {<<r>> : r \in Rng} \cup {<<r1, r2>> \in Rng \X Rng : r2[1] <= r2[2] /\ r2[2] < r1[1] /\ r1[1] <= r1[2]}

Evs(res) == {res.ev[i] : i \in DOMAIN res.ev}
Step(op, res) == /\ R' = res.r /\ ev' = res.ev /\ H' = H \cup {<<e.k, e.pn>> : e \in Evs(res)}
                 /\ L' = [op |-> op, ping |-> res.ping, err |-> res.err, s |-> res.s]
                 /\ stepc' = stepc + 1 /\ UNCHANGED T
Quiet(op, r2) == /\ R' = r2 /\ ev' = <<>> /\ L' = [L0 EXCEPT !.op = op] /\ stepc' = stepc + 1 /\ UNCHANGED <<H, T>>

SendA == /\ "send" \in OPS
         /\ \E d \in DELTAS, pn \in (R.ls + 1)..(R.ls + 2), size \in SIZES, p \in 0..PMAX, rep \in FLAGS,
               probe \in FLAGS, fr \in Frs :
              /\ pn <= PNMAX /\ R.clock + d <= HOR
              /\ Step("send", Send(R, [pn |-> pn, time |-> R.clock + d, size |-> size, path |-> p, rep |-> rep,
                                       probe |-> probe, fr |-> fr]))
UntrackedA == /\ "untracked" \in OPS /\ R.ls + 1 <= PNMAX /\ Step("untracked", Untracked(R, R.ls + 1))
AckA == /\ "ack" \in OPS
        /\ \E d \in DELTAS, rgs \in Ranges : R.clock + d <= HOR /\ Step("ack", Ack(R, R.clock + d, rgs))
TimeoutA == /\ "timeout" \in OPS
            /\ \E d \in DELTAS : R.clock + d <= HOR /\ Step("timeout", Timeout(R, R.clock + d))
FlushA == /\ "flush" \in OPS /\ \E d \in DELTAS : R.clock + d <= HOR /\ Step("flush", Flush(R, R.clock + d))
SwitchA == /\ "switch" \in OPS /\ \E p \in 0..MP : Quiet("switch", SwitchPath(R, p).r)
FollowA == /\ "follow" \in OPS /\ \E p \in 0..MP : Quiet("follow", FollowPath(R, p).r)
ForgetA == /\ "forget" \in OPS /\ \E p \in 0..MP : Quiet("forget", ForgetPath(R, p).r)
KindA == /\ "kind" \in OPS /\ \E p \in 0..MP, k \in BOOLEAN : Quiet("kind", SetKind(R, p, k).r)
AsleepA == /\ "asleep" \in OPS /\ \E b \in BOOLEAN : Quiet("asleep", Asleep(R, b))
DownA == /\ "down" \in OPS /\ \E b \in BOOLEAN : Quiet("down", Down(R, b))
ActivityA == /\ "activity" \in OPS /\ \E d \in DELTAS : R.clock + d <= HOR /\ Quiet("activity", Activity(R, R.clock + d))
SeedA == /\ "seed" \in OPS /\ \E x \in SIZES : Quiet("seed", SeedRtt(R, x))
NodeA == /\ "node" \in OPS /\ \E x \in SIZES : Quiet("node", NodeRtt(HsRtt(R, x), x))
TailA == /\ "tail" \in OPS
         /\ \/ \E pn \in 0..PNMAX, plain \in BOOLEAN, inel \in BOOLEAN : T' = TailPacket(T, pn, plain, inel)
            \/ T' = TailDrain(T).t
         /\ ev' = <<>> /\ L' = [L0 EXCEPT !.op = "tail"] /\ stepc' = stepc + 1 /\ UNCHANGED <<R, H>>

Next == SendA \/ UntrackedA \/ AckA \/ TimeoutA \/ FlushA \/ SwitchA \/ FollowA \/ ForgetA \/ KindA \/ AsleepA \/ DownA
        \/ ActivityA \/ SeedA \/ NodeA \/ TailA
Spec == Init /\ [][Next]_vars

(* ---- state invariants ---- *)
Acct == /\ R.sent = R.acked + R.inf + R.lost
        /\ R.inf = SumSizes(R.ring, 0)
        /\ R.infp = CountSt(R.ring, 0)
        /\ SumSizes(R.ring, 1) <= R.lost
RingShape == /\ Len(R.ring) <= N
             /\ \A i \in 1..(Len(R.ring) - 1) : R.ring[i].pn < R.ring[i + 1].pn
             /\ \A i \in DOMAIN R.ring : R.ring[i].pn <= R.ls /\ R.ring[i].path < MP
             /\ R.la <= R.ls
RoomShape == ~HasRoom(R.ring) => (Len(R.ring) = N /\ FirstIF(R.ring) = 1)
LateSendsShape == /\ Len(R.late) <= LATEN
                  /\ \A i \in DOMAIN R.late : R.late[i][1] <= R.ls
EventsOnce == \A p \in 0..PNMAX :
                /\ ~(<<"acked", p>> \in H /\ <<"lost", p>> \in H)
                /\ ~(<<"acked", p>> \in H /\ <<"late", p>> \in H)
                /\ (<<"late", p>> \in H => <<"lost", p>> \in H)
DurMonotone == PtoDur([R EXCEPT !.pc = R.pc + 1]) >= PtoDur(R)
DurCapped == /\ PtoDur(R) <= IF PtoSlow(R) THEN PtoWide(R) ELSE PTOCAP
             /\ PtoDur(R) >= Mn(PtoSrtt(R), PTOCAP)
TailShape == /\ T.burst <= 2 /\ (T.cand >= 0 => T.burst = 1)
\* a round trip held for a path comes from the packet of its present occupant (a stale acknowledgement writes none)
PathRttFresh == \A p \in 0..(MP - 1) : R.ps[p] >= 0 => R.ps[p] = R.gen[p]
ReoShape == \A p \in 0..(MP - 1) : R.reo[p].seen >= 0 \/ R.reo[p].ext = 0

(* ---- action properties (ev' and L' are the events and results of the step) ---- *)
OldOf(pn) == CHOOSE i \in DOMAIN R.ring : R.ring[i].pn = pn
NewHas(pn) == \E j \in DOMAIN R'.ring : R'.ring[j].pn = pn
NewOf(pn) == CHOOSE j \in DOMAIN R'.ring : R'.ring[j].pn = pn
Gone(i) == ~(\E j \in DOMAIN R'.ring : R'.ring[j].pn = R.ring[i].pn)
Mono == /\ R'.ls >= R.ls /\ R'.la >= R.la /\ R'.clock >= R.clock /\ R'.hrd >= R.hrd
        /\ (R'.ls > R.ls => \A i \in DOMAIN R.ring : R.ring[i].pn < R'.ls)
        /\ R'.gs >= R.gs /\ (R'.gs # R.gs => R'.gs >= R.gs + GSCAN)
\* a done slot stays done, a slot only moves forward, nothing else about a recorded packet changes
DoneStays == \A i \in DOMAIN R.ring : \A j \in DOMAIN R'.ring :
    R.ring[i].pn = R'.ring[j].pn =>
        /\ R'.ring[j].st >= R.ring[i].st
        /\ R'.ring[j].size = R.ring[i].size /\ R'.ring[j].fr = R.ring[i].fr /\ R'.ring[j].time = R.ring[i].time
        /\ (R.ring[i].st = 2 => R'.ring[j].st = 2)
EventsSound == \A k \in DOMAIN ev' :
    LET e == ev'[k] IN
    /\ \E i \in DOMAIN R.ring : R.ring[i].pn = e.pn
    /\ LET o == R.ring[OldOf(e.pn)]
       IN /\ e.k = "acked" => (o.st = 0 /\ e.size = o.size /\ e.fr = o.fr /\ (NewHas(e.pn) => R'.ring[NewOf(e.pn)].st = 2))
          /\ e.k = "late" => (o.st = 1 /\ e.fr = DataFrames(o.fr) /\ (NewHas(e.pn) => R'.ring[NewOf(e.pn)].st = 2))
          /\ e.k = "lost" => (o.st = 0 /\ e.size = o.size /\ e.fr = o.fr /\ e.f1 = ~(o.rep \/ o.probe) /\ e.f2 = o.probe
                              /\ (NewHas(e.pn) => R'.ring[NewOf(e.pn)].st # 0))
EventsFresh == \A k \in DOMAIN ev' : <<ev'[k].k, ev'[k].pn>> \notin H
EventsDistinct == \A k1, k2 \in DOMAIN ev' : (ev'[k1].pn = ev'[k2].pn /\ ev'[k1].k = ev'[k2].k) => k1 = k2
\* every packet that left the in-flight set in a step is reported, as acknowledged or lost
LeavesReported == \A i \in DOMAIN R.ring : R.ring[i].st = 0 =>
    ((Gone(i) \/ R'.ring[NewOf(R.ring[i].pn)].st # 0) =>
        \E k \in DOMAIN ev' : ev'[k].pn = R.ring[i].pn /\ ev'[k].k \in {"acked", "lost"})
\* the ring drops from the head only, and only a done slot or an expired ghost (or a packet lost in this step)
SlotsLeaveFromHead == \A i \in DOMAIN R.ring : Gone(i) =>
    /\ \A k \in 1..(i - 1) : Gone(k)
    /\ (R.ring[i].st # 0 \/ \E k \in DOMAIN ev' : ev'[k].pn = R.ring[i].pn)
SendOk == L'.op = "send" =>
    IF L'.err = "ok" THEN R'.ls > R.ls /\ R'.infp = R.infp + 1 /\ R'.sent > R.sent
    ELSE R'.ls = R.ls /\ R'.sent = R.sent /\ R'.infp = R.infp
SummaryAgrees == L'.op \in {"ack", "timeout", "flush"} =>
    /\ L'.s.ap = Cardinality({k \in DOMAIN ev' : ev'[k].k = "acked"})
    /\ L'.s.lap = Cardinality({k \in DOMAIN ev' : ev'[k].k = "late"})
    /\ L'.s.lp = Cardinality({k \in DOMAIN ev' : ev'[k].k = "lost"})
PtoOldest == (L'.op = "timeout" /\ L'.ping) =>
    /\ ev' # <<>> /\ ev'[Len(ev')].k = "lost"
    /\ \A j \in DOMAIN R'.ring : R'.ring[j].st = 0 => R'.ring[j].pn > ev'[Len(ev')].pn
PtoBackoff == L'.op = "timeout" =>
    /\ (R'.pc = R.pc \/ R'.pc = R.pc + 1)
    /\ ((R.asleep \/ R.down) => R'.pc = R.pc)
    /\ (L'.ping => (R'.pc = R.pc + 1 \/ R.down))
    /\ (R.asleep => ~L'.ping)
\* the earlier statement, too strong: a sleeping peer holds the probe timer and its back-off, not loss detection, so a
\* timeout may still report a packet lost by the time threshold (Recovery_asleep_w finds it)
PtoBackoffStrict == PtoBackoff /\ (L'.op = "timeout" => (R.asleep => ev' = <<>>))
RoomProgress == (L'.op = "timeout" /\ L'.ping /\ ~HasRoom(R.ring)) => HasRoom(R'.ring)
GhostBound == (L'.op \in {"ack", "timeout"} /\ L'.s.lp > 0) => Ghosts(R'.ring) <= MAXG
FlushAll == L'.op = "flush" => (R'.inf = 0 /\ R'.infp = 0 /\ R'.pc = 0 /\ R'.lt = -1)

\* the events and results of the last step are for the action properties; they do not identify a state
View == <<R, H, T>>
Bound == stepc <= KMAX

Steps == /\ Mono /\ DoneStays /\ EventsSound /\ EventsFresh /\ EventsDistinct /\ LeavesReported /\ SlotsLeaveFromHead
         /\ SendOk /\ SummaryAgrees /\ PtoOldest /\ PtoBackoff /\ RoomProgress /\ GhostBound /\ FlushAll
StepProps == [][Steps]_vars
StrictProps == [][PtoBackoffStrict]_vars
=============================================================================
