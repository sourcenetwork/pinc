---------------------------- MODULE MembershipSys ---------------------------
(***************************************************************************)
(* A bounded system model of pinc-membership: hubs and members, each a      *)
(* Membership node (the operators of MembershipOps.tla, validated against   *)
(* the real code by TraceMembership.tla), a network of reliable ordered     *)
(* streams, the host environment the machines read, and an adversary that   *)
(* follows a script.                                                        *)
(*                                                                         *)
(* The world is the test world of tests/membership_world.rs: a frame sent   *)
(* on a route arrives (instantly, in order) iff the route works when it is  *)
(* sent: a hub reaches a member over the session unless the pair is cut or  *)
(* its default path is dead (carrier gone), a member's transport answers on *)
(* any working path, the direct path needs a validated direct pair, a relay *)
(* route needs both legs. A delivery shows the receiver the packet at once  *)
(* (evidence rx) and the sender the transport acknowledgement when the      *)
(* return path works. A slow member (Slow) processes a delivered frame      *)
(* SlowCpu later; its transport still answers. Keepalives refresh rx every  *)
(* 30 s on working sessions. Sessions are made by Connect (members dial all *)
(* hubs, hubs dial lower hubs) and ended by Detect after a crash or a cut.  *)
(*                                                                         *)
(* Scheduling is deterministic where the order does not matter for the     *)
(* property: the script entry that is due runs first, then deliveries and   *)
(* processing in node order, then due timers in node order, then keepalives,*)
(* then time advances to the next deadline (a timer, a processing time, a   *)
(* keepalive, a script entry) without skipping one. Nothing branches: the  *)
(* adversary follows the script too (a probe loss, a crash, a cut are      *)
(* script entries), so Init has one state and Next one successor, and a    *)
(* TLC run walks one deterministic chain per configuration (about nine     *)
(* states per simulated second, by the report, not verified here). It     *)
(* checks that scripted scenario only, not other choices of the adversary  *)
(* and not other interleavings of simultaneous events (a stated limit).    *)
(*                                                                         *)
(* The script is a sequence of entries <<kind, seconds after the start,     *)
(* args...>>: crash n | restart n wall | cut a b | heal a b | gone hub m |  *)
(* back hub m | leave n | leavelost n hub | revoke node m | jump seconds |   *)
(* move n | lose k (the next k PROBE frames sent are lost) | direct a b (a   *)
(* validated direct path between a and b: the session of the pair runs on   *)
(* it) | refuse hub (the host refuses a relayed probe through hub's relay,  *)
(* as a full probe queue does). leavelost n hub: n leaves and is gone, and  *)
(* its close to hub never arrives.                                          *)
(*                                                                         *)
(* History variables record what the nodes reported, for the properties:  *)
(* down/left (observer, member) events, susp (hub, member) suspicion        *)
(* records (internal state, not an event), conf (hub, member) confirmed,    *)
(* accepted DOWNs, restores, resubscribes, releases, holds, and the flags   *)
(* okDown (a DOWN was accepted only on a stale lease), okInc (announced     *)
(* words only go up, strictly across a restart), okBounds (tables within    *)
(* their capacity).                                                         *)
(*                                                                         *)
(* Lean counterpart: Pinc/MembershipSys*.lean.                              *)
(***************************************************************************)
EXTENDS MembershipOps

CONSTANTS Hubs, Members, Slow, SlowCpuSec, Pers, Script, MaxSec, KeepaliveOn

Nodes == Hubs \cup Members
START == 100
SRTT == <<20000, 305, 0, 0, 0>>              \* 20 ms
Pr(a, b) == IF a < b THEN <<a, b>> ELSE <<b, a>>
SecW(n) == N!Sec(n)
NodeSeq == Ordered(Nodes, NONE)
HubSeq == Ordered(Hubs, NONE)

(* ---- the world (one record) ---- *)
VARIABLE w

NetOk(x, a, b) == a \in x.alive /\ b \in x.alive /\ Pr(a, b) \notin x.cut
SessOk(x, a, b) == NetOk(x, a, b) /\ Pr(a, b) \notin x.dead
AnyAlt(x, a, b) == (Pr(a, b) \in x.direct /\ NetOk(x, a, b)) \/ \E h \in Hubs \ {a, b} : NetOk(x, a, h) /\ NetOk(x, h, b)
PathOk(x, a, b, route) ==
    CASE route.r = "s" -> IF a \in Hubs THEN SessOk(x, a, b) ELSE SessOk(x, a, b) \/ AnyAlt(x, a, b)
      [] route.r = "d" -> Pr(a, b) \in x.direct /\ NetOk(x, a, b)
      [] route.r = "v" -> NetOk(x, a, route.via) /\ NetOk(x, route.via, b)

EnvFor(x, n) ==
    [ev |-> [p \in {p \in Nodes : Pr(n, p) \in x.sess} |->
                 [rx |-> x.rx[<<n, p>>], srtt |-> x.srtt[<<n, p>>], pto |-> 0, inf |-> 0, direct |-> Pr(n, p) \in x.direct]],
     car |-> [m \in {m \in Members : n \in Hubs /\ x.car[<<n, m>>].k # "unknown"} |-> x.car[<<n, m>>]],
     acc |-> {p \in Nodes : Pr(n, p) \in x.sess},
     rv |-> x.refuse,
     ver |-> 1, tk |-> n, refl |-> TRUE, pers |-> Pers, sealed |-> x.store[n], failseal |-> FALSE, failunseal |-> FALSE,
     floor |-> [p \in 0..255 |-> <<241, p, 0, 0, 0, 0, 0, 0, 1>>], gu |-> EmptyFn]

EvS(S) == {S.ev[i] : i \in 1..Len(S.ev)}
TrS(S) == {S.tr[i] : i \in 1..Len(S.tr)}
BcS(S) == {S.bc[i] : i \in 1..Len(S.bc)}
ClS(S) == {S.cl[i] : i \in 1..Len(S.cl)}

\* the frames a call sent that a session took and whose route works now
RECURSIVE Enq(_, _, _, _)
Enq(x, n, snt, i) ==
    IF i > Len(snt) THEN x.net
    ELSE LET e == snt[i]
             k == <<n, e.to>>
             drop == e.f.k = "probe" /\ x.lose > 0
             ok == e.ok /\ PathOk(x, n, e.to, e)
         IN IF ~ok THEN Enq(x, n, snt, i + 1)
            ELSE IF drop THEN Enq([x EXCEPT !.lose = @ - 1, !.hist.lostProbes = @ + 1], n, snt, i + 1)
            ELSE Enq([x EXCEPT !.net[k] = Append(@, e.f)], n, snt, i + 1)

\* record what a call reported, and enqueue what it sent
Done(x, n, S1, now) ==
    LET S0 == x.nodes[n]
        h == x.hist
        down == {<<n, e.m>> : e \in {e \in EvS(S1) : e.k = "down"}}
        left == {<<n, e.m>> : e \in {e \in EvS(S1) : e.k = "left"}}
        susp == {<<n, m>> : m \in DOMAIN S1.susp}
        conf == {<<n, t.member>> : t \in {t \in TrS(S1) : t.k = "confirmed"}}
        acc == {<<n, t.member>> : t \in {t \in TrS(S1) : t.k = "down_accepted"}}
        rest == {<<n, t.member>> : t \in {t \in TrS(S1) : t.k = "carrier_returned" /\ t.restored}}
        resub == {<<n, c.hub>> : c \in {c \in BcS(S1) : c.k = "resub"}}
        rel == {<<n, c.m>> : c \in {c \in BcS(S1) : c.k = "release"}}
        hold == {<<n, c.m>> : c \in {c \in BcS(S1) : c.k = "hold"}}
        restore == {<<n, c.m>> : c \in {c \in BcS(S1) : c.k = "restore"}}
        supp == {<<n, t.hub>> : t \in {t \in TrS(S1) : t.k = "hello_suppressed"}}
        revcl == {<<n, c[1]>> : c \in {c \in ClS(S1) : c[2] = "revoked"}}
        lvcl == {<<n, c[1]>> : c \in {c \in ClS(S1) : c[2] = "leave"}}
        \* a DOWN is accepted only on a lease that was stale before the call
        accOK == \A t \in {t \in TrS(S1) : t.k = "down_accepted"} :
                   t.member \in DOMAIN S0.roster =>
                     LET eff == IF Pr(n, t.member) \in x.sess THEN Max2(S0.roster[t.member].renewed, x.rx[<<n, t.member>>])
                                ELSE S0.roster[t.member].renewed
                     IN Gt(SatSub(now, eff), RENEW)
        \* #284: unless a late timer ran in the call, a removal that waits before and after it moved only on its own
        \* schedule: an entry not due is as it was, a due entry whose extra look had not begun has it now, a due entry
        \* whose extra look ran was recomputed (whatever waits under its key after that is a new deferral)
        late == \E t \in TrS(S1) : t.k = "quiet" /\ t.cause = 0
        waitOK == late \/ \A m \in DOMAIN S0.recheck \cap DOMAIN S1.recheck :
                    LET a == S0.recheck[m] b == S1.recheck[m]
                    IN b = a \/ (Le(a.due, now) /\ (a.grace \/ b = [due |-> SatAdd(now, RECHECK_GAP), grace |-> TRUE]))
        \* a heal at a node while a removal waits for a later instant
        healWait == (\E t \in TrS(S1) : t.k = "quiet" /\ t.cause = 1) /\ \E m \in DOMAIN S0.recheck : Lt(now, S0.recheck[m].due)
        words == INC!Word(S1.inc)
        wordOK == Le(h.lastInc[n], words)
        boundsOK == /\ Cardinality(DOMAIN S1.roster) <= MAX_TABLE /\ Cardinality(S1.attached) <= MAX_TABLE
                    /\ Cardinality(S1.homed) <= MAX_TABLE /\ Cardinality(DOMAIN S1.susp) <= MAX_TABLE
                    /\ Cardinality(DOMAIN S1.downed) <= MAX_TABLE /\ Cardinality(S1.revoked) <= MAX_TABLE
                    /\ Cardinality(DOMAIN S1.members) <= MAX_TABLE /\ Cardinality(DOMAIN S1.hv) <= MAX_HUBS
                    /\ Len(S1.ev) <= QUEUE_CAP + 1 /\ Len(S1.tr) <= QUEUE_CAP + 1
        x1 == [x EXCEPT !.nodes[n] = S1,
                        !.hist.down = @ \cup down, !.hist.left = @ \cup left, !.hist.susp = @ \cup susp,
                        !.hist.conf = @ \cup conf, !.hist.acc = @ \cup acc, !.hist.rest = @ \cup rest,
                        !.hist.resub = @ \cup resub, !.hist.rel = @ \cup rel, !.hist.hold = @ \cup hold,
                        !.hist.restore = @ \cup restore, !.hist.primN[n] = @ + Cardinality({c \in BcS(S1) : c.k = "primary"}), !.hist.supp = @ \cup supp, !.hist.revcl = @ \cup revcl, !.hist.lvcl = @ \cup lvcl,
                        !.hist.okDown = @ /\ accOK, !.hist.okInc = @ /\ wordOK, !.hist.okBounds = @ /\ boundsOK,
                        !.hist.okWait = @ /\ waitOK, !.hist.healWait = @ \/ healWait,
                        !.hist.lastInc[n] = words]
    IN [x1 EXCEPT !.net = Enq(x1, n, S1.sent, 1)]

(* ---- calls into a node, through the world ---- *)
CallAt(x, n, F(_, _)) == Done(x, n, F(x.nodes[n], EnvFor(x, n)), x.now)

\* a delivery: the receiver sees the packet, the sender its acknowledgement when the return path works
SeeRx(x, a, b) ==
    LET x1 == [x EXCEPT !.rx[<<b, a>>] = x.now]
    IN IF PathOk(x1, b, a, [r |-> "s", via |-> 0]) THEN [x1 EXCEPT !.rx[<<a, b>>] = x.now] ELSE x1

(* ---- priorities ---- *)
ScriptDue(x) == x.pc <= Len(Script) /\ Ge(x.now, SecW(START + Script[x.pc][2]))
HeadPair(x) == IF {p \in Nodes \X Nodes : x.net[p] # <<>>} = {} THEN <<>>
               ELSE <<CHOOSE p \in {p \in Nodes \X Nodes : x.net[p] # <<>>} :
                        \A q \in {q \in Nodes \X Nodes : x.net[q] # <<>>} : p[1] < q[1] \/ (p[1] = q[1] /\ p[2] <= q[2])>>
InboxDue(x) == {n \in Nodes : x.inbox[n] # <<>> /\ Ge(x.now, x.inbox[n][1].due)}
\* A node that left keeps no membership timer: on_timeout does nothing once it is leaving, so the host neither asks its
\* deadline nor calls it (pinc-node Node::mem_timed, pinc#551). LeftTimed is that rule. The witness
\* MembershipSys_w_lefttimer overrides it with OldLeftTimed, the node before the fix, which kept asking the deadline of a
\* node that left: the deadline stays due, every call leaves it due, and the host calls again at once (TimerMoves fails).
LeftTimed(S) == ~S.leaving
OldLeftTimed(S) == TRUE
\* the nodes whose membership timer is due: the host calls them now
TimerDue(x) == {n \in x.alive : LeftTimed(x.nodes[n]) /\ Le(PollTimeout(x.nodes[n]), x.now)}
KaDue(x) == KeepaliveOn /\ Ge(x.now, x.nextKA)
\* sessions that must be dialed or ended
ToDial(x) == {p \in Nodes \X Nodes : p[2] \in Hubs /\ p[1] > p[2] /\ Pr(p[1], p[2]) \notin x.sess
                                      /\ NetOk(x, p[1], p[2]) /\ x.dial}
ToDetect(x) == {p \in Nodes \X Nodes : p[1] \in x.alive /\ p[2] \notin x.alive /\ Pr(p[1], p[2]) \in x.sess}
Quiescent(x) == HeadPair(x) = <<>> /\ InboxDue(x) = {} /\ TimerDue(x) = {} /\ ~KaDue(x) /\ ~ScriptDue(x)
                /\ ToDial(x) = {} /\ ToDetect(x) = {}

(* ---- the steps ---- *)
Connect(x) ==
    LET p == CHOOSE p \in ToDial(x) : \A q \in ToDial(x) : p[1] < q[1] \/ (p[1] = q[1] /\ p[2] <= q[2])
        a == p[1]
        b == p[2]
        x1 == [x EXCEPT !.sess = @ \cup {Pr(a, b)}, !.rx[<<a, b>>] = x.now, !.rx[<<b, a>>] = x.now]
        x2 == CallAt(x1, b, LAMBDA S, e : CallUp(S, e, x1.now, a, TRUE))
    IN CallAt(x2, a, LAMBDA S, e : CallUp(S, e, x2.now, b, FALSE))

Detect(x) ==
    LET p == CHOOSE p \in ToDetect(x) : \A q \in ToDetect(x) : p[1] < q[1] \/ (p[1] = q[1] /\ p[2] <= q[2])
        x1 == [x EXCEPT !.sess = @ \ {Pr(p[1], p[2])}, !.net[<<p[2], p[1]>>] = <<>>, !.net[<<p[1], p[2]>>] = <<>>]
    IN CallAt(x1, p[1], LAMBDA S, e : CallDown(S, e, x1.now, p[2], Z))

DeliverStep(x) ==
    LET p == HeadPair(x)[1]
        a == p[1]
        b == p[2]
        f == x.net[p][1]
        x0 == [x EXCEPT !.net[p] = Tail(@)]
        reach == b \in x.alive /\ Pr(a, b) \in x.sess
    IN IF ~reach THEN x0
       ELSE LET x1 == SeeRx(x0, a, b)
            IN IF b \in Slow
               THEN [x1 EXCEPT !.inbox[b] = Append(@, [from |-> a, f |-> f, due |-> SatAdd(x.now, SecW(SlowCpuSec))])]
               ELSE CallAt(x1, b, LAMBDA S, e : CallBytes(S, e, x1.now, a, <<f>>, FALSE))

ProcessStep(x) ==
    LET n == CHOOSE n \in InboxDue(x) : \A m \in InboxDue(x) : n <= m
        it == x.inbox[n][1]
        x1 == [x EXCEPT !.inbox[n] = Tail(@)]
    IN IF n \notin x.alive THEN x1
       ELSE CallAt(x1, n, LAMBDA S, e : CallBytes(S, e, x1.now, it.from, <<it.f>>, FALSE))

\* a timer call moves the node's deadline past now: otherwise the host would call again at once, forever
FireStep(x) ==
    LET n == CHOOSE n \in TimerDue(x) : \A m \in TimerDue(x) : n <= m
        x1 == CallAt(x, n, LAMBDA S, e : CallTimeout(S, e, x.now))
    IN [x1 EXCEPT !.hist.okTimer = @ /\ Lt(x.now, PollTimeout(x1.nodes[n]))]

KaStep(x) ==
    [x EXCEPT !.nextKA = SatAdd(x.now, SecW(30)),
              !.rx = [p \in DOMAIN x.rx |-> IF Pr(p[1], p[2]) \in x.sess /\ SessOk(x, p[1], p[2]) /\ SessOk(x, p[2], p[1])
                                            THEN x.now ELSE x.rx[p]]]

Deadlines(x) ==
    {PollTimeout(x.nodes[n]) : n \in {n \in x.alive : LeftTimed(x.nodes[n])}} \cup {x.nextKA} \cup {i.due : i \in {x.inbox[n][1] : n \in {n \in Nodes : x.inbox[n] # <<>>}}}
      \cup (IF x.pc <= Len(Script) THEN {SecW(START + Script[x.pc][2])} ELSE {})
FutureDeadlines(x) == {d \in Deadlines(x) : Lt(x.now, d)}
MinD(S) == CHOOSE d \in S : \A e \in S : Le(d, e)

AdvanceStep(x) ==
    LET d == MinD(FutureDeadlines(x)) IN [x EXCEPT !.now = d]

(* ---- the script ---- *)
\* ends every session of n at the live peers (code `code` as seen by the peer) and at n
\* the same, except that the close to `skip` is lost: that peer keeps its session
CloseSessionsBut(x, n, code, skip) ==
    LET peers == Ordered({p \in Nodes : Pr(n, p) \in x.sess /\ p # skip}, NONE)
        RECURSIVE Go(_, _)
        Go(y, i) == IF i > Len(peers) THEN y
                    ELSE LET p == peers[i]
                             y1 == [y EXCEPT !.sess = @ \ {Pr(n, p)}, !.net[<<n, p>>] = <<>>, !.net[<<p, n>>] = <<>>]
                             y2 == IF p \in y.alive THEN CallAt(y1, p, LAMBDA S, e : CallDown(S, e, y1.now, n, code)) ELSE y1
                             y3 == IF n \in y2.alive THEN CallAt(y2, n, LAMBDA S, e : CallDown(S, e, y2.now, p, Z)) ELSE y2
                         IN Go(y3, i + 1)
    IN Go(x, 1)
CloseSessions(x, n, code) == CloseSessionsBut(x, n, code, 0)

ScriptStep(x) ==
    LET en == Script[x.pc]
        k == en[1]
        x0 == [x EXCEPT !.pc = @ + 1]
    IN CASE k = "crash" -> [x0 EXCEPT !.alive = @ \ {en[3]}, !.hist.crashAt[en[3]] = <<x.now>>]
         [] k = "restart" ->
              LET n == en[3]
                  r == CallStart([me |-> n, isHub |-> n \in Hubs, hubs |-> HubSeq], EnvFor(x0, n), x0.now, U!W(en[4]), Z)
              IN IF r.err # "ok" THEN x0
                 ELSE [x0 EXCEPT !.alive = @ \cup {n}, !.nodes[n] = r.S, !.store[n] = r.S.loc.sealed, !.dial = TRUE,
                                  !.hist.restarts = @ + 1]
         [] k = "cut" -> [x0 EXCEPT !.cut = @ \cup {Pr(en[3], en[4])}]
         [] k = "heal" -> LET y == [x0 EXCEPT !.cut = @ \ {Pr(en[3], en[4])}] IN
                          \* the harness closes the session on both sides and redials
                          IF Pr(en[3], en[4]) \in y.sess
                          THEN LET a == en[3] b == en[4]
                                   y1 == [y EXCEPT !.sess = @ \ {Pr(a, b)}, !.net[<<a, b>>] = <<>>, !.net[<<b, a>>] = <<>>]
                                   y2 == CallAt(y1, a, LAMBDA S, e : CallDown(S, e, y1.now, b, Z))
                               IN CallAt(y2, b, LAMBDA S, e : CallDown(S, e, y2.now, a, Z))
                          ELSE y
         [] k = "gone" -> LET h == en[3] m == en[4]
                              y == [x0 EXCEPT !.car[<<h, m>>] = [k |-> "gone", since |-> x.now, sleep |-> <<>>],
                                              !.dead = @ \cup {Pr(h, m)}]
                          IN CallAt(y, h, LAMBDA S, e : CallCarrierGone(S, e, y.now, m))
         [] k = "notice" -> LET h == en[3] m == en[4]
                                y == [x0 EXCEPT !.car[<<h, m>>] = [k |-> "gone", since |-> x.now, sleep |-> <<>>]]
                            IN CallAt(y, h, LAMBDA S, e : CallCarrierGone(S, e, y.now, m))
         [] k = "back" -> LET h == en[3] m == en[4]
                              y == [x0 EXCEPT !.car[<<h, m>>] = [k |-> "open"], !.dead = @ \ {Pr(h, m)}]
                          IN CallAt(y, h, LAMBDA S, e : CallCarrierReturn(S, e, y.now, m))
         [] k = "leave" -> LET n == en[3]
                               y == CallAt(x0, n, LAMBDA S, e : CallLeave(S, e))
                           IN CloseSessions(y, n, LEAVE_CODE)
         [] k = "leavelost" -> LET n == en[3]
                                   y == CallAt(x0, n, LAMBDA S, e : CallLeave(S, e))
                                   z == CloseSessionsBut(y, n, LEAVE_CODE, en[4])
                               IN [z EXCEPT !.alive = @ \ {n}, !.hist.crashAt[n] = <<x.now>>]
         [] k = "direct" -> [x0 EXCEPT !.direct = @ \cup {Pr(en[3], en[4])}]
         [] k = "refuse" -> [x0 EXCEPT !.refuse = @ \cup {en[3]}]
         [] k = "revoke" -> LET n == en[3] m == en[4]
                                r == CallRevoke(x0.nodes[n], EnvFor(x0, n), x0.now, m)
                            IN Done(x0, n, r.S, x0.now)
         [] k = "jump" -> [x0 EXCEPT !.now = SatAdd(@, SecW(en[3]))]
         [] k = "move" -> CallAt(x0, en[3], LAMBDA S, e : CallMoved(S, e, x0.now))
         [] k = "lose" -> [x0 EXCEPT !.lose = en[3]]
         [] k = "rtt" -> [x0 EXCEPT !.srtt[<<en[3], en[4]>>] = N!Millis(en[5]), !.srtt[<<en[4], en[3]>>] = N!Millis(en[5])]

(* ---- the specification ---- *)
HistInit == [down |-> {}, left |-> {}, susp |-> {}, conf |-> {}, acc |-> {}, rest |-> {}, resub |-> {}, rel |-> {},
             hold |-> {}, restore |-> {}, revcl |-> {}, lvcl |-> {}, lostProbes |-> 0, primN |-> [n \in Nodes |-> 0], supp |-> {}, restarts |-> 0,
             okDown |-> TRUE, okInc |-> TRUE, okBounds |-> TRUE, okWait |-> TRUE, okTimer |-> TRUE, healWait |-> FALSE,
             lastInc |-> [n \in Nodes |-> Z], crashAt |-> [n \in Nodes |-> <<>>]]

StartAll ==
    LET RECURSIVE St(_, _)
        St(x, i) == IF i > Len(NodeSeq) THEN x
                    ELSE LET n == NodeSeq[i]
                             r == CallStart([me |-> n, isHub |-> n \in Hubs, hubs |-> HubSeq], EnvFor(x, n), x.now, U!W(1000000 + n), Z)
                         IN St([x EXCEPT !.nodes[n] = r.S, !.store[n] = r.S.loc.sealed, !.hist.lastInc[n] = INC!Word(r.S.inc)], i + 1)
        x0 == [now |-> SecW(START), nodes |-> [n \in Nodes |-> <<>>], alive |-> Nodes,
               net |-> [p \in Nodes \X Nodes |-> <<>>], inbox |-> [n \in Nodes |-> <<>>],
               rx |-> [p \in Nodes \X Nodes |-> SecW(START)], srtt |-> [p \in Nodes \X Nodes |-> SRTT], sess |-> {}, cut |-> {}, dead |-> {}, direct |-> {}, refuse |-> {},
               car |-> [p \in Hubs \X Members |-> [k |-> "unknown"]], store |-> [n \in Nodes |-> <<>>],
               hist |-> HistInit, steps |-> 0, pc |-> 1, lose |-> 0, nextKA |-> SecW(START + 30), dial |-> TRUE]
    IN St(x0, 1)

Init == w = StartAll

\* the run is deterministic: one successor function
Nxt(x) ==
    IF ScriptDue(x) THEN ScriptStep(x)
    ELSE IF HeadPair(x) # <<>> THEN DeliverStep(x)
    ELSE IF InboxDue(x) # {} THEN ProcessStep(x)
    ELSE IF ToDetect(x) # {} THEN Detect(x)
    ELSE IF ToDial(x) # {} THEN Connect(x)
    ELSE IF TimerDue(x) # {} THEN FireStep(x)
    ELSE IF KaDue(x) THEN KaStep(x)
    ELSE AdvanceStep(x)

CanAdvance(x) == FutureDeadlines(x) # {} /\ Le(MinD(FutureDeadlines(x)), SecW(START + MaxSec))
Live(x) == ~Quiescent(x) \/ CanAdvance(x)
Step == Live(w) /\ w' = [Nxt(w) EXCEPT !.steps = w.steps + 1]

Done0 == ~Live(w)
Next == Step \/ (Done0 /\ UNCHANGED w)

(* No fairness is needed: the scripted run is a deterministic chain, and the awareness bound is the safety property Awareness.
   Liveness (a crashed member is eventually gone) is the bounded-time statement: 145 s after the crash it holds. *)
Spec == Init /\ [][Next]_w

(* Liveness. The scripted run is forced: every state that is not Finished has exactly one successor, and each step
   counts in `steps`, so the state graph is acyclic. TLC's exploration finishing (0 states left on queue) therefore
   shows that EVERY execution of the model, under every adversary choice, reaches a Finished state; the properties
   below are invariants of the Finished states. Together they are the leads-to statements (`crashed ~> removed`, ...)
   at the end of the run, with no bound beyond the model's time. A temporal check with WF_w on Step was tried and
   does not finish in TLC (it stalls on the second state of even the smallest model), see the report. *)
Finished == ~Live(w)
LiveCompleteAll == Finished => (w.hist.crashAt[4] # <<>> => \A o \in w.alive : 4 \notin DOMAIN w.nodes[o].members)
LiveRestored == Finished => <<1, 4>> \in w.hist.restore
LiveLeaveReported == Finished => \A o \in w.alive \ {4} : <<o, 4>> \in w.hist.left
\* convergence: every live node lists exactly the live nodes other than itself
LiveConverged == Finished => \A o \in w.alive : DOMAIN w.nodes[o].members = w.alive \ {o}
StepsBound == w.steps <= 200000

(* Temporal liveness under fairness. A run that never stops while Step is enabled (infinitely many steps, or it ends
   in a state where Step is disabled and stays there) is FairRun; this is weak fairness of Step written as a
   hypothesis of the property, so TLC checks every property below as FairRun => property over the whole state graph,
   with no scripted bound beyond the model's MaxSec. Each is a leads-to or an eventually-always statement. *)
FairRun == ([]<><<Step>>_w) \/ (<>[]Done0)
CrashedMember == w.hist.crashAt[4] # <<>>
GoneFromAll == \A o \in w.alive : 4 \notin DOMAIN w.nodes[o].members
Converged == \A o \in w.alive : DOMAIN w.nodes[o].members = w.alive \ {o}
TLiveComplete == FairRun => (CrashedMember ~> GoneFromAll)
TLiveRestored == FairRun => (TRUE ~> (<<1, 4>> \in w.hist.restore))
TLiveLeave == FairRun => (TRUE ~> (\A o \in w.alive \ {4} : <<o, 4>> \in w.hist.left))
TLiveNever == FairRun => (TRUE ~> (\A o \in w.alive : <<o, 4>> \in w.hist.down))
TLiveConverged == FairRun => <>[]Converged
NeverFinished == ~Finished

(* ---- properties ---- *)
SecsSince(x, t) == U!Lt(SecW(START + t), x.now)

\* the history flags and the tables
Bounds == w.hist.okBounds
DownOK == w.hist.okDown
IncOK == w.hist.okInc
\* no DOWN accepted on a fresh lease (property 3d) and no early confirmation by a lost probe/slow member are
\* stated per config with NoConf / NoDown below
NoConf(hub, m) == <<hub, m>> \notin w.hist.conf
NoDownEv(obs, m) == <<obs, m>> \notin w.hist.down
\* a member that left is reported as left everywhere and never as down (property 7)
LeaveReported(m) == \A o \in Nodes \ {m} : <<o, m>> \notin w.hist.down
\* no node lists itself, and none lists a revoked node (view invariants)
ViewSelf == \A n \in Nodes : n \notin DOMAIN w.nodes[n].members
ViewRevoked == \A n \in Nodes : \A m \in w.nodes[n].revoked : m \notin DOMAIN w.nodes[n].members
EpochMono == \A n \in Nodes : TRUE
\* property 2 (awareness bound): 145 s after a member crashed no live node lists it
Awareness(m, bound) ==
    w.hist.crashAt[m] # <<>> /\ Gt(SatSub(w.now, w.hist.crashAt[m][1]), SecW(bound))
      => \A o \in w.alive : m \notin DOMAIN w.nodes[o].members
\* property 5: a returning carrier within the lease restores
RestoredBack(h, m) == <<h, m>> \in w.hist.rest => <<h, m>> \in w.hist.restore
\* property 6: a revoke closes the sessions and releases at once
RevokeEffect(n, m) == <<n, m>> \in w.hist.revcl => m \notin DOMAIN w.nodes[n].members /\ m \notin DOMAIN w.nodes[n].roster
\* property 9 for the queues: each call's queue is bounded
Aware4 == Awareness(4, 145)
NoDown34 == NoDownEv(3, 4) /\ NoDownEv(4, 3)
NoConf14 == NoConf(1, 4) /\ NoConf(2, 4)
NoDownAny == w.hist.down = {} /\ w.hist.conf = {}
Restored14 == RestoredBack(1, 4)
Revoke14 == RevokeEffect(1, 4)
\* a member that left, with the close lost at one hub, is out of every live node's list soon after the leave: the hub that
\* saw it tells the other, which drops it as left (and so never reports it down after the lease)
LeftGone == SecsSince(w, 45) => \A o \in w.alive : 4 \notin DOMAIN w.nodes[o].members
LeaveNotDown4 == LeaveReported(4) /\ <<1, 4>> \notin w.hist.hold /\ <<2, 4>> \notin w.hist.hold
\* property 10: the primary of a member does not flap inside the hysteresis (at most the first choice and one switch)
PrimaryStable == \A n \in Members : w.hist.primN[n] <= 2
\* #284: a removal that a quiet window deferred moves only on its own schedule; no heal defers it again (only a late
\* timer does, the reference model's rule)
WaitKept == w.hist.okWait
\* pinc#551: every timer call the host makes moves the node's membership deadline past now, so a host that serves due
\* timers first (the facade's run_as, under Endpoint::close) always gets past membership's; the other layers'
\* deadlines are not in this model
TimerMoves == w.hist.okTimer
\* ScrHealWait: the removal hub 1 reports at 76 s, deferred by the window of the heal at 75 s, is applied at the tick after
\* that window's end and the extra look (75 + 10 + 5 s, ticks every 0.5 s), whatever window the heal at 79 s opened
HealGone == SecsSince(w, 91) => 5 \notin DOMAIN w.nodes[4].members
\* witnesses (TLC must find a violation of each)
NeverSuppressed == w.hist.supp = {}
NeverSwitched == \A n \in Members : w.hist.primN[n] <= 1
NoFlap == NeverSwitched
NeverConfirmed == w.hist.conf = {}
NeverDown == w.hist.down = {}
\* no hub ever kept a suspicion record, the internal state that drives the probes (a suspicion is not an event)
NeverSusp == w.hist.susp = {}
\* a lost probe is answered: once the member is back, no hub still suspects it
SuspEnded == Ge(w.now, SecW(START + 70)) => \A h \in Hubs : 4 \notin DOMAIN w.nodes[h].susp
NeverRestore == w.hist.restore = {}
NeverRestarted == w.hist.restarts = 0
NeverLeft == w.hist.left = {}
NeverRevoked == w.hist.revcl = {}
\* a heal reaches a node while a removal waits there for a later instant
NeverHealWait == ~w.hist.healWait

(***************************************************************************)
(* The scripts of the scenarios (hubs 1 and 2, members 3 and 4 unless noted) *)
(***************************************************************************)
ScrNone == <<>>
\* a member crashes and its carrier to both hubs drops (churn, completeness)
ScrCrash == <<<<"crash", 40, 4>>, <<"gone", 40, 1, 4>>, <<"gone", 40, 2, 4>>>>
\* a crash with no carrier event: the lease decides
ScrCrashQuiet == <<<<"crash", 40, 4>>>>
\* a live member's carrier drops with one probe lost: never confirmed
ScrLostProbe == <<<<"lose", 39, 1>>, <<"notice", 40, 1, 4>>, <<"back", 50, 1, 4>>>>
\* a slow member (Slow = {4}) whose carrier drops: the transport still answers
ScrSlow == <<<<"gone", 40, 1, 4>>, <<"back", 60, 1, 4>>>>
\* a partition longer than the lease, then a heal: members 3 and 4 cut from both hubs
ScrPartition == <<<<"cut", 40, 1, 3>>, <<"cut", 40, 2, 3>>, <<"cut", 40, 1, 4>>, <<"cut", 40, 2, 4>>,
                  <<"heal", 150, 1, 3>>, <<"heal", 150, 2, 3>>, <<"heal", 150, 1, 4>>, <<"heal", 150, 2, 4>>>>
\* a carrier drop and return within the lease: the entry and subscriptions come back
ScrReturn == <<<<"cut", 40, 2, 4>>, <<"gone", 40, 1, 4>>, <<"heal", 45, 2, 4>>, <<"back", 50, 1, 4>>>>
\* a graceful leave
ScrLeave == <<<<"leave", 40, 4>>>>
\* a graceful leave whose close to hub 2 is lost, the member gone: only hub 1 sees it, and tells hub 2
ScrLeaveLost == <<<<"leavelost", 40, 4, 2>>>>
\* member 4's session to hub 1 runs on a validated direct path; the pair is cut and its carrier drops; hub 2's relay
\* still reaches the member, which is alive
ScrDirectCut == <<<<"direct", 20, 1, 4>>, <<"cut", 40, 1, 4>>, <<"gone", 40, 1, 4>>>>
\* hub 1's host refuses a relayed probe through hub 2, the first probe is lost, the member is alive
ScrRefused == <<<<"refuse", 1, 2>>, <<"lose", 39, 1>>, <<"notice", 40, 1, 4>>, <<"back", 50, 1, 4>>>>
\* a revocation
ScrRevoke == <<<<"revoke", 40, 1, 4>>>>
\* crash and restart on the same host store, a wall clock that went back
ScrRestart == <<<<"crash", 40, 4>>, <<"restart", 60, 4, 5>>>>
\* a suspension: time jumps with timers due
ScrJump == <<<<"jump", 40, 20>>>>
\* an address move
ScrMove == <<<<"move", 40, 4>>>>
\* primary hub: member 3 starts with hubs at 100 ms and 90 ms (inside the hysteresis), then hub 2 gets to 40 ms
ScrPrimaryHyst == <<<<"rtt", 1, 3, 1, 100>>, <<"rtt", 1, 3, 2, 90>>, <<"rtt", 100, 3, 2, 40>>>>
ScrPrimaryFlat == <<<<"rtt", 1, 3, 1, 100>>, <<"rtt", 1, 3, 2, 90>>>>
\* quick profile: ScrPrimaryHyst with hub 2's drop to 40 ms at 20 s instead of 100 s
ScrPrimaryHystQuick == <<<<"rtt", 1, 3, 1, 100>>, <<"rtt", 1, 3, 2, 90>>, <<"rtt", 20, 3, 2, 40>>>>
\* #343: hub 1 is cut from hub 2 and hub 2 from member 4 from the start; member 3 homes on hub 1 (100 ms against 120 ms)
\* and lists 4, which hub 2 never hears of; at 100 s hub 2 drops to 40 ms and 3 moves its home there; 4 crashes at 130 s
\* and only hub 1 learns it; every cut heals at 250 s. Hub 2's complete snapshot omits 4, so 3 must let 4 go too.
ScrStaleView == <<<<"cut", 0, 1, 2>>, <<"cut", 0, 2, 4>>, <<"rtt", 0, 3, 1, 100>>, <<"rtt", 0, 3, 2, 120>>,
                  <<"rtt", 100, 3, 2, 40>>, <<"crash", 130, 4>>, <<"heal", 250, 1, 2>>, <<"heal", 250, 2, 4>>>>
\* #284 (hubs 1, 2 and 3, members 4 and 5): member 4 homes on hub 1 and is cut from hubs 2 and 3 at 10 s; hub 2 is
\* heard again at 75 s (a heal: 65 s of silence), hub 1 revokes member 5 at 76 s, so its DOWN delta reaches 4 inside
\* that window and the removal waits, and hub 3 is heard again at 79 s (a second heal) while it waits.
ScrHealWait == <<<<"rtt", 0, 4, 2, 100>>, <<"rtt", 0, 4, 3, 100>>, <<"cut", 10, 2, 4>>, <<"cut", 10, 3, 4>>,
                 <<"heal", 75, 2, 4>>, <<"revoke", 76, 1, 5>>, <<"heal", 79, 3, 4>>>>
=============================================================================
