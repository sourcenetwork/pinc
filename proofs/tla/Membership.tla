------------------------------ MODULE Membership ----------------------------
(***************************************************************************)
(* The membership machine of vinc-membership: the member view (view.rs)     *)
(* and the hub roster (hub.rs), operator for operator.                      *)
(*                                                                         *)
(* Every Rust function is an operator of the same name in CamelCase, from   *)
(* (state, env, now, arguments) to the state, or to [S, ...] where the      *)
(* function returns a value. The state S holds the fields of `Membership`   *)
(* (node.rs) in camelCase, the host's incarnation store (loc), and the      *)
(* output of the call so far (sent, bc, cl, ev, tr, lostE, lostT). The      *)
(* statements of a function are the LET chain of its operator, in the       *)
(* order of the code, so the order of sent frames, broadcast-layer calls,   *)
(* events and traces is the order of the code. A loop over a BTreeMap is a  *)
(* recursion on NextKey, the cursor of node.rs next_key.                    *)
(*                                                                         *)
(* The functions that call each other in a cycle (renew, push_delta,        *)
(* apply_delta, on_self_entry) are declared RECURSIVE; the cycle is cut at  *)
(* run time because a hub's delta about itself returns at once.             *)
(*                                                                         *)
(* The timers, the dispatch of frames and the session events are in         *)
(* MembershipOps.tla. Lean counterpart: Vinc/MembershipModel*.lean.         *)
(***************************************************************************)
EXTENDS MemCore

INC == INSTANCE Incarnation WITH PersModes <- {TRUE}, TrackFloor <- FALSE, Faults <- FALSE, MaxSteps <- 0,
                                 loc <- 0, inc <- 0, ann <- 0, mono <- 0, floorOK <- 0, obsOK <- 0, heard <- 0, steps <- 0

RSession == [r |-> "s", via |-> 0]
RDirect == [r |-> "d", via |-> 0]
RVia(x) == [r |-> "v", via |-> x]

SatMul3(a) == LET p == N!MulAt(a, 3, 1, 0) IN IF U!Fits(p) THEN p ELSE U!Max64

IsBoot(S, x) == IsHubIn(S, x)
RecOf(S) == [inc |-> INC!Word(S.inc), ver |-> S.ver, th |-> S.th]
NewCopy == [entries |-> EmptyFn, round |-> Z, open |-> FALSE]

(* ---- node.rs: sending ---- *)
Tx(S, env, peer, route, f) ==
    IF peer \in S.revoked \/ peer = S.me THEN [S |-> S, ok |-> FALSE]
    ELSE LET s1 == Trace(S, [k |-> "frame_out", peer |-> peer, ty |-> TyOf(f)])
             ok == peer \in env.acc
         IN [S |-> [s1 EXCEPT !.sent = Append(@, [to |-> peer, r |-> route.r, via |-> route.via, f |-> f, ok |-> ok])],
             ok |-> ok]
SendS(S, env, peer, route, f) == Tx(S, env, peer, route, f).S
DeltaTo(S, env, peer, m, rec, a) == SendS(S, env, peer, RSession, [k |-> "delta", m |-> m, rec |-> rec, a |-> a])

HubUp(S, now, x) ==
    x = S.me \/ (x \in DOMAIN S.up /\ x \in DOMAIN S.heard /\ Lt(SatSub(now, S.heard[x]), HUB_STALE))

\* recheck holds, per member whose removal a quiet window deferred, [due |-> the instant it is re-checked,
\* grace |-> whether its extra look has begun]. WaitOnQuiet is the rule of the code (begin_quiet, #284): a late timer
\* (cause 0) defers every waiting removal to the new window's end with its extra look not begun, a heal (cause 1)
\* leaves each at its own instant and grace state. A witness config overrides it with OldWaitOnQuiet, the rule before
\* #284, under which a heal defers every waiting removal again as well.
WaitOnQuiet(rc, until, cause) == IF cause = 0 THEN [m \in DOMAIN rc |-> [due |-> until, grace |-> FALSE]] ELSE rc
OldWaitOnQuiet(rc, until, cause) == [m \in DOMAIN rc |-> [due |-> until, grace |-> FALSE]]

BeginQuiet(S, now, cause) ==
    LET until == SatAdd(now, QUIET)
    IN Trace([S EXCEPT !.quietUntil = until, !.regrace = FALSE, !.recheck = WaitOnQuiet(S.recheck, until, cause)],
             [k |-> "quiet", cause |-> cause])

\* recheck.entry(m).or_insert((quiet_until, regrace)): a member already waiting keeps its instant and grace state
Defer(S, m) == IF m \in DOMAIN S.recheck THEN S.recheck ELSE Put(S.recheck, m, [due |-> S.quietUntil, grace |-> S.regrace])

(* ---- view.rs: hello, record, renew ---- *)
HelloTo(S, env, peer, snap) ==
    IF S.leaving THEN S
    ELSE SendS(S, env, peer, RSession,
               [k |-> "hello", rec |-> RecOf(S), snap |-> snap, homed |-> (~S.isHub /\ S.primary = <<peer>>)])

\* hello_at and hsent hold Options; a cleared entry stays in the table as <<>> (an entry never leaves)
TimeAt(f, k) == IF k \in DOMAIN f THEN f[k] ELSE <<>>
Unset(f, k) == IF k \in DOMAIN f THEN [f EXCEPT ![k] = <<>>] ELSE f

BumpRecord(S) ==
    LET r == INC!NextOp(S.loc, S.inc)
    IN IF r.err = "ok"
       THEN Trace([S EXCEPT !.inc = r.inc, !.loc = r.loc], [k |-> "incarnation", inc |-> INC!Word(r.inc)])
       ELSE Trace([S EXCEPT !.sealFailed = TRUE], [k |-> "seal_failed"])

PulseFreshOn(env, now, hub) ==
    LET e == Evidence(env, hub)
    IN e # <<>> /\ e[1].pto = 0 /\ Lt(SatSub(now, e[1].rx), PULSE_FRESH)

RECURSIVE Renew(_, _, _, _, _), PushDelta(_, _, _, _, _, _), ApplyDelta(_, _, _, _, _), OnSelfEntry(_, _, _, _, _, _)

RECURSIVE RenewLoop(_, _, _, _, _, _)
RenewLoop(S, env, now, forceSnap, periodic, i) ==
    IF i > Len(S.boot) THEN S
    ELSE LET hub == S.boot[i]
         IN IF hub = S.me \/ hub \notin DOMAIN S.up THEN RenewLoop(S, env, now, forceSnap, periodic, i + 1)
            ELSE LET snap == forceSnap \/ hub \notin DOMAIN S.hv
                 IN IF periodic /\ ~snap /\ (S.primary # <<hub>> \/ S.homeOk = <<hub>>) /\ PulseFreshOn(env, now, hub)
                    THEN RenewLoop(Trace(S, [k |-> "hello_suppressed", hub |-> hub]), env, now, forceSnap, periodic, i + 1)
                    ELSE LET s1 == [S EXCEPT !.helloAt = Put(@, hub, IF TimeAt(@, hub) = <<>> THEN <<now>> ELSE TimeAt(@, hub)),
                                             !.hsent = Put(@, hub, <<now>>)]
                         IN RenewLoop(HelloTo(s1, env, hub, snap), env, now, forceSnap, periodic, i + 1)

Renew(S, env, now, forceSnap, periodic) ==
    LET s1 == IF S.sentRec # <<>> /\ S.sentRec[1] # <<S.ver, S.th>> THEN BumpRecord(S) ELSE S
        periodic1 == IF s1.sentRec # <<<<S.ver, S.th>>>> THEN FALSE ELSE periodic
        s2 == [s1 EXCEPT !.sentRec = <<<<S.ver, S.th>>>>]
        cur == [inc |-> INC!Word(s2.inc), ver |-> S.ver, th |-> S.th]
        s3 == IF s2.isHub /\ s2.own # cur
              THEN PushDelta([s2 EXCEPT !.own = cur], env, now, s2.me, cur, 1)
              ELSE s2
        s4 == RenewLoop(s3, env, now, forceSnap, periodic1, 1)
    IN [s4 EXCEPT !.nextRenew = SatAdd(now, RENEW)]

(* ---- view.rs: the primary hub ---- *)
RttOf(S, x) == Get(Lookup(S.hrtt, x), RTT_UNKNOWN)

RECURSIVE BestHub(_, _, _, _, _)
\* the lowest (round trip, position) among the live hubs other than this node, in preference order
BestHub(S, now, F, i, best) ==
    IF i > Len(F) THEN best
    ELSE LET hub == F[i]
             k == <<RttOf(S, hub), i>>
             lt == best = <<>> \/ Lt(k[1], best[1][1][1]) \/ (k[1] = best[1][1][1] /\ i < best[1][1][2])
         IN IF HubUp(S, now, hub) /\ lt THEN BestHub(S, now, F, i + 1, <<<<k, hub>>>>) ELSE BestHub(S, now, F, i + 1, best)

Reselect(S, env, now) ==
    LET F == SelectSeq(S.boot, LAMBDA x : x # S.me)
        b == BestHub(S, now, F, 1, <<>>)
        p0 == IF S.isHub THEN <<S.me>> ELSE IF b = <<>> THEN <<>> ELSE <<b[1][2]>>
        p == IF ~S.isHub /\ p0 # <<>> /\ S.primary # <<>> /\ p0[1] # S.primary[1] /\ HubUp(S, now, S.primary[1])
                /\ Ge(SatAdd(RttOf(S, p0[1]), HYST_ABS), N!Div(SatMul3(RttOf(S, S.primary[1])), 4))
             THEN S.primary ELSE p0
    IN IF p = <<>> \/ S.primary = p THEN S
       ELSE LET np == p[1]
                s1 == Trace([S EXCEPT !.primary = p], [k |-> "primary", hub |-> np])
                s2 == IF ~S.isHub
                      THEN LET s2a == [s1 EXCEPT !.homeOk = <<>>]
                               s2b == HelloTo(s2a, env, np, TRUE)
                           IN IF S.primary # <<>> /\ S.primary[1] \in DOMAIN S.up
                              THEN HelloTo(s2b, env, S.primary[1], FALSE) ELSE s2b
                      ELSE s1
            IN Bc(s2, [k |-> "primary", old |-> S.primary, new |-> np])

RttSample(S, hub, r) ==
    LET old == Lookup(S.hrtt, hub)
        v == IF old = <<>> THEN r ELSE Min2(r, N!Div(N!Add(N!Mul(old[1], 3), r), 4))
    IN [S EXCEPT !.hrtt = Put(@, hub, v)]

Bump(S) ==
    LET e == U!Add64(S.epoch, One)
    IN Emit([S EXCEPT !.epoch = e], EvView(e, Cardinality(DOMAIN S.members)))

(* ---- view.rs: the source of the view, one member's place in it ---- *)
Source(S, now) ==
    LET home == IF ~S.isHub /\ S.primary # <<>> /\ S.homeOk = S.primary /\ S.primary[1] \in DOMAIN S.hv
                   /\ HubUp(S, now, S.primary[1]) THEN S.primary ELSE <<>>
    IN IF home # <<>> THEN [only |-> home, hold |-> FALSE, anyFresh |-> TRUE]
       ELSE [only |-> <<>>, hold |-> ~S.isHub, anyFresh |-> \E k \in DOMAIN S.hv : HubUp(S, now, k)]

OnSelfEntry(S, env, now, hub, rec, alive) ==
    IF hub = S.me THEN S
    ELSE LET s1 == Trace(S, [k |-> "self_delta", hub |-> hub])
         IN IF alive = 1 /\ Gt(rec.inc, INC!Word(S.inc))
            THEN LET r == INC!ObserveOp(S.loc, S.inc, rec.inc)
                 IN IF r.err = "ok"
                    THEN IF r.ch
                         THEN LET s2 == Trace([s1 EXCEPT !.inc = r.inc, !.loc = r.loc],
                                              [k |-> "incarnation", inc |-> INC!Word(r.inc)])
                              IN Renew(s2, env, now, FALSE, FALSE)
                         ELSE s1
                    ELSE Trace([s1 EXCEPT !.sealFailed = TRUE], [k |-> "seal_failed"])
            ELSE IF alive # 1 \/ Lt(rec.inc, INC!Word(S.inc)) THEN HelloTo(s1, env, hub, FALSE)
            ELSE Bc(s1, [k |-> "resub", hub |-> hub])

(* one hub's entry for m, after the absence lease: the fold of recompute_one over the hub copies in order *)
RECURSIVE PickBest(_, _, _, _, _, _, _)
PickBest(S, now, m, src, cur, best, expired) ==
    LET hub == NextKey(DOMAIN S.hv, cur)
    IN IF hub = NONE THEN [best |-> best, expired |-> expired]
       ELSE LET copy == S.hv[hub]
                eligible == IF src.only # <<>> THEN src.only[1] = hub ELSE (~src.anyFresh \/ HubUp(S, now, hub))
            IN IF ~eligible \/ m \notin DOMAIN copy.entries THEN PickBest(S, now, m, src, hub, best, expired)
               ELSE LET ce == copy.entries[m]
                        absent == ce.absentSince # <<>>
                    IN IF absent /\ Ge(SatSub(now, ce.absentSince[1]), LEASE)
                       THEN PickBest(S, now, m, src, hub, best, TRUE)
                       ELSE IF best = <<>> \/ Gt(ce.rec.inc, best[1][1].inc)
                               \/ (ce.rec.inc = best[1][1].inc /\ best[1][2] /\ ~absent)
                            THEN PickBest(S, now, m, src, hub, <<<<ce.rec, absent>>>>, expired)
                            ELSE PickBest(S, now, m, src, hub, best, expired)

HomeDelta(S, env, m, rec, alive) ==
    LET RECURSIVE Loop(_, _)
        Loop(s, cur) ==
            LET p == NextKey(S.homed, cur)
            IN IF p = NONE THEN s
               ELSE IF p # m THEN Loop(DeltaTo(s, env, p, m, rec, alive), p) ELSE Loop(s, p)
    IN Loop(S, NONE)

RemoveFromView(S, env, now, m, cur, src, expired) ==
    IF cur = <<>> THEN [S |-> S, ch |-> FALSE]
    ELSE LET c == cur[1] IN
         IF src.hold
         THEN [S |-> IF Cardinality(DOMAIN S.recheck) < MAX_TABLE THEN [S EXCEPT !.recheck = Defer(S, m)] ELSE S, ch |-> FALSE]
         ELSE IF Lt(now, S.quietUntil) /\ Cardinality(DOMAIN S.recheck) < MAX_TABLE
              THEN [S |-> Trace([S EXCEPT !.recheck = Defer(S, m)], [k |-> "deferred", member |-> m]), ch |-> FALSE]
              ELSE LET s1 == [S EXCEPT !.members = Del(@, m),
                                       !.goneVer = IF Cardinality(DOMAIN @) < MAX_TABLE \/ m \in DOMAIN @
                                                   THEN Put(@, m, <<c.rec.ver, c.rec.th>>) ELSE @]
                       wasLeft == m \in S.left
                       s2 == [s1 EXCEPT !.left = @ \ {m}]
                       why == IF wasLeft THEN 1 ELSE IF expired THEN 2 ELSE 0
                       alive == IF wasLeft THEN 2 ELSE 0
                       s3 == Trace(s2, [k |-> "removed", member |-> m, why |-> why])
                       s4 == Emit(s3, IF wasLeft THEN EvLeft(m) ELSE EvDown(m))
                       s5 == IF s4.isHub THEN HomeDelta(s4, env, m, c.rec, alive) ELSE s4
                   IN [S |-> s5, ch |-> TRUE]

RecomputeOne(S, env, now, m) ==
    LET src == Source(S, now)
        pb == PickBest(S, now, m, src, NONE, <<>>, FALSE)
        cur == Lookup(S.members, m)
    IN IF pb.best = <<>> THEN RemoveFromView(S, env, now, m, cur, src, pb.expired)
       ELSE LET best == pb.best[1][1]
                absent == pb.best[1][2]
                s1 == IF S.isHub /\ (cur = <<>> \/ cur[1].rec # best) THEN HomeDelta(S, env, m, best, 1) ELSE S
                c == IF cur = <<>> THEN <<>> ELSE cur[1]
                \* the arm for a known member whose best record is not of a newer epoch
                known == cur # <<>> /\ Le(Epoch(best.inc), Epoch(c.rec.inc))
                upd == known /\ Epoch(best.inc) = Epoch(c.rec.inc) /\ Ge(best.inc, c.rec.inc)
                sA == IF ~upd THEN [S |-> s1, ch |-> FALSE]
                      ELSE LET e1 == [s1.members[m] EXCEPT !.rec.inc = best.inc]
                               verCh == best.ver # c.rec.ver
                               e2 == IF verCh THEN [e1 EXCEPT !.rec.ver = best.ver] ELSE e1
                               sa1 == IF verCh THEN Emit(s1, EvStack(m, best.ver)) ELSE s1
                               thCh == best.th # c.rec.th
                               e3 == IF thCh THEN [e2 EXCEPT !.rec.th = best.th] ELSE e2
                               sa2 == IF thCh THEN Emit(sa1, EvAddr(m)) ELSE sa1
                           IN [S |-> [sa2 EXCEPT !.members = Put(@, m, e3)], ch |-> verCh \/ thCh]
                \* the arm for a new member, or one reincarnated in a newer epoch
                full == cur = <<>> /\ Cardinality(DOMAIN s1.members) >= MAX_TABLE
                sB == LET sb1 == Emit([s1 EXCEPT !.members = Put(@, m, [rec |-> best])], EvJoined(m))
                          old == IF cur # <<>> THEN <<<<c.rec.ver, c.rec.th>>>> ELSE Lookup(s1.goneVer, m)
                          sb2 == [sb1 EXCEPT !.goneVer = IF m \in DOMAIN @ THEN Del(@, m) ELSE @]
                          sb3 == IF old # <<>> /\ old[1][1] # best.ver THEN Emit(sb2, EvStack(m, best.ver)) ELSE sb2
                          sb4 == IF old # <<>> /\ cur = <<>> /\ old[1][2] # best.th THEN Emit(sb3, EvAddr(m)) ELSE sb3
                      IN [S |-> sb4, ch |-> TRUE]
                r == IF known THEN sA ELSE sB
            IN IF ~known /\ full THEN [S |-> s1, ch |-> FALSE] ELSE r

ApplyDelta(S, env, now, hub, e) ==
    IF e.m = S.me THEN OnSelfEntry(S, env, now, hub, e.rec, e.a)
    ELSE IF e.m \in S.revoked THEN S
    ELSE IF hub \notin DOMAIN S.hv /\ Cardinality(DOMAIN S.hv) >= MAX_HUBS THEN S
    ELSE LET s0 == IF hub \in DOMAIN S.hv THEN S ELSE [S EXCEPT !.hv = Put(@, hub, NewCopy)]
             c == s0.hv[hub]
             alive == e.a = 1
             insOK == alive /\ (Cardinality(DOMAIN c.entries) < MAX_TABLE \/ e.m \in DOMAIN c.entries)
             delOK == ~alive /\ e.m \in DOMAIN c.entries /\ Le(Epoch(c.entries[e.m].rec.inc), Epoch(e.rec.inc))
             c1 == IF insOK THEN [c EXCEPT !.entries = Put(@, e.m, [rec |-> e.rec, round |-> c.round, absentSince |-> <<>>])]
                   ELSE IF delOK THEN [c EXCEPT !.entries = Del(@, e.m)] ELSE c
             s1 == [s0 EXCEPT !.hv[hub] = c1,
                              !.left = IF insOK THEN @ \ {e.m}
                                       ELSE IF delOK /\ e.a = 2 /\ Cardinality(@) < MAX_TABLE THEN @ \cup {e.m} ELSE @]
             r == RecomputeOne(s1, env, now, e.m)
         IN IF r.ch THEN Bump(r.S) ELSE r.S

PushDelta(S, env, now, m, rec, alive) ==
    LET RECURSIVE Loop(_, _)
        Loop(s, cur) ==
            LET p == NextKey(S.attached, cur)
            IN IF p = NONE THEN s
               ELSE IF p # m /\ (IsBoot(S, p) \/ (m = S.me /\ p \in S.homed))
                    THEN Loop(DeltaTo(s, env, p, m, rec, alive), p)
                    ELSE Loop(s, p)
        s1 == Loop(S, NONE)
    IN ApplyDelta(s1, env, now, S.me, [m |-> m, rec |-> rec, a |-> alive])

ApplyDown(S, env, now, hub, member, inc) ==
    ApplyDelta(S, env, now, hub, [m |-> member, rec |-> [inc |-> inc, ver |-> 0, th |-> <<0, 0, 0, 0, 0, 0, 0, 0>>], a |-> 0])

(* ---- hub.rs: snapshots and the replay floor ---- *)
RECURSIVE Ordered(_, _)
Ordered(dom, cur) == LET k == NextKey(dom, cur) IN IF k = NONE THEN <<>> ELSE <<k>> \o Ordered(dom, k)

SnapEntries(S, peer) ==
    LET toHub == IsBoot(S, peer)
        ks == Ordered(IF toHub THEN DOMAIN S.roster ELSE DOMAIN S.members, NONE)
        own == [m |-> S.me, rec |-> S.own]
        es == [i \in 1..Len(ks) |-> [m |-> ks[i], rec |-> IF toHub THEN S.roster[ks[i]].rec ELSE S.members[ks[i]].rec]] \o <<own>>
    IN SelectSeq(es, LAMBDA e : e.m # peer)

RECURSIVE SendChunks(_, _, _, _, _)
SendChunks(S, env, peer, partial, es) ==
    IF Len(es) > SNAP_CHUNK
    THEN SendChunks(SendS(S, env, peer, RSession, [k |-> "snap", partial |-> partial, more |-> TRUE, es |-> SubSeq(es, 1, SNAP_CHUNK)]),
                    env, peer, partial, SubSeq(es, SNAP_CHUNK + 1, Len(es)))
    ELSE SendS(S, env, peer, RSession, [k |-> "snap", partial |-> partial, more |-> FALSE, es |-> es])

SendSnapshot(S, env, now, peer) ==
    SendChunks(S, env, peer, Lt(SatSub(now, S.born), LEASE), SnapEntries(S, peer))

SendFloor(S, env, peer) ==
    LET body == env.floor[peer]
        n == IF Len(body) < FLOOR_MAX THEN Len(body) ELSE FLOOR_MAX
    IN IF n = 0 THEN S
       ELSE SendS(S, env, peer, RSession, [k |-> "other", ty |-> 14, topic |-> <<>>, rest |-> SubSeq(body, 1, n)])

(* ---- hub.rs: a HELLO ---- *)
OnHello(S, env, now, peer, hello) ==
    LET s1 == IF hello.homed /\ ~IsBoot(S, peer)
              THEN (IF Cardinality(S.homed) < MAX_TABLE THEN [S EXCEPT !.homed = @ \cup {peer}] ELSE S)
              ELSE [S EXCEPT !.homed = @ \ {peer}]
        s2 == IF peer \in DOMAIN s1.downed THEN Bc([s1 EXCEPT !.downed = Del(@, peer)], [k |-> "restore", m |-> peer]) ELSE s1
        newAttach == peer \notin s2.attached
        s3 == IF newAttach /\ Cardinality(s2.attached) < MAX_TABLE THEN [s2 EXCEPT !.attached = @ \cup {peer}] ELSE s2
        s4 == IF newAttach THEN SendFloor(Trace(s3, [k |-> "attached", member |-> peer]), env, peer) ELSE s3
        s5 == IF hello.snap \/ newAttach THEN SendSnapshot(s4, env, now, peer)
              ELSE SendS(s4, env, peer, RSession, [k |-> "ack"])
        held == Lookup(s5.roster, peer)
    IN IF held # <<>> /\ Lt(hello.rec.inc, held[1].rec.inc)
       THEN DeltaTo([s5 EXCEPT !.roster[peer].renewed = now], env, peer, peer, held[1].rec, 1)
       ELSE IF held # <<>> /\ held[1].rec = hello.rec
       THEN [s5 EXCEPT !.roster[peer].renewed = now]
       ELSE IF held = <<>> /\ Cardinality(DOMAIN s5.roster) >= MAX_TABLE THEN s5
       ELSE PushDelta([s5 EXCEPT !.roster = Put(@, peer, [rec |-> hello.rec, renewed |-> now])], env, now, peer, hello.rec, 1)

(* ---- hub.rs: dropping a lease, DOWN ---- *)
\* cause: [c |-> "conf", proof |-> p], [c |-> "remote"], [c |-> "left"]
HubDown(S, env, now, member, cause) ==
    IF member \notin DOMAIN S.roster THEN S
    ELSE LET lease == S.roster[member]
             s1 == [S EXCEPT !.roster = Del(@, member), !.susp = IF member \in DOMAIN @ THEN Del(@, member) ELSE @,
                              !.attached = @ \ {member}]
             left == cause.c = "left"
             s2 == Bc(s1, IF left THEN [k |-> "release", m |-> member] ELSE [k |-> "hold", m |-> member])
             s3 == PushDelta(s2, env, now, member, lease.rec, IF left THEN 2 ELSE 0)
             s4 == IF ~left /\ (Cardinality(DOMAIN s3.downed) < MAX_TABLE \/ member \in DOMAIN s3.downed)
                   THEN [s3 EXCEPT !.downed = Put(@, member, <<lease, now>>)] ELSE s3
             RECURSIVE Downs(_, _)
             Downs(s, i) ==
                 IF i > Len(s.boot) THEN s
                 ELSE LET hub == s.boot[i] IN
                      IF hub = s.me THEN Downs(s, i + 1)
                      ELSE LET f == [k |-> "down", m |-> member, inc |-> lease.rec.inc, sil |-> cause.proof.sil, pr |-> cause.proof.pr]
                               t == Tx(s, env, hub, RSession, f)
                           IN Downs(IF t.ok THEN Trace(t.S, [k |-> "down_sent", member |-> member]) ELSE t.S, i + 1)
         IN IF cause.c = "conf" THEN Downs(Trace(s4, [k |-> "confirmed", member |-> member]), 1) ELSE s4

IndependentPaths(proof) == \E i, j \in 1..Len(proof.pr) : proof.pr[i].path # proof.pr[j].path

OldestAge(proof) == IF proof.pr = <<>> THEN Z ELSE LET ages == {proof.pr[i].age : i \in 1..Len(proof.pr)}
                                                   IN CHOOSE a \in ages : \A b \in ages : Le(b, a)

OnDown(S, env, now, d) ==
    LET m == d.m
        refuse(why) == Trace(S, [k |-> "down_refused", member |-> m, why |-> why])
        l == Lookup(S.roster, m)
        oldest == OldestAge(d)
        ev == Evidence(env, m)
        renewed == IF l = <<>> THEN Z ELSE IF ev # <<>> THEN Max2(l[1].renewed, ev[1].rx) ELSE l[1].renewed
        window == Max2(N!FromMs(oldest), RENEW)
    IN IF IsBoot(S, m) THEN refuse(0)
       ELSE IF l = <<>> THEN refuse(1)
       ELSE IF Epoch(l[1].rec.inc) # Epoch(d.inc) THEN refuse(1)
       ELSE IF ~IndependentPaths(d) THEN refuse(4)
       ELSE IF Lt(d.sil, oldest) THEN refuse(5)
       ELSE IF CarrierOf(env, m).k = "open" THEN refuse(3)
       ELSE LET s1 == [S EXCEPT !.roster[m].renewed = renewed]
            IN IF Le(SatSub(now, renewed), window) THEN Trace(s1, [k |-> "down_refused", member |-> m, why |-> 2])
               ELSE HubDown(Trace(s1, [k |-> "down_accepted", member |-> m]), env, now, m, [c |-> "remote"])

(* ---- hub.rs: carrier events ---- *)
IndependentRoute(S, now, m, ev) ==
    IF ev # <<>> /\ ev[1].direct THEN <<[route |-> RDirect, path |-> 1]>>
    ELSE LET F == SelectSeq(S.boot, LAMBDA x : x # S.me /\ x # m /\ HubUp(S, now, x))
         IN IF F = <<>> THEN <<>> ELSE <<[route |-> RVia(F[1]), path |-> 2]>>

ScheduleConfirm(S, now, at) ==
    LET at1 == Max2(at, U!Add64(now, One))
    IN [S EXCEPT !.nextConf = <<IF S.nextConf = <<>> THEN at1 ELSE Min2(S.nextConf[1], at1)>>]

Confirm(S, env, now, m, sp, l) ==
    LET p0 == [age |-> N!Ms(SatSub(now, sp.probeA)), path |-> 0]
        pr == IF sp.probeB = <<>> THEN <<p0>>
              ELSE <<p0, [age |-> N!Ms(SatSub(now, sp.probeB[1].t)), path |-> sp.probeB[1].path]>>
    IN HubDown(S, env, now, m, [c |-> "conf", proof |-> [sil |-> N!Ms(SatSub(now, l.renewed)), pr |-> pr]])

CarrierWatch(S, env, now, m) ==
    LET l == Lookup(S.roster, m)
        car == CarrierOf(env, m)
        rmSusp == [S EXCEPT !.susp = IF m \in DOMAIN @ THEN Del(@, m) ELSE @]
    IN IF l = <<>> \/ car.k # "gone" THEN rmSusp
       ELSE LET lease == l[1]
                since == car.since
                ev == Evidence(env, m)
                heard == ev # <<>> /\ Ge(ev[1].rx, since)
            IN IF Ge(lease.renewed, since) \/ heard \/ (car.sleep # <<>> /\ Ge(SatAdd(car.sleep[1], SLEEP_WIN), since))
               THEN IF heard THEN [rmSusp EXCEPT !.roster[m].renewed = Max2(@, ev[1].rx)] ELSE rmSusp
               ELSE LET sp0 == Lookup(S.susp, m)
                    IN IF sp0 # <<>> /\ sp0[1].since = since
                       THEN LET spo == sp0[1]
                                \* the watch runs again when the first probe's wait ends; a suspicion is not reported
                                sp == spo
                                at == U!Add64(spo.probeA, spo.wait)
                                sA == IF Lt(now, at) THEN ScheduleConfirm(S, now, at) ELSE S
                                rt == IndependentRoute(S, now, m, ev)
                                needB == sp.probeB = <<>> /\ rt # <<>>
                                s1 == IF needB
                                      THEN LET t1 == SendS(sA, env, m, rt[1].route, [k |-> "probe"])
                                               t2 == Trace(t1, [k |-> "probe_sent", member |-> m, path |-> rt[1].path])
                                           IN [t2 EXCEPT !.susp = Put(@, m, [sp EXCEPT !.probeB = <<[t |-> now, path |-> rt[1].path]>>])]
                                      ELSE sA
                                spB == IF needB THEN [sp EXCEPT !.probeB = <<[t |-> now, path |-> rt[1].path]>>] ELSE sp
                            IN IF spB.probeB = <<>> THEN s1
                               ELSE LET tb == spB.probeB[1].t
                                        dl == Max2(Max2(U!Add64(spB.since, CONFIRM), U!Add64(spB.probeA, spB.wait)), U!Add64(tb, spB.wait))
                                    IN IF Ge(now, dl) THEN Confirm(s1, env, now, m, spB, lease) ELSE ScheduleConfirm(s1, now, dl)
                       ELSE IF Cardinality(DOMAIN S.susp) >= MAX_TABLE THEN S
                       ELSE LET wait == Max2(PROBE_WAIT_MIN, IF ev = <<>> THEN Z ELSE SatMul3(ev[1].srtt))
                                t1 == SendS(S, env, m, RSession, [k |-> "probe"])
                                t2 == Trace(t1, [k |-> "probe_sent", member |-> m, path |-> 0])
                                rt == IndependentRoute(S, now, m, ev)
                                t4 == IF rt = <<>> THEN t2
                                      ELSE Trace(SendS(t2, env, m, rt[1].route, [k |-> "probe"]), [k |-> "probe_sent", member |-> m, path |-> rt[1].path])
                                pB == IF rt = <<>> THEN <<>> ELSE <<[t |-> now, path |-> rt[1].path]>>
                                sp == [since |-> since, probeA |-> now, probeB |-> pB, wait |-> wait]
                                t5 == [t4 EXCEPT !.susp = Put(@, m, sp)]
                                t6 == ScheduleConfirm(t5, now, U!Add64(now, wait))
                            IN IF pB # <<>>
                               THEN ScheduleConfirm(t6, now, Max2(Max2(U!Add64(since, CONFIRM), U!Add64(now, wait)), U!Add64(now, wait)))
                               ELSE Trace(t6, [k |-> "no_independent_path", member |-> m])

CarrierGone(S, env, now, member) ==
    IF S.isHub /\ ~IsBoot(S, member)
    THEN CarrierWatch(Trace(S, [k |-> "carrier_gone", member |-> member]), env, now, member)
    ELSE S

CarrierReturn(S, env, now, member) ==
    IF member \notin DOMAIN S.downed
    THEN Trace(S, [k |-> "carrier_returned", member |-> member, restored |-> FALSE])
    ELSE LET l0 == S.downed[member][1]
             s1 == [S EXCEPT !.downed = Del(@, member)]
         IN IF member \in DOMAIN s1.roster \/ member \in s1.revoked THEN s1
            ELSE IF Cardinality(DOMAIN s1.roster) >= MAX_TABLE
            THEN Trace(Bc(s1, [k |-> "release", m |-> member]), [k |-> "carrier_returned", member |-> member, restored |-> FALSE])
            ELSE LET l == [l0 EXCEPT !.renewed = now]
                     s2 == [s1 EXCEPT !.roster = Put(@, member, l)]
                     s3 == IF member \in DOMAIN s2.up /\ Cardinality(s2.attached) < MAX_TABLE
                           THEN [s2 EXCEPT !.attached = @ \cup {member}] ELSE s2
                     s4 == Bc(s3, [k |-> "restore", m |-> member])
                     s5 == PushDelta(s4, env, now, member, l.rec, 1)
                     s6 == DeltaTo(s5, env, member, member, l.rec, 1)
                 IN Trace(s6, [k |-> "carrier_returned", member |-> member, restored |-> TRUE])

(* ---- hub.rs: the once-a-tick hub work ---- *)
RECURSIVE RosterTick(_, _, _, _)
RosterTick(S, env, now, cur) ==
    LET m == NextKey(DOMAIN S.roster, cur)
    IN IF m = NONE THEN S
       ELSE LET l0 == S.roster[m]
                ev == Evidence(env, m)
                pulse == Gt(SatSub(now, l0.renewed), RENEW) /\ ev # <<>> /\ Gt(ev[1].rx, l0.renewed)
                l == IF pulse THEN [l0 EXCEPT !.renewed = ev[1].rx] ELSE l0
                s1 == IF pulse THEN Trace([S EXCEPT !.roster[m].renewed = ev[1].rx], [k |-> "pulse", member |-> m]) ELSE S
                s2 == IF Gt(SatSub(now, l.renewed), LEASE)
                      THEN LET a == [s1 EXCEPT !.roster = Del(@, m), !.susp = IF m \in DOMAIN @ THEN Del(@, m) ELSE @]
                               b == Trace(a, [k |-> "lease_expired", member |-> m])
                               c == PushDelta(b, env, now, m, l.rec, 0)
                           IN Bc(c, [k |-> "release", m |-> m])
                      ELSE IF ~IsBoot(s1, m) THEN CarrierWatch(s1, env, now, m) ELSE s1
            IN RosterTick(s2, env, now, m)

RECURSIVE DownedTick(_, _, _, _)
DownedTick(S, env, now, cur) ==
    LET m == NextKey(DOMAIN S.downed, cur)
    IN IF m = NONE THEN S
       ELSE LET t0 == S.downed[m][2]
                s1 == IF Gt(SatSub(now, t0), LEASE) \/ m \in DOMAIN S.roster \/ m \in S.revoked
                      THEN Bc([S EXCEPT !.downed = Del(@, m)], [k |-> "release", m |-> m])
                      ELSE IF CarrierOf(env, m).k = "open" THEN CarrierReturn(S, env, now, m) ELSE S
            IN DownedTick(s1, env, now, m)

HubTick(S, env, now) == DownedTick(RosterTick(S, env, now, NONE), env, now, NONE)

(* ---- view.rs: snapshots, absence, the sweep, the recheck ---- *)
RECURSIVE SnapLoop(_, _, _, _, _, _, _, _)
SnapLoop(S, env, now, hub, round, es, i, ch) ==
    IF i > Len(es) THEN [S |-> S, ch |-> ch]
    ELSE LET e == es[i] IN
         IF e.m = S.me THEN SnapLoop(OnSelfEntry(S, env, now, hub, e.rec, 1), env, now, hub, round, es, i + 1, ch)
         ELSE IF e.m \in S.revoked THEN SnapLoop(S, env, now, hub, round, es, i + 1, ch)
         ELSE IF Cardinality(DOMAIN S.hv[hub].entries) >= MAX_TABLE /\ e.m \notin DOMAIN S.hv[hub].entries
              THEN SnapLoop(S, env, now, hub, round, es, i + 1, ch)
              ELSE LET s1 == [S EXCEPT !.hv[hub].entries = Put(@, e.m, [rec |-> e.rec, round |-> round, absentSince |-> <<>>]),
                                       !.left = @ \ {e.m}]
                       r == RecomputeOne(s1, env, now, e.m)
                   IN SnapLoop(r.S, env, now, hub, round, es, i + 1, ch \/ r.ch)

\* a complete snapshot of hub listed round `round`: an earlier entry of a member the view does not list is dropped from
\* the copy (view.rs drop_gone)
DropGone(S, hub, round) ==
    IF hub \notin DOMAIN S.hv THEN S
    ELSE LET es == S.hv[hub].entries
         IN [S EXCEPT !.hv[hub].entries =
                [m \in {k \in DOMAIN es : es[k].round = round \/ k \in DOMAIN S.members} |-> es[m]]]

\* a complete snapshot of hub listed round `round`: everything else in its copy is absent, which starts that member's
\* lease clock without removing it
RECURSIVE MarkAbsent(_, _, _, _, _, _, _)
MarkAbsent(S, env, now, hub, round, cur, ch) ==
    LET m == IF hub \in DOMAIN S.hv THEN NextKey(DOMAIN S.hv[hub].entries, cur) ELSE NONE
    IN IF m = NONE THEN [S |-> S, ch |-> ch]
       ELSE LET ce == S.hv[hub].entries[m]
                marked == ce.round # round /\ ce.absentSince = <<>>
            IN IF ~marked THEN MarkAbsent(S, env, now, hub, round, m, ch)
               ELSE LET s1 == Trace([S EXCEPT !.hv[hub].entries[m].absentSince = <<now>>], [k |-> "absent", member |-> m])
                        r == RecomputeOne(s1, env, now, m)
                    IN MarkAbsent(r.S, env, now, hub, round, m, ch \/ r.ch)

\* the round one before `round`, wrapping in 32 bits (the code's round.wrapping_sub(1))
RoundBefore(round) == U!Low(U!Sub(U!Add(round, U!Pw(32)), One), 32)

\* a complete snapshot of the confirmed home listed round `round`: it is the whole view, so every view member the home's
\* copy does not hold, whichever hub's copy listed it, gets an entry there carrying the view's record, one round before
\* `round`, with the omission clock started; with the copy full there is no room and the member is recomputed at once
\* (view.rs mark_view_absent)
RECURSIVE MarkViewAbsent(_, _, _, _, _, _, _)
MarkViewAbsent(S, env, now, hub, round, cur, ch) ==
    LET m == NextKey(DOMAIN S.members, cur)
    IN IF m = NONE \/ hub \notin DOMAIN S.hv THEN [S |-> S, ch |-> ch]
       ELSE IF m \in DOMAIN S.hv[hub].entries THEN MarkViewAbsent(S, env, now, hub, round, m, ch)
       ELSE IF Cardinality(DOMAIN S.hv[hub].entries) >= MAX_TABLE
            THEN LET r == RecomputeOne(S, env, now, m) IN MarkViewAbsent(r.S, env, now, hub, round, m, ch \/ r.ch)
       ELSE LET s1 == Trace([S EXCEPT !.hv[hub].entries = Put(@, m, [rec |-> S.members[m].rec, round |-> RoundBefore(round),
                                                                      absentSince |-> <<now>>])],
                            [k |-> "absent", member |-> m])
                r == RecomputeOne(s1, env, now, m)
            IN MarkViewAbsent(r.S, env, now, hub, round, m, ch \/ r.ch)

\* ViewAbsent is the rule of the code (mark_view_absent, after mark_absent); a witness config overrides it with
\* OldViewAbsent, the rule before #343, under which a view member that only another hub's copy listed is never looked
\* at again
ViewAbsent(S, env, now, hub, round, ch) ==
    IF ~S.isHub /\ S.primary = <<hub>> THEN MarkViewAbsent(S, env, now, hub, round, NONE, ch) ELSE [S |-> S, ch |-> ch]
OldViewAbsent(S, env, now, hub, round, ch) == [S |-> S, ch |-> ch]

ApplySnap(S, env, now, hub, sn) ==
    IF hub \notin DOMAIN S.hv /\ Cardinality(DOMAIN S.hv) >= MAX_HUBS THEN S
    ELSE LET s0 == IF hub \in DOMAIN S.hv THEN S ELSE [S EXCEPT !.hv = Put(@, hub, NewCopy)]
             c == s0.hv[hub]
             round == IF c.open THEN c.round ELSE U!Low(U!Add(c.round, One), 32)
             s1 == [s0 EXCEPT !.hv[hub].round = round, !.hv[hub].open = TRUE]
             s2 == IF ~s1.isHub /\ s1.primary = <<hub>> THEN [s1 EXCEPT !.homeOk = <<hub>>, !.homeSeen = TRUE] ELSE s1
             r == SnapLoop(s2, env, now, hub, round, sn.es, 1, FALSE)
             s3 == Trace(r.S, [k |-> "snap_applied", hub |-> hub, entries |-> Len(sn.es), more |-> sn.more])
         IN IF sn.more THEN (IF r.ch THEN Bump(s3) ELSE s3)
            ELSE LET s4 == IF hub \in DOMAIN s3.hv THEN [s3 EXCEPT !.hv[hub].open = FALSE] ELSE s3
                     m == IF ~sn.partial
                          THEN LET a == MarkAbsent(DropGone(s4, hub, round), env, now, hub, round, NONE, r.ch)
                               IN ViewAbsent(a.S, env, now, hub, round, a.ch)
                          ELSE [S |-> s4, ch |-> r.ch]
                     s5 == IF m.S.primary = <<hub>> THEN Bc(m.S, [k |-> "resub", hub |-> hub]) ELSE m.S
                 IN IF m.ch THEN Bump(s5) ELSE s5

RECURSIVE SweepEntries(_, _, _, _, _, _)
SweepEntries(S, env, now, hub, cur, ch) ==
    LET m == IF hub \in DOMAIN S.hv THEN NextKey(DOMAIN S.hv[hub].entries, cur) ELSE NONE
    IN IF m = NONE THEN [S |-> S, ch |-> ch]
       ELSE LET ce == S.hv[hub].entries[m]
                expired == ce.absentSince # <<>> /\ Ge(SatSub(now, ce.absentSince[1]), LEASE)
            IN IF ~expired THEN SweepEntries(S, env, now, hub, m, ch)
               ELSE LET r == RecomputeOne(S, env, now, m)
                        s1 == IF hub \in DOMAIN r.S.hv THEN [r.S EXCEPT !.hv[hub].entries = Del(@, m)] ELSE r.S
                    IN SweepEntries(s1, env, now, hub, m, ch \/ r.ch)

RECURSIVE SweepHubs(_, _, _, _, _)
SweepHubs(S, env, now, hcur, ch) ==
    LET hub == NextKey(DOMAIN S.hv, hcur)
    IN IF hub = NONE THEN [S |-> S, ch |-> ch]
       ELSE LET r == SweepEntries(S, env, now, hub, NONE, ch) IN SweepHubs(r.S, env, now, hub, r.ch)

SweepAbsent(S, env, now) == LET r == SweepHubs(S, env, now, NONE, FALSE) IN IF r.ch THEN Bump(r.S) ELSE r.S

RECURSIVE RecheckLoop(_, _, _, _, _, _)
RecheckLoop(S, env, now, set, cur, ch) ==
    LET m == NextKey(set, cur)
    IN IF m = NONE THEN [S |-> S, ch |-> ch]
       ELSE LET r == RecomputeOne(S, env, now, m) IN RecheckLoop(r.S, env, now, set, m, ch \/ r.ch)

\* recheck_due (#284): an entry is due once its instant has come. A due entry whose extra look has not begun gets it
\* (RECHECK_GAP from now, and the window lasts at least that long); the due entries whose extra look ran leave the
\* table and are recomputed in key order with no window open (a removal a window already deferred is believed now,
\* whatever window a heal has opened since), and the window is restored after.
RecheckDue(S, env, now) ==
    LET due == {m \in DOMAIN S.recheck : Le(S.recheck[m].due, now)}
        ready == {m \in due : S.recheck[m].grace}
        look == due \ ready
        s1 == [S EXCEPT !.recheck = [m \in DOMAIN S.recheck \ ready |->
                                       IF m \in look THEN [due |-> SatAdd(now, RECHECK_GAP), grace |-> TRUE]
                                       ELSE S.recheck[m]]]
        s2 == IF look # {} THEN [s1 EXCEPT !.regrace = TRUE, !.quietUntil = Max2(@, SatAdd(now, RECHECK_GAP))] ELSE s1
    IN IF ready = {} THEN s2
       ELSE LET r == RecheckLoop([s2 EXCEPT !.regrace = FALSE, !.quietUntil = Z], env, now, ready, NONE, FALSE)
                s3 == [r.S EXCEPT !.quietUntil = s2.quietUntil]
            IN IF r.ch THEN Bump(s3) ELSE s3
=============================================================================
