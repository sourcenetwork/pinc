---------------------------- MODULE MembershipOps ---------------------------
(***************************************************************************)
(* The calls into a membership machine: start and the session events      *)
(* (node.rs), the timers (timers.rs) and the dispatch of frames (input.rs), *)
(* on top of the view and hub operators of Membership.tla.                  *)
(*                                                                         *)
(* A call is one of the operators Call* below: it sets the host's store     *)
(* from the env, runs the operator of the Rust function of the same name    *)
(* and drains the output queues. The trace check and the system models     *)
(* apply exactly these operators.                                           *)
(*                                                                         *)
(* Lean counterpart: Vinc/MembershipModel*.lean.                            *)
(***************************************************************************)
EXTENDS Membership

LEAVE_CODE == <<76, 0, 0, 0, 0>>

SatMulK(a, k) == LET p == N!MulAt(a, k, 1, 0) IN IF U!Fits(p) THEN p ELSE U!Max64

(* ---- node.rs: start ---- *)
Dedup(hubs) ==
    LET RECURSIVE D(_, _)
        D(i, acc) == IF i > Len(hubs) THEN acc
                     ELSE IF \E j \in 1..Len(acc) : acc[j] = hubs[i] THEN D(i + 1, acc) ELSE D(i + 1, Append(acc, hubs[i]))
    IN D(1, <<>>)

\* returns [err, S]; err is "ok", "toomany", "nohubs", "store" or "exhausted"; a failed start has no state
StartOp(cfg, env, now, wall, floor) ==
    LET b0 == Dedup(cfg.hubs)
        boot == IF cfg.isHub /\ ~(\E j \in 1..Len(b0) : b0[j] = cfg.me) THEN Append(b0, cfg.me) ELSE b0
        r == INC!StartOp(LocalOf(env), wall, floor)
        t == INC!TagOp(INC!TagInit, now, env.refl, env.tk)
        rec0 == [inc |-> INC!Word(r.inc), ver |-> env.ver, th |-> t.tag]
        S0 == [me |-> cfg.me, isHub |-> cfg.isHub, boot |-> boot, born |-> now, leaving |-> FALSE, inc |-> r.inc,
               tag |-> t.t, ver |-> env.ver, th |-> t.tag, sentRec |-> <<>>, sealFailed |-> FALSE, maxFrame |-> MAX_BODY,
               up |-> EmptyFn, heard |-> EmptyFn, revoked |-> {},
               hv |-> IF cfg.isHub THEN [x \in {cfg.me} |-> NewCopy] ELSE EmptyFn,
               members |-> EmptyFn, epoch |-> Z, hrtt |-> EmptyFn, hsent |-> EmptyFn, helloAt |-> EmptyFn,
               primary |-> IF cfg.isHub THEN <<cfg.me>> ELSE <<>>, homeOk |-> <<>>, homeSeen |-> FALSE,
               recheck |-> {}, quietUntil |-> Z, regrace |-> FALSE, goneVer |-> EmptyFn, left |-> {},
               nextRenew |-> now, nextTick |-> <<>>, nextSlow |-> now,
               own |-> rec0, roster |-> EmptyFn, attached |-> {}, homed |-> {}, susp |-> EmptyFn, downed |-> EmptyFn,
               nextConf |-> <<>>, tracing |-> TRUE, loc |-> r.loc,
               sent |-> <<>>, bc |-> <<>>, cl |-> <<>>, ev |-> <<>>, tr |-> <<>>, lostE |-> 0, lostT |-> 0]
    IN IF Len(boot) > MAX_HUBS THEN [err |-> "toomany"]
       ELSE IF ~cfg.isHub /\ boot = <<>> THEN [err |-> "nohubs"]
       ELSE IF r.err # "ok" THEN [err |-> r.err]
       ELSE [err |-> "ok", S |-> Drain(Trace(S0, [k |-> "started", inc |-> INC!Word(r.inc)]))]

(* ---- node.rs: sessions, leave, revoke, address ---- *)
DropPeer(S, env, now, peer) ==
    LET s1 == [S EXCEPT !.up = IF peer \in DOMAIN @ THEN Del(@, peer) ELSE @,
                        !.attached = @ \ {peer}, !.homed = @ \ {peer},
                        !.helloAt = Unset(@, peer), !.hsent = Unset(@, peer)]
        s2 == IF ~s1.isHub /\ s1.homeOk = <<peer>> THEN [s1 EXCEPT !.homeOk = <<>>] ELSE s1
        s3 == IF peer \notin DOMAIN s2.downed THEN Bc(s2, [k |-> "release", m |-> peer]) ELSE s2
    IN IF IsBoot(s3, peer) /\ s3.primary = <<peer>> THEN Reselect(s3, env, now) ELSE s3

SessionUp(S, env, now, peer, incoming) ==
    IF peer = S.me THEN S
    ELSE IF peer \in S.revoked THEN Close(S, peer, "revoked")
    ELSE LET silent == peer \in DOMAIN S.heard /\ Gt(SatSub(now, S.heard[peer]), GiveUp(env, peer))
             s1 == IF ~S.isHub /\ IsBoot(S, peer) /\ silent THEN BeginQuiet(S, now, 1) ELSE S
         IN IF Cardinality(DOMAIN s1.up) >= MAX_TABLE /\ peer \notin DOMAIN s1.up THEN Close(s1, peer, "stale")
            ELSE LET s2 == [s1 EXCEPT !.up = Put(@, peer, now), !.attached = IF incoming THEN @ \ {peer} ELSE @]
                 IN IF IsBoot(s2, peer) /\ (~incoming \/ s2.isHub)
                    THEN LET s3 == IF ~s2.isHub /\ s2.primary = <<peer>> THEN Bc(s2, [k |-> "resub", hub |-> peer]) ELSE s2
                         IN HelloTo(s3, env, peer, TRUE)
                    ELSE s2

SessionDown(S, env, now, peer, code) ==
    IF peer \notin DOMAIN S.up THEN S
    ELSE LET s1 == [S EXCEPT !.up = Del(@, peer)]
             s2 == IF s1.isHub /\ code = LEAVE_CODE /\ ~IsBoot(s1, peer)
                   THEN HubDown(Trace(s1, [k |-> "leave_seen", member |-> peer]), env, now, peer, [c |-> "left"])
                   ELSE s1
         IN DropPeer(s2, env, now, peer)

LeaveOp(S) ==
    LET RECURSIVE Loop(_, _)
        Loop(s, cur) == LET p == NextKey(DOMAIN S.up, cur) IN IF p = NONE THEN s ELSE Loop(Close(s, p, "leave"), p)
    IN Loop([S EXCEPT !.leaving = TRUE], NONE)

\* returns [ok, S]
RevokeOp(S, env, now, member) ==
    IF member \notin S.revoked /\ Cardinality(S.revoked) >= MAX_TABLE THEN [ok |-> FALSE, S |-> S]
    ELSE LET s1 == [S EXCEPT !.revoked = @ \cup {member},
                             !.hv = [k \in DOMAIN @ |-> IF member \in DOMAIN @[k].entries
                                                       THEN [@[k] EXCEPT !.entries = Del(@, member)] ELSE @[k]],
                             !.recheck = @ \ {member}, !.left = @ \ {member},
                             !.susp = IF member \in DOMAIN @ THEN Del(@, member) ELSE @,
                             !.downed = IF member \in DOMAIN @ THEN Del(@, member) ELSE @,
                             !.attached = @ \ {member}, !.homed = @ \ {member}]
             e == Lookup(S.members, member)
             s2 == IF e = <<>> THEN s1
                   ELSE LET a == Trace([s1 EXCEPT !.members = Del(@, member),
                                                  !.goneVer = IF member \in DOMAIN @ THEN Del(@, member) ELSE @],
                                       [k |-> "removed", member |-> member, why |-> 3])
                            b == IF a.isHub THEN HomeDelta(a, env, member, e[1].rec, 0) ELSE a
                        IN Bump(b)
             l == Lookup(s2.roster, member)
             s3 == IF l = <<>> THEN s2
                   ELSE PushDelta([s2 EXCEPT !.roster = Del(@, member)], env, now, member, l[1].rec, 0)
             s4 == Bc(s3, [k |-> "release", m |-> member])
             s5 == IF member \in DOMAIN s4.up THEN Close(s4, member, "revoked") ELSE s4
         IN [ok |-> TRUE, S |-> Emit(s5, EvRevoked(member))]

AddressChangedOp(S, now) == [S EXCEPT !.tag = INC!MovedOp(@, now)]

\* hub.rs snapshot_to: a hub sends an attached peer its snapshot again, without a new attachment
SnapshotToOp(S, env, now, peer) == IF S.isHub /\ peer \in S.attached THEN SendSnapshot(S, env, now, peer) ELSE S

\* node.rs set_max_frame: the limit never goes below the default
SetMaxFrameOp(S, mb) == [S EXCEPT !.maxFrame = Max2(mb, MAX_BODY)]

(* ---- input.rs ---- *)
RECURSIVE PulseLoop(_, _, _, _)
PulseLoop(S, env, now, i) ==
    IF i > Len(S.boot) THEN S
    ELSE LET hub == S.boot[i]
         IN IF hub = S.me \/ hub \notin DOMAIN S.up THEN PulseLoop(S, env, now, i + 1)
            ELSE LET t == Lookup(S.heard, hub)
                     ev == Evidence(env, hub)
                 IN IF (t = <<>> \/ Ge(SatSub(now, t[1]), RENEW)) /\ ev # <<>> /\ (t = <<>> \/ Gt(ev[1].rx, t[1]))
                    THEN LET s1 == IF ~S.isHub /\ t # <<>> /\ Gt(SatSub(ev[1].rx, t[1]), GiveUp(env, hub))
                                   THEN BeginQuiet(S, now, 1) ELSE S
                         IN PulseLoop([s1 EXCEPT !.heard = Put(@, hub, ev[1].rx)], env, now, i + 1)
                    ELSE PulseLoop(S, env, now, i + 1)
PulseRefresh(S, env, now) == PulseLoop(S, env, now, 1)

OnFrame(S, env, now, peer, f) ==
    IF peer \in S.revoked \/ S.leaving THEN S
    ELSE LET s0 == PulseRefresh(Trace(S, [k |-> "frame_in", peer |-> peer, ty |-> TyOf(f)]), env, now)
             fromHub == IsBoot(s0, peer)
             silent == peer \in DOMAIN s0.heard /\ Gt(SatSub(now, s0.heard[peer]), GiveUp(env, peer))
             sA == IF fromHub /\ ~s0.isHub /\ silent THEN BeginQuiet(s0, now, 1) ELSE s0
             sB == IF fromHub THEN [sA EXCEPT !.heard = Put(@, peer, now), !.helloAt = Unset(@, peer)]
                   ELSE sA
             isSample == f.k \in {"ack", "snap"}
             t0 == IF fromHub /\ isSample THEN TimeAt(sB.hsent, peer) ELSE <<>>
             sC == IF fromHub /\ isSample THEN [sB EXCEPT !.hsent = Unset(@, peer)] ELSE sB
             sD == IF t0 # <<>> /\ Lt(SatSub(now, t0[1]), RTT_SAMPLE_MAX) THEN RttSample(sC, peer, N!Sub(now, t0[1])) ELSE sC
             switch == t0 # <<>> /\ Lt(SatSub(now, t0[1]), RTT_SAMPLE_MAX) /\ ~sD.isHub /\ sD.primary # <<>> /\ sD.primary[1] # peer
                       /\ HubUp(sD, now, peer)
                       /\ LET cur == Lookup(sD.hrtt, sD.primary[1])
                              new == Get(Lookup(sD.hrtt, peer), U!Max64)
                          IN cur = <<>> \/ Lt(SatAdd(new, HYST_ABS), N!Div(N!Mul(cur[1], 3), 4))
             sE == IF switch THEN Reselect(sD, env, now) ELSE sD
             sF == IF fromHub /\ sE.primary = <<>> THEN Reselect(sE, env, now) ELSE sE
             sG == IF sF.isHub /\ f.k # "hello" /\ peer \in DOMAIN sF.roster THEN [sF EXCEPT !.roster[peer].renewed = now] ELSE sF
         IN CASE f.k = "hello" -> IF sG.isHub THEN OnHello(sG, env, now, peer, f) ELSE sG
              [] f.k = "probe" -> IF fromHub /\ ~sG.isHub THEN HelloTo(sG, env, peer, FALSE) ELSE sG
              [] f.k = "down" -> IF sG.isHub /\ fromHub THEN OnDown(sG, env, now, f)
                                 ELSE IF fromHub THEN ApplyDown(sG, env, now, peer, f.m, f.inc) ELSE sG
              [] f.k = "delta" -> IF fromHub THEN ApplyDelta(sG, env, now, peer, f) ELSE sG
              [] f.k = "snap" -> IF fromHub THEN ApplySnap(sG, env, now, peer, f) ELSE sG
              [] f.k = "ack" -> sG
              [] f.k = "other" -> Bc(sG, [k |-> "frame", from |-> peer, ty |-> f.ty, topic |-> f.topic, rest |-> f.rest])

(* ---- timers.rs ---- *)
\* a stale hub's copy is dropped while another hub is fresh, and its session is closed so a fresh one is made
RECURSIVE StaleLoop(_, _, _, _, _)
StaleLoop(S, env, now, cur, ch) ==
    LET hub == NextKey(DOMAIN S.hv, cur)
    IN IF hub = NONE THEN [S |-> S, ch |-> ch]
       ELSE IF HubUp(S, now, hub) THEN StaleLoop(S, env, now, hub, ch)
       ELSE LET copy == S.hv[hub]
                s1 == Trace([S EXCEPT !.hv = Del(@, hub)], [k |-> "hub_stale", hub |-> hub])
                s2 == IF hub \in DOMAIN s1.up /\ Ge(SatSub(now, Get(Lookup(s1.heard, hub), Z)), HUB_STALE)
                      THEN Close(s1, hub, "stale") ELSE s1
                RECURSIVE Each(_, _, _)
                Each(s, c, k) ==
                    LET m == NextKey(DOMAIN copy.entries, k)
                    IN IF m = NONE THEN [S |-> s, ch |-> c]
                       ELSE LET r == RecomputeOne(s, env, now, m) IN Each(r.S, c \/ r.ch, m)
                e == Each(s2, ch, NONE)
            IN StaleLoop(e.S, env, now, hub, e.ch)

DropStaleHubs(S, env, now) ==
    LET stale == Cardinality({k \in DOMAIN S.hv : ~HubUp(S, now, k)})
    IN IF stale = 0 \/ stale >= Cardinality(DOMAIN S.hv) THEN S
       ELSE LET r == StaleLoop(S, env, now, NONE, FALSE) IN IF r.ch THEN Bump(r.S) ELSE r.S

RECURSIVE SampleLoop(_, _, _, _)
SampleLoop(S, env, now, i) ==
    IF i > Len(S.boot) THEN S
    ELSE LET hub == S.boot[i]
             ev == Evidence(env, hub)
         IN IF hub = S.me THEN SampleLoop(S, env, now, i + 1)
            ELSE IF ev # <<>> /\ hub \in DOMAIN S.up /\ Lt(Z, ev[1].srtt) /\ Lt(SatSub(now, ev[1].rx), PULSE_FRESH)
                    /\ ev[1].inf <= RTT_QUIET
                 THEN SampleLoop(RttSample(S, hub, ev[1].srtt), env, now, i + 1)
                 ELSE SampleLoop(S, env, now, i + 1)

SampleSessionRtts(S, env, now) ==
    LET s1 == SampleLoop(S, env, now, 1)
        cur == IF s1.primary = <<>> THEN <<>> ELSE Lookup(s1.hrtt, s1.primary[1])
        better == \E i \in 1..Len(s1.boot) :
                    LET x == s1.boot[i]
                        r == Lookup(s1.hrtt, x)
                    IN x # s1.me /\ s1.primary # <<x>> /\ HubUp(s1, now, x) /\ r # <<>>
                       /\ (cur = <<>> \/ Lt(SatAdd(r[1], HYST_ABS), N!Div(N!Mul(cur[1], 2), 3)))
    IN IF better THEN Reselect(s1, env, now) ELSE s1

RECURSIVE WatchdogLoop(_, _, _, _)
WatchdogLoop(S, env, now, cur) ==
    LET hub == NextKey(DOMAIN S.helloAt, cur)
    IN IF hub = NONE THEN S
       ELSE IF S.helloAt[hub] = <<>> THEN WatchdogLoop(S, env, now, hub)
       ELSE LET t0 == S.helloAt[hub][1]
                opened == Get(Lookup(S.up, hub), now)
                ev == Evidence(env, hub)
                wt == IF ev = <<>> THEN Z ELSE Max2(ACK_WAIT, SatMulK(ev[1].srtt, 4))
                spared == ev # <<>> /\ (Le(SatSub(now, t0), wt) \/ Lt(SatSub(now, ev[1].rx), N!Div(wt, 2)))
            IN IF Gt(SatSub(now, t0), ACK_WAIT) /\ Gt(SatSub(now, opened), HS_GRACE) /\ ~spared
               THEN LET s1 == [S EXCEPT !.helloAt = Put(@, hub, <<>>)]
                        s2 == IF hub \in DOMAIN s1.up THEN DropPeer(Close(s1, hub, "noack"), env, now, hub) ELSE s1
                    IN WatchdogLoop(s2, env, now, hub)
               ELSE WatchdogLoop(S, env, now, hub)

SlowTick(S, env, now) ==
    LET s1 == WatchdogLoop(S, env, now, NONE)
        s2 == IF ~s1.isHub THEN SampleSessionRtts(s1, env, now) ELSE s1
        s3 == SweepAbsent(DropStaleHubs(s2, env, now), env, now)
        down == s3.primary = <<>> \/ ~HubUp(s3, now, s3.primary[1])
    IN IF down THEN Reselect(s3, env, now) ELSE s3

Tick(S, env, now) ==
    LET s1 == IF S.recheck # {} /\ Ge(now, S.quietUntil)
              THEN (IF S.regrace THEN RecheckNow([S EXCEPT !.regrace = FALSE], env, now)
                    ELSE [S EXCEPT !.regrace = TRUE, !.quietUntil = SatAdd(now, RECHECK_GAP)])
              ELSE S
        s2 == IF s1.sentRec # <<<<s1.ver, s1.th>>>> THEN Renew(s1, env, now, FALSE, FALSE) ELSE s1
        s3 == IF s2.isHub \/ Ge(now, s2.nextSlow)
              THEN SlowTick(IF ~s2.isHub THEN [s2 EXCEPT !.nextSlow = SatAdd(now, SLOW_TICK)] ELSE s2, env, now)
              ELSE s2
    IN IF s3.isHub THEN HubTick(s3, env, now) ELSE s3

RefreshLocal(S, env, now) ==
    LET t == INC!TagOp(S.tag, now, env.refl, env.tk)
    IN [S EXCEPT !.ver = env.ver, !.th = t.tag, !.tag = t.t]

RECURSIVE ConfLoop(_, _, _, _)
ConfLoop(S, env, now, cur) ==
    LET m == NextKey(DOMAIN S.susp, cur)
    IN IF m = NONE THEN S ELSE ConfLoop(CarrierWatch(S, env, now, m), env, now, m)

OnTimeout(S, env, now) ==
    IF S.leaving THEN S
    ELSE LET s1 == RefreshLocal(PulseRefresh(S, env, now), env, now)
             s2 == IF Ge(now, s1.nextRenew) THEN Renew(s1, env, now, FALSE, TRUE) ELSE s1
             s3 == IF s2.nextConf # <<>> /\ Ge(now, s2.nextConf[1])
                   THEN (IF s2.isHub THEN ConfLoop([s2 EXCEPT !.nextConf = <<>>], env, now, NONE) ELSE [s2 EXCEPT !.nextConf = <<>>])
                   ELSE s2
         IN IF Ge(now, Get(s3.nextTick, Z))
            THEN LET s4 == IF ~s3.isHub /\ s3.nextTick # <<>> /\ Gt(SatSub(now, s3.nextTick[1]), WAKE_GAP)
                           THEN Renew(BeginQuiet(s3, now, 0), env, now, TRUE, FALSE) ELSE s3
                     s5 == [s4 EXCEPT !.nextTick = <<SatAdd(now, IF s4.isHub THEN HUB_TICK ELSE NODE_TICK)>>]
                 IN Tick(s5, env, now)
            ELSE s3

PollTimeout(S) ==
    LET t == Min2(S.nextRenew, Get(S.nextTick, S.born))
    IN IF S.nextConf = <<>> THEN t ELSE Min2(t, S.nextConf[1])

(* ---- the calls: the host's store is set from the env, the queues are drained at the end ---- *)
Begin(S, env) == [ClearOut(S) EXCEPT !.loc = LocalOf(env)]
CallUp(S, env, now, peer, incoming) == Drain(SessionUp(Begin(S, env), env, now, peer, incoming))
CallDown(S, env, now, peer, code) == Drain(SessionDown(Begin(S, env), env, now, peer, code))
\* the frames of one on_bytes call, then BadFrame if the next frame failed to parse
CallBytes(S, env, now, peer, fs, bad) ==
    LET RECURSIVE Fold(_, _)
        Fold(s, i) == IF i > Len(fs) THEN s ELSE Fold(OnFrame(s, env, now, peer, fs[i]), i + 1)
        s1 == Fold(Begin(S, env), 1)
    IN Drain(IF bad THEN Trace(s1, [k |-> "bad_frame", peer |-> peer]) ELSE s1)
CallTimeout(S, env, now) == Drain(OnTimeout(Begin(S, env), env, now))
CallCarrierGone(S, env, now, member) == Drain(CarrierGone(Begin(S, env), env, now, member))
CallCarrierReturn(S, env, now, member) == Drain(CarrierReturn(Begin(S, env), env, now, member))
CallLeave(S, env) == Drain(LeaveOp(Begin(S, env)))
CallRevoke(S, env, now, member) ==
    LET r == RevokeOp(Begin(S, env), env, now, member) IN [ok |-> r.ok, S |-> Drain(r.S)]
CallMoved(S, env, now) == Drain(AddressChangedOp(Begin(S, env), now))
CallSnapshotTo(S, env, now, peer) == Drain(SnapshotToOp(Begin(S, env), env, now, peer))
CallSetMaxFrame(S, env, mb) == Drain(SetMaxFrameOp(Begin(S, env), mb))
CallStart(cfg, env, now, wall, floor) == StartOp(cfg, env, now, wall, floor)
=============================================================================
