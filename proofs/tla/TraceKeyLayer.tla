----------------------------- MODULE TraceKeyLayer -----------------------------
(***************************************************************************)
(* Trace validation of the flip and hold layer of the key roll:            *)
(* pinc-transport conn/keys.rs (RecvKeys, Keys), the sending and receiving *)
(* paths of conn/send.rs and conn/recv.rs that call it, and keyroll.rs     *)
(* (Roll) under it.                                                        *)
(*                                                                         *)
(* The Rust test tests/trace_keylayer.rs connects a client and a server of *)
(* pinc-transport (built with the cargo feature `trace`) and drives them   *)
(* datagram by datagram through seeded schedules: data written so that     *)
(* rolls become due, packets built, any datagram of the pool delivered any *)
(* number of times in any order or never, some with the phase bit flipped  *)
(* by an attacker, time moved in steps that run the timers. After every    *)
(* step of the key layer the connection shows its key state: the phase     *)
(* bits, the sending, staged, current, previous and next keys, the floor   *)
(* and the hold deadline, the packet numbers, the roll machine and the     *)
(* REKEY message waiting, with the time and the probe timeout in force.    *)
(*                                                                         *)
(* Every event must be the step the operators of KeyRoll.tla compute from  *)
(* the state before it: BeginOp (roll_tick), SendOp (a packet sealed, with *)
(* the polled REKEY message), DeliverOp (RecvKeys, the packet number set,  *)
(* RekeyRx), RequeueAns and RequestLostOp (loss detection); the state the  *)
(* model computes must be the state recorded. Keys, shares and echoes are  *)
(* ids (one per distinct value of a run); the checker keeps one bijection  *)
(* between ids and the symbolic terms of the model (a key is Base or       *)
(* RollSec of the Diffie-Hellman values the roll machines computed, a      *)
(* share is Pub of an atom, an echo is RId of a share). So a packet opens, *)
(* is dropped, or is held under the previous key exactly when the terms    *)
(* say it does. A request carries the roll count of its sender; the trace *)
(* does not record it, so the checker keeps the count each request was     *)
(* sent with (rq, from the model message at the send), as the Lean replay  *)
(* does.                                                                   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds keylayer.ndjson.      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd

VARIABLES i, rs
vars == <<i, rs>>

KR == INSTANCE KeyRoll WITH PTO <- 1, MaxTime <- 1, Cap0 <- 1, Cap1 <- 1, MaxPn <- 1, Sat <- 100000,
                            ForgeOn <- TRUE,
                            nd <- 0, net <- 0, now <- 0, slog <- 0, ev <- 0, comp <- 0

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/keylayer.ndjson")

NONEROLL == [none |-> TRUE]
Ev == Trace[i]

(* ---- the oracle: a bijection between recorded ids and model terms ---- *)
TermOf(om, id) == (CHOOSE p \in om : p[2] = id)[1]
Bound(om, id) == \E p \in om : p[2] = id

(* the pairs <<new>> keep the oracle a bijection *)
BijOK(om, new) ==
    /\ \A p \in new, q \in om : (p[1] = q[1]) <=> (p[2] = q[2])
    /\ \A p, q \in new : (p[1] = q[1]) <=> (p[2] = q[2])

(* ---- what a recorded view and message say about the model state ---- *)
Opt(x, id) == IF id = -1 THEN {} ELSE {<<x, id>>}

MsgPairs(m, k, sh, to) ==
    IF k = 0 THEN {} ELSE {<<m.sh, sh>>} \cup (IF k = 2 THEN {<<m.to, to>>} ELSE {})

MsgShape(m, k, spn) ==
    IF k = 0 THEN m = KR!NONE ELSE m # KR!NONE /\ (m.ans <=> k = 2) /\ (k = 2 => m.spn = spn)

ViewPairs(s, v) ==
    {<<s.sk.sec, v.sk>>, <<s.cur.sec, v.cur>>}
    \cup (IF s.stg = KR!NONE THEN {} ELSE {<<s.stg.sec, v.stg>>})
    \cup (IF s.prev = KR!NONE THEN {} ELSE {<<s.prev.k.sec, v.prev>>})
    \cup (IF s.nxt = KR!NONE THEN {} ELSE {<<s.nxt.k.sec, v.next>>})
    \cup (IF s.roll.req = KR!NONE THEN {} ELSE {<<s.roll.req.sh, v.pend>>})
    \cup (IF s.roll.last = KR!NONE THEN {} ELSE {<<s.roll.last.sh, v.last>>, <<s.roll.last.ans.sh, v.lastsh>>})
    \cup MsgPairs(s.out, v.ok, v.osh, v.oto)
    \cup MsgPairs(s.lastAns, v.lk, v.lsh, v.lto)

ViewShape(s, v) ==
    /\ s.sph = v.sph /\ s.rph = v.rph /\ s.first = v.first /\ s.npn = v.npn
    /\ (s.roll.st = "idle") = v.idle /\ s.roll.rolls = v.rolls
    /\ (s.stg = KR!NONE) = (v.stg = -1)
    /\ (s.prev = KR!NONE) = (v.prev = -1) /\ (s.prev # KR!NONE => s.prev.until = v.prevdl)
    /\ (s.nxt = KR!NONE) = (v.next = -1) /\ (s.nxt # KR!NONE => s.nxt.floor = v.floor)
    /\ (s.roll.req = KR!NONE) = (v.pend = -1)
    /\ (s.roll.last = KR!NONE) = (v.last = -1)
    /\ (s.reqAt = KR!NOTIME) = (v.reqat = -1) /\ (s.reqAt # KR!NOTIME => s.reqAt = v.reqat)
    /\ MsgShape(s.out, v.ok, v.ospn) /\ MsgShape(s.lastAns, v.lk, v.lspn)

(* the node s is the node recorded in v, and the oracle stays a bijection with the terms of v added *)
ViewOK(om, s, v, extra) == ViewShape(s, v) /\ BijOK(om, ViewPairs(s, v) \cup extra)

(* the roll count the request of share t was sent with (Sent says one was) *)
Sent(rq, t) == \E q \in rq : q[1] = t
RollOf(rq, t) == (CHOOSE q \in rq : q[1] = t)[2]

(* the REKEY message of a packet, from the recorded ids (the ghost field gdh is not recorded) *)
MsgOf(om, rq, k, sh, to, spn) ==
    IF k = 0 THEN KR!NONE
    ELSE IF k = 1 THEN KR!Req(TermOf(om, sh), RollOf(rq, TermOf(om, sh)))
    ELSE KR!Ans(TermOf(om, sh), spn, TermOf(om, to), KR!NONE)

Init == i = 1 /\ rs = [run |-> 0, nd |-> <<>>, om |-> {}, rq |-> {}]

NodeId(n) == Ev.n

(* ---- one event ---- *)
InitEv ==
    LET v0 == Ev.a  v1 == Ev.b
        n0 == [KR!NodeInit(0) EXCEPT !.npn = v0.npn, !.first = v0.first]
        n1 == [KR!NodeInit(1) EXCEPT !.npn = v1.npn, !.first = v1.first]
        p0 == ViewPairs(n0, v0)
        p1 == ViewPairs(n1, v1)
    IN /\ Ev.op = "init" /\ rs.run = 0
       /\ ViewShape(n0, v0) /\ ViewShape(n1, v1)
       /\ BijOK({}, p0 \cup p1)
       /\ rs' = [run |-> Ev.run, nd |-> <<n0, n1>>, om |-> p0 \cup p1, rq |-> {}]

BeginEv ==
    LET n == Ev.n s == rs.nd[n + 1]
        s2 == KR!BeginOp(s, n)
    IN /\ Ev.op = "begin" /\ Ev.run = rs.run
       /\ KR!CanBegin(s, n)
       /\ ViewOK(rs.om, s2, Ev.v, {})
       /\ rs' = [rs EXCEPT !.nd[n + 1] = s2, !.om = @ \cup ViewPairs(s2, Ev.v)]

SendEv ==
    LET n == Ev.n s0 == rs.nd[n + 1]
        o == KR!SendOp(s0, Ev.now, Ev.pto, Ev.mk # 0, n)
        pl == o.p.pl
        extra == {<<o.p.sec, Ev.key>>} \cup MsgPairs(pl, Ev.mk, Ev.msh, Ev.mto)
    IN /\ Ev.op = "send" /\ Ev.run = rs.run
       /\ o.ok /\ o.p.ph = Ev.ph /\ o.p.pn = Ev.pn
       /\ MsgShape(pl, Ev.mk, Ev.mspn)
       /\ ViewOK(rs.om, o.s, Ev.v, extra)
       /\ rs' = [rs EXCEPT !.nd[n + 1] = o.s, !.om = @ \cup ViewPairs(o.s, Ev.v) \cup extra,
                           !.rq = @ \cup (IF Ev.mk = 1 THEN {<<pl.sh, pl.roll>>} ELSE {})]

SelCode(sel) == IF sel = "cur" THEN 0 ELSE IF sel = "prev" THEN 1 ELSE IF sel = "next" THEN 2 ELSE 3

RecvEv ==
    LET n == Ev.n s0 == rs.nd[n + 1]
        m == MsgOf(rs.om, rs.rq, Ev.mk, Ev.msh, Ev.mto, Ev.mspn)
        p == [from |-> 1 - n, ph |-> Ev.ph, pn |-> Ev.pn, sec |-> TermOf(rs.om, Ev.key), pl |-> m]
        o == KR!DeliverOp(s0, p, Ev.forged, Ev.now, Ev.pto, n)
    IN /\ Ev.op = "recv" /\ Ev.run = rs.run
       /\ Bound(rs.om, Ev.key)
       /\ (Ev.mk # 0 => Bound(rs.om, Ev.msh))
       /\ (Ev.mk = 1 => Sent(rs.rq, TermOf(rs.om, Ev.msh)))
       /\ (Ev.mk = 2 => Bound(rs.om, Ev.mto))
       /\ Ev.slot = SelCode(o.k.sel)
       /\ Ev.opened = o.k.acc
       /\ Ev.dup = (o.k.acc /\ ~o.proc)
       /\ Ev.promoted = (o.k.acc /\ o.k.sel = "next")
       /\ ViewOK(rs.om, o.s, Ev.v, {})
       /\ rs' = [rs EXCEPT !.nd[n + 1] = o.s, !.om = @ \cup ViewPairs(o.s, Ev.v)]

RequeueEv ==
    /\ Ev.op = "requeue" /\ Ev.run = rs.run
    /\ rs' = [rs EXCEPT !.nd[Ev.n + 1] = KR!RequeueAns(@)]

RlostEv ==
    /\ Ev.op = "rlost" /\ Ev.run = rs.run
    /\ rs' = [rs EXCEPT !.nd[Ev.n + 1] = KR!RequestLostOp(@)]

EndEv ==
    /\ Ev.op = "end" /\ Ev.run = rs.run
    /\ rs' = [run |-> 0, nd |-> <<>>, om |-> {}, rq |-> {}]

Step ==
    /\ i <= Len(Trace)
    /\ Ev.t = "kl"
    /\ \/ InitEv \/ BeginEv \/ SendEv \/ RecvEv \/ RequeueEv \/ RlostEv \/ EndEv
    /\ i' = i + 1

\* the trace has ended: every event was a step of the model
Finished == i > Len(Trace) /\ UNCHANGED vars

TNext == Step \/ Finished

TraceSpec == Init /\ [][TNext]_vars

(* the safety facts of the model hold on every recorded state *)
Inv ==
    rs.run > 0 =>
        \A n \in 0..1 :
            /\ rs.nd[n + 1].roll.st \in {"idle", "req"}
            /\ rs.nd[n + 1].sph = (rs.nd[n + 1].sk.g % 2 = 1)
            /\ rs.nd[n + 1].rph = (rs.nd[n + 1].cur.g % 2 = 1)
            /\ rs.nd[n + 1].sk.g = KR!Depth(rs.nd[n + 1].sk.sec)
            /\ rs.nd[n + 1].cur.g = KR!Depth(rs.nd[n + 1].cur.sec)
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
