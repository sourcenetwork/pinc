---------------------------- MODULE TraceMembership --------------------------
(***************************************************************************)
(* Trace validation of the membership machine: vinc-membership node.rs,    *)
(* hub.rs, view.rs, input.rs and timers.rs.                                 *)
(*                                                                         *)
(* The Rust test tests/trace_membership.rs (part node) runs the real hub    *)
(* and member state machines over the membership test world: attachment,   *)
(* PULSE, churn, loss, partitions and heals, slow members, carrier drops   *)
(* probed on every path, DOWN with every refusal, carrier returns, leave,  *)
(* revocation (table-full included), crash and restart on the persistent   *)
(* counter and on the clock, suspension, a heal and a late timer while a   *)
(* removal waits (#284: the recheck table of Membership.tla holds each      *)
(* removal's own instant and grace state), the primary switch, the address  *)
(* move, snapshots of several frames and malformed input. Every call into a *)
(* machine is one line: the call, the host as the call found it, what the  *)
(* machine asked of the host and reported, and the public state after.     *)
(*                                                                         *)
(* Each line must be the call of MembershipOps.tla (CallStart, CallUp,     *)
(* CallDown, CallBytes, CallTimeout, CallCarrierGone, CallCarrierReturn,   *)
(* CallLeave, CallRevoke, CallMoved) on the node of the slot with the same *)
(* env: the same sent frames in order (route and whether a session took   *)
(* them), the same broadcast-layer calls, closes, events and trace records *)
(* in order, the same store, and the same members, epoch, primary,         *)
(* incarnation and roster. Each of these is an invariant of its own, so a  *)
(* failure names the field.                                                 *)
(*                                                                         *)
(* The host's floor body is the harness's: [0xF1, member id, 0 x 6, 1].    *)
(* Frame bytes ("hex") are checked by the Lean replay against the codec     *)
(* model; here a frame is its fields.                                      *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds membership.ndjson.     *)
(* Lean counterpart: Vinc/TraceMembership.lean.                             *)
(***************************************************************************)
EXTENDS MembershipOps, Json, IOUtils

VARIABLES i, nodes, chk
vars == <<i, nodes, chk>>

Tr == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/membership.ndjson")
Ev == Tr[i]

L(l) == U!FromLimbs(l)
OptL(l) == IF l = <<>> THEN <<>> ELSE <<L(l[1])>>

(* ---- the recorded values as model values ---- *)
RecJ(j) == [inc |-> L(j.inc), ver |-> j.ver, th |-> j.th]
FrameOf(j) ==
    CASE j.k = "hello" -> [k |-> "hello", rec |-> RecJ(j), snap |-> j.snap, homed |-> j.homed]
      [] j.k = "ack" -> [k |-> "ack"]
      [] j.k = "probe" -> [k |-> "probe"]
      [] j.k = "delta" -> [k |-> "delta", m |-> j.m, rec |-> RecJ(j), a |-> j.a]
      [] j.k = "snap" -> [k |-> "snap", partial |-> j.partial, more |-> j.more,
                          es |-> [x \in 1..Len(j.es) |-> [m |-> j.es[x].m, rec |-> RecJ(j.es[x])]]]
      [] j.k = "down" -> [k |-> "down", m |-> j.m, inc |-> L(j.inc), sil |-> U!W(j.sil),
                          pr |-> [x \in 1..Len(j.pr) |-> [age |-> U!W(j.pr[x][1]), path |-> j.pr[x][2]]]]
      [] j.k = "other" -> [k |-> "other", ty |-> j.ty, topic |-> j.topic, rest |-> j.rest]

SentOf(j) == [to |-> j.to, r |-> j.r, via |-> j.via, f |-> FrameOf(j.f), ok |-> j.ok]
EvOf(j) == IF j.k = "view" THEN [j EXCEPT !.epoch = L(j.epoch)] ELSE j
TrOf(j) == IF j.k \in {"started", "incarnation"} THEN [j EXCEPT !.inc = L(j.inc)] ELSE j

EvidenceOf(j) == [rx |-> L(j.rx), srtt |-> L(j.srtt), pto |-> j.pto, inf |-> j.inf, direct |-> j.direct]
CarOf(j) == IF j.k = "open" THEN j ELSE [k |-> "gone", since |-> L(j.since), sleep |-> OptL(j.sleep)]

EnvOf(e) ==
    [ev |-> [x \in {e.ev[a][1] : a \in 1..Len(e.ev)} |->
                 EvidenceOf(e.ev[CHOOSE a \in 1..Len(e.ev) : e.ev[a][1] = x][2])],
     car |-> [x \in {e.car[a][1] : a \in 1..Len(e.car)} |->
                  CarOf(e.car[CHOOSE a \in 1..Len(e.car) : e.car[a][1] = x][2])],
     acc |-> {e.acc[a] : a \in 1..Len(e.acc)},
     rv |-> {e.rv[a] : a \in 1..Len(e.rv)},
     ver |-> e.ver, tk |-> e.tk, refl |-> e.refl, pers |-> e.pers, sealed |-> OptL(e.sealed),
     failseal |-> e.failseal, failunseal |-> e.failunseal,
     floor |-> [p \in 0..255 |-> <<241, p, 0, 0, 0, 0, 0, 0, 1>>],
     gu |-> [x \in {e.gu[a][1] : a \in 1..Len(e.gu)} |-> L(e.gu[CHOOSE a \in 1..Len(e.gu) : e.gu[a][1] = x][2])]]

(* ---- the checks ---- *)
SeqEq(a, b, F(_)) == Len(a) = Len(b) /\ \A x \in 1..Len(a) : F(a[x]) = b[x]
Ident(x) == x
SentEq(S, o) == SeqEq(o.sent, S.sent, SentOf)
BcEq(S, o) == SeqEq(o.bc, S.bc, Ident)
ClEq(S, o) == SeqEq(o.cl, S.cl, Ident)
EvEq(S, o) == SeqEq(o.ev, S.ev, EvOf)
TrEq(S, o) == SeqEq(o.tr, S.tr, TrOf)

StEq(S, st) ==
    LET ks == Ordered(DOMAIN S.members, NONE)
        rs == Ordered(DOMAIN S.roster, NONE)
    IN /\ Len(st.members) = Len(ks)
       /\ \A x \in 1..Len(ks) :
            st.members[x] = <<ks[x], L(st.members[x][2]) , S.members[ks[x]].rec.ver, S.members[ks[x]].rec.th>>
               \/ (st.members[x][1] = ks[x] /\ L(st.members[x][2]) = S.members[ks[x]].rec.inc
                   /\ st.members[x][3] = S.members[ks[x]].rec.ver /\ st.members[x][4] = S.members[ks[x]].rec.th)
       /\ L(st.epoch) = S.epoch
       /\ st.primary = S.primary
       /\ L(st.inc) = INC!Word(S.inc)
       /\ Len(st.roster) = Len(rs)
       /\ \A x \in 1..Len(rs) : st.roster[x][1] = rs[x] /\ L(st.roster[x][2]) = S.roster[rs[x]].renewed
       /\ st.sealfailed = S.sealFailed
       /\ L(st.maxframe) = S.maxFrame
       /\ st.hu = Ordered({x \in ({S.me} \cup DOMAIN S.up) : HubUp(S, L(Ev.now), x)}, NONE)

Flags(S, o, st, ret) ==
    [sent |-> SentEq(S, o), bc |-> BcEq(S, o), cl |-> ClEq(S, o), ev |-> EvEq(S, o), tr |-> TrEq(S, o),
     sealed |-> OptL(o.sealed) = S.loc.sealed, st |-> StEq(S, st), ret |-> ret]

Init == i = 1 /\ nodes = [n \in 0..80 |-> <<>>]
        /\ chk = [sent |-> TRUE, bc |-> TRUE, cl |-> TRUE, ev |-> TRUE, tr |-> TRUE, sealed |-> TRUE, st |-> TRUE, ret |-> TRUE]

(* ---- one event ---- *)
Cur == nodes[Ev.n][1]
Now == L(Ev.now)

Done(S, ret) == /\ nodes' = [nodes EXCEPT ![Ev.n] = <<S>>]
                /\ chk' = Flags(S, Ev.out, Ev.st, ret)

StartEv ==
    LET r == CallStart([me |-> Ev.me, isHub |-> Ev.hub, hubs |-> Ev.hubs], EnvOf(Ev.env), Now, L(Ev.wall), L(Ev.floor))
    IN /\ Ev.op = "start"
       /\ IF r.err = "ok"
          THEN Done(r.S, Ev.ret = "ok")
          ELSE /\ nodes' = nodes
               /\ chk' = Flags(IF nodes[Ev.n] = <<>> THEN r.S ELSE Cur, Ev.out, Ev.st, Ev.ret = r.err)

CallEv(op, S1) == /\ Ev.op = op /\ Done(S1, TRUE)

UpEv == CallEv("up", CallUp(Cur, EnvOf(Ev.env), Now, Ev.peer, Ev.inc))
DownEv == CallEv("dn", CallDown(Cur, EnvOf(Ev.env), Now, Ev.peer, L(Ev.code)))
BytesEv == /\ Ev.op = "by" /\ L(Ev.mf) = Cur.maxFrame
           /\ CallEv("by", CallBytes(Cur, EnvOf(Ev.env), Now, Ev.peer, [x \in 1..Len(Ev.fs) |-> FrameOf(Ev.fs[x].f)], Ev.bad))
TimeoutEv == CallEv("to", CallTimeout(Cur, EnvOf(Ev.env), Now))
GoneEv == CallEv("cg", CallCarrierGone(Cur, EnvOf(Ev.env), Now, Ev.member))
ReturnEv == CallEv("cr", CallCarrierReturn(Cur, EnvOf(Ev.env), Now, Ev.member))
LeaveEv == CallEv("lv", CallLeave(Cur, EnvOf(Ev.env)))
MovedEv == CallEv("mv", CallMoved(Cur, EnvOf(Ev.env), Now))
SnapshotEv == CallEv("sn", CallSnapshotTo(Cur, EnvOf(Ev.env), Now, Ev.peer))
MaxFrameEv == CallEv("sm", CallSetMaxFrame(Cur, EnvOf(Ev.env), L(Ev.mf)))
RevokeEv ==
    LET r == CallRevoke(Cur, EnvOf(Ev.env), Now, Ev.member)
    IN /\ Ev.op = "rv" /\ nodes' = [nodes EXCEPT ![Ev.n] = <<r.S>>]
       /\ chk' = Flags(r.S, Ev.out, Ev.st, Ev.ret = (IF r.ok THEN "ok" ELSE "full"))

Step ==
    /\ i <= Len(Tr)
    /\ Ev.t = "mem"
    /\ \/ StartEv \/ UpEv \/ DownEv \/ BytesEv \/ TimeoutEv \/ GoneEv \/ ReturnEv \/ LeaveEv \/ MovedEv \/ SnapshotEv \/ MaxFrameEv \/ RevokeEv
    /\ i' = i + 1

\* the trace has ended: every event was a step of the model
Finished == i > Len(Tr) /\ UNCHANGED vars

TNext == Step \/ Finished

TraceSpec == Init /\ [][TNext]_vars

(* every field of every recorded call equals the model's *)
SentOK == chk.sent
BcOK == chk.bc
ClOK == chk.cl
EvOK == chk.ev
TrOK == chk.tr
SealedOK == chk.sealed
StOK == chk.st
RetOK == chk.ret
=============================================================================
