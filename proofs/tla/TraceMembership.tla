---------------------------- MODULE TraceMembership --------------------------
(***************************************************************************)
(* Trace validation of the membership machine: pinc-membership node.rs,    *)
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
(* CallLeave, CallRevoke, CallMoved, CallStreamReset; CallStaleFrames for  *)
(* the frames the node drops without a call) on the node of the slot     *)
(* with the same env: the same sent frames in order (route and whether a session took   *)
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
(* variable PINC_TRACE_DIR, the directory that holds membership.ndjson.     *)
(* Lean counterpart: Pinc/TraceMembership.lean.                             *)
(***************************************************************************)
EXTENDS MembershipOps, Json, IOUtils, TraceEnd

VARIABLES i, nodes, ret
vars == <<i, nodes, ret>>

Tr == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/membership.ndjson")
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

StEq(S, st, now) ==
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
       /\ st.hu = Ordered({x \in ({S.me} \cup DOMAIN S.up) : HubUp(S, now, x)}, NONE)

\* The runs of the trace are worlds of their own (the test makes a new one for each run), so a line of a new run
\* finds every slot empty; each run starts a slot before it calls it. The state holds only the nodes of the run.
NoNodes == [n \in 0..80 |-> <<>>]
Init == i = 1 /\ nodes = NoNodes /\ ret = "ok"

(* ---- one event ---- *)
\* Each step applies the line's call once and keeps the node it leaves and what the call returned; the checks of
\* the line are the invariants below, on the state after it. TLC evaluates an operator's argument again at each of
\* its uses in a step, and the model's call was used by every check; the \E over a one-value set evaluates the call
\* and its env once, and a state predicate reads the node from the state.
Pre == IF i > 1 /\ Tr[i - 1].run # Ev.run THEN NoNodes ELSE nodes
Cur == Pre[Ev.n][1]
Now == L(Ev.now)

Done(S, r) == nodes' = [Pre EXCEPT ![Ev.n] = <<S>>] /\ ret' = r

\* a failed start leaves the slot as it was
StartEv ==
    /\ Ev.op = "start"
    /\ \E r \in {CallStart([me |-> Ev.me, isHub |-> Ev.hub, hubs |-> Ev.hubs], EnvOf(Ev.env), Now, L(Ev.wall), L(Ev.floor))} :
          IF r.err = "ok" THEN Done(r.S, "ok") ELSE nodes' = Pre /\ ret' = r.err

\* the call of op on the node of the line, with the line's env
Call(op, F(_)) == /\ Ev.op = op /\ \E env \in {EnvOf(Ev.env)} : \E S \in {F(env)} : Done(S, "ok")

UpOf(env) == CallUp(Cur, env, Now, Ev.peer, Ev.inc)
DownOf(env) == CallDown(Cur, env, Now, Ev.peer, L(Ev.code))
BytesOf(env) == CallBytes(Cur, env, Now, Ev.peer, [x \in 1..Len(Ev.fs) |-> FrameOf(Ev.fs[x].f)], Ev.bad)
TimeoutOf(env) == CallTimeout(Cur, env, Now)
GoneOf(env) == CallCarrierGone(Cur, env, Now, Ev.member)
ReturnOf(env) == CallCarrierReturn(Cur, env, Now, Ev.member)
LeaveOf(env) == CallLeave(Cur, env)
MovedOf(env) == CallMoved(Cur, env, Now)
SnapshotOf(env) == CallSnapshotTo(Cur, env, Now, Ev.peer)
MaxFrameOf(env) == CallSetMaxFrame(Cur, env, L(Ev.mf))
ResetOf(env) == CallStreamReset(Cur, env, Ev.peer)
StaleOf(env) == CallStaleFrames(Cur, env)

UpEv == Call("up", UpOf)
DownEv == Call("dn", DownOf)
BytesEv == Ev.op = "by" /\ L(Ev.mf) = Cur.maxFrame /\ Call("by", BytesOf)
TimeoutEv == Call("to", TimeoutOf)
GoneEv == Call("cg", GoneOf)
ReturnEv == Call("cr", ReturnOf)
LeaveEv == Call("lv", LeaveOf)
MovedEv == Call("mv", MovedOf)
SnapshotEv == Call("sn", SnapshotOf)
MaxFrameEv == Call("sm", MaxFrameOf)
ResetEv == Call("sr", ResetOf)
StaleEv == Call("xs", StaleOf)
RevokeEv ==
    /\ Ev.op = "rv"
    /\ \E r \in {CallRevoke(Cur, EnvOf(Ev.env), Now, Ev.member)} : Done(r.S, IF r.ok THEN "ok" ELSE "full")

Step ==
    /\ i <= Len(Tr)
    /\ Ev.t = "mem"
    /\ \/ StartEv \/ UpEv \/ DownEv \/ BytesEv \/ TimeoutEv \/ GoneEv \/ ReturnEv \/ LeaveEv \/ MovedEv \/ SnapshotEv \/ MaxFrameEv \/ RevokeEv
          \/ ResetEv \/ StaleEv
    /\ i' = i + 1

\* the trace has ended: every event was a step of the model
Finished == i > Len(Tr) /\ UNCHANGED vars

TNext == Step \/ Finished

TraceSpec == Init /\ [][TNext]_vars

\* The states seen are told apart by the line index alone (VIEW in the config): every line is the step of exactly one
\* of StartEv .. RevokeEv (each requires its op) and each sets nodes' and ret' as functions of the state and the line,
\* so a behaviour has one state per index and the view merges none. TLC then does not fingerprint the nodes of the
\* run (71 of them in the snapshot run) at every state; the same traces are accepted, and every invariant is still
\* checked in every state.
IdxView == i

(* every field of every recorded call equals the model's: the line last applied (i - 1) against the node it left *)
Last == Tr[i - 1]
Lf(F(_, _)) == i > 1 => nodes[Last.n] # <<>> /\ F(nodes[Last.n][1], Last)
SentAt(S, l) == SentEq(S, l.out)
BcAt(S, l) == BcEq(S, l.out)
ClAt(S, l) == ClEq(S, l.out)
EvAt(S, l) == EvEq(S, l.out)
TrAt(S, l) == TrEq(S, l.out)
SealedAt(S, l) == OptL(l.out.sealed) = S.loc.sealed
StAt(S, l) == StEq(S, l.st, L(l.now))
SentOK == Lf(SentAt)
BcOK == Lf(BcAt)
ClOK == Lf(ClAt)
EvOK == Lf(EvAt)
TrOK == Lf(TrAt)
SealedOK == Lf(SealedAt)
StOK == Lf(StAt)
\* what start and revoke returned; every other call returns nothing
RetOK == i > 1 /\ Last.op \in {"start", "rv"} => Last.ret = ret
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Tr))
ReplayEnded == ReplayRead(Len(Tr))
=============================================================================
