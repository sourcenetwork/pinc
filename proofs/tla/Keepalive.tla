------------------------------ MODULE Keepalive ------------------------------
(***************************************************************************)
(* The keepalive schedule of vinc-core keepalive.rs, checked over every    *)
(* combination of a role, a side, a path kind and boundary values of the   *)
(* five times and two flags it reads (KeepaliveOps.tla has the operators,  *)
(* on u64 nanosecond words; the sets of times are in the config, in whole  *)
(* seconds, with offsets below u64::MAX to exercise saturation).           *)
(*                                                                         *)
(* Checked, for the plan p = Plan(x):                                      *)
(*  - a ping is never due before now nor before 5 s after the last send    *)
(*    (NotBeforeNow, NotBeforeTx); a review moment is after now            *)
(*    (ReviewAfterNow);                                                    *)
(*  - ceilings: a quiet session is always pinged, by its idle interval     *)
(*    after the last send (QuietCeiling); a plain one while its 90 s       *)
(*    window is open (PlainCeiling) and never after it closes              *)
(*    (PlainStops); a standby path 5 s after the last send while data      *)
(*    moved in the last 20 s (StandbyCeiling); a silent direct path of a   *)
(*    quiet dialing session after 14 s (DirectCeiling); each is raised to  *)
(*    the end of the quiet period only while that period holds back;       *)
(*  - floors by role: without a standby window and a watched direct path,  *)
(*    not before the idle interval after the last send (RoleFloor);        *)
(*  - after a resume nothing is due before the quiet period ends unless    *)
(*    something is in flight, which makes it no part of the plan           *)
(*    (ResumeHolds, ResumeInert);                                          *)
(*  - the plan does not change before its review moment (Stable): at any   *)
(*    later now below it the review moment is the same and the ping is     *)
(*    the same, raised to that now;                                        *)
(*  - the idle intervals leave 5 s below the idle timeout (KeepOrder) and  *)
(*    a quiet session planned in time has its ping due by then             *)
(*    (BeforeIdle): the host calling on time is the hypothesis of the      *)
(*    Lean theorem sent_before_peer_idle, not a state here.                *)
(* Witness configs: Keepalive_acc80 (an accepting-side interval of 80 s:   *)
(* KeepOrder fails), Keepalive_norev (the close of the 20 s window not a  *)
(* review moment: Stable fails), Keepalive_plain (a plain session that     *)
(* stops is reachable), Keepalive_direct (a watched silent direct path     *)
(* pinged is reachable), Keepalive_moved (a review moment that is later    *)
(* than a time at which the plan is computed again is reachable, so        *)
(* Stable is not about an empty set of times).                             *)
(* Lean counterpart: proofs/lean/Vinc/CoreKeepalive*.lean.                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets
CONSTANTS NOWS, TXS, RXS, APPS, QUS, TOPS, ACC, ACTREV
VARIABLE x
vars == <<x>>

INSTANCE KeepaliveOps
U == INSTANCE U64

Times(S) == {Sc(s) : s \in S} \cup {N!SatSub(U!Max64, Sc(k)) : k \in TOPS}

Inputs == [role : {"hub", "member", "other"}, dialer : BOOLEAN, direct : BOOLEAN,
           now : Times(NOWS), tx : Times(TXS), rx : Times(RXS), app : Times(APPS), qu : Times(QUS),
           flight : BOOLEAN]

Init == x \in Inputs
Next == UNCHANGED x
Spec == Init /\ [][Next]_vars

Pl(y) == PlanWith(y, ACC, ACTREV)
P == Pl(x)
p == P.ping
r == P.review
Le(a, b) == N!Le(a, b)
Lt(a, b) == N!Lt(a, b)
Idle == IdleDueWith(x, ACC)
Sb == StandbyDue(x.now, x.tx, x.app)
HeldQ == Held(x)

NotBeforeNow == p.some => Le(x.now, p.v)
NotBeforeTx == p.some => Le(N!SatAdd(x.tx, PathKeep), p.v)
ReviewAfterNow == r.some => Lt(x.now, r.v)

QuietCeiling == Quiet(x) =>
    /\ p.some
    /\ Le(p.v, N!Max(x.qu, Idle))
    /\ ~HeldQ => Le(p.v, Idle)
PlainCeiling == (~Quiet(x) /\ Lt(Idle, N!SatAdd(x.app, IdleDrop))) =>
    /\ p.some
    /\ ~HeldQ => Le(p.v, Idle)
PlainStops == (~Quiet(x) /\ Le(N!SatAdd(x.app, IdleDrop), x.now)) => ~p.some
StandbyCeiling == Sb.some =>
    /\ p.some
    /\ ~HeldQ => Le(p.v, Sb.v)
DirectCeiling == (Watch(x) /\ Lt(DirectDue(x), N!SatAdd(x.app, HoldWindow))) =>
    /\ p.some
    /\ ~HeldQ => Le(p.v, DirectDue(x))

RoleFloor == (~Sb.some /\ ~(Watch(x) /\ Lt(DirectDue(x), N!SatAdd(x.app, HoldWindow))) /\ p.some) =>
    Le(N!SatAdd(x.tx, IdleKeepWith(x, ACC)), p.v)

ResumeHolds == (HeldQ /\ p.some) => Le(x.qu, p.v)
ResumeInert == ~HeldQ => P = Pl([x EXCEPT !.qu = N!Zero])

\* every later now below the review moment gives the same plan: the review moment, and the ping raised to it
Stable == \A n \in Times(NOWS) :
    (Le(x.now, n) /\ (r.some => Lt(n, r.v))) =>
        LET q == Pl([x EXCEPT !.now = n])
        IN q.review = r /\ q.ping = MapMax(n, p)

\* an idle interval and the 5 s between a planned ping and the peer's idle timeout fit in it
KeepOrder == N!Le(N!SatAdd(IdleKeepWith(x, ACC), PathKeep), IdleTimeout)

\* a quiet session planned no later than its idle interval after its last send has its ping due by then
BeforeIdle == (Quiet(x) /\ ~HeldQ /\ Le(x.now, N!SatAdd(x.tx, IdleKeepWith(x, ACC)))) =>
    p.some /\ Le(p.v, N!SatAdd(x.tx, IdleKeepWith(x, ACC)))

Inv == /\ NotBeforeNow /\ NotBeforeTx /\ ReviewAfterNow
       /\ QuietCeiling /\ PlainCeiling /\ PlainStops /\ StandbyCeiling /\ DirectCeiling
       /\ RoleFloor /\ ResumeHolds /\ ResumeInert /\ Stable /\ BeforeIdle

\* reachability witnesses
NotStopped == ~(~Quiet(x) /\ Le(N!SatAdd(x.app, IdleDrop), x.now) /\ ~p.some)
NotDirect == ~(Watch(x) /\ Lt(DirectDue(x), N!SatAdd(x.app, HoldWindow)) /\ p.some /\ Le(p.v, DirectDue(x))
               /\ ~Sb.some /\ ~HeldQ)
\* a later time below the review moment exists, so Stable is not empty
StableMoved == ~(\E n \in Times(NOWS) : Lt(x.now, n) /\ r.some /\ Lt(n, r.v))
=============================================================================
