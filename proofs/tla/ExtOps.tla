------------------------------ MODULE ExtOps ------------------------------
(***************************************************************************)
(* Operators of the extension frame registry and the dispatch of a         *)
(* received extension frame, one for one with the code:                    *)
(*                                                                         *)
(*   Tab      ASSIGNED of pinc-transport frame/ext.rs, with the layer that *)
(*            takes each type: the sub-session open (pinc-core sub.rs),    *)
(*            the three transport-test types (no layer: the application    *)
(*            ring), REACH_OUT (pinc-core reach.rs), PROOF_REQ (the values *)
(*            server) and PROOF (the values fetch);                        *)
(*   Uniq     the const check of ext.rs (every range well formed and at    *)
(*            or above EXTENSION_BASE, the ranges pairwise disjoint);      *)
(*   Decodes  Frame::decode: every type from EXTENSION_BASE up is an       *)
(*            extension frame whose body is length-prefixed;               *)
(*   Route    the Co::Extension arm of on_conn_event in pinc-core          *)
(*            events.rs;                                                   *)
(*   ServeTakes, FetchTakes  the type tests of the values server           *)
(*            (Server::on_event, ServerIn::Ext) and the values fetch       *)
(*            (Fetch::on_ext), which receive the frames the endpoint holds *)
(*            for the application (pinc-node values.rs).                   *)
(*                                                                         *)
(* The wrong variants (TabCollide, RouteRingAny, RouteNoGate) are the      *)
(* witnesses: a table with two types the same, a dispatch that lets a      *)
(* REACH_OUT too long for its ring fall into the application ring, and a   *)
(* dispatch that does not look at the access check.                        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

BASE == 64
SUB == 64
TESTFIRST == 65
TESTLAST == 67
REACH == 68
PROOFREQ == 73
PROOFFRAME == 79
REACHMAX == 153

E(lo, hi, who) == [lo |-> lo, hi |-> hi, who |-> who]

RealTab == <<E(SUB, SUB, "sub"), E(TESTFIRST, TESTLAST, "test"), E(REACH, REACH, "reach"),
             E(PROOFREQ, PROOFREQ, "serve"), E(PROOFFRAME, PROOFFRAME, "fetch")>>
\* a registry in which REACH_OUT and PROOF_REQ overlap
TabCollide == <<E(SUB, SUB, "sub"), E(TESTFIRST, TESTLAST, "test"), E(REACH, PROOFREQ, "reach"),
                E(PROOFREQ, PROOFREQ, "serve"), E(PROOFFRAME, PROOFFRAME, "fetch")>>
Tab == RealTab

Covers(e, t) == e.lo <= t /\ t <= e.hi
Overlap(a, b) == a.lo <= b.hi /\ b.lo <= a.hi
Wf(e) == ~(e.lo > e.hi \/ e.lo < BASE)

\* the loops of `unique` in ext.rs
Uniq(r) == \A i \in 1..Len(r) : Wf(r[i]) /\ \A j \in (i + 1)..Len(r) : ~Overlap(r[i], r[j])

Owners(t) == {i \in 1..Len(Tab) : Covers(Tab[i], t)}
Owner(t) == IF Owners(t) = {} THEN "none" ELSE Tab[CHOOSE i \in Owners(t) : TRUE].who

Decodes(t) == t >= BASE

\* the layer a type is for, as the destination it must route to
DestOf(who) == IF who = "sub" THEN "sub" ELSE IF who = "reach" THEN "reach" ELSE "ring"

\* allowed: the session may release events to the application (Endpoint::may_release: the access check allowed it
\* and its peer's cached answer has not lapsed and is an allow); the dispatch asks that one predicate
Route(ty, len, allowed) ==
    IF ty = SUB /\ len > 0 THEN "sub"
    ELSE IF ty = REACH /\ len > 0 /\ len <= REACHMAX THEN "reach"
    ELSE IF ty # SUB /\ ty # REACH /\ len > 0 /\ allowed THEN "ring"
    ELSE "drop"

RouteRingAny(ty, len, allowed) ==
    IF ty = SUB /\ len > 0 THEN "sub"
    ELSE IF ty = REACH /\ len > 0 /\ len <= REACHMAX THEN "reach"
    ELSE IF ty # SUB /\ len > 0 /\ allowed THEN "ring"
    ELSE "drop"

RouteNoGate(ty, len, allowed) ==
    IF ty = SUB /\ len > 0 THEN "sub"
    ELSE IF ty = REACH /\ len > 0 /\ len <= REACHMAX THEN "reach"
    ELSE IF ty # SUB /\ ty # REACH /\ len > 0 THEN "ring"
    ELSE "drop"

ServeTakes(t) == t = PROOFREQ
FetchTakes(t) == t = PROOFFRAME

=============================================================================
