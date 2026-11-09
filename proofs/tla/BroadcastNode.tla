------------------------------ MODULE BroadcastNode ------------------------------
(***************************************************************************)
(* One vinc-broadcast node under every input: the receive path of          *)
(* BroadcastNodeOps with an environment that delivers any message by any   *)
(* frame type at any time (hub push, gap repair, the member fallback, a    *)
(* replay by a relay), answers or leaves unanswered the access checks,     *)
(* settles the replay floors in any way or lets the wait run out, restarts *)
(* the node, and lets time pass only up to the next deadline poll_timeout  *)
(* names (the host calls on_timer there). IsHub chooses the role.          *)
(*                                                                         *)
(* Checked, with the bounds in the .cfg files:                             *)
(*  - EpochBound: an id is delivered at most once per epoch, an epoch    *)
(*    being a record the dedupe set made while it held none for the id;    *)
(*    EpochSpacing: a new epoch starts only when the previous record is    *)
(*    older than TTL ("ttl") or the full set dropped it early to make      *)
(*    room ("cap"). OnceNoDup: no id is delivered twice in one step. So    *)
(*    the guarantee is a window of TTL measured between arrivals, and of   *)
(*    the last SeenCap recorded ids when the set is full.                  *)
(*  - SeenAccounted: every id the set holds was delivered, held, refused   *)
(*    with a reason or dropped for a stated cause (nothing is lost         *)
(*    silently after it was marked seen).                                  *)
(*  - Log eviction marks the id seen (EvictedSeen), so a late copy of an   *)
(*    evicted message is a duplicate.                                      *)
(*  - ACP: at most HeldMax held; nothing is delivered without an allow     *)
(*    (DeliveredAllowed); a deny drops what was held for the origin        *)
(*    (DenyDrops); a verdict is trusted for AcpCap (VerdictCached); the    *)
(*    cache never answers after it expired.                                *)
(*  - Floors: nothing is delivered while the node gathers (FloorHold), a   *)
(*    delivered message is not at or below the floors (FloorRespected),    *)
(*    and the gathering ends at the first timer past the wait              *)
(*    (GatherEnds); a node no hub ever sent to skips the local clock rule  *)
(*    (FreshKeep).                                                         *)
(*  - GarbageInert: a frame that does not parse, is over the limit or     *)
(*    fails the signature changes no state (only a counted rejection).     *)
(*  - Every table stays within its capacity (Bounds).                      *)
(*  - A timer leaves no expired id and no expired message (Swept).         *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/BroadcastNode.lean.                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS TTL, SeenCap, LogRing, LogCap, LogWin, FholdMax, HeldMax, ChecksMax, AcpCap, AcpMax, FloorWait, OldSlack,
          Mids, Origins, Me, IsHub, Revoked, HeldDedup, HeldFullKeepsUnseen, TopicFull, AckAfterStore, Gather, EvictGuard, LogTrack, Stamps, Sizes, MaxNow, MaxLife, Paths

N == INSTANCE BroadcastNodeOps

VARIABLES n, now, life, cnt, rec, capd, ep, acct, outs, dls, last, ackd, lm
vars == <<n, now, life, cnt, rec, capd, ep, acct, outs, dls, last, ackd, lm>>

Msgs == [mid : Mids, origin : Origins, ts : Stamps, kind : {"good", "badhead", "big", "badsig"}, n : Sizes]

Init == /\ n = N!NodeInit(0) /\ now = 0 /\ life = 0 /\ cnt = [m \in Mids |-> 0] /\ rec = [m \in Mids |-> 0] /\ capd = [m \in Mids |-> FALSE] /\ ep = [m \in Mids |-> 0]
        /\ acct = {} /\ outs = <<>> /\ dls = <<>> /\ last = "init" /\ ackd = 0 /\ lm = 0

\* the ghosts: when an id was last recorded in the dedupe set, and whether the set dropped it early (while younger
\* than TTL, to make room)
Rec(old, new) == [m \in Mids |-> IF new.seen.map[m] # N!NoT /\ new.seen.map[m] # old.seen.map[m] THEN new.seen.map[m] ELSE rec[m]]
Cap(old, new) == [m \in Mids |-> IF new.seen.map[m] # N!NoT /\ new.seen.map[m] # old.seen.map[m] THEN FALSE
                                 ELSE IF old.seen.map[m] # N!NoT /\ new.seen.map[m] = N!NoT /\ N!Sub(now, old.seen.map[m]) <= TTL THEN TRUE
                                 ELSE capd[m]]

\* a new record (not a refresh of a live one) starts a new epoch of the id
NewRec(old, new, m) == new.seen.map[m] # N!NoT /\ new.seen.map[m] # old.seen.map[m]
                       /\ (old.seen.map[m] = N!NoT \/ N!Sub(now, old.seen.map[m]) > TTL)
Ep(old, new) == [m \in Mids |-> IF NewRec(old, new, m) THEN ep[m] + 1 ELSE ep[m]]

Count(dl) == [m \in Mids |-> cnt[m] + Cardinality({i \in 1..Len(dl) : dl[i] = m})]

Apply(r, what, mid) ==
    /\ n' = r.n /\ outs' = r.outs /\ dls' = r.dl /\ cnt' = Count(r.dl) /\ rec' = Rec(n, r.n) /\ capd' = Cap(n, r.n) /\ ep' = Ep(n, r.n)
    /\ acct' = acct \union r.acc /\ last' = what /\ ackd' = r.ack /\ lm' = mid
    /\ UNCHANGED <<now, life>>

Msg == \E t \in Paths, b \in BOOLEAN, m \in Msgs : Apply(N!OnMsg(n, now, now, t, b, m), IF m.kind = "good" THEN "msg" ELSE "garbage", m.mid)

Timer == Apply(N!OnTimer(n, now), "timer", 0)

Answer == \E i \in 1..Len(n.checks), allow \in BOOLEAN : Apply(N!AcpAnswer(n, now, n.checks[i].id, allow), "answer", 0)

\* the hubs' floors are settled in any consistent way (BroadcastFloors proves what the real floors are)
Floors == /\ n.phase = "gathering"
          /\ \E rf \in Stamps \union {N!NoT}, nh \in BOOLEAN, ofl \in [Origins -> Stamps \union {N!NoT}], useOf \in BOOLEAN :
                Apply(N!FloorsSettled(n, now, TRUE, rf, IF useOf THEN ofl ELSE N!NoOf, nh), "floors", 0)

\* time passes up to the next deadline poll_timeout names; the host runs the timer there
Tick == /\ now < MaxNow
        /\ (N!PollTimeout(n) = N!NoT \/ now < N!PollTimeout(n))
        /\ now' = now + 1
        /\ outs' = <<>> /\ dls' = <<>> /\ last' = "tick" /\ ackd' = 0 /\ lm' = 0
        /\ UNCHANGED <<n, life, cnt, rec, capd, ep, acct>>

Restart == /\ life < MaxLife
           /\ n' = N!NodeInit(now) /\ life' = life + 1 /\ cnt' = [m \in Mids |-> 0] /\ rec' = [m \in Mids |-> 0] /\ capd' = [m \in Mids |-> FALSE] /\ ep' = [m \in Mids |-> 0]
           /\ acct' = {} /\ outs' = <<>> /\ dls' = <<>> /\ last' = "restart" /\ ackd' = 0 /\ lm' = 0 /\ UNCHANGED now

Next == Msg \/ Timer \/ Answer \/ Floors \/ Tick \/ Restart
Spec == Init /\ [][Next]_vars

(* ---------------------------- the checked properties ---------------------------- *)
TypeOK == /\ n.phase \in {"never", "gathering", "done"} /\ life \in 0..MaxLife

\* an id is delivered at most once per epoch (a record the set made while it held none for the id), a new epoch
\* starts only after the record is older than TTL or the full set dropped it, and no id twice in one step
EpochBound == \A m \in Mids : cnt[m] <= ep[m]
EpochSpacing == [][ \A m \in Mids : NewRec(n, n', m) => (ep[m] = 0 \/ capd[m] \/ now - rec[m] > TTL) ]_vars
OnceNoDup == \A i, j \in 1..Len(dls) : i < j => dls[i] # dls[j]

SeenAccounted == \A m \in Mids : n.seen.map[m] # N!NoT => m \in acct

LogIds(L) == {L.entries[i].mid : i \in 1..Len(L.entries)}

\* a message that left the log (evicted by a push or expired) is in the dedupe set afterwards
EvictedSeen == [][ \A m \in LogIds(n.lg) \ LogIds(n'.lg) : n'.seen.map[m] # N!NoT ]_vars

DeliveredAllowed == \A i \in 1..Len(outs) : outs[i].k = "Delivered" =>
    IF outs[i].via = "cache"
    THEN n.acp[outs[i].origin] # N!NoAcp /\ n.acp[outs[i].origin].allow /\ n.acp[outs[i].origin].exp >= now
    ELSE \E j \in 1..Len(outs) : outs[j].k = "AcpAnswered" /\ outs[j].allow /\ outs[j].origin = outs[i].origin

\* a deny delivers nothing for its origin and drops what was held for it
DenyDrops == \A j \in 1..Len(outs) : (outs[j].k = "AcpAnswered" /\ ~outs[j].allow) =>
    /\ \A h \in 1..Len(n.held) : n.held[h].origin # outs[j].origin
    /\ \A i \in 1..Len(outs) : outs[i].k = "Delivered" => outs[i].origin # outs[j].origin

\* an answer is trusted for AcpCap (when the cache has room), and the cache never answers after that
VerdictCached == \A j \in 1..Len(outs) : (outs[j].k = "AcpAnswered" /\ n.acp[outs[j].origin] # N!NoAcp) =>
    n.acp[outs[j].origin].exp = now + AcpCap
NoAskWhileCached == [][ \A j \in 1..Len(outs') : outs'[j].k = "AcpAsked" =>
    (n.acp[outs'[j].origin] = N!NoAcp \/ n.acp[outs'[j].origin].exp < now) ]_vars

Bounds == /\ Len(n.held) <= HeldMax /\ Len(n.fhold) <= FholdMax /\ Len(n.checks) <= ChecksMax
          /\ Len(n.seen.order) <= SeenCap /\ Len(n.lg.entries) <= LogCap
          /\ Cardinality({o \in Origins : n.acp[o] # N!NoAcp}) <= AcpMax

FloorHold == (last \in {"msg", "garbage", "timer", "answer"} /\ ~IsHub) =>
    (\A i \in 1..Len(outs) : outs[i].k = "Delivered" => n.phase # "gathering")
FloorRespected == \A i \in 1..Len(outs) : outs[i].k = "Delivered" => ~N!IsOld(n, outs[i].origin, outs[i].ts)
GatherBound == n.phase = "gathering" => now <= n.born + FloorWait + 1
GatherEnds == [][ (last' = "timer" /\ n.phase = "gathering" /\ now - n.born > FloorWait) => n'.phase # "gathering" ]_vars
FreshKeep == (n.nohist /\ n.rfloor = N!NoT /\ n.ofloor = N!NoOf) => \A o \in Origins, t \in Stamps : ~N!IsOld(n, o, t)

\* a frame that does not parse, is over the limit or fails the signature changes nothing but the trace
GarbageInert == [][ last' = "garbage" => n' = n /\ dls' = <<>> ]_vars

Swept == last = "timer" => /\ \A i \in 1..Len(n.seen.order) : now - n.seen.order[i][2] <= TTL
                           /\ \A i \in 1..Len(n.lg.entries) : now - n.lg.entries[i].at <= LogWin

\* a hub acknowledges (PACK) only a message it holds
AckOnlyStored == ackd > 0 => (lm \in LogIds(n.lg) \/ n.seen.map[lm] # N!NoT)
=============================================================================
