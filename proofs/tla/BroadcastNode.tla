------------------------------ MODULE BroadcastNode ------------------------------
(***************************************************************************)
(* One pinc-broadcast node under every input: the receive path of          *)
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
(*    fails the signature changes no state (only a counted rejection); a   *)
(*    graft (the id and signature of a stored message, another body) is    *)
(*    such a frame: acknowledged like the message when due, never stored,  *)
(*    forwarded or delivered.                                              *)
(*  - AckOnlyStored: a hub acknowledges only the very message it holds the *)
(*    print of (the log or the dedupe map holds the id, and the content    *)
(*    stored under it is the message's); RetryAcked: an exact retry is     *)
(*    acknowledged after the log let the message go too; UndueDuplicate: a *)
(*    copy due no acknowledgement is never compared; GraftTaken: a graft   *)
(*    for an id the hub holds no print for (its own id the log refused) is *)
(*    answered IdTaken and not acknowledged. Ghosts record the last three  *)
(*    (a step that broke one sets its ghost for good).                     *)
(*  - Every table stays within its capacity (Bounds).                      *)
(*  - A timer leaves no expired id and no expired message (Swept).         *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/BroadcastNode.lean.                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS TTL, SeenCap, LogRing, LogCap, LogWin, FholdMax, HeldMax, ChecksMax, AcpCap, AcpMax, FloorWait, OldSlack,
          Mids, Origins, Me, IsHub, Revoked, HeldDedup, HeldFullKeepsUnseen, TopicFull, AckAfterStore, Gather, EvictGuard, LogTrack, Stamps, Sizes, MaxNow, MaxLife, Paths, AckById, Bodies, KeepPrint, DueOnly, GraftStored

N == INSTANCE BroadcastNodeOps

VARIABLES n, now, life, cnt, rec, capd, ep, acct, outs, dls, last, ackd, lm, retryLost, undueTaken, graftLost
vars == <<n, now, life, cnt, rec, capd, ep, acct, outs, dls, last, ackd, lm, retryLost, undueTaken, graftLost>>

\* lm: the message of the last step when it was acknowledged; no message otherwise
NoMsg == [none |-> TRUE]

Msgs == [mid : Mids, origin : Origins, ts : Stamps, kind : {"good", "badhead", "big", "badsig", "graft"}, n : Sizes, body : Bodies]

Init == /\ n = N!NodeInit(0) /\ now = 0 /\ life = 0 /\ cnt = [m \in Mids |-> 0] /\ rec = [m \in Mids |-> 0] /\ capd = [m \in Mids |-> FALSE] /\ ep = [m \in Mids |-> 0]
        /\ acct = {} /\ outs = <<>> /\ dls = <<>> /\ last = "init" /\ ackd = 0 /\ lm = NoMsg
        /\ retryLost = FALSE /\ undueTaken = FALSE /\ graftLost = FALSE

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

\* the ghosts retryLost and undueTaken become TRUE (and stay) in a step that broke RetryAcked or UndueDuplicate
ApplyG(r, what, msg, lost, taken, gl) ==
    /\ n' = N!Tidy(r.n) /\ outs' = r.outs /\ dls' = r.dl /\ cnt' = Count(r.dl) /\ rec' = Rec(n, r.n) /\ capd' = Cap(n, r.n) /\ ep' = Ep(n, r.n)
    /\ acct' = acct \union r.acc /\ last' = what /\ ackd' = r.ack /\ lm' = IF r.ack > 0 THEN msg ELSE NoMsg
    /\ retryLost' = (retryLost \/ lost) /\ undueTaken' = (undueTaken \/ taken) /\ graftLost' = (graftLost \/ gl)
    /\ UNCHANGED <<now, life>>

Apply(r, what, msg) == ApplyG(r, what, msg, FALSE, FALSE, FALSE)

\* a PUB or FANP at a hub is due an acknowledgement
Due(t) == IsHub /\ t \in {"PUB", "FANP"}
TakenOut(r) == \E i \in 1..Len(r.outs) : r.outs[i].k = "Rejected" /\ r.outs[i].why = "IdTaken"

\* a retry of the very message a hub holds the print of is a good message due an acknowledgement under a known id
Msg == \E t \in Paths, b \in BOOLEAN, m \in Msgs :
    LET r == N!OnMsg(n, now, now, t, b, m)
        retry == Due(t) /\ N!IsDup(n, m.mid, now) /\ N!Same(n, m)
        noPrint == Due(t) /\ m.kind = "graft" /\ N!IsDup(n, m.mid, now) /\ n.store[m.mid] = N!NoM
    IN ApplyG(r, IF m.kind = "good" THEN "msg" ELSE "garbage", m, retry /\ r.ack = 0, TakenOut(r) /\ ~Due(t),
              noPrint /\ (r.ack > 0 \/ ~TakenOut(r)))

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
        /\ outs' = <<>> /\ dls' = <<>> /\ last' = "tick" /\ ackd' = 0 /\ lm' = NoMsg
        /\ UNCHANGED <<n, life, cnt, rec, capd, ep, acct, retryLost, undueTaken, graftLost>>

Restart == /\ life < MaxLife
           /\ n' = N!NodeInit(now) /\ life' = life + 1 /\ cnt' = [m \in Mids |-> 0] /\ rec' = [m \in Mids |-> 0] /\ capd' = [m \in Mids |-> FALSE] /\ ep' = [m \in Mids |-> 0]
           /\ acct' = {} /\ outs' = <<>> /\ dls' = <<>> /\ last' = "restart" /\ ackd' = 0 /\ lm' = NoMsg /\ UNCHANGED <<now, retryLost, undueTaken, graftLost>>

\* the hub publishes a message of its own (publish.rs): the id is recorded, then the log stores the message or, when it
\* is over the ring, refuses it, which leaves the id known with no print held
Own == IsHub /\ \E m \in Msgs : m.kind = "good" /\ m.origin = Me /\ ~N!IsDup(n, m.mid, now) /\ Apply(N!Own(n, now, now, m), "own", m)

Next == Msg \/ Timer \/ Answer \/ Floors \/ Tick \/ Restart
Spec == Init /\ [][Next]_vars
\* the hub also publishes its own messages (the configs ending in _graft and _graftOld)
SpecOwn == Init /\ [][Next \/ Own]_vars

(* ---------------------------- the checked properties ---------------------------- *)
TypeOK == /\ n.phase \in {"never", "gathering", "done"} /\ life \in 0..MaxLife

\* an id is delivered at most once per epoch (a record the set made while it held none for the id), a new epoch
\* starts only after the record is older than TTL or the full set dropped it, and no id twice in one step
EpochBound == \A m \in Mids : cnt[m] <= ep[m]
EpochSpacing == [][ \A m \in Mids : NewRec(n, n', m) => (ep[m] = 0 \/ capd[m] \/ now - rec[m] > TTL) ]_vars
OnceNoDup == \A i, j \in 1..Len(dls) : i < j => dls[i] # dls[j]
\* a bound for the model checker alone (a config names it as its CONSTRAINT): a hub that stores its own messages forgets and records an id again for ever
EpochsLe3 == \A m \in Mids : ep[m] <= 3
\* the quick profile of BroadcastNode_hubcap: two epochs of an id (the second one starts after the set dropped the id)
EpochsLe3Quick == \A m \in Mids : ep[m] <= 2

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

\* a hub acknowledges (PACK) only the very message it holds the print of: the log or the dedupe map holds the id, and
\* the content stored under it (origin, timestamp, body) is the message's; another message under a known id is
\* refused with IdTaken (AckById is the old rule that acknowledged any known id: the witness)
AckOnlyStored == ackd > 0 => ((lm.mid \in LogIds(n.lg) \/ n.seen.map[lm.mid] # N!NoT) /\ n.store[lm.mid] = N!PrintOf(n, lm))

\* a retry of the stored message (same content, a good signature) due an acknowledgement is acknowledged, after the
\* log let the message go as much as while it holds it (KeepPrint = FALSE is the witness)
RetryAcked == ~retryLost

\* a copy due no acknowledgement is a plain duplicate: it is never refused as another message's, so no body is
\* compared for it (DueOnly = FALSE is the witness)
UndueDuplicate == ~undueTaken

\* a graft due an acknowledgement for an id the hub is known to hold but holds no print for (its own id, which the
\* log refused) is answered IdTaken and not acknowledged (GraftStored = FALSE is the witness)
GraftTaken == ~graftLost
=============================================================================
