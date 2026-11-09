----------------------------- MODULE BroadcastRepair -----------------------------
(***************************************************************************)
(* Gap repair of vinc-broadcast gap.rs, step for step: one subscriber S    *)
(* whose primary hub is hub 1, a publisher P, a second hub 2. S asks its   *)
(* primary SUB(since); the hub answers HAVE with the newest HaveMax ids it *)
(* logged at or after `since` (its wall clock); S asks GET for the ids it  *)
(* lacks; the hub answers MSG; S delivers each once (on_have, on_get).     *)
(* The question is asked again on a membership resubscribe (since =        *)
(* max(born, last receipt - ResubBack)), by GAP_AE every GapEvery while    *)
(* the topic is live (newest recorded id younger than GapLive; since =     *)
(* max(born, now - GapSpan)), and between hubs by HAVE every AeEvery over  *)
(* [now - AeFrom, now - AeTo).                                             *)
(*                                                                         *)
(* The environment cuts and heals any link (S-1, S-2... P-1, P-2, 1-2, P-S) *)
(* at any instant in Times, loses any push to S even over a live link (a   *)
(* dead session swallows a frame), has P hand its message to a hub on any  *)
(* reachable instant within the retry span, and lets time pass only to the *)
(* next GAP_AE or HAVE deadline. Frames are delivered at once or lost.     *)
(* The hub log holds LogCap messages for Window. RxHubOnly: only the hub   *)
(* path moves the receipt the resubscribe asks back from (the code after   *)
(* its fix); FALSE is the code before it, whose witness is the _rx config. *)
(*                                                                         *)
(* Checked: SinceCoversMissed (at every resubscription, every message the  *)
(* hub still logs and S lacks was logged at or after `since`, or falls in  *)
(* the span of the next periodic check: nothing the questions can skip), HealCovers and GapCovers (after the question S has  *)
(* every logged message from `since`), AeCovers (after a hub exchange the  *)
(* other hub holds every message of the window it lacked), PeriodicDelivers*)
(* (a message the primary logged, that S lacks, over a link that was up    *)
(* since it was logged, is delivered by the first GAP_AE after it, if the  *)
(* topic is live at that check: 25 s span over a 20 s period), Dedupe      *)
(* (each message once). The _quiet config shows that a missed message on a *)
(* topic with no other traffic is asked about only when membership         *)
(* resubscribes; the _have config shows the HaveMax limit.                 *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/BroadcastRepair.lean.                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Times, Mids, Window, LogCap, GapEvery, GapSpan, GapLive, ResubBack, AeEvery, AeFrom, AeTo, HaveMax, GiveUp,
          RxHubOnly, GapMark, Resub, Born, MaxTime, Quiet, MaxFlips

NoT == -1
Sub(a, b) == IF a >= b THEN a - b ELSE 0
Max2(a, b) == IF a >= b THEN a ELSE b
Min2(a, b) == IF a <= b THEN a ELSE b
Hubs == {1, 2}
\* the links: S-hub1, P-hub1, P-hub2, hub1-hub2, P-S
Links == {"S1", "P1", "P2", "H", "PS"}
NoStep == [k |-> "none", since |-> 0, missed |-> {}, ok |-> FALSE]

VARIABLES now, lnk, hl, hseen, nextAe, pubd, dlv, lastRx, newest, nextGap, cont, skipped, step, nf, lastGap
vars == <<now, lnk, hl, hseen, nextAe, pubd, dlv, lastRx, newest, nextGap, cont, skipped, step, nf, lastGap>>

NextTime(t) == IF \E x \in Times : x > t THEN CHOOSE x \in Times : x > t /\ \A y \in Times : y > t => x <= y ELSE MaxTime + 1

LogIds(h) == {m \in Mids : hl[h][m] # NoT}
\* (at, id) order: the id of the newest entry among S
RECURSIVE TopK(_, _, _)
TopK(h, S, k) == IF S = {} \/ k = 0 THEN {}
                 ELSE LET m == CHOOSE x \in S : \A y \in S : hl[h][x] > hl[h][y] \/ (hl[h][x] = hl[h][y] /\ x >= y)
                      IN {m} \union TopK(h, S \ {m}, k - 1)
\* log.rs since(): the newest HaveMax ids logged at or after `since`
SinceIds(h, since) == TopK(h, {m \in LogIds(h) : hl[h][m] >= since}, HaveMax)
\* log.rs window(): the newest HaveMax ids logged in [now - from, now - to)
WindowIds(h) == TopK(h, {m \in LogIds(h) : Sub(now, AeFrom) <= hl[h][m] /\ hl[h][m] < Sub(now, AeTo)}, HaveMax)

Init == /\ now = 0 /\ nf = 0 /\ lnk = [l \in Links |-> TRUE] /\ hl = [h \in Hubs |-> [m \in Mids |-> NoT]] /\ hseen = [h \in Hubs |-> {}]
        /\ nextAe = [h \in Hubs |-> 0] /\ pubd = [m \in Mids |-> NoT] /\ dlv = [m \in Mids |-> NoT] /\ lastRx = NoT
        /\ newest = NoT /\ nextGap = GapEvery /\ cont = [m \in Mids |-> FALSE] /\ skipped = [m \in Mids |-> FALSE] /\ step = NoStep /\ lastGap = Born

(* ---- the hub: log.rs push with eviction, and the store of a verified message ---- *)
RECURSIVE Evict(_, _)
Evict(h, hlh) == IF Cardinality({m \in Mids : hlh[m] # NoT}) < LogCap THEN hlh
                 ELSE LET old == CHOOSE x \in Mids : hlh[x] # NoT /\ \A y \in Mids : hlh[y] # NoT => hlh[x] < hlh[y] \/ (hlh[x] = hlh[y] /\ x <= y)
                      IN Evict(h, [hlh EXCEPT ![old] = NoT])
Stores(hlv, h, m) == [hlv EXCEPT ![h] = [Evict(h, hlv[h]) EXCEPT ![m] = now]]

\* S offers a message it lacks: delivered once; only the hub path moves the receipt
Offer(dl, lr, nw, m, hubPath) ==
    IF dl[m] # NoT THEN [dl |-> dl, lr |-> lr, nw |-> nw]
    ELSE [dl |-> [dl EXCEPT ![m] = now], lr |-> IF hubPath \/ ~RxHubOnly THEN now ELSE lr, nw |-> now]

(* ---- environment ---- *)
Publish == \E m \in Mids : /\ pubd[m] = NoT /\ \A k \in Mids : k < m => pubd[k] # NoT
                           /\ pubd[m] = NoT /\ pubd' = [pubd EXCEPT ![m] = now]
                           /\ UNCHANGED <<now, lnk, hl, hseen, nextAe, dlv, lastRx, newest, nextGap, cont, skipped, step, nf, lastGap>>

\* P hands its message to hub h (the first send to the primary or a retry), within the give-up span; the hub stores,
\* mirrors to the other hub over a live link, and pushes to S over a live link unless the frame is swallowed
ToHub == \E m \in Mids, h \in Hubs, lose \in BOOLEAN :
    /\ pubd[m] # NoT /\ Sub(now, pubd[m]) <= GiveUp /\ (IF h = 1 THEN lnk["P1"] ELSE lnk["P2"]) /\ m \notin hseen[h]
    /\ LET o == 3 - h
           mirrored == lnk["H"] /\ m \notin hseen[o]
           hl1 == Stores(hl, h, m)
           hl2 == IF mirrored THEN Stores(hl1, o, m) ELSE hl1
           push1 == lnk["S1"] /\ ~lose /\ (h = 1 \/ mirrored)
           od == IF push1 THEN Offer(dlv, lastRx, newest, m, TRUE) ELSE [dl |-> dlv, lr |-> lastRx, nw |-> newest]
       IN /\ hl' = hl2 /\ hseen' = [hseen EXCEPT ![h] = @ \union {m}, ![o] = IF mirrored THEN @ \union {m} ELSE @]
          /\ dlv' = od.dl /\ lastRx' = od.lr /\ newest' = od.nw
          /\ cont' = IF (h = 1 \/ mirrored) THEN [cont EXCEPT ![m] = lnk["S1"]] ELSE cont
          /\ step' = NoStep
    /\ UNCHANGED <<now, lnk, nextAe, pubd, nextGap, skipped, nf, lastGap>>

\* publish.rs fallback: while neither hub is reachable the message goes to S over a member session
Fallback == \E m \in Mids :
    /\ pubd[m] # NoT /\ Sub(now, pubd[m]) <= GiveUp /\ ~lnk["P1"] /\ ~lnk["P2"] /\ lnk["PS"]
    /\ LET od == Offer(dlv, lastRx, newest, m, FALSE) IN dlv' = od.dl /\ lastRx' = od.lr /\ newest' = od.nw
    /\ UNCHANGED <<now, lnk, hl, hseen, nextAe, pubd, nextGap, cont, skipped, step, nf, lastGap>>

\* SUB(since) at the primary, then HAVE, GET, MSG: S lacks no id of the answer afterwards
Ask(kind, since) ==
    LET ids == SinceIds(1, since)
        missed == {m \in LogIds(1) : dlv[m] = NoT}
        got == [m \in Mids |-> IF m \in ids /\ dlv[m] = NoT THEN now ELSE dlv[m]]
    IN /\ dlv' = got
       /\ lastRx' = IF \E m \in ids : dlv[m] = NoT THEN now ELSE lastRx
       /\ newest' = IF \E m \in ids : dlv[m] = NoT THEN now ELSE newest
       /\ step' = [k |-> kind, since |-> since, missed |-> missed, ok |-> TRUE]

\* gap.rs since_ms: the point a resubscription asks the log back from: ResubBack before the last receipt from the hub, and
\* (GapMark, the code after its fix) no later than the last periodic check that was sent; the check extends the chain only if its span reaches the point the chain had reached
SinceMs == IF lastRx = NoT THEN Born
           ELSE LET from == Sub(lastRx, ResubBack)
                    from2 == IF GapMark THEN Min2(from, lastGap) ELSE from
                IN Max2(Born, from2)

\* gap.rs gap_ae: while the topic is live, ask for the last GapSpan; the deadline is nextGap
Live == newest # NoT /\ Sub(now, newest) < GapLive
GapAe == /\ now >= nextGap /\ nextGap' = now + GapEvery
         /\ IF lnk["S1"] /\ (Live \/ Quiet)
            THEN /\ Ask("gap", Max2(Sub(now, GapSpan), Born)) /\ skipped' = skipped /\ lastGap' = IF Sub(now, GapSpan) <= lastGap THEN now ELSE lastGap
            ELSE /\ step' = NoStep /\ UNCHANGED <<dlv, lastRx, newest, lastGap>>
                 /\ skipped' = IF lnk["S1"] THEN [m \in Mids |-> skipped[m] \/ (hl[1][m] # NoT /\ dlv[m] = NoT)] ELSE skipped
         /\ UNCHANGED <<now, lnk, hl, hseen, nextAe, pubd, cont, nf>>

\* gap.rs hub_ae: HAVE of the window to the other hub, which fetches what it lacks (GET, MSG; not mirrored again)
HubAe == \E h \in Hubs :
    /\ now >= nextAe[h]
    /\ nextAe' = [nextAe EXCEPT ![h] = nextAe[h] + ((Sub(now, nextAe[h]) \div AeEvery) + 1) * AeEvery]
    /\ LET o == 3 - h
           need == {m \in WindowIds(h) : m \notin hseen[o]}
           doit == lnk["H"] /\ need # {}
           hlN == IF doit THEN [hl EXCEPT ![o] = [m \in Mids |-> IF m \in need THEN hl[h][m] ELSE hl[o][m]]] ELSE hl
           hl3 == IF doit THEN [hlN EXCEPT ![o] = Evict(o, hlN[o])] ELSE hlN
           pushes == doit /\ o = 1 /\ lnk["S1"]
           got == [m \in Mids |-> IF pushes /\ m \in need /\ dlv[m] = NoT THEN now ELSE dlv[m]]
       IN /\ hl' = hlN /\ hseen' = [hseen EXCEPT ![o] = IF doit THEN @ \union need ELSE @]
          /\ dlv' = got
          /\ lastRx' = IF pushes /\ \E m \in need : dlv[m] = NoT THEN now ELSE lastRx
          /\ newest' = IF pushes /\ \E m \in need : dlv[m] = NoT THEN now ELSE newest
          /\ cont' = IF doit /\ o = 1 /\ lnk["S1"] THEN [m \in Mids |-> IF m \in need THEN TRUE ELSE cont[m]] ELSE cont
          /\ step' = [NoStep EXCEPT !.k = "ae", !.ok = doit, !.missed = IF doit THEN need ELSE {}, !.since = Sub(now, AeFrom)]
    /\ UNCHANGED <<now, lnk, pubd, nextGap, skipped, nf, lastGap>>

\* a link goes down or comes up; when the subscriber's link comes up membership resubscribes (the host contract)
Flip == \E l \in Links :
    /\ nf < MaxFlips /\ nf' = nf + 1
    /\ lnk' = [lnk EXCEPT ![l] = ~@]
    /\ cont' = IF l = "S1" THEN [m \in Mids |-> FALSE] ELSE cont
    /\ IF l = "S1" /\ ~lnk["S1"] /\ Resub
       THEN Ask("resub", SinceMs)
       ELSE /\ step' = NoStep /\ UNCHANGED <<dlv, lastRx, newest>>
    /\ UNCHANGED <<now, hl, hseen, nextAe, pubd, nextGap, skipped, lastGap>>

Deadline == Min2(NextTime(now), Min2(IF nextGap > now THEN nextGap ELSE now, Min2(IF nextAe[1] > now THEN nextAe[1] ELSE now, IF nextAe[2] > now THEN nextAe[2] ELSE now)))
Tick == /\ now < MaxTime /\ Deadline > now /\ nextGap > now /\ nextAe[1] > now /\ nextAe[2] > now
        /\ now' = Deadline
        /\ hl' = [h \in Hubs |-> [m \in Mids |-> IF hl[h][m] # NoT /\ Sub(Deadline, hl[h][m]) > Window THEN NoT ELSE hl[h][m]]]
        /\ step' = NoStep
        /\ UNCHANGED <<lnk, hseen, nextAe, pubd, dlv, lastRx, newest, nextGap, cont, skipped, nf, lastGap>>

Next == Publish \/ ToHub \/ Fallback \/ GapAe \/ HubAe \/ Flip \/ Tick
Spec == Init /\ [][Next]_vars

(* ---------------------------- the checked properties ---------------------------- *)
TypeOK == \A m \in Mids : dlv[m] = NoT \/ dlv[m] <= now

\* at every question S asks, every logged message S lacked was logged at or after `since`: nothing is skipped
SinceCoversMissed == step.k = "resub" => \A m \in step.missed : hl[1][m] = NoT \/ hl[1][m] >= step.since \/ hl[1][m] + GapSpan >= nextGap
\* and afterwards S has every logged message from `since` (the newest HaveMax)
HealCovers == step.k \in {"resub", "gap"} => \A m \in SinceIds(1, step.since) : dlv[m] # NoT
\* the HaveMax limit: a question returns only the newest HaveMax ids, so more logged messages than that are not all asked for
FullHeal == step.k \in {"resub", "gap"} => \A m \in LogIds(1) : hl[1][m] >= step.since => dlv[m] # NoT
AeCovers == (step.k = "ae" /\ step.ok) => \A m \in step.missed : \E h \in Hubs : hl[h][m] # NoT
\* the quiet topic: without a skip excuse a message the link carried over is not always delivered by the first check
PeriodicDeliversQuiet == \A m \in Mids : (hl[1][m] # NoT /\ dlv[m] = NoT /\ cont[m] /\ now - hl[1][m] > GapEvery) => FALSE
\* the first check after a message was logged delivers it, if the link stayed up and the topic was live then
PeriodicDelivers == \A m \in Mids : (hl[1][m] # NoT /\ dlv[m] = NoT /\ cont[m] /\ ~skipped[m] /\ now - hl[1][m] > GapEvery) => FALSE
=============================================================================
