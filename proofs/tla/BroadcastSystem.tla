----------------------------- MODULE BroadcastSystem -----------------------------
(***************************************************************************)
(* The scenarios of pinc-broadcast at system level: two hubs, a publisher  *)
(* P and subscribers S (several), with churn (any link cut or healed), the *)
(* late publish (P and a subscriber cut off from every hub but able to     *)
(* reach each other), hub failover (a subscriber whose primary is           *)
(* unreachable moves to the other hub and asks again) and a subscriber     *)
(* restart that gathers the replay floors the hubs kept.                   *)
(*                                                                         *)
(* The components are the ones the other models check in detail; here they *)
(* are the steps that matter at this level, each mirroring one function:   *)
(*  PubToHub     publish.rs + msg.rs hub_store: the hub logs the message,  *)
(*               mirrors it to the other hub over a live link, pushes it   *)
(*               to a subscriber whose primary it is (floors: noted)       *)
(*  Fallback     publish.rs fallback_step: only while P reaches no hub     *)
(*  Repair       gap.rs SUB, HAVE, GET, MSG: a subscriber asks its primary *)
(*               for the log (since covers every logged message: the       *)
(*               BroadcastRepair invariant SinceCoversMissed)              *)
(*  Failover     gap.rs primary_changed, then Repair at the new primary    *)
(*  HubAe        gap.rs hub_ae: the hubs exchange the ids of the window    *)
(*  Restart      a new life of a subscriber: empty dedupe set; floors from *)
(*               every hub judge what an earlier life took as old          *)
(*  Flip         a link goes down or up (a budget bounds the churn)        *)
(* Delivery is through Offer: a message the dedupe set holds or a floor    *)
(* covers is not delivered again.                                          *)
(*                                                                         *)
(* Safety: AtMostOnce (a subscriber's application hears each message at    *)
(* most once across all lives: dedupe within a life, floors across);       *)
(* FloorsCover (every message a hub sent a subscriber is old for it after  *)
(* a restart). Liveness (weak fairness of the steps): LateLive (the late   *)
(* publish: every subscriber has the message), ChurnHeals (once the links  *)
(* stay up every subscriber has the message), FailoverDelivers (with the   *)
(* primary hub lost for good and the other up, every subscriber has it).   *)
(* The _fb config shows that a message only the fallback delivered can be  *)
(* delivered again after a restart (AtMostOnceStrict fails).                                         *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/BroadcastSystem.lean.                *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Subs, MaxFlips, MaxRestarts, Fallback0

Hubs == {1, 2}
\* links: <<0, h>>, <<s, h>>, <<0, s>>, <<1, 2>> hub-hub
Nodes == {0} \union Subs
LinkIds == {<<0, 1>>, <<0, 2>>, <<1, 2>>} \union {<<s, h>> : s \in Subs, h \in Hubs} \union {<<0, s>> : s \in Subs}

VARIABLES up, pubd, hubLog, deliv, primary, sent, floor, count, nf, nr, fbOnly
vars == <<up, pubd, hubLog, deliv, primary, sent, floor, count, nf, nr, fbOnly>>

\* delivered in this life (set), floor set learned at restart, sent[h][s] the messages the hub sent s
Init == /\ up = [l \in LinkIds |-> TRUE] /\ pubd = FALSE /\ hubLog = [h \in Hubs |-> FALSE] /\ deliv = [s \in Subs |-> FALSE]
        /\ primary = [s \in Subs |-> 1] /\ sent = [h \in Hubs |-> [s \in Subs |-> FALSE]] /\ floor = [s \in Subs |-> FALSE]
        /\ count = [s \in Subs |-> 0] /\ nf = 0 /\ nr = 0 /\ fbOnly = [s \in Subs |-> FALSE]

\* Offer at s: a message already seen in this life, or covered by the floor, is not delivered again
Offer(s) == IF deliv[s] \/ floor[s] THEN [d |-> deliv, c |-> count] ELSE [d |-> [deliv EXCEPT ![s] = TRUE], c |-> [count EXCEPT ![s] = @ + 1]]

Publish == /\ ~pubd /\ pubd' = TRUE /\ UNCHANGED <<up, hubLog, deliv, primary, sent, floor, count, nf, nr, fbOnly>>

\* P hands the message to hub h over a live link; h logs it, mirrors it, and pushes it to its subscribers
PubToHub == \E h \in Hubs :
    /\ pubd /\ up[<<0, h>>] /\ ~hubLog[h]
    /\ LET o == 3 - h
           mir == up[<<1, 2>>]
           pushTo(hh, s) == hubLog'[hh] /\ primary[s] = hh /\ up[<<s, hh>>]
       IN /\ hubLog' = [hh \in Hubs |-> IF hh = h \/ (hh = o /\ mir) THEN TRUE ELSE hubLog[hh]]
          /\ \E push \in [Subs -> BOOLEAN] :   \* a live session may swallow the frame
               /\ LET pushed == {s \in Subs : push[s] /\ pushTo(primary[s], s) /\ (primary[s] = h \/ mir)}
                  IN /\ deliv' = [s \in Subs |-> IF s \in pushed THEN Offer(s).d[s] ELSE deliv[s]]
                     /\ count' = [s \in Subs |-> IF s \in pushed THEN Offer(s).c[s] ELSE count[s]]
                     /\ sent' = [hh \in Hubs |-> [s \in Subs |-> IF s \in pushed /\ primary[s] = hh THEN TRUE ELSE sent[hh][s]]]
    /\ UNCHANGED <<up, pubd, primary, floor, nf, nr, fbOnly>>

\* publish.rs fallback: while P reaches no hub, over a member link to a subscriber
FallbackStep == \E s \in Subs :
    /\ pubd /\ ~up[<<0, 1>>] /\ ~up[<<0, 2>>] /\ up[<<0, s>>]
    /\ deliv' = Offer(s).d /\ count' = Offer(s).c
    /\ fbOnly' = [fbOnly EXCEPT ![s] = @ \/ ~(deliv[s] \/ floor[s] \/ sent[1][s] \/ sent[2][s])]
    /\ UNCHANGED <<up, pubd, hubLog, primary, sent, floor, nf, nr>>

\* SUB(since), HAVE, GET, MSG at the primary
Repair == \E s \in Subs :
    /\ up[<<s, primary[s]>>] /\ hubLog[primary[s]]
    /\ deliv' = Offer(s).d /\ count' = Offer(s).c
    /\ sent' = [h \in Hubs |-> [x \in Subs |-> IF h = primary[s] /\ x = s /\ ~(deliv[s] \/ floor[s]) THEN TRUE ELSE sent[h][x]]]
    /\ UNCHANGED <<up, pubd, hubLog, primary, floor, nf, nr, fbOnly>>

\* primary_changed: a subscriber whose primary is unreachable moves to the other hub
Failover == \E s \in Subs :
    /\ ~up[<<s, primary[s]>>] /\ up[<<s, 3 - primary[s]>>]
    /\ primary' = [primary EXCEPT ![s] = 3 - primary[s]]
    /\ UNCHANGED <<up, pubd, hubLog, deliv, sent, floor, count, nf, nr, fbOnly>>

HubAe == \E h \in Hubs :
    /\ up[<<1, 2>>] /\ hubLog[h] /\ ~hubLog[3 - h]
    /\ hubLog' = [hubLog EXCEPT ![3 - h] = TRUE]
    /\ UNCHANGED <<up, pubd, deliv, primary, sent, floor, count, nf, nr, fbOnly>>

\* a subscriber starts a new life: the dedupe set is empty and the floors of every hub (what they sent it) apply
Restart == \E s \in Subs :
    /\ nr < MaxRestarts /\ nr' = nr + 1
    /\ deliv' = [deliv EXCEPT ![s] = FALSE]
    /\ floor' = [floor EXCEPT ![s] = floor[s] \/ sent[1][s] \/ sent[2][s]]
    /\ UNCHANGED <<up, pubd, hubLog, primary, sent, count, nf, fbOnly>>

Flip == \E l \in LinkIds : nf < MaxFlips /\ nf' = nf + 1 /\ up' = [up EXCEPT ![l] = ~@]
        /\ UNCHANGED <<pubd, hubLog, deliv, primary, sent, floor, count, nr, fbOnly>>

Next == Publish \/ PubToHub \/ FallbackStep \/ Repair \/ Failover \/ HubAe \/ Restart \/ Flip
Fair == WF_vars(Publish) /\ WF_vars(PubToHub) /\ WF_vars(Repair) /\ WF_vars(Failover) /\ WF_vars(HubAe) /\ WF_vars(FallbackStep)
Spec == Init /\ [][Next]_vars
LSpec == Spec /\ Fair

(* ---------------------------- the checked properties ---------------------------- *)
TypeOK == \A s \in Subs : count[s] \in 0..(1 + MaxRestarts)

\* the application hears the message at most once across the lives of the subscriber, unless its first delivery was
\* by the fallback alone: no hub sent it, so the floors of a restart do not name it (a node no hub ever sent to keeps
\* what is new by the clock, FRESH_KEEP)
AtMostOnce == \A s \in Subs : count[s] <= 1 \/ fbOnly[s]
\* the strict form fails: a message only the fallback delivered has no hub record, so a restart cannot tell it
AtMostOnceStrict == \A s \in Subs : count[s] <= 1

FloorsCover == \A s \in Subs, h \in Hubs : sent[h][s] => (floor[s] \/ deliv[s] \/ nr = 0)

AllDelivered == \A s \in Subs : count[s] >= 1
Stable == \A l \in LinkIds : up[l]
\* the late publish: P and every subscriber are cut off from both hubs and can reach each other
LateCond == /\ ~up[<<0, 1>>] /\ ~up[<<0, 2>>] /\ \A s \in Subs : ~up[<<s, 1>>] /\ ~up[<<s, 2>>] /\ up[<<0, s>>]
\* the primary hub lost for good, everything else up
FailCond == \A l \in LinkIds : up[l] <=> (l[1] # 1 /\ l[2] # 1)
LateLive == []LateCond => <>AllDelivered
ChurnHeals == (<>[]Stable) => <>AllDelivered
FailoverDelivers == []FailCond => <>AllDelivered
=============================================================================
