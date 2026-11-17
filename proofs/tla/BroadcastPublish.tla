----------------------------- MODULE BroadcastPublish -----------------------------
(***************************************************************************)
(* Publishing in vinc-broadcast publish.rs and frames.rs (on_pack), step   *)
(* for step: send_publish (FANP to the primary and FAN to the others when  *)
(* every hub is up, else PUB to the primary), the pending entry with its   *)
(* retry clock, pub_retry (give up when strictly older than GiveUp; else   *)
(* every Retry the PUB goes to hubs[idx mod n] with idx counting from 1),  *)
(* on_pack, and fallback_step (the member-to-member push to the topic's    *)
(* subscribers, at most Batch per step, one step at publish and one at     *)
(* each retry, only while no hub is up, never twice to one subscriber,     *)
(* only to nodes the view lists and never to the publisher itself).        *)
(*                                                                         *)
(* The environment moves hubs up and down at any time (a partition), loses *)
(* any PACK, and lets time pass only to the next deadline                  *)
(* (pending_deadline: the earlier of next_try and t0 + GiveUp + 1), where  *)
(* the host runs the timer. A hub that is up when a frame is sent stores a *)
(* PUB or FANP (and a FAN) at once; Node's AckOnlyStored shows that a PACK *)
(* follows only a store of this message. A hub in Rivals already holds the *)
(* id for another message: it stores nothing and, by the code's rule, sends*)
(* no PACK (AckById is the old rule, which acknowledged any known id and   *)
(* is kept as a witness).                                                  *)
(*                                                                         *)
(* Checked: PendingBound (a pending publish is never older than GiveUp + 1 *)
(* ticks); GiveUpExact (the give-up happens exactly at the first instant   *)
(* strictly older than GiveUp); AckImpliesStored (a PACK ends the publish  *)
(* only after a hub stored this very message, and no hub holding the id   *)
(* for another message acknowledges it: the publish ends in the give-up); RetryCadence (every retry is at   *)
(* least Retry after the previous step and goes to the hub the index       *)
(* names); FanShape (the fan out iff every hub was up); ReachBound (with a hub that stays up and PACKs that   *)
(* arrive, the publish is acknowledged within Retry * hubs, when no rival holds the id); TakenGivesUp (all hubs holding it for another message: never acknowledged); the fallback: *)
(* it fires only while no hub is up (FallbackOnlyNoHub), at most Batch per *)
(* step, no repeat, only subscribers in view that are reachable, never the *)
(* publisher (FallbackBound), and with every hub unreachable every         *)
(* reachable subscriber has the message by t0 + Retry * (steps - 1)        *)
(* (FallbackDelivers). FallbackCeiling is the finding of the _ceiling      *)
(* config: more than Batch * (GiveUp / Retry + 1) subscribers cannot all   *)
(* be reached before the publish is given up (248 of the default 256).     *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/BroadcastPublish.lean.               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Retry, GiveUp, Batch, MaxNow, NHubs, PeerSet, InView, Reach, Me, AlwaysUp, PackReliable, Churn, Rivals, AckById

Sub(a, b) == IF a >= b THEN a - b ELSE 0
Hub == 1..NHubs
RECURSIVE SortSet(_)
SortSet(S) == IF S = {} THEN <<>> ELSE LET m == CHOOSE x \in S : \A y \in S : x <= y IN <<m>> \o SortSet(S \ {m})
\* the subscribers in id order, as the code keeps them
Peers == SortSet(PeerSet)
NoP == [none |-> TRUE]
Primary == 1

VARIABLES now, up, pend, outcome, stored, ackers, served, evs, nsteps, t0, lastT, mode, hubSent, started
vars == <<now, up, pend, outcome, stored, ackers, served, evs, nsteps, t0, lastT, mode, hubSent, started>>

\* on_msg: a hub acknowledges a known id only for the message it stored; a hub in Rivals holds another one
Acks(h) == h \notin Rivals \/ AckById

AnyUp == \E h \in Hub : up[h]
AllUp == \A h \in Hub : up[h]

\* publish.rs fallback_step: serve up to Batch peers (list order) that are in view, reachable and not served yet
RECURSIVE Fall(_, _, _, _)
Fall(i, srv, sent, acc) ==
    IF i > Len(Peers) \/ sent >= Batch THEN [srv |-> srv, sent |-> sent, acc |-> acc]
    ELSE LET p == Peers[i]
         IN IF p = Me \/ p \in srv \/ p \notin InView THEN Fall(i + 1, srv, sent, acc)
            ELSE IF p \in Reach THEN Fall(i + 1, srv \union {p}, sent + 1, Append(acc, p))
            ELSE Fall(i + 1, srv, sent, acc)

Init == /\ now = 0 /\ up \in [Hub -> BOOLEAN] /\ pend = NoP /\ outcome = "none" /\ stored = {} /\ ackers = {}
        /\ served = {} /\ evs = <<>> /\ nsteps = 0 /\ t0 = 0 /\ lastT = 0 /\ mode = "none" /\ hubSent = 0 /\ started = FALSE
        /\ \A h \in AlwaysUp : up[h]

\* publish: FANP to the primary and FAN to the others when every hub is up, else PUB to the primary; a taken
\* PUB or FANP is stored and will be acknowledged, a taken FAN is stored without an acknowledgement
Publish ==
    /\ ~started /\ now = 0
    /\ LET fan == AllUp
           stSet == IF fan THEN Hub ELSE IF up[Primary] THEN {Primary} ELSE {}
           ak == IF up[Primary] /\ Acks(Primary) THEN {Primary} ELSE {}
           fb == IF AnyUp THEN [srv |-> {}, sent |-> 0, acc |-> <<>>] ELSE Fall(1, {}, 0, <<>>)
       IN /\ stored' = stSet \ Rivals /\ ackers' = ak /\ mode' = IF fan THEN "fan" ELSE "single"
          /\ served' = fb.srv /\ evs' = fb.acc /\ nsteps' = 1 /\ lastT' = now
          /\ pend' = [next |-> now + Retry, idx |-> 0] /\ started' = TRUE
    /\ UNCHANGED <<now, up, outcome, t0, hubSent>>

\* on_pack: a hub that stored a PUB or FANP acknowledges; the frame may be lost (PackReliable fixes it)
Pack == \E h \in ackers :
    /\ pend # NoP /\ up[h]
    /\ pend' = NoP /\ outcome' = "acked"
    /\ UNCHANGED <<now, up, stored, ackers, served, evs, nsteps, t0, lastT, mode, hubSent, started>>

\* pub_retry
GiveUpStep ==
    /\ pend # NoP /\ Sub(now, t0) > GiveUp
    /\ pend' = NoP /\ outcome' = "gaveup" /\ evs' = <<>>
    /\ UNCHANGED <<now, up, stored, ackers, served, nsteps, t0, lastT, mode, hubSent, started>>

RetryStep ==
    /\ pend # NoP /\ Sub(now, t0) <= GiveUp /\ now >= pend.next
    /\ LET idx == pend.idx + 1
           hub == (idx % NHubs) + 1
           fb == IF AnyUp THEN [srv |-> served, sent |-> 0, acc |-> <<>>] ELSE Fall(1, served, 0, <<>>)
       IN /\ stored' = IF up[hub] /\ hub \notin Rivals THEN stored \union {hub} ELSE stored
          /\ ackers' = IF up[hub] /\ Acks(hub) THEN ackers \union {hub} ELSE ackers
          /\ pend' = [next |-> now + Retry, idx |-> idx]
          /\ served' = fb.srv /\ evs' = fb.acc /\ nsteps' = nsteps + 1 /\ hubSent' = hub
    /\ lastT' = now
    /\ UNCHANGED <<now, up, outcome, t0, mode, started>>

Partition == /\ Churn /\ \E h \in Hub \ AlwaysUp : up' = [up EXCEPT ![h] = ~@]
             /\ UNCHANGED <<now, pend, outcome, stored, ackers, served, evs, nsteps, t0, lastT, mode, hubSent, started>>

Deadline == IF pend = NoP THEN MaxNow + 1 ELSE IF pend.next < t0 + GiveUp + 1 THEN pend.next ELSE t0 + GiveUp + 1
Tick == /\ now < MaxNow /\ now < Deadline /\ now' = now + 1 /\ evs' = <<>>
        /\ ~(PackReliable /\ pend # NoP /\ \E h \in ackers : up[h])
        /\ UNCHANGED <<up, pend, outcome, stored, ackers, served, nsteps, t0, lastT, mode, hubSent, started>>

Next == Publish \/ Pack \/ GiveUpStep \/ RetryStep \/ Partition \/ Tick
Spec == Init /\ [][Next]_vars

(* ---------------------------- the checked properties ---------------------------- *)
Target == (PeerSet \cap InView \cap Reach) \ {Me}
TypeOK == served \subseteq PeerSet /\ outcome \in {"none", "acked", "gaveup"}

PendingBound == pend # NoP => now - t0 <= GiveUp + 1
GiveUpExact == [][ (outcome = "none" /\ outcome' = "gaveup") => now = t0 + GiveUp + 1 ]_vars
AckImpliesStored == (outcome = "acked" => ackers # {}) /\ ackers \subseteq stored
\* every hub holds the id for another message: no acknowledgement ever comes, the publisher gives up
TakenGivesUp == Rivals = Hub => outcome # "acked"
RetryCadence == [][ RetryStep => (now - lastT >= Retry /\ hubSent' = ((pend.idx + 1) % NHubs) + 1) ]_vars
FanShape == [][ Publish => (AllUp => stored' = Hub \ Rivals /\ mode' = "fan") /\ (~AllUp => mode' = "single" /\ stored' \subseteq {Primary}) ]_vars
FallbackOnlyNoHub == [][ (evs' # <<>> /\ nsteps' > nsteps) => ~AnyUp ]_vars
FallbackFirst == [][ (Publish /\ evs' # <<>>) => ~AnyUp ]_vars
FallbackBound == /\ Cardinality(served) <= Batch * nsteps /\ served \subseteq Target /\ Len(evs) <= Batch
FallbackNoRepeat == [][ \A i \in 1..Len(evs') : evs'[i] \notin served \/ evs'[i] \in served' ]_vars
\* with every hub down for ever, every reachable subscriber has the message by t0 + Retry * (steps - 1)
Steps == (Cardinality(Target) + Batch - 1) \div Batch
FallbackDelivers == (started /\ ~AnyUp /\ outcome = "none" /\ now - t0 >= Retry * (Steps - 1) /\ Steps <= nsteps)
                      => served = Target
ReachBound == (started /\ AlwaysUp # {} /\ PackReliable /\ now - t0 >= Retry * NHubs + 1 /\ Sub(now, t0) <= GiveUp)
                => outcome = "acked"
\* the finding: after the give-up not every subscriber was reached
AllServedAtGiveUp == outcome = "gaveup" => served = Target
=============================================================================
