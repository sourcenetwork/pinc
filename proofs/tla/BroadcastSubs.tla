------------------------------ MODULE BroadcastSubs ------------------------------
(***************************************************************************)
(* Subscriptions on a hub across a member's absence, pinc-broadcast        *)
(* subs.rs and gap.rs (on_sub, on_unsub): SUB makes a member's entry live, *)
(* UNSUB removes it, hold keeps every live entry of a member but marks it  *)
(* held (nothing is pushed to it), restore makes the held entries live and *)
(* sends the member one RESTORED per topic it restored, release forgets    *)
(* the member's entries and publisher marks. A push goes to the live       *)
(* entries only. The environment applies any of these in any order.        *)
(*                                                                         *)
(* Checked: HeldGetsNoPush (a push reaches exactly the live entries);      *)
(* RestoreTellsExactly (the RESTORED frames of a restore name exactly the  *)
(* topics that were held for the member, no more and no fewer);            *)
(* RestoreOnlyHeld (a live entry is not told again, a released member is   *)
(* told nothing); HoldKeeps (a hold changes live entries to held and       *)
(* nothing else); ReleaseForgets (afterwards the member has no entry);     *)
(* TableBound (entries per topic stay within TableMax). A SUB is taken or  *)
(* answered with the hub-full notice, never dropped: the hub cannot hold   *)
(* it when its topic table has no room for a topic it has no entry of, or  *)
(* when the topic has TableMax subscribers. SubTakes (a SUB that is taken  *)
(* makes the entry live); NoticeOnlyWhenFull (the notice goes only to a    *)
(* member without an entry, at a full topic or a topic the hub could not   *)
(* add). BroadcastSubs_busy.cfg finds the notice sent (NoNotice violated). *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/BroadcastSubs.lean.                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Members, Topics, TableMax

VARIABLES subs, step
vars == <<subs, step>>
St == {"none", "live", "held"}
NoStep == [k |-> "none", member |-> 0, told |-> {}, pushed |-> {}, before |-> {}, topic |-> 0]

Entries(t) == {m \in Members : subs[t][m] # "none"}

Init == subs = [t \in Topics |-> [m \in Members |-> "none"]] /\ step = NoStep

\* on_sub: record the subscriber live (an unknown member only if the topic has room, and a topic the hub has no
\* entry of only if its topic table has room: room), else answer with the hub-full notice and change nothing
Sub == \E m \in Members, t \in Topics, room \in BOOLEAN :
    LET takes == subs[t][m] # "none" \/ ((room \/ Entries(t) # {}) /\ Cardinality(Entries(t)) < TableMax)
    IN IF takes
       THEN /\ subs' = [subs EXCEPT ![t][m] = "live"]
            /\ step' = [NoStep EXCEPT !.k = "sub", !.member = m, !.topic = t]
       ELSE /\ UNCHANGED subs
            /\ step' = [NoStep EXCEPT !.k = "notice", !.member = m, !.topic = t]

Unsub == \E m \in Members, t \in Topics : subs' = [subs EXCEPT ![t][m] = "none"] /\ step' = NoStep

\* subs.rs hold: live entries of the member become held
Hold == \E m \in Members :
    /\ subs' = [t \in Topics |-> [x \in Members |-> IF x = m /\ subs[t][x] = "live" THEN "held" ELSE subs[t][x]]]
    /\ step' = [NoStep EXCEPT !.k = "hold", !.member = m, !.before = {t \in Topics : subs[t][m] = "live"}]

\* subs.rs restore: held entries become live and the member is told each topic
Restore == \E m \in Members :
    /\ subs' = [t \in Topics |-> [x \in Members |-> IF x = m /\ subs[t][x] = "held" THEN "live" ELSE subs[t][x]]]
    /\ step' = [NoStep EXCEPT !.k = "restore", !.member = m, !.told = {t \in Topics : subs[t][m] = "held"},
                              !.before = {t \in Topics : subs[t][m] = "held"}]

\* subs.rs release: forget the member
Release == \E m \in Members :
    /\ subs' = [t \in Topics |-> [x \in Members |-> IF x = m THEN "none" ELSE subs[t][x]]]
    /\ step' = [NoStep EXCEPT !.k = "release", !.member = m]

\* hub_store: a message is pushed to the live entries of its topic
Push == \E t \in Topics :
    /\ step' = [NoStep EXCEPT !.k = "push", !.topic = t, !.pushed = {m \in Members : subs[t][m] = "live"}]
    /\ UNCHANGED subs

Next == Sub \/ Unsub \/ Hold \/ Restore \/ Release \/ Push
Spec == Init /\ [][Next]_vars

TypeOK == \A t \in Topics, m \in Members : subs[t][m] \in St

HeldGetsNoPush == step.k = "push" => step.pushed = {m \in Members : subs[step.topic][m] = "live"}
RestoreTellsExactly == step.k = "restore" =>
    /\ step.told = step.before
    /\ \A t \in step.told : subs[t][step.member] = "live"
RestoreOnlyHeld == step.k = "restore" => \A t \in Topics : subs[t][step.member] # "held"
HoldKeeps == step.k = "hold" => /\ \A t \in step.before : subs[t][step.member] = "held"
                                /\ \A t \in Topics : subs[t][step.member] # "live"
ReleaseForgets == step.k = "release" => \A t \in Topics : subs[t][step.member] = "none"
TableBound == \A t \in Topics : Cardinality(Entries(t)) <= TableMax
\* a SUB that is taken leaves the member's entry live
SubTakes == step.k = "sub" => subs[step.topic][step.member] = "live"
\* the notice goes only to a member without an entry, at a topic with TableMax entries or one the hub has none of
NoticeOnlyWhenFull == step.k = "notice" =>
    /\ subs[step.topic][step.member] = "none"
    /\ (Cardinality(Entries(step.topic)) >= TableMax \/ Entries(step.topic) = {})
\* witness only (BroadcastSubs_busy.cfg): TLC finds a SUB answered with the notice
NoNotice == step.k # "notice"
=============================================================================
