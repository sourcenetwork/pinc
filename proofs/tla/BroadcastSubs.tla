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
(* TableBound (entries per topic stay within TableMax; past it a SUB is    *)
(* ignored, as in the code).                                               *)
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

\* on_sub: record the subscriber live (an unknown member only if the table has room)
Sub == \E m \in Members, t \in Topics :
    /\ IF subs[t][m] # "none" \/ Cardinality(Entries(t)) < TableMax
       THEN subs' = [subs EXCEPT ![t][m] = "live"] ELSE UNCHANGED subs
    /\ step' = NoStep

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
=============================================================================
