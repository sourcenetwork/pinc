------------------------------ MODULE PunchChain ------------------------------
(***************************************************************************)
(* A punch between two ends behind translators that map every destination *)
(* to a new external port and admit anyone to a port they handed out      *)
(* (pinc-transport conn/path.rs start_punch, challenge_back,               *)
(* on_path_response, back_left; conn/recv.rs, which learns a path from     *)
(* each new source after authentication; pinc-connect client/drive.rs,     *)
(* which punches again on the Puncher's schedule and for each candidate a *)
(* peer's REACH_OUT lists).                                                *)
(*                                                                         *)
(* The story. Each end sends the P punch probes (path challenges) of a     *)
(* round. Every datagram arrives from a port the receiver has not seen, so *)
(* it is a new path: a challenge on it is answered there with a response,  *)
(* and the answer carries a challenge of its own while the end's budget    *)
(* lasts (challenge_back, back_left: CB per round). The answer leaves the  *)
(* answering end's translator from yet another port, so a response never   *)
(* comes back on the path its challenge left on and never validates it     *)
(* (on_path_response); a challenge carried with it is a challenge on a new *)
(* path again. An end starts a new round (Round: start_punch, which sets   *)
(* the probes to P and the budget to CB) on its own schedule or when the   *)
(* peer's REACH_OUT asks it to, up to R rounds; a validation also refills  *)
(* the budget, and none happens here. A challenge received refills         *)
(* nothing.                                                                *)
(*                                                                         *)
(* What must never happen: an end sends more than its probes and one      *)
(* answer per challenge it may receive, rounds[e] * P + rounds[peer] *     *)
(* (P + CB) datagrams (Cost: 2P + CB for one round each); the exchange     *)
(* always ends (Ends, under weak fairness).                                *)
(*                                                                         *)
(* RED configuration PunchChain_unbounded: every answer on a new path      *)
(* carries a challenge (the code before the bound of challenge_back), so   *)
(* the challenges answer each other without end. Cost fails.               *)
(* Witness PunchChain_w_reachout: with a second round, which the peer can  *)
(* ask for with a REACH_OUT, an end sends more than the 2P + CB of one     *)
(* round (CostOne fails): the budget is per round, and the rounds are the  *)
(* caller's to bound.                                                      *)
(*                                                                         *)
(* Why the earlier models let it through: PathMove gives each path a fixed *)
(* remote address, so an answer always returns on the path it answers and  *)
(* validates it; no model had a translator that changes the source port    *)
(* per destination.                                                        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS P, CB, R, UNBOUNDED

Side == {"a", "b"}
Peer(e) == IF e = "a" THEN "b" ELSE "a"
Kinds == {"ch", "rc", "r"}  \* a challenge, a response with a challenge, a response alone

VARIABLES probes, back, sent, wire, rounds
vars == <<probes, back, sent, wire, rounds>>

Init == /\ probes = [e \in Side |-> P]
        /\ back = [e \in Side |-> CB]
        /\ sent = [e \in Side |-> 0]
        /\ wire = [e \in Side |-> [k \in Kinds |-> 0]]
        /\ rounds = [e \in Side |-> 1]

Probe(e) == /\ probes[e] > 0
            /\ probes' = [probes EXCEPT ![e] = @ - 1]
            /\ sent' = [sent EXCEPT ![e] = @ + 1]
            /\ wire' = [wire EXCEPT ![Peer(e)]["ch"] = @ + 1]
            /\ UNCHANGED <<back, rounds>>

Recv(e, k) ==
    /\ wire[e][k] > 0
    /\ IF k = "r"
       THEN /\ wire' = [wire EXCEPT ![e]["r"] = @ - 1]
            /\ UNCHANGED <<back, sent>>
       ELSE LET more == UNBOUNDED \/ back[e] > 0
                ans == IF more THEN "rc" ELSE "r"
            IN  /\ wire' = [wire EXCEPT ![e][k] = @ - 1, ![Peer(e)][ans] = @ + 1]
                /\ back' = IF more /\ ~UNBOUNDED THEN [back EXCEPT ![e] = @ - 1] ELSE back
                /\ sent' = [sent EXCEPT ![e] = @ + 1]
    /\ UNCHANGED <<probes, rounds>>

\* start_punch: a new round, on the end's schedule or at the peer's REACH_OUT; the probes not sent yet are replaced
Round(e) == /\ rounds[e] < R
            /\ rounds' = [rounds EXCEPT ![e] = @ + 1]
            /\ probes' = [probes EXCEPT ![e] = P]
            /\ back' = [back EXCEPT ![e] = CB]
            /\ UNCHANGED <<sent, wire>>

Next == \E e \in Side : Probe(e) \/ Round(e) \/ \E k \in Kinds : Recv(e, k)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Cost == \A e \in Side : sent[e] <= rounds[e] * P + rounds[Peer(e)] * (P + CB)
CostOne == \A e \in Side : sent[e] <= 2 * P + CB
Quiet == \A e \in Side : probes[e] = 0 /\ rounds[e] = R /\ \A k \in Kinds : wire[e][k] = 0
Ends == <>[]Quiet
=============================================================================
