------------------------------ MODULE PunchChain ------------------------------
(***************************************************************************)
(* A punch between two ends behind translators that map every destination *)
(* to a new external port and admit anyone to a port they handed out      *)
(* (pinc-transport conn/path.rs start_punch, challenge_back,               *)
(* on_path_response; conn/recv.rs, which learns a path from each new       *)
(* source after authentication).                                           *)
(*                                                                         *)
(* The story. Each end sends its P punch probes (path challenges). Every   *)
(* datagram arrives from a port the receiver has not seen, so it is a new  *)
(* path: a challenge on it is answered there with a response, and the      *)
(* answer may carry a challenge of its own (challenge_back). The answer    *)
(* leaves the answering end's translator from yet another port, so a       *)
(* response never comes back on the path its challenge left on and never  *)
(* validates it (on_path_response); a challenge carried with it is a       *)
(* challenge on a new path again.                                          *)
(*                                                                         *)
(* What must never happen: an end sends more than its probes and an       *)
(* answer to each challenge it may receive, 2P + CB datagrams (Cost); the  *)
(* exchange always ends (Ends, under weak fairness).                       *)
(*                                                                         *)
(* RED configuration PunchChain_unbounded: every answer on a new path      *)
(* carries a challenge (the code before the bound of challenge_back), so   *)
(* the challenges answer each other without end. Cost fails.               *)
(*                                                                         *)
(* Why the earlier models let it through: PathMove gives each path a fixed *)
(* remote address, so an answer always returns on the path it answers and  *)
(* validates it; no model had a translator that changes the source port    *)
(* per destination.                                                        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS P, CB, UNBOUNDED

Side == {"a", "b"}
Peer(e) == IF e = "a" THEN "b" ELSE "a"
Kinds == {"ch", "rc", "r"}  \* a challenge, a response with a challenge, a response alone

VARIABLES probes, back, sent, wire
vars == <<probes, back, sent, wire>>

Init == /\ probes = [e \in Side |-> P]
        /\ back = [e \in Side |-> CB]
        /\ sent = [e \in Side |-> 0]
        /\ wire = [e \in Side |-> [k \in Kinds |-> 0]]

Probe(e) == /\ probes[e] > 0
            /\ probes' = [probes EXCEPT ![e] = @ - 1]
            /\ sent' = [sent EXCEPT ![e] = @ + 1]
            /\ wire' = [wire EXCEPT ![Peer(e)]["ch"] = @ + 1]
            /\ UNCHANGED back

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
    /\ UNCHANGED probes

Next == \E e \in Side : Probe(e) \/ \E k \in Kinds : Recv(e, k)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Cost == \A e \in Side : sent[e] <= 2 * P + CB
Quiet == \A e \in Side : probes[e] = 0 /\ \A k \in Kinds : wire[e][k] = 0
Ends == <>[]Quiet
=============================================================================
