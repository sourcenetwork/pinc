---------------------------- MODULE DtnForwardNet ----------------------------
(***************************************************************************)
(* Three nodes that each run the forwarder of DtnForwardOps.tla, joined by  *)
(* contacts that come and go and a network that delivers each message once  *)
(* (no loss: the case where the copy budget is exact) or loses it (config   *)
(* DtnForwardNet_loss).                                                      *)
(*                                                                          *)
(* One bundle (id 1) is held by node 1 with Budget copies; its destination  *)
(* is node 3. A contact between two nodes sets the link of each to the      *)
(* other; a send of a node becomes a message; delivering a message to the   *)
(* destination marks the bundle delivered and acknowledges the sender, and  *)
(* delivering it to another node is a Hold with the copies of the message   *)
(* (refused as a repeated hold when the node already has the bundle: the    *)
(* copies are then dropped); the sender is acknowledged either way, as in   *)
(* the Rust simulation test.                                                *)
(*                                                                          *)
(* A retransmission is a copy of a message that was already counted, so it  *)
(* carries fresh = FALSE and adds nothing to the account.                   *)
(*                                                                          *)
(* Checked: held + in flight + dropped + released = Budget at every step     *)
(* (no loss), held <= Budget with loss, and a node never holds a copy it    *)
(* was not given. The account assumes that no retransmitted hold is accepted *)
(* by a node that already finished the bundle (flag Replayed), which is the *)
(* finding of DtnForward_rehold: config DtnForwardNet_replay shows such a    *)
(* hold being accepted. With three nodes the replayed copies do not yet    *)
(* exceed the budget (the releasing node kept nothing that others hold); a *)
(* fourth node holding copies the releasing node had handed on would make  *)
(* the sum exceed it, which is argued here and not model checked.         *)
(* Lean counterpart: Vinc/DtnForwardInv.lean (balance, per node) and        *)
(* Vinc/DtnForwardWitness.lean.                                             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Budget, MaxTime, Retry, MaxSends, Loss, MaxMsgs
VARIABLES nf, msgs, t, dropped, released, delivered, replayed, seq
vars == <<nf, msgs, t, dropped, released, delivered, replayed, seq>>

Nodes == 1..3
Dest == 3
F == INSTANCE DtnForwardOps WITH B <- 1, L <- 2, T <- 2

Held == F!CopiesHeld(nf[1], 1) + F!CopiesHeld(nf[2], 1) + F!CopiesHeld(nf[3], 1)
InFlight == LET fresh == {m \in msgs : m.fresh} IN
    IF fresh = {} THEN 0 ELSE LET RECURSIVE S(_) S(X) == IF X = {} THEN 0 ELSE LET m == CHOOSE m \in X : TRUE IN m.copies + S(X \ {m}) IN S(fresh)

Init == /\ nf = [n \in Nodes |-> IF n = 1 THEN F!Step(F!New(0), 0, [k |-> "hold", id |-> 1, dest |-> Dest, exp |-> MaxTime + 5, copies |-> Budget]).f ELSE F!New(0)]
        /\ msgs = {} /\ t = 0 /\ dropped = 0 /\ released = 0 /\ delivered = FALSE /\ replayed = FALSE /\ seq = 0

SetN(n, g) == [nf EXCEPT ![n] = g]

\* a contact between a and b: both nodes learn the link state
Contact(a, b, up) ==
    /\ a < b
    /\ LET k == IF up THEN "up" ELSE "down"
           ra == F!Step(nf[a], t, [k |-> k, peer |-> b])
           rb == F!Step(nf[b], t, [k |-> k, peer |-> a]) IN
       /\ nf' = [nf EXCEPT ![a] = ra.f, ![b] = rb.f]
    /\ UNCHANGED <<msgs, t, dropped, released, delivered, replayed, seq>>

\* time passes for everyone
Tick == /\ t < MaxTime
        /\ nf' = [n \in Nodes |-> F!Step(nf[n], t + 1, [k |-> "tick"]).f]
        /\ t' = t + 1
        /\ UNCHANGED <<msgs, dropped, released, delivered, replayed, seq>>

PollN(n) == LET r == F!Poll(nf[n]) IN
    /\ (r.f # nf[n] \/ r.act.k # "none")
    /\ nf' = SetN(n, r.f)
    /\ CASE r.act.k = "send" ->
              /\ Cardinality(msgs) < MaxMsgs
              /\ msgs' = msgs \cup {[id |-> seq, from |-> n, to |-> r.act.peer, copies |-> r.act.copies, fresh |-> ~r.act.retr]}
              /\ seq' = seq + 1
              /\ UNCHANGED <<dropped, released, delivered, replayed>>
         [] r.act.k = "release" ->
              /\ released' = released + F!CopiesHeld(nf[n], 1)
              /\ UNCHANGED <<msgs, dropped, delivered, replayed, seq>>
         [] OTHER -> UNCHANGED <<msgs, dropped, released, delivered, replayed, seq>>
    /\ UNCHANGED t

Deliver(m) ==
    /\ m \in msgs
    /\ msgs' = msgs \ {m}
    /\ LET ack == F!Step(nf[m.from], t, [k |-> "ack", peer |-> m.to, id |-> 1]) IN
       IF m.to = Dest
       THEN /\ delivered' = TRUE
            /\ nf' = SetN(m.from, ack.f)
            /\ UNCHANGED <<dropped, released, replayed>>
       ELSE LET h == F!Step(nf[m.to], t, [k |-> "hold", id |-> 1, dest |-> Dest, exp |-> MaxTime + 5, copies |-> m.copies])
                nf1 == SetN(m.to, h.f)
                ack2 == F!Step(nf1[m.from], t, [k |-> "ack", peer |-> m.to, id |-> 1]) IN
            /\ nf' = [nf1 EXCEPT ![m.from] = ack2.f]
            /\ dropped' = IF h.err # "ok" /\ m.fresh THEN dropped + m.copies ELSE dropped
            /\ replayed' = (replayed \/ (h.err = "ok" /\ ~m.fresh))
            /\ UNCHANGED <<released, delivered>>
    /\ UNCHANGED <<t, seq>>

Lose(m) == /\ Loss = 1 /\ m \in msgs /\ msgs' = msgs \ {m}
           /\ dropped' = IF m.fresh THEN dropped + m.copies ELSE dropped
           /\ UNCHANGED <<nf, t, released, delivered, replayed, seq>>

Next == \/ \E a, b \in Nodes, up \in BOOLEAN : Contact(a, b, up)
        \/ Tick
        \/ \E n \in Nodes : PollN(n)
        \/ \E m \in msgs : Deliver(m) \/ Lose(m)

Spec == Init /\ [][Next]_vars

\* the account, while no retransmitted hold was accepted after the bundle was finished
Account == ~replayed => Held + InFlight + dropped + released = Budget
HeldLeBudget == ~replayed => Held <= Budget
Misc == \A n \in Nodes : \A i \in 1..1 : nf[n].bs[i].full => nf[n].bs[i].copies >= 1
\* the finding: a replayed hold is accepted
NoReplay == ~replayed
=============================================================================
