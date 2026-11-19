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
(* carries fresh = FALSE and adds nothing to the account. Whichever message  *)
(* of a transfer arrives first accounts for its copies (ghost landed): a     *)
(* retransmission may overtake the original, and the original is then a      *)
(* repeat.                                                                  *)
(*                                                                          *)
(* Every hold of the net model is a transmission of the same bundle (a     *)
(* retransmission is a repeat of it), so a hold refused for any reason      *)
(* (repeated, finished, a full table) drops its copies, like a lost message. *)
(*                                                                          *)
(* Checked: held + in flight + dropped + released = Budget at every step     *)
(* (no loss), held <= Budget with loss and in the four-node config           *)
(* DtnForwardNet_over, and a node never holds a copy it was not given.      *)
(* These hold because a node remembers every bundle it accepted until its   *)
(* expiry (the memory table of DtnForwardOps.tla): a retransmitted hold     *)
(* that reaches a node after it released the bundle is refused (Finished),   *)
(* so the copies the budget already counted are never re-created. The ghost *)
(* flag replayed records an accepted hold at a node that had released the   *)
(* bundle (the bundle never expires within the horizon, exp = MaxTime + 5); *)
(* NoReplay (config DtnForwardNet_replay) checks that it never happens.     *)
(* Lean counterpart: Pinc/DtnForwardInv.lean (balance, per node) and        *)
(* Pinc/DtnForwardWitness.lean.                                             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Budget, MaxTime, Retry, MaxSends, Loss, MaxMsgs, NN, L, T, D
VARIABLES nf, msgs, t, dropped, released, delivered, replayed, rel, landed, seq
vars == <<nf, msgs, t, dropped, released, delivered, replayed, rel, landed, seq>>

Nodes == 1..NN
Dest == NN
\* the contacts that can happen: all pairs of three nodes, or a source, a relay, a neighbour and the destination
Edges == IF NN = 3 THEN {<<1, 2>>, <<1, 3>>, <<2, 3>>} ELSE {<<1, 2>>, <<2, 3>>, <<2, 4>>}
F == INSTANCE DtnForwardOps WITH B <- 1

RECURSIVE SumH(_)
SumH(X) == IF X = {} THEN 0 ELSE LET n == CHOOSE n \in X : TRUE IN F!CopiesHeld(nf[n], 1) + SumH(X \ {n})
Held == SumH(Nodes)
\* the copies of the transfers whose first message has not arrived yet (a retransmission is a repeat, never more copies)
InFlight == LET fresh == {m \in msgs : m.fresh /\ <<m.from, m.to>> \notin landed} IN
    IF fresh = {} THEN 0 ELSE LET RECURSIVE S(_) S(X) == IF X = {} THEN 0 ELSE LET m == CHOOSE m \in X : TRUE IN m.copies + S(X \ {m}) IN S(fresh)

Init == /\ nf = [n \in Nodes |-> IF n = 1 THEN F!Step(F!New(0), 0, [k |-> "hold", id |-> 1, dest |-> Dest, exp |-> MaxTime + 5, copies |-> Budget]).f ELSE F!New(0)]
        /\ msgs = {} /\ t = 0 /\ dropped = 0 /\ released = 0 /\ delivered = FALSE /\ replayed = FALSE /\ rel = {} /\ landed = {} /\ seq = 0

SetN(n, g) == [nf EXCEPT ![n] = g]

\* a contact between a and b: both nodes learn the link state
Contact(a, b, up) ==
    /\ a < b /\ <<a, b>> \in Edges
    /\ LET k == IF up THEN "up" ELSE "down"
           ra == F!Step(nf[a], t, [k |-> k, peer |-> b])
           rb == F!Step(nf[b], t, [k |-> k, peer |-> a]) IN
       /\ nf' = [nf EXCEPT ![a] = ra.f, ![b] = rb.f]
    /\ UNCHANGED <<msgs, t, dropped, released, delivered, replayed, rel, landed, seq>>

\* time passes for everyone
Tick == /\ t < MaxTime
        /\ nf' = [n \in Nodes |-> F!Step(nf[n], t + 1, [k |-> "tick"]).f]
        /\ t' = t + 1
        /\ UNCHANGED <<msgs, dropped, released, delivered, replayed, rel, landed, seq>>

PollN(n) == LET r == F!Poll(nf[n]) IN
    /\ (r.f # nf[n] \/ r.act.k # "none")
    /\ nf' = SetN(n, r.f)
    /\ CASE r.act.k = "send" ->
              /\ Cardinality(msgs) < MaxMsgs
              /\ msgs' = msgs \cup {[id |-> seq, from |-> n, to |-> r.act.peer, copies |-> r.act.copies, fresh |-> ~r.act.retr]}
              /\ seq' = seq + 1
              /\ UNCHANGED <<dropped, released, delivered, replayed, rel, landed>>
         [] r.act.k = "release" ->
              /\ released' = released + F!CopiesHeld(nf[n], 1)
              /\ rel' = rel \cup {n}
              /\ UNCHANGED <<msgs, dropped, delivered, replayed, landed, seq>>
         [] OTHER -> UNCHANGED <<msgs, dropped, released, delivered, replayed, rel, landed, seq>>
    /\ UNCHANGED t

Deliver(m) ==
    /\ m \in msgs
    /\ msgs' = msgs \ {m}
    /\ LET ack == F!Step(nf[m.from], t, [k |-> "ack", peer |-> m.to, id |-> 1]) IN
       IF m.to = Dest
       THEN /\ delivered' = TRUE
            /\ nf' = SetN(m.from, ack.f)
            /\ landed' = landed \cup {<<m.from, m.to>>}
            /\ UNCHANGED <<dropped, released, replayed, rel>>
       ELSE LET h == F!Step(nf[m.to], t, [k |-> "hold", id |-> 1, dest |-> Dest, exp |-> MaxTime + 5, copies |-> m.copies])
                nf1 == SetN(m.to, h.f)
                ack2 == F!Step(nf1[m.from], t, [k |-> "ack", peer |-> m.to, id |-> 1]) IN
            /\ nf' = [nf1 EXCEPT ![m.from] = ack2.f]
            /\ dropped' = IF h.err # "ok" /\ <<m.from, m.to>> \notin landed THEN dropped + m.copies ELSE dropped
            /\ landed' = landed \cup {<<m.from, m.to>>}
            /\ replayed' = (replayed \/ (h.err = "ok" /\ m.to \in rel))
            /\ UNCHANGED <<released, delivered, rel>>
    /\ UNCHANGED <<t, seq>>

Lose(m) == /\ Loss = 1 /\ m \in msgs /\ msgs' = msgs \ {m}
           /\ dropped' = IF m.fresh /\ <<m.from, m.to>> \notin landed THEN dropped + m.copies ELSE dropped
           /\ UNCHANGED <<nf, t, released, delivered, replayed, rel, landed, seq>>

Next == \/ \E a, b \in Nodes, up \in BOOLEAN : Contact(a, b, up)
        \/ Tick
        \/ \E n \in Nodes : PollN(n)
        \/ \E m \in msgs : Deliver(m) \/ Lose(m)

Spec == Init /\ [][Next]_vars

Account == Held + InFlight + dropped + released = Budget
HeldLeBudget == Held <= Budget
Misc == \A n \in Nodes : \A i \in 1..1 : nf[n].bs[i].full => nf[n].bs[i].copies >= 1
\* no node accepts a hold of a bundle it released
NoReplay == ~replayed
\* held copies never exceed the budget (the same bound as HeldLeBudget, checked on its own at four nodes)
HeldAlways == Held <= Budget
=============================================================================
