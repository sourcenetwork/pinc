---------------------------- MODULE DtnScenario ----------------------------
(***************************************************************************)
(* Several nodes that each run the forwarder (DtnForwardOps.tla), the       *)
(* custody book and the charged ledger (DtnCustodyOps.tla, DtnStoreOps.tla) *)
(* joined by contacts that come and go and a network that delays, and with  *)
(* Loss = 1 loses, messages. The node-level operators are instantiated, not *)
(* restated: the system adds only the host glue below, which the Rust test  *)
(* tests/trace_dtn_scenario.rs implements with the real crate types.        *)
(*                                                                          *)
(* One bundle (id 1, 1 byte) is created at node 1 with Budget copies and is *)
(* addressed to node N. The host glue, per node:                            *)
(*  - origin: accept custody (previous = none) and Hold Budget copies       *)
(*  - tick: forwarder tick, then the book expires the ledger                *)
(*  - contact a b: forwarder LinkUp/LinkDown of each side                   *)
(*  - poll: Send  -> a message; a handover of copies (not a retransmission) *)
(*          is offered custody (book.offer) when Offerable                  *)
(*          Release -> book.delivered (the ledger drops the item)           *)
(*  - a bundle message at the destination: delivered, and an ack comes back *)
(*    at a relay: accept custody (store may refuse: the copies are dropped, *)
(*    no ack), then Hold (a repeated hold ignores the copies); an ack back  *)
(*  - an ack at the sender: forwarder Acked and book.on_ack (the signature  *)
(*    of the ack is the boolean valid = TRUE; invalid acks move nothing)    *)
(*  - pressure: the mailbox layer admits an item to the shared ledger; a    *)
(*    bundle evicted from the ledger is forgotten by the forwarder          *)
(* Offerable(n, p) is TRUE for every p (Ranked = 0) or only for p > n       *)
(* (Ranked = 1): see the finding below.                                     *)
(*                                                                          *)
(* Checked on every reachable state and step:                               *)
(*  Account       held + in flight + dropped + released = Budget (no        *)
(*                retransmitted hold accepted after the bundle finished)    *)
(*  HeldLeBudget  held <= Budget under loss                                 *)
(*  LedgerOk      every ledger is within its budget and every held bundle's *)
(*                item is custody (a node never loses custody behind its    *)
(*                back)                                                     *)
(*  CustodyExit   a node's custody record ends only by an ack consumed at   *)
(*                that node from exactly the node custody was offered to,   *)
(*                by delivery, or by expiry                                 *)
(*  CustodyAlive  until the bundle is delivered or expires, some node holds *)
(*                custody (needs Ranked = 1)                                *)
(*  A_TickExpires at expiry every ledger drops the bundle and every book    *)
(*                its record, whatever the links did                        *)
(*  A_FrozenDown  a tick never runs a timer whose link is down              *)
(*  DeliveredByExpiry  (witness only) the bundle is delivered by expiry     *)
(*  Served        (liveness, FairSpec) the bundle reaches its destination   *)
(* Side conditions of the liveness, all in the configs: contacts last until *)
(* the exchange is done (Lasting), time passes only when the network is     *)
(* quiet and not past the contact deadline until the Recur contacts were    *)
(* made (Gate), the Recur contacts recur (strong fairness), the transfer    *)
(* table has room (T = N - 1 = one transfer per peer) and the store admits  *)
(* custody (LedgerBudget >= 1).                                             *)
(*                                                                          *)
(* Finding (config DtnScenario_cycle): with Ranked = 0, an acknowledgement  *)
(* is accepted from the node custody was offered to however old it is, so a *)
(* stale ack of a first handover and the ack of a handover back relieve both*)
(* nodes of a custody cycle and no node keeps custody (the bundle stays as  *)
(* transit in the ledgers, evictable). Ranked = 1 (custody is offered only  *)
(* to a higher node) rules it out, which the Lean theorem custody_chain     *)
(* proves for every number of nodes. Lean: proofs/lean/Vinc/DtnScenario*.lean*)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS N, Budget, Exp, MaxTime, Retry, MaxSends, LedgerBudget, LedgerSlots, BookSlots, MaxMsgs,
          Loss, Ranked, Pressure, PB, PK, Edges, Recur, Lasting, Gate, Cdl, TightNode

VARIABLES nf, cb, lg, msgs, t, seq, dropped, released, delivered, replayed, acc, met
vars == <<nf, cb, lg, msgs, t, seq, dropped, released, delivered, replayed, acc, met>>

Nodes == 1..N
Src == 1
Dest == N
F == INSTANCE DtnForwardOps WITH B <- 1, L <- N - 1, T <- N - 1
C == INSTANCE DtnCustodyOps WITH MaxU <- 1000
Key == <<1, 1>>

\* edge sets of the configs (a cfg cannot spell a set of tuples)
E3 == {<<1, 2>>, <<2, 3>>, <<1, 3>>}
E12 == {<<1, 2>>}
E13 == {<<1, 3>>}
E23 == {<<1, 2>>, <<2, 3>>}
E12_13 == {<<1, 2>>, <<1, 3>>}
R13 == {<<1, 3>>}
R23 == {<<2, 3>>}
NoE == {}

\* the node whose ledger has no room at all (0: none): it refuses custody
Led(n) == C!New(IF n = TightNode THEN 0 ELSE LedgerBudget, LedgerSlots)
EmptyBook == [i \in 1..BookSlots |-> C!BNone]

Offerable(n, p) == IF Ranked = 1 THEN p > n ELSE TRUE

HoldIn(copies) == [k |-> "hold", id |-> 1, dest |-> Dest, exp |-> Exp, copies |-> copies]

Init ==
    LET a == C!Accept(EmptyBook, Led(Src), 1, 1, Exp, 0, 0)
        h == F!Step(F!New(0), 0, HoldIn(Budget)) IN
    /\ Assert(a.err = "ok" /\ h.err = "ok", "the origin was refused")
    /\ nf = [n \in Nodes |-> IF n = Src THEN h.f ELSE F!New(0)]
    /\ cb = [n \in Nodes |-> IF n = Src THEN a.B ELSE EmptyBook]
    /\ lg = [n \in Nodes |-> IF n = Src THEN a.L ELSE Led(n)]
    /\ msgs = {} /\ t = 0 /\ seq = 0 /\ dropped = 0 /\ released = 0 /\ delivered = FALSE /\ replayed = FALSE
    /\ acc = {Src} /\ met = {}

Quiet(n) == LET r == F!Poll(nf[n]) IN r.f = nf[n] /\ r.act.k = "none"
AllQuiet == msgs = {} /\ \A n \in Nodes : Quiet(n)

(* a contact between the nodes of an edge: both forwarders learn the link state *)
Contact(e, up) ==
    /\ e \in Edges
    /\ LET a == e[1] b == e[2]
           k == IF up THEN "up" ELSE "down"
           ra == F!Step(nf[a], t, [k |-> k, peer |-> b])
           rb == F!Step(nf[b], t, [k |-> k, peer |-> a]) IN
       /\ nf' = [nf EXCEPT ![a] = ra.f, ![b] = rb.f]
       /\ (up => (ra.f # nf[a] \/ rb.f # nf[b]))
       /\ (~up => (ra.f # nf[a] \/ rb.f # nf[b]))
       \* a lasting contact ends only when both sides finished the exchange
       /\ (~up /\ Lasting = 1) => (Quiet(a) /\ Quiet(b) /\ ~\E m \in msgs : {m.from, m.to} = {a, b})
       /\ met' = IF up /\ e \in Recur THEN met \cup {e} ELSE met
    /\ UNCHANGED <<cb, lg, msgs, t, seq, dropped, released, delivered, replayed, acc>>

(* time passes: every forwarder ticks, then every book expires its ledger *)
Tick ==
    /\ t < MaxTime
    /\ (Gate = 1) => (AllQuiet /\ (t + 1 < Cdl \/ Recur \subseteq met))
    /\ nf' = [n \in Nodes |-> F!Step(nf[n], t + 1, [k |-> "tick"]).f]
    /\ cb' = [n \in Nodes |-> C!BExpire(cb[n], lg[n], t + 1).B]
    /\ lg' = [n \in Nodes |-> C!BExpire(cb[n], lg[n], t + 1).L]
    /\ t' = t + 1
    /\ UNCHANGED <<msgs, seq, dropped, released, delivered, replayed, acc, met>>

Msg(kind, from, to, copies, fresh) == [kind |-> kind, id |-> seq, from |-> from, to |-> to, copies |-> copies, fresh |-> fresh]

PollN(n) ==
    LET r == F!Poll(nf[n]) IN
    /\ (r.f # nf[n] \/ r.act.k # "none")
    /\ nf' = [nf EXCEPT ![n] = r.f]
    /\ CASE r.act.k = "send" ->
              /\ Cardinality(msgs) < MaxMsgs
              /\ msgs' = msgs \cup {Msg("bun", n, r.act.peer, r.act.copies, ~r.act.retr)}
              /\ seq' = seq + 1
              /\ cb' = IF r.act.copies > 0 /\ ~r.act.retr /\ Offerable(n, r.act.peer)
                       THEN [cb EXCEPT ![n] = C!Offer(cb[n], 1, r.act.peer).B] ELSE cb
              /\ UNCHANGED <<lg, dropped, released, delivered, replayed, acc, met>>
         [] r.act.k = "release" ->
              /\ released' = released + F!CopiesHeld(nf[n], 1)
              /\ cb' = [cb EXCEPT ![n] = C!Delivered(cb[n], lg[n], 1).B]
              /\ lg' = [lg EXCEPT ![n] = C!Delivered(cb[n], lg[n], 1).L]
              /\ UNCHANGED <<msgs, seq, dropped, delivered, replayed, acc, met>>
         [] OTHER -> UNCHANGED <<cb, lg, msgs, seq, dropped, released, delivered, replayed, acc, met>>
    /\ UNCHANGED t

DeliverBun(m) ==
    /\ m \in msgs /\ m.kind = "bun"
    /\ LET r == m.to
           ack == Msg("ack", r, m.from, 0, FALSE)
           a == C!Accept(cb[r], lg[r], 1, 1, Exp, m.from, t)
           h == F!Step(nf[r], t, HoldIn(m.copies)) IN
       IF r = Dest
       THEN /\ delivered' = TRUE
            /\ msgs' = (msgs \ {m}) \cup {ack} /\ seq' = seq + 1
            /\ UNCHANGED <<nf, cb, lg, dropped, released, replayed, acc, met>>
       ELSE IF a.err # "ok"
       THEN /\ cb' = [cb EXCEPT ![r] = a.B] /\ lg' = [lg EXCEPT ![r] = a.L]
            /\ msgs' = msgs \ {m}
            /\ dropped' = IF m.fresh THEN dropped + m.copies ELSE dropped
            /\ UNCHANGED <<nf, seq, released, delivered, replayed, acc, met>>
       ELSE /\ cb' = [cb EXCEPT ![r] = a.B] /\ lg' = [lg EXCEPT ![r] = a.L]
            /\ nf' = [nf EXCEPT ![r] = h.f]
            /\ dropped' = IF h.err # "ok" /\ m.fresh THEN dropped + m.copies ELSE dropped
            /\ replayed' = (replayed \/ (h.err = "ok" /\ ~m.fresh))
            /\ acc' = acc \cup {r}
            /\ msgs' = (msgs \ {m}) \cup {ack} /\ seq' = seq + 1
            /\ UNCHANGED <<released, delivered, met>>
    /\ UNCHANGED t

DeliverAck(m) ==
    /\ m \in msgs /\ m.kind = "ack"
    /\ LET p == m.to
           s == F!Step(nf[p], t, [k |-> "ack", peer |-> m.from, id |-> 1])
           o == C!OnAck(cb[p], lg[p], 1, m.from, TRUE) IN
       /\ nf' = [nf EXCEPT ![p] = s.f]
       /\ cb' = [cb EXCEPT ![p] = o.B]
       /\ lg' = [lg EXCEPT ![p] = o.L]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<t, seq, dropped, released, delivered, replayed, acc, met>>

Lose(m) ==
    /\ Loss = 1 /\ m \in msgs
    /\ msgs' = msgs \ {m}
    /\ dropped' = IF m.kind = "bun" /\ m.fresh THEN dropped + m.copies ELSE dropped
    /\ UNCHANGED <<nf, cb, lg, t, seq, released, delivered, replayed, acc, met>>

(* the mailbox layer admits an item to the shared ledger; an evicted bundle is forgotten by the forwarder *)
PressureAt(n, k) ==
    /\ Pressure = 1
    /\ LET a == C!Admit(lg[n], <<2, k>>, PB, "transit", Exp + 100, t)
           gone == \E i \in 1..Len(a.ev) : a.ev[i].key[1] = 1
           fg == F!Step(nf[n], t, [k |-> "forget", id |-> 1]) IN
       /\ a.err = "ok"
       /\ lg' = [lg EXCEPT ![n] = a.L]
       /\ nf' = IF gone THEN [nf EXCEPT ![n] = fg.f] ELSE nf
       /\ released' = IF gone THEN released + F!CopiesHeld(nf[n], 1) ELSE released
    /\ UNCHANGED <<cb, msgs, t, seq, dropped, delivered, replayed, acc, met>>

Next == \/ \E e \in Edges, up \in BOOLEAN : Contact(e, up)
        \/ Tick
        \/ \E n \in Nodes : PollN(n)
        \/ \E m \in msgs : DeliverBun(m) \/ DeliverAck(m) \/ Lose(m)
        \/ \E n \in Nodes, k \in 1..PK : PressureAt(n, k)

Spec == Init /\ [][Next]_vars

Progress == (\E n \in Nodes : PollN(n)) \/ (\E m \in msgs : DeliverBun(m) \/ DeliverAck(m))
FairSpec == Spec /\ WF_vars(Progress)
            /\ \A e \in Recur : SF_vars(Contact(e, TRUE))

(* ---- observables ---- *)

Held == LET RECURSIVE S(_) S(X) == IF X = {} THEN 0 ELSE LET n == CHOOSE n \in X : TRUE IN F!CopiesHeld(nf[n], 1) + S(X \ {n}) IN S(Nodes)
InFlight == LET RECURSIVE S(_) S(X) == IF X = {} THEN 0 ELSE LET m == CHOOSE m \in X : TRUE IN m.copies + S(X \ {m}) IN
            S({m \in msgs : m.kind = "bun" /\ m.fresh})
CustodyHeld(n) == C!Holds(cb[n], 1)

(* ---- properties ---- *)

Account == ~replayed => Held + InFlight + dropped + released = Budget
HeldLeBudget == ~replayed => Held <= Budget

LedgerOk == \A n \in Nodes :
    /\ lg[n].used = C!Total(lg[n]) /\ lg[n].used <= lg[n].budget
    /\ \A i \in C!RIdx(cb[n]), e \in C!Ents(lg[n]) : e.key = Key => e.cls = "custody"
    /\ \A i, j \in C!RIdx(cb[n]) : i # j => cb[n][i].bundle # cb[n][j].bundle

\* the clocks of all forwarders are the clock of the system
Clocks == \A n \in Nodes : nf[n].now = t

CustodyAlive == (~delivered /\ t < Exp) => \E n \in Nodes : CustodyHeld(n)

\* a custody record ends only by a consumed ack from the offered node, by delivery or by expiry
A_CustodyExit == [][\A n \in Nodes :
    (CustodyHeld(n) /\ ~C!Holds(cb'[n], 1)) =>
        \/ t' >= Exp
        \/ \E m \in msgs : /\ m.kind = "ack" /\ m.to = n /\ m \notin msgs'
                           /\ cb[n][C!SlotOf(cb[n], 1)].off = m.from
        \/ nf[n].bs[1].delivered /\ nf[n].bs[1].full /\ nf[n].bs[1].id = 1]_vars

A_TickExpires == [][(t' = t + 1 /\ t' >= Exp) =>
    \A n \in Nodes : ~C!Holds(cb'[n], 1) /\ ~C!Contains(lg'[n], Key)]_vars

A_FrozenDown == [][t' = t + 1 =>
    \A n \in Nodes, i \in 1..(N - 1) :
        (nf[n].ts[i].full /\ nf[n].ts[i].ph = "sent" /\ ~F!Up(nf[n], nf[n].ts[i].peer)) =>
            nf'[n].ts[i].rem = nf[n].ts[i].rem]_vars

NoReplay == ~replayed
NoForget == released = 0
DeliveredByExpiry == t < MaxTime \/ delivered
Served == <>delivered
=============================================================================
