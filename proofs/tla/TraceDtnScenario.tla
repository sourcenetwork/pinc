-------------------------- MODULE TraceDtnScenario --------------------------
(***************************************************************************)
(* Trace validation of the delay-tolerant scenarios: four nodes that each  *)
(* run the real Forwarder, CustodyBook and Ledger, joined by a network     *)
(* that delays and loses messages (vinc-dtn forward.rs, custody.rs,        *)
(* store.rs).                                                              *)
(*                                                                         *)
(* The Rust test tests/trace_dtn_scenario.rs runs seeded random scenarios  *)
(* and three scripted ones (a chain with a recurring contact, an outage    *)
(* over the expiry, a lost ack) and records every event of the host glue.  *)
(* Each recorded event must be a step of DtnScenario.tla (which instances  *)
(* the node operators): a contact, a tick, a poll with the action the code *)
(* returned, the delivery of a bundle message with its outcome (dest,      *)
(* held, holdrefused, refused), the delivery of an ack with the book's     *)
(* answer, a loss, pressure from the mailbox layer, a forged ack that      *)
(* changes nothing. After every event the observables of every node read   *)
(* back from the code must equal the model's: copies held and handed,      *)
(* whether the book holds the bundle, the bytes and length of the ledger,  *)
(* the class of the bundle's item, the length of the book and the timer of *)
(* each peer. The offered node and the link flags are not readable; the    *)
(* model has to reproduce them for later observations to match.            *)
(*                                                                         *)
(* The world is that of the test: 4 nodes, 4 copies, expiry 30, retry 2,   *)
(* 3 sends, ledgers of 3 slots and 3 bytes (node 3 has none), books of 2.  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds dtn_scenario.ndjson.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES i, nf, cb, lg, msgs, t, seq, dropped, released, delivered, replayed, acc, met, nx, lo, fins, refin
vars == <<i, nf, cb, lg, msgs, t, seq, dropped, released, delivered, replayed, acc, met, nx, lo, fins, refin>>
sv == <<nf, cb, lg, msgs, t, seq, dropped, released, delivered, replayed, acc, met, nx, lo, fins, refin>>

AllEdges == {e \in (1..4) \X (1..4) : e[1] < e[2]}
NoRecur == {}
SC == INSTANCE DtnScenario WITH N <- 4, Budget <- 4, Exp <- 30, MaxTime <- 1000, Retry <- 2, MaxSends <- 3,
          LedgerBudget <- 3, LedgerSlots <- 3, BookSlots <- 2, MaxMsgs <- 100000, Loss <- 1, Ranked <- 1,
          Pressure <- 1, PB <- 2, PK <- 2, Edges <- AllEdges, Recur <- NoRecur, Lasting <- 0, Gate <- 0, Cdl <- 0,
          TightNode <- 3, FD <- 2
F == INSTANCE DtnForwardOps WITH B <- 1, L <- 3, T <- 3, D <- 2, Retry <- 2, MaxSends <- 3
C == INSTANCE DtnCustodyOps WITH MaxU <- 1000

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/dtn_scenario.ndjson")

Tm(g, p) == IF F!TIdx(g, 1, p) # {} /\ g.ts[F!MinOf(F!TIdx(g, 1, p))].ph = "sent"
            THEN g.ts[F!MinOf(F!TIdx(g, 1, p))].rem ELSE -1

Cls(L) == IF ~C!Contains(L, <<1, 1>>) THEN 0
          ELSE IF (CHOOSE e \in C!Ents(L) : e.key = <<1, 1>>).cls = "custody" THEN 1 ELSE 2

PeerAt(n, k) == IF k < n THEN k ELSE k + 1

\* what the code lets an observer read back from node n after the event (the state after the step)
NodeSeenP(n, o) ==
    /\ o[1] = F!CopiesHeld(nf'[n], 1)
    /\ o[2] = F!Handed(nf'[n], 1)
    /\ o[3] = IF C!Holds(cb'[n], 1) THEN 1 ELSE 0
    /\ o[4] = lg'[n].used
    /\ o[5] = C!Count(lg'[n])
    /\ o[6] = Cls(lg'[n])
    /\ o[7] = Cardinality(C!RIdx(cb'[n]))
    /\ \A k \in 1..3 : o[8][k] = Tm(nf'[n], PeerAt(n, k))

SeenP(ev) == \A n \in 1..4 : NodeSeenP(n, ev.ns[n])

NewRun == /\ Trace[i].e = "new"
          /\ nf' = SC!OriginNf /\ cb' = SC!OriginCb /\ lg' = SC!OriginLg
          /\ msgs' = {} /\ t' = 0 /\ seq' = 0 /\ dropped' = 0 /\ released' = 0 /\ delivered' = FALSE
          /\ replayed' = FALSE /\ acc' = {1} /\ met' = {}
          /\ nx' = SC!OriginNx /\ lo' = [n \in 1..4 |-> [p \in 1..4 |-> 0]] /\ fins' = {} /\ refin' = FALSE
          /\ i' = i + 1

ContactEv == /\ Trace[i].e = "contact"
             /\ SC!Contact(<<Trace[i].a, Trace[i].b>>, Trace[i].up)
             /\ i' = i + 1

TickEv == /\ Trace[i].e = "tick" /\ SC!Tick /\ i' = i + 1

PollEv == /\ Trace[i].e = "poll"
          /\ LET n == Trace[i].n
                 r == F!Poll(nf[n]) IN
             /\ r.act.k = (CASE Trace[i].a = "none" -> "none" [] Trace[i].a = "send" -> "send" [] OTHER -> "release")
             /\ (r.act.k = "send" => /\ r.act.peer = Trace[i].p /\ r.act.copies = Trace[i].c
                                     /\ r.act.retr = Trace[i].r /\ seq = Trace[i].mid
                                     /\ Trace[i].off = (IF r.act.retr THEN lo[n][r.act.peer]
                                          ELSE IF r.act.copies > 0 /\ SC!Offerable(n, r.act.peer) /\ C!Offer(cb[n], nx[n], 1, r.act.peer).err = "ok"
                                               THEN nx[n] ELSE 0))
             /\ (SC!PollN(n) \/ (r.f = nf[n] /\ r.act.k = "none" /\ UNCHANGED sv))
          /\ i' = i + 1

BunEv == /\ Trace[i].e = "bun"
         /\ \E m \in msgs :
              /\ m.id = Trace[i].m /\ m.kind = "bun"
              /\ LET a == C!Accept(cb[m.to], lg[m.to], 1, 1, 30, m.from, m.off, t)
                     h == F!Step(nf[m.to], t, SC!HoldIn(m.copies))
                     out == IF m.to = 4 THEN "dest"
                            ELSE IF a.err = "custody" THEN "refused"
                            ELSE IF a.err = "capacity" THEN "capacity"
                            ELSE IF a.err # "ok" THEN "other"
                            ELSE IF h.err = "ok" THEN "held" ELSE "holdrefused" IN
                 /\ out = Trace[i].o
                 /\ (out \notin {"refused", "capacity", "other"} => seq = Trace[i].aid)
              /\ SC!DeliverBun(m)
         /\ i' = i + 1

AckEv == /\ Trace[i].e = "ack"
         /\ \E m \in msgs :
              /\ m.id = Trace[i].m /\ m.kind = "ack"
              /\ C!OnAck(cb[m.to], lg[m.to], 1, m.from, m.off, TRUE).err = Trace[i].o
              /\ SC!DeliverAck(m)
         /\ i' = i + 1

LoseEv == /\ Trace[i].e = "lose"
          /\ \E m \in msgs : m.id = Trace[i].m /\ SC!Lose(m)
          /\ i' = i + 1

PressEv == /\ Trace[i].e = "press" /\ SC!PressureAt(Trace[i].n, Trace[i].k) /\ i' = i + 1

BadEv == /\ Trace[i].e = "bad" /\ UNCHANGED sv /\ i' = i + 1

Init == i = 1 /\ SC!Init

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace)
         /\ (ContactEv \/ TickEv \/ PollEv \/ BunEv \/ AckEv \/ LoseEv \/ PressEv \/ BadEv \/ NewRun)
         \* the observables of the state reached by the event just replayed
         /\ SeenP(Trace[i])) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)
TraceAccepted == <>(i = Len(Trace) + 1)
=============================================================================

