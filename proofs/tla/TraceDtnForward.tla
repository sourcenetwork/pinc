--------------------------- MODULE TraceDtnForward ---------------------------
(***************************************************************************)
(* Trace validation of the spray-and-wait forwarder                        *)
(* (pinc-dtn/src/forward.rs).                                              *)
(*                                                                         *)
(* The Rust test tests/trace_dtn_forward.rs drives the real Forwarder with *)
(* seeded random inputs (ticks, holds, links, acknowledgements, forgets    *)
(* and polls, with time going forwards and backwards) and records every    *)
(* call. Each recorded step must be a step of the operators of            *)
(* DtnForwardOps.tla (Step and Poll), the error and the action the code    *)
(* returned must be those the operators return, and after every call the   *)
(* copies held and handed per bundle and the timer of every (bundle, peer) *)
(* transfer read back from the code must equal the model's, and so must   *)
(* the live memory entry of every bundle (mm: the expiry of its entry in   *)
(* the table of accepted bundles, 0 for none; the table is private, the    *)
(* test reads it through the behaviour of a copy of the forwarder). The    *)
(* links, the delivered flags, the transfer phases and the slots of        *)
(* expired memory entries are not readable through the API, so the model   *)
(* has to reproduce them for the later observations to match.              *)
(*                                                                         *)
(* The constants are those of the main world of the test: two bundle       *)
(* slots, two link slots, two transfer slots, two memory slots, retry 3    *)
(* and 3 sends. The                                                        *)
(* edge world (other capacities and policies, times next to u64::MAX) is   *)
(* replayed by Lean only.                                                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds dtn_forward.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd

VARIABLES i, f
vars == <<i, f>>

NMem == 2
F == INSTANCE DtnForwardOps WITH B <- 2, L <- 2, T <- 2, D <- NMem, Retry <- 3, MaxSends <- 3

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/dtn_forward.ndjson")

Init == i = 1 /\ f = F!New(0)

Tm(g, id, p) == IF F!TIdx(g, id, p) # {} /\ g.ts[F!MinOf(F!TIdx(g, id, p))].ph = "sent"
                THEN g.ts[F!MinOf(F!TIdx(g, id, p))].rem + 1 ELSE 0

\* the expiry of the live memory entry of a bundle, 0 for none
Mm(g, id) == LET live == {j \in 1..NMem : g.ds[j].full /\ g.ds[j].id = id /\ g.ds[j].exp > g.now}
                 exps == {g.ds[j].exp : j \in live} IN
    IF live = {} THEN 0 ELSE CHOOSE e \in exps : \A x \in exps : e >= x

\* what the code lets an observer read back after a call
Seen(g, ev) ==
    /\ \A id \in 1..Len(ev.ch) : ev.ch[id] = F!CopiesHeld(g, id)
    /\ \A id \in 1..Len(ev.cd) : ev.cd[id] = F!Handed(g, id)
    /\ \A id \in 1..Len(ev.mm) : ev.mm[id] = Mm(g, id)
    /\ \A id \in 1..Len(ev.tm) : \A p \in 1..Len(ev.tm[id]) : ev.tm[id][p] = Tm(g, id, p)

NewRun == /\ Trace[i].e = "new"
          /\ Trace[i].b = 2 /\ Trace[i].l = 2 /\ Trace[i].tt = 2 /\ Trace[i].d = 2 /\ Trace[i].retry = 3 /\ Trace[i].max = 3
          /\ f' = F!New(Trace[i].now)
          /\ i' = i + 1

StepEv == /\ Trace[i].e = "step"
          /\ \A r \in {F!Step(f, Trace[i].now, Trace[i].in)} :
                /\ r.err = Trace[i].err
                /\ f' = r.f
                /\ Seen(r.f, Trace[i])
          /\ i' = i + 1

ActIs(a, ev) ==
    /\ a.k = ev.k
    /\ (a.k = "send" => a.peer = ev.peer /\ a.bundle = ev.bundle /\ a.copies = ev.copies /\ a.retr = ev.retr)
    /\ (a.k = "release" => a.bundle = ev.bundle)

PollEv == /\ Trace[i].e = "poll"
          /\ \A r \in {F!Poll(f)} :
                /\ ActIs(r.act, Trace[i].act)
                /\ f' = r.f
                /\ Seen(r.f, Trace[i])
          /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (NewRun \/ StepEv \/ PollEv)) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of DtnForwardOps.tla
TraceAccepted == <>(i = Len(Trace) + 1)
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
