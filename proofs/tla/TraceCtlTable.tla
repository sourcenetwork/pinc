---------------------------- MODULE TraceCtlTable ----------------------------
(***************************************************************************)
(* Trace validation of the control-frame state, pinc-transport conn/ctl.rs *)
(* (Ctl and `apply` for Control frame references), at its real sizes       *)
(* (TABLE = 24, EXT_SLOTS = 8).                                            *)
(*                                                                         *)
(* The Rust test tests/trace_ctl.rs drives a real Ctl, Streams and         *)
(* BufferPool through CtlProbe (cargo feature `trace`): stream frames      *)
(* tracked past a full table, extension frames held (bodies at and over    *)
(* EXT_BODY_MAX, with the pool full), sent and shed, ticket batches issued *)
(* and sent, READY asked for and built, the pool's other users, and every  *)
(* reference reported through `apply` as acknowledged, lost (to be         *)
(* requeued) or acknowledged late, in seeded orders. Every call must be    *)
(* the step of CtlTableOps.tla, with the answer the code gave; after every *)
(* call the table, `next_key`, the flags, the extension slots, `next_ext`  *)
(* and the chunks the pool charges must be the model's (the batch held is  *)
(* recorded by the generation the test issued it with).                    *)
(*                                                                         *)
(* DOC = TRUE replays the documented rule for tickets (an acknowledgement  *)
(* or a loss acts only on the batch it carried), which the code keeps with *)
(* fix T1; before T1 the replay stopped at the first acknowledgement of an *)
(* older batch while a newer one was held (the finding). DOC = FALSE       *)
(* replays the code before T1. An acknowledgement or a loss is recorded    *)
(* with the id of its reference and g, the batch it carried; with DOC the  *)
(* id of a tickets reference must equal g (fix T1: the generation).        *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds ctl.ndjson.           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils
CONSTANT DOC
VARIABLES i, c, pu, p
vars == <<i, c, pu, p>>
INSTANCE CtlTableOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/ctl.ndjson")
Ev0 == Trace[i]

\* the recorded state: tab and ext as JSON arrays (an empty extension slot is [])
ExtView(x) == IF x.on THEN <<x.key, x.pend>> ELSE <<>>
Same(x, u, v) == /\ Len(v.tab) = Cardinality(DOMAIN x.tab) /\ v.tab = [j \in 1..Len(v.tab) |-> x.tab[j - 1]]
                 /\ Len(v.ext) = Cardinality(DOMAIN x.ext) /\ v.ext = [j \in 1..Len(v.ext) |-> ExtView(x.ext[j - 1])]
                 /\ v.nk = x.nk /\ v.ne = x.ne /\ v.ready = x.ready /\ v.tk = x.tk /\ v.tp = x.tp
                 /\ v.used = u

InitEv == /\ Ev0.op = "init" /\ c' = CNew(24, 8) /\ pu' = 0 /\ p' = Ev0.p
TrackEv == LET r == Track(c)
           IN /\ Ev0.op = "track" /\ r.ok = Ev0.ok /\ (r.ok => r.key = Ev0.key) /\ c' = r.c /\ UNCHANGED <<pu, p>>
HoldEv == LET r == HoldExt(c, pu, p, Ev0.long)
          IN /\ Ev0.op = "hold" /\ r.ok = Ev0.ok /\ c' = r.c /\ pu' = r.used /\ UNCHANGED p
SendExtEv == /\ Ev0.op = "send_ext" /\ c.ext[Ev0.slot].on /\ c.ext[Ev0.slot].pend
             /\ c' = SendExt(c, Ev0.slot) /\ UNCHANGED <<pu, p>>
ShedEv == LET f == FreeExt(c, pu, Ev0.slot)
          IN /\ Ev0.op = "shed" /\ c' = f.c /\ pu' = f.used /\ UNCHANGED p
TakeEv == /\ Ev0.op = "take" /\ Ev0.ok = (pu < p) /\ pu' = (IF pu < p THEN pu + 1 ELSE pu) /\ UNCHANGED <<c, p>>
GiveEv == /\ Ev0.op = "give" /\ pu > 0 /\ pu' = pu - 1 /\ UNCHANGED <<c, p>>
IssueEv == /\ Ev0.op = "issue" /\ c' = Issue(c, Ev0.g) /\ UNCHANGED <<pu, p>>
SendTkEv == LET r == SendTickets(c)
            IN /\ Ev0.op = "send_tickets" /\ r.ok = Ev0.ok /\ (r.ok => r.g = Ev0.g) /\ c' = r.c /\ UNCHANGED <<pu, p>>
SendReadyEv == /\ Ev0.op = "send_ready" /\ c' = SendReady(c) /\ UNCHANGED <<pu, p>>
BuildReadyEv == LET r == BuildReady(c)
                IN /\ Ev0.op = "build_ready" /\ r.ok = Ev0.ok /\ c' = r.c /\ UNCHANGED <<pu, p>>
\* g: the batch the reported frame carried (as the test issued it, from 1 in each run, which is also the count of
\* batches the Ctl held). With fix T1 a tickets reference's id is that generation (fill_tickets writes tickets_gen):
\* checked on every report of tickets, so the code's match by id is the model's match by batch.
TkRef == Ev0.k = "tk" => Ev0.id = Ev0.g
AckEv == LET a == Acked(c, pu, Ev0.k, Ev0.id, Ev0.g, DOC)
         IN /\ Ev0.op \in {"ack", "late_ack"} /\ c' = a.c /\ pu' = a.used /\ UNCHANGED p
            /\ (Ev0.k = "sc" => (a.layer = "acked") = Ev0.handed) /\ (DOC => TkRef)
LoseEv == LET l == Lost(c, Ev0.k, Ev0.id, Ev0.g, DOC)
          IN /\ Ev0.op = "lose" /\ c' = l.c /\ UNCHANGED <<pu, p>>
             /\ (Ev0.k = "sc" => (l.layer = "lost") = Ev0.handed) /\ (DOC => TkRef)

Init == i = 1 /\ c = CNew(1, 1) /\ pu = 0 /\ p = 0
Step == /\ i <= Len(Trace) /\ Ev0.t = "ctl"
        /\ (InitEv \/ TrackEv \/ HoldEv \/ SendExtEv \/ ShedEv \/ TakeEv \/ GiveEv \/ IssueEv \/ SendTkEv
            \/ SendReadyEv \/ BuildReadyEv \/ AckEv \/ LoseEv)
        /\ Same(c', pu', Ev0.v)
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* never more chunks charged than the pool has
Inv == pu <= p
=============================================================================
