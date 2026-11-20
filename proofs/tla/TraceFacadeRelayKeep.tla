------------------------- MODULE TraceFacadeRelayKeep -------------------------
(***************************************************************************)
(* Trace validation of what a node that carries the relay role keeps       *)
(* across a restart: relay/state/keep.rs over the real state machine and   *)
(* MemStore.                                                               *)
(*                                                                         *)
(* The Rust test tests/trace_facade_relay_keep.rs drives a real relay core *)
(* through the probe KeepProbe (crates/pinc, cargo feature `trace`):       *)
(* records published (new, refreshed, stale, past a full table), packets   *)
(* held and handed over, timers, the store writes the core asks for (each  *)
(* written to a real MemStore, or failed and given back as Part does),     *)
(* restarts with the same store at any clock, some in the middle of a      *)
(* write that lands torn, and ends of a run with the same core run again   *)
(* (the write out given back, nothing restored). Every call must be the    *)
(* step the operators of FacadeRelayKeepOps.tla compute: the answer of     *)
(* each call, the record and the packets the machine holds after it, every *)
(* write job (a failed one tried again behind the marks not tried yet, at  *)
(* most MAX_TRIES times), and after each restore and rerun the whole of    *)
(* what the machine holds and the store error count.                       *)
(*                                                                         *)
(* Times are in units of RECORD_TTL_NS / 4; nodes and members are numbered *)
(* in the order of their store key. Needs the TLA+ CommunityModules (Json, *)
(* IOUtils) and PINC_TRACE_DIR, the directory that holds                   *)
(* relay-keep.ndjson.                                                      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd
CONSTANTS NR, NM, RCAP, MCAP, MBP, MAILQ, TTL, AGE, MAXT, FQ
VARIABLES i, s, st, job
vars == <<i, s, st, job>>
INSTANCE FacadeRelayKeepOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/relay-keep.ndjson")
E == Trace[i]
Rng(f) == {f[j] : j \in DOMAIN f}
Ids(l) == [j \in 1..Len(l) |-> l[j].id]
\* the clock of a call within one run never goes back; the probe sets last_now as the calls that bring these events do
At(t) == [s EXCEPT !.now = t, !.ln = t]

\* what the test read back after a restore: every record held, every member's packets (members 1..NM in order)
View(m, e) == /\ {x.n : x \in Rng(e.recs)} = {n \in Nodes : m.rec[n].seq # 0}
              /\ \A x \in Rng(e.recs) : m.rec[x.n].seq = x.seq /\ m.rec[x.n].rcv = x.rcv
              /\ Len(e.mail) = NM
              /\ \A k \in Members : Ids(m.mb[k]) = e.mail[k]
              /\ m.errs = e.errs

Torn(e) == IF job.k = "none" THEN st ELSE Tear(st, job, e.tear)
TearFits(e) == IF job.k = "none" THEN e.tear = "none" ELSE TearOk(job, e.tear)

RestartEv == /\ E.op = "restart" /\ TearFits(E)
             /\ LET st1 == Torn(E)
                    m == Restore(Machine0(E.t), E.t, st1)
                IN st' = st1 /\ s' = m /\ View(m, E)
             /\ job' = NoJob

\* Part::end gives the write out back; the part was restored, so the next run restores nothing (R2)
RerunEv == /\ E.op = "rerun" /\ TearFits(E) /\ E.t >= s.now
           /\ LET m == IF job.k = "none" THEN s ELSE Requeue(s, job)
              IN st' = Torn(E) /\ s' = m /\ View(m, E)
           /\ job' = NoJob

PublishEv == /\ E.op = "publish" /\ E.t >= s.now
             /\ LET a == Accept(At(E.t), E.n, E.seq, E.t, TRUE)
                IN /\ a.ok = E.ok /\ s' = a.s
                   /\ (a.s.rec[E.n].seq # 0) = E.has
                   /\ E.has => a.s.rec[E.n].seq = E.cur /\ a.s.rec[E.n].rcv = E.rcv
             /\ UNCHANGED <<st, job>>

HoldEv == /\ E.op = "hold" /\ E.t >= s.now
          /\ LET r == Hold(At(E.t), E.m, E.id)
             IN r.ok = E.ok /\ s' = r.s /\ Ids(r.s.mb[E.m]) = E.held
          /\ UNCHANGED <<st, job>>

HeardEv == /\ E.op = "heard" /\ E.t >= s.now
           /\ s' = Heard(At(E.t), E.m) /\ Ids(s'.mb[E.m]) = E.held
           /\ UNCHANGED <<st, job>>

TickEv == /\ E.op = "tick" /\ E.t >= s.now
          /\ s' = Tick(At(E.t)) /\ Count(s'.rec) = E.cnt
          /\ UNCHANGED <<st, job>>

JobEv == /\ E.op = "job" /\ job.k = "none"
         /\ LET r == NextJob(s) IN
            /\ r.job.k = E.k
            /\ E.k # "none" => r.job.n = E.n
            /\ E.k = "put" => r.job.seq = E.seq /\ r.job.rcv = E.rcv
            /\ E.k = "mail" => r.job.pk = E.pk
            /\ s' = r.s /\ job' = r.job
         /\ UNCHANGED st

\* Part::store_written: a failure is counted and queued behind the marks not tried yet, or given up and counted once
\* more; the next write waits for the clock to move on (R3)
WriteEv == /\ E.op = "write" /\ job.k # "none"
           /\ st' = IF E.ok THEN Apply(st, job) ELSE st
           /\ s' = IF E.ok THEN s ELSE Failed(s, job)
           /\ job' = NoJob

Init == i = 1 /\ s = Machine0(0) /\ st = St0 /\ job = NoJob
Step == /\ i <= Len(Trace)
        /\ \/ RestartEv \/ RerunEv \/ PublishEv \/ HoldEv \/ HeardEv \/ TickEv \/ JobEv \/ WriteEv
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* The states seen are told apart by the event index alone (VIEW in the config): every event is the step of exactly one
\* of RestartEv .. WriteEv (each requires its op) and each sets s', st' and job' as functions of the state and the
\* event, so a behaviour has one state per index and the view merges none. TLC then does not fingerprint the record
\* table of 1030 nodes at every state; the same traces are accepted, and Inv is still checked in every state.
IdxView == i

\* the tables of the real run stay within their sizes
Inv == /\ Count(s.rec) <= RCAP
       /\ \A m \in Members : Len(s.mb[m]) <= MBP
       /\ Cardinality(s.slot) <= MCAP
       /\ Len(s.fq) <= FQ /\ s.tr < MAXT
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
