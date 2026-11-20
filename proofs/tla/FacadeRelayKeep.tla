--------------------------- MODULE FacadeRelayKeep ---------------------------
(***************************************************************************)
(* The records and mailboxes a node that carries the relay role keeps in   *)
(* its Store, and what a restart with the same identity reads back:        *)
(* relay/state/keep.rs (note_record, note_mail, note_sweep, next_job,      *)
(* requeue, restore), relay/part.rs (next_store_write, store_written:      *)
(* one write out at a time, a failure counted, marked again and tried      *)
(* again once the part's clock moved on; end: the write out is given       *)
(* back; restored: a second run loads and restores nothing), relay/run.rs  *)
(* and drive/role_io.rs role_task (load, restore at the relay clock, then  *)
(* the writes), relay/store.rs (Store, MemStore, Kept). The operators are  *)
(* in FacadeRelayKeepOps.tla.                                              *)
(*                                                                         *)
(* The networks. The role and the relay binary keep the same records and   *)
(* mailboxes through the same Store trait: in a network of ordinary nodes  *)
(* only, a node with the role keeps them in the store its host gives       *)
(* (MemStore when none); where relay binaries are the only relays, each    *)
(* binary keeps them on disk, possibly the only copy of the network's      *)
(* records and mailboxes, and is restarted with the same identity; in a    *)
(* mixed network both do this, each for its own members. No rule here      *)
(* depends on which node holds the role, on the carrier (TCP or            *)
(* WebSocket), or on the library version of the members (the store holds   *)
(* signed records and blobs; an older member reads nothing of it). A       *)
(* disk store of the relay binary can tear a write when the process stops  *)
(* in the middle of it: the restart modes model that; MemStore never       *)
(* tears.                                                                  *)
(*                                                                         *)
(* Environment: the relay clock starts at 0 and moves on by Advance, one   *)
(* unit at a time; the host runs on_timeout at least once per unit (the    *)
(* machine asks for it every SWEEP_NS, far below a unit), so Advance       *)
(* waits for a Tick at the current time. A restart starts the clock again  *)
(* at any value of CLOCKS: at 0, back in time, or ahead.                   *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - RestoredLive (keep.rs: nothing past its lifetime is restored; a      *)
(*    record that does not verify is not restored);                        *)
(*  - MailOrdered (packets restored oldest first, each once, over a second *)
(*    run too);                                                            *)
(*  - RecSynced, LifeSynced, MailSynced (store.rs, keep.rs: what the       *)
(*    machine holds is what the store holds once the writes are done, a    *)
(*    failed one retried; a record dropped by lifetime is removed; the     *)
(*    remaining lifetime is the same after a restart; packets past their   *)
(*    age excepted, which restore refuses);                                *)
(*  - MailCounted (keep.rs note_mail: a mailbox mark the table has no room *)
(*    for leaves the store behind only with a store error counted);        *)
(*  - MarksBounded (keep.rs: the records marked, held and to remove are    *)
(*    each at most twice the record table, the members marked at most the  *)
(*    mailbox members); KeptBounded (store.rs: Kept.records is bounded by  *)
(*    RECORDS);                                                            *)
(*  - WritingHasJob (part.rs: a write is out only while one runs, over the *)
(*    end of a run too).                                                   *)
(* Witnesses of documented limits (each must be violated): _w_life         *)
(* (LifeSynced: a refresh of the same seq is not written, R7 open),        *)
(* _w_noparse (RecSynced: a record that does not parse is counted and left *)
(* in the store), _w_mailq (MailSynced: a lost mailbox mark, counted).     *)
(***************************************************************************)
EXTENDS FacadeRelayKeepOps

CONSTANTS TMAX,    \* the largest relay clock
          CLOCKS,  \* the clocks a restart may start at
          SEQS,    \* the record sequence numbers 1..SEQS
          PUBS,    \* the most publishes
          PMAX,    \* the most packets held
          MAXR,    \* the most restarts and second runs
          REFRESH, \* whether a node publishes the seq it has again (records.rs Refreshed)
          TORN,    \* the tear modes besides "lost" and "whole"
          FAIL,    \* whether a store write may fail
          RERUN    \* whether the same part is run a second time (Relay::run, Endpoint::run)

VARIABLES s,       \* the machine and Keep
          st,      \* the store
          job,     \* the write out (NoJob when none)
          writing, \* Part.writing
          failed,  \* a store write failed
          rs,      \* what the last restore put back, at which clock
          g        \* ghosts: full, tear, back, ticked, pubs, pid, rst
vars == <<s, st, job, writing, failed, rs, g>>

Init == /\ s = Restore(Machine0(0), 0, St0)
        /\ st = St0
        /\ job = NoJob
        /\ writing = FALSE
        /\ failed = FALSE
        /\ rs = [at |-> 0, recs |-> {}, pks |-> {}]
        /\ g = [full |-> FALSE, tear |-> FALSE, back |-> FALSE, ticked |-> FALSE, pubs |-> 0, pid |-> 0, rst |-> 0]

Publish(n, q) ==
    /\ g.pubs < PUBS
    /\ REFRESH \/ s.rec[n].seq # q
    /\ LET a == Accept(Called(s), n, q, s.now, TRUE)
       IN /\ s' = a.s
          /\ g' = [g EXCEPT !.pubs = @ + 1, !.full = @ \/ a.full]
    /\ UNCHANGED <<st, job, writing, failed, rs>>

HoldA(m) ==
    /\ g.pid < PMAX
    /\ s' = Hold(Called(s), m, g.pid + 1).s
    /\ g' = [g EXCEPT !.pid = @ + 1]
    /\ UNCHANGED <<st, job, writing, failed, rs>>

HeardA(m) ==
    /\ s.mb[m] # <<>>
    /\ s' = Heard(Called(s), m)
    /\ UNCHANGED <<st, job, writing, failed, rs, g>>

TickA ==
    /\ s' = Tick(s)
    /\ g' = [g EXCEPT !.ticked = TRUE]
    /\ UNCHANGED <<st, job, writing, failed, rs>>

Advance ==
    /\ g.ticked /\ s.now < TMAX
    /\ s' = [s EXCEPT !.now = @ + 1]
    /\ g' = [g EXCEPT !.ticked = FALSE]
    /\ UNCHANGED <<st, job, writing, failed, rs>>

\* Part::next_store_write (a call that finds no job may still pop marks of records gone)
Take ==
    /\ ~writing
    /\ LET r == NextJob(s) IN
       /\ r.s # s \/ r.job.k # "none"
       /\ s' = r.s
       /\ job' = r.job
       /\ writing' = (r.job.k # "none")
    /\ UNCHANGED <<st, failed, rs, g>>

WriteOk ==
    /\ writing /\ job.k # "none"
    /\ st' = Apply(st, job)
    /\ job' = NoJob /\ writing' = FALSE
    /\ UNCHANGED <<s, failed, rs, g>>

\* Part::store_written(false): counted, the node marked again, the next write after the part's clock moved on
WriteFail ==
    /\ FAIL /\ writing /\ job.k # "none"
    /\ s' = Failed(s, job)
    /\ job' = NoJob /\ writing' = FALSE /\ failed' = TRUE
    /\ UNCHANGED <<st, rs, g>>

\* what a restore put back, for RestoredLive
Restored(m, t, st1) ==
    [at |-> t,
     recs |-> {[n |-> n, rcv |-> m.rec[n].rcv, bad |-> st1.rec[n].bad] : n \in {k \in Nodes : m.rec[k].seq # 0}},
     pks |-> UNION {{m.mb[k][j] : j \in 1..Len(m.mb[k])} : k \in Members}]

\* the process stops (in the middle of the write out, if one is) and starts again with the same identity and store
Restart(t, mode) ==
    /\ g.rst < MAXR
    /\ IF writing THEN mode \in TORN \cup {"lost", "whole"} /\ TearOk(job, mode) ELSE mode = "lost"
    /\ LET st1 == IF writing THEN Tear(st, job, mode) ELSE st
           m == Restore(Machine0(t), t, st1)
       IN /\ st' = st1
          /\ s' = m
          /\ rs' = Restored(m, t, st1)
          /\ g' = [g EXCEPT !.rst = @ + 1, !.ticked = FALSE,
                            !.tear = @ \/ (mode \in {"noparse", "noverify", "prefix"}),
                            !.back = @ \/ (t < s.now /\ (rs'.recs # {} \/ rs'.pks # {}))]
    /\ job' = NoJob /\ writing' = FALSE
    /\ UNCHANGED failed

\* the run ends (Part::end) and the same part is run again: the write future of the first run is dropped (it may
\* have landed in part) and Part::end gives its node back to be written again; the part was restored, so the next
\* run loads and restores nothing (fix R2)
Rerun(mode) ==
    /\ RERUN /\ g.rst < MAXR
    /\ IF writing THEN mode \in TORN \cup {"lost", "whole"} /\ TearOk(job, mode) ELSE mode = "lost"
    /\ st' = IF writing THEN Tear(st, job, mode) ELSE st
    /\ s' = IF writing THEN Requeue(s, job) ELSE s
    /\ job' = NoJob /\ writing' = FALSE
    /\ g' = [g EXCEPT !.rst = @ + 1]
    /\ UNCHANGED <<failed, rs>>

Next == \/ \E n \in Nodes, q \in 1..SEQS : Publish(n, q)
        \/ \E m \in Members : HoldA(m) \/ HeardA(m)
        \/ TickA \/ Advance \/ Take \/ WriteOk \/ WriteFail
        \/ \E t \in CLOCKS, mode \in TORN \cup {"lost", "whole"} : Restart(t, mode) \/ Rerun(mode)

Spec == Init /\ [][Next]_vars

TypeOK == /\ s.now \in 0..TMAX
          /\ writing \in BOOLEAN
          /\ job.k \in {"none", "put", "remove", "mail"}
          /\ \A n \in Nodes : s.rec[n].seq \in 0..SEQS /\ st.rec[n].seq \in 0..SEQS
          /\ \A m \in Members : Len(s.mb[m]) <= MBP

RestoredLive == /\ \A x \in rs.recs : SatSub(rs.at, x.rcv) < TTL /\ x.bad = "ok"
                /\ \A p \in rs.pks : SatSub(rs.at, p.at) < AGE

MailOrdered == \A m \in Members : \A j \in 1..(Len(s.mb[m]) - 1) : s.mb[m][j].id < s.mb[m][j + 1].id

\* every write the machine asked for is done
Quiet == ~writing /\ s.kr = {} /\ s.kx = {} /\ s.km = <<>>

RecSynced == Quiet => \A n \in Nodes :
                 /\ (s.rec[n].seq = 0) = (st.rec[n].seq = 0)
                 /\ s.rec[n].seq # 0 => st.rec[n].seq = s.rec[n].seq /\ st.rec[n].bad = "ok"

LifeSynced == Quiet => \A n \in Nodes :
                  s.rec[n].seq # 0 /\ st.rec[n].seq = s.rec[n].seq => st.rec[n].rcv = s.rec[n].rcv

MailSynced == Quiet => \A m \in Members : Live(st.mail[m].pk, s.now) = Live(s.mb[m], s.now)

\* a store behind the machine's mailboxes is counted (counters live as long as the machine: a restart restores
\* from the store, and the two agree again)
MailCounted == Quiet => (\A m \in Members : Live(st.mail[m].pk, s.now) = Live(s.mb[m], s.now)) \/ s.errs > 0

MarksBounded == /\ Cardinality(s.kr) <= XCAP /\ Cardinality(s.kh) <= XCAP /\ Cardinality(s.kx) <= XCAP
                /\ Len(s.km) <= NM

KeptBounded == Cardinality({n \in Nodes : st.rec[n].seq # 0}) <= RCAP

WritingHasJob == writing = (job.k # "none")

\* witnesses: each must be violated
NoFull == ~g.full
NoTear == ~g.tear
NoBack == ~g.back
=============================================================================
