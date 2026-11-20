--------------------------- MODULE FacadeRelayKeep ---------------------------
(***************************************************************************)
(* The records and mailboxes a node that carries the relay role keeps in   *)
(* its Store, and what a restart with the same identity reads back:        *)
(* relay/state/keep.rs (note_record, note_mail, note_sweep, next_job,      *)
(* requeue, write_failed, restore), relay/part.rs (next_store_write,      *)
(* store_written: one write out at a time, a failure counted and tried     *)
(* again once the part's clock moved on, behind the marks not tried yet,   *)
(* at most MAX_TRIES times from a queue of at most FAILED, a write given   *)
(* up counted once more; end: the write out is given back, a write tried   *)
(* before to the front of the failed writes; restored: a second run loads  *)
(* and restores nothing), relay/run.rs                                     *)
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
(*    mailbox members); RoleBounded (the role's own tables: records,       *)
(*    member slots, mailboxes, marks, failed writes and tries stay within  *)
(*    their bounds, in every config, failing writes included);             *)
(*  - StoreOwed (every record in the store that the machine does not hold  *)
(*    is owed a removal: marked, waiting in the failed writes, or out; or  *)
(*    its removal was given up or never marked, for want of room or bytes  *)
(*    that do not parse) and DropsCounted (each such step counted a store  *)
(*    error), in every config; a restart restores from the store and       *)
(*    marks the removal of every record it does not take, so the store     *)
(*    comes back to the machine's records once the removals land;          *)
(*    KeptBounded (the store holds at most RECORDS records) only where     *)
(*    writes do not fail: while removals are refused the store holds more  *)
(*    (_w_kept), and the contract of store.rs Kept.records says the relay  *)
(*    keeps at most RECORDS and removes the rest;                          *)
(*  - WritingHasJob (part.rs: a write is out only while one runs, over the *)
(*    end of a run too);                                                   *)
(*  - TriesBounded, FailedBounded (keep.rs: no write is tried more than    *)
(*    MAX_TRIES times; the failed writes never pass FAILED); FreshFirst    *)
(*    (a failed write delays a mark not tried yet only until the clock     *)
(*    moves on, RETRY_NS); GivenCounted (every failure counts, a write     *)
(*    given up once more); RecBehindCounted, MailBehindCounted (_retry:    *)
(*    with writes given up, the store is behind the machine only for a     *)
(*    node or member whose write was given up since the restart).          *)
(* Witnesses of documented limits (each must be violated): _w_life         *)
(* (LifeSynced: a refresh of the same seq is not written, R7 open),        *)
(* _w_noparse (RecSynced: a record that does not parse is counted and left *)
(* in the store), _w_mailq (MailSynced: a lost mailbox mark, counted),     *)
(* _w_given and _w_gfull (NoGivenTries, NoGivenFull: a write is given up   *)
(* after MAX_TRIES tries, and when the failed writes are full), _w_owed    *)
(* (OwedOnly: a record the machine dropped stays in the store with its     *)
(* removal given up, counted: StoreOwed's other case), _w_kept             *)
(* (KeptBounded: a failed removal waits behind a put that lands, so the    *)
(* store holds more records than the table until the removal lands, or,   *)
(* given up, until a restart marks it again).                              *)
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
          g        \* ghosts: full, tear, back, ticked, pubs, pid, rst; since the last restart: wf (writes failed), gu
                   \* (writes given up), gv (their nodes and members), gt and gq (given up by tries, by a full queue),
                   \* gx (the nodes whose removal was given up), dr (the nodes whose removal was not marked for want
                   \* of room, or whose kept bytes do not parse) and nd (the steps that dropped one: each counts)
vars == <<s, st, job, writing, failed, rs, g>>

Init == /\ s = Restore(Machine0(0), 0, St0)
        /\ st = St0
        /\ job = NoJob
        /\ writing = FALSE
        /\ failed = FALSE
        /\ rs = [at |-> 0, recs |-> {}, pks |-> {}]
        /\ g = [full |-> FALSE, tear |-> FALSE, back |-> FALSE, ticked |-> FALSE, pubs |-> 0, pid |-> 0, rst |-> 0,
               wf |-> 0, gu |-> 0, gv |-> {}, gt |-> FALSE, gq |-> FALSE, gx |-> {}, dr |-> {}, nd |-> 0]

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

\* note_sweep takes the records the machine dropped out of held and marks their removal; one with no room is lost
TickA ==
    LET s1 == Tick(s)
        lost == (s.kh \ s1.kh) \ s1.kx
    IN /\ s' = s1
       /\ g' = [g EXCEPT !.ticked = TRUE, !.dr = @ \cup lost, !.nd = IF lost # {} THEN @ + 1 ELSE @]
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

\* the node or member a write is about
Kind(j) == [k |-> IF j.k = "mail" THEN "mail" ELSE "rec", n |-> j.n]

\* the removal of node n is still to be written: marked, waiting in the failed writes, or out
RemoveOwed(m, j, n) == \/ n \in m.kx
                       \/ \E x \in 1..Len(m.fq) : m.fq[x].k = "remove" /\ m.fq[x].n = n
                       \/ j.k = "remove" /\ j.n = n

\* Part::store_written(false): counted, queued behind the marks not tried yet or given up, the next write after the
\* part's clock moved on
WriteFail ==
    /\ FAIL /\ writing /\ job.k # "none"
    /\ s' = Failed(s, job)
    /\ job' = NoJob /\ writing' = FALSE /\ failed' = TRUE
    /\ LET give == GivenUp(s)
       IN g' = [g EXCEPT !.wf = @ + 1, !.gu = IF give THEN @ + 1 ELSE @, !.gv = IF give THEN @ \cup {Kind(job)} ELSE @,
                         !.gt = @ \/ (give /\ s.tr + 1 >= MAXT), !.gq = @ \/ (give /\ Len(s.fq) >= FQ),
                         !.gx = IF give /\ job.k = "remove" THEN @ \cup {job.n} ELSE @]
    /\ UNCHANGED <<st, rs>>

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
           \* the kept records restore neither takes nor marks for removal: bytes that do not parse, or a mark with
           \* no room; each counted once
           lost == {n \in Nodes : st1.rec[n].seq # 0 /\ m.rec[n].seq = 0 /\ n \notin m.kx}
       IN /\ st' = st1
          /\ s' = m
          /\ rs' = Restored(m, t, st1)
          /\ g' = [g EXCEPT !.rst = @ + 1, !.ticked = FALSE, !.wf = 0, !.gu = 0, !.gv = {}, !.gx = {}, !.dr = lost,
                            !.nd = Cardinality(lost),
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
    /\ LET lost == IF writing /\ job.k = "remove" /\ ~RemoveOwed(s', NoJob, job.n) THEN {job.n} ELSE {}
       IN g' = [g EXCEPT !.rst = @ + 1, !.dr = @ \cup lost, !.nd = IF lost # {} THEN @ + 1 ELSE @]
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

\* every write the machine asked for is done (a failed write waiting to be tried again is one not done)
Quiet == ~writing /\ s.kr = {} /\ s.kx = {} /\ s.km = <<>> /\ s.fq = <<>>

RecOk(n) == /\ (s.rec[n].seq = 0) = (st.rec[n].seq = 0)
            /\ s.rec[n].seq # 0 => st.rec[n].seq = s.rec[n].seq /\ st.rec[n].bad = "ok"
LifeOk(n) == s.rec[n].seq # 0 /\ st.rec[n].seq = s.rec[n].seq => st.rec[n].rcv = s.rec[n].rcv
MailOk(m) == Live(st.mail[m].pk, s.now) = Live(s.mb[m], s.now)

RecSynced == Quiet => \A n \in Nodes : RecOk(n)

LifeSynced == Quiet => \A n \in Nodes : LifeOk(n)

MailSynced == Quiet => \A m \in Members : MailOk(m)

\* a store behind the machine's mailboxes is counted (counters live as long as the machine: a restart restores
\* from the store, and the two agree again)
MailCounted == Quiet => (\A m \in Members : MailOk(m)) \/ s.errs > 0

\* with writes given up (_retry): the store is behind only for a node or member whose write was given up since the
\* restart, which counted it (GivenCounted)
RecBehindCounted == Quiet => \A n \in Nodes : (RecOk(n) /\ LifeOk(n)) \/ [k |-> "rec", n |-> n] \in g.gv
MailBehindCounted == Quiet => \A m \in Members : MailOk(m) \/ [k |-> "mail", n |-> m] \in g.gv

MarksBounded == /\ Cardinality(s.kr) <= XCAP /\ Cardinality(s.kh) <= XCAP /\ Cardinality(s.kx) <= XCAP
                /\ Len(s.km) <= NM /\ Len(s.km) <= MAILQ

\* keep.rs: the write out is at most its MAX_TRIES-th try, and a failed write waits with fewer tries than that
TriesBounded == s.tr < MAXT /\ \A x \in 1..Len(s.fq) : s.fq[x].tr \in 1..(MAXT - 1)
\* keep.rs FAILED: the failed writes never pass the bound
FailedBounded == Len(s.fq) <= FQ
\* a mark not tried yet: a removal, a record the machine still holds, a member's packets
Fresh == s.kx # {} \/ (\E n \in s.kr : s.rec[n].seq # 0) \/ s.km # <<>>
\* a failed write holds the writes back only until the part's clock moves on past the failure (RETRY_NS is below a
\* unit), and then a mark not tried yet is written before any failed write
FreshFirst == /\ s.ra <= s.ln
              /\ (~writing /\ s.ln > s.ra /\ Fresh) => LET r == NextJob(s) IN r.job.k # "none" /\ r.s.tr = 0
\* every failed write is counted, and a write given up once more (since the restart, as the counters)
GivenCounted == s.errs >= g.wf + g.gu

KeptBounded == Cardinality({n \in Nodes : st.rec[n].seq # 0}) <= RCAP

\* every record in the store that the machine does not hold is owed a removal, or its removal was given up or never
\* marked (no room, or bytes that do not parse), which DropsCounted counts; a restart restores from the store and
\* marks the removal of every record it does not take, so what is owed comes back
StoreOwed == \A n \in Nodes : (st.rec[n].seq # 0 /\ s.rec[n].seq = 0) =>
                 RemoveOwed(s, job, n) \/ n \in g.gx \/ n \in g.dr
\* every failed write counts, a write given up once more, and every step that dropped a removal at least once
\* (counters live as long as the machine, as the ghosts since the restart)
DropsCounted == s.errs >= g.wf + g.gu + g.nd

\* the role's own tables within their bounds, whatever the store does: the machine's records, member slots and
\* mailboxes, the marks (MarksBounded), the failed writes (FailedBounded) and the tries (TriesBounded)
RoleBounded == /\ Count(s.rec) <= RCAP /\ Cardinality(s.slot) <= MCAP /\ \A m \in Members : Len(s.mb[m]) <= MBP
               /\ MarksBounded /\ FailedBounded /\ TriesBounded

WritingHasJob == writing = (job.k # "none")

\* witnesses: each must be violated
NoFull == ~g.full
NoTear == ~g.tear
NoBack == ~g.back
NoGivenTries == ~g.gt
NoGivenFull == ~g.gq
\* every record in the store the machine does not hold is owed a removal: fails where a removal is given up or not
\* marked (_w_owed), the case StoreOwed lets the error counter account for
OwedOnly == \A n \in Nodes : (st.rec[n].seq # 0 /\ s.rec[n].seq = 0) => RemoveOwed(s, job, n)
=============================================================================
