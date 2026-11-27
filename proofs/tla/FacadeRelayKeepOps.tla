------------------------- MODULE FacadeRelayKeepOps -------------------------
(***************************************************************************)
(* What a node that carries the relay role keeps across a restart, step    *)
(* for step: crates/pinc/src/relay/state/keep.rs (Keep, note_record,       *)
(* note_mail, note_sweep, next_job, requeue, write_failed, restore) and    *)
(* relay/part.rs store_written, over the parts of the state                *)
(* machine it reads (pinc-connect relay/records.rs accept and sweep,       *)
(* mailbox.rs push_at, expire, sweep and the drain of route.rs             *)
(* deliver_held), and the Store calls of relay/store.rs (put, remove,      *)
(* put_mailbox, load). FacadeRelayKeep.tla checks them over every          *)
(* sequence of calls at small sizes; TraceFacadeRelayKeep.tla replays the  *)
(* calls a test made on the real code.                                     *)
(*                                                                         *)
(* Time is in units: the trace test uses only multiples of one unit, so    *)
(* every comparison of the code (now - at < max) has the same answer at    *)
(* unit scale. Record nodes are 1..NR and mailbox members 1..NM, numbered  *)
(* in the order of their store key (store.rs node_key), which is the order *)
(* MemStore::load gives them back in.                                      *)
(*                                                                         *)
(* The machine state s:                                                    *)
(*   now   the relay clock;                                                *)
(*   ln    Core.last_now, the clock of the last call that brought an       *)
(*         event (on_read, on_datagram, on_timeout; Core::new at start);   *)
(*   ls    the machine's last sweep (clients.rs last_sweep, 0 at start);   *)
(*   rec   per node [seq, rcv], seq 0 when no record is stored;            *)
(*   mb    per member the held packets [id, at], oldest first;             *)
(*   sl    per member the time of its sleep mark, -1 when none (a mark     *)
(*         lasts AGE, the life of a held packet, and its packets end with  *)
(*         it);                                                            *)
(*   slot  the members holding a mailbox member slot;                      *)
(*   kr kh kx   Keep.records, held, removed: sets of nodes, taken lowest   *)
(*         store key first (BTreeMap pop_first);                           *)
(*   km    Keep.mail, a list taken from its front (first in, first out); *)
(*   kn    the clock of Keep's last check of held, -1 before the first     *)
(*         (Keep.next_sweep is SWEEP_NS later, far below a unit);          *)
(*   ra    the last_now of the last failed write, -1 when none: the next   *)
(*         write waits for RETRY_NS (Keep.retry_at), far below a unit;     *)
(*   fq    Keep.failed, the failed writes [k, n, tr] oldest first, tr the  *)
(*         tries so far, served after every mark not tried yet;            *)
(*   tr    Keep.tries, the tries of the write taken last (0: a fresh mark);*)
(*   errs  Counters.store_errors.                                          *)
(* Packets of one member have equal length, so MAILBOX_BYTES is MBP        *)
(* packets. The store st: per node [seq, rcv, bad] (bad: "ok", or a torn   *)
(* put that does not parse or does not verify), per member [has, pk] (pk   *)
(* the packets a blob decodes to, up to the first that does not parse, mk  *)
(* the mark the blob's trailer keeps, -1 when it keeps none, gb whether    *)
(* bytes follow that are neither a packet nor a version 1 trailer: a torn  *)
(* packet or a torn trailer, which restore counts as a store error).       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NR,    \* record nodes
          NM,    \* mailbox members
          RCAP,  \* the record table of the machine (limits.rs RECORDS)
          MCAP,  \* the mailbox member table (MAILBOX_MEMBERS)
          MBP,   \* the packets one member's mailbox holds (MAILBOX_BYTES over equal packets)
          MAILQ, \* the most members marked for a mailbox write (keep.rs: CARRIERS + MAILBOX_MEMBERS)
          TTL,   \* RECORD_TTL_NS in units
          AGE,   \* Limits.mailbox_max_age_ns in units
          MAXT,  \* the tries before a failing write is given up (keep.rs MAX_TRIES)
          FQ     \* the most failed writes waiting (keep.rs FAILED)

Nodes == 1..NR
Members == 1..NM

NoRec == [seq |-> 0, rcv |-> 0]
NoSt == [seq |-> 0, rcv |-> 0, bad |-> "ok"]
NoMail == [has |-> FALSE, pk |-> <<>>, mk |-> -1, gb |-> FALSE]
NoJob == [k |-> "none", n |-> 0, seq |-> 0, rcv |-> 0, pk |-> <<>>, mk |-> -1]

SatSub(a, b) == IF a > b THEN a - b ELSE 0
InSeq(x, q) == \E j \in 1..Len(q) : q[j] = x
Front(q) == SubSeq(q, 1, Len(q) - 1)
Count(rec) == Cardinality({n \in Nodes : rec[n].seq # 0})
MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y
\* keep.rs: the removals waiting for the store, at most twice the record table
XCAP == 2 * RCAP

\* Core::new at relay clock t: an empty machine and an empty Keep
Machine0(t) == [now |-> t, ln |-> t, ls |-> 0, rec |-> [n \in Nodes |-> NoRec], mb |-> [m \in Members |-> <<>>],
                slot |-> {}, sl |-> [m \in Members |-> -1], kr |-> {}, kh |-> {}, kx |-> {}, km |-> <<>>, kn |-> -1, ra |-> -1, fq |-> <<>>, tr |-> 0,
                errs |-> 0]
\* a call that brings an event at the machine's clock (on_read, on_datagram) sets last_now
Called(s) == [s EXCEPT !.ln = s.now]
St0 == [rec |-> [n \in Nodes |-> NoSt], mail |-> [m \in Members |-> NoMail]]

\* keep.rs note_record: skipped while restoring (the caller passes note = FALSE then)
NoteRecord(s, n) == [s EXCEPT !.kr = @ \cup {n}, !.kh = @ \cup {n}]
\* keep.rs push_mail: a mark past CARRIERS + MAILBOX_MEMBERS is lost and counted as a failed store write (fix R10)
PushMail(s, m) == IF Len(s.km) < MAILQ THEN [s EXCEPT !.km = Append(@, m)] ELSE [s EXCEPT !.errs = @ + 1]
\* keep.rs note_mail: a member marked already stays marked once
NoteMail(s, m) == IF InSeq(m, s.km) THEN s ELSE PushMail(s, m)

\* Keep::mark_removed for each node of g, lowest key first: a node already marked stays, a new one is marked while
\* the table has room; lost when a mark found no room
RECURSIVE MarkRm(_, _)
MarkRm(x, g) ==
    IF g = {} THEN [x |-> x, lost |-> FALSE]
    ELSE LET n == MinOf(g)
             fit == n \in x \/ Cardinality(x) < XCAP
             r == MarkRm(IF fit THEN x \cup {n} ELSE x, g \ {n})
         IN [x |-> r.x, lost |-> r.lost \/ ~fit]
\* one node marked for removal; a mark with no room is counted
MarkOne(s, n) == LET r == MarkRm(s.kx, {n}) IN [s EXCEPT !.kx = r.x, !.errs = IF r.lost THEN @ + 1 ELSE @]

\* records.rs accept, through store (RecordStored traced only for a new record or a higher seq); t is the time the
\* record is received at: now for a publish, the kept received time for restore_record
Accept(s, n, q, t, note) ==
    LET r == s.rec[n] IN
    IF r.seq # 0 /\ q < r.seq THEN [ok |-> FALSE, full |-> FALSE, s |-> s]
    ELSE IF r.seq # 0 /\ q = r.seq THEN [ok |-> TRUE, full |-> FALSE, s |-> [s EXCEPT !.rec[n].rcv = t]]
    ELSE IF r.seq = 0 /\ Count(s.rec) >= RCAP THEN [ok |-> FALSE, full |-> TRUE, s |-> s]
    ELSE LET s1 == [s EXCEPT !.rec[n] = [seq |-> q, rcv |-> t]]
         IN [ok |-> TRUE, full |-> FALSE, s |-> IF note THEN NoteRecord(s1, n) ELSE s1]

\* mailbox.rs expire: drop from the front while the oldest is past its age
RECURSIVE Expire(_, _)
Expire(l, t) == IF l # <<>> /\ SatSub(t, Head(l).at) >= AGE THEN Expire(Tail(l), t) ELSE l
\* push_at: the oldest go while the new packet does not fit
Room(l) == IF Len(l) >= MBP THEN SubSeq(l, Len(l) - MBP + 2, Len(l)) ELSE l
\* mailbox.rs push_at at the machine's now for packet p = [id, at]: NoSlot when the member table is full
PushAt(s, m, p) ==
    IF m \notin s.slot /\ Cardinality(s.slot) >= MCAP THEN [ok |-> FALSE, s |-> s]
    ELSE [ok |-> TRUE, s |-> [s EXCEPT !.slot = @ \cup {m}, !.mb[m] = Append(Room(Expire(@, s.now)), p)]]

\* a sleep mark ended at time t: set, and AGE or more before t
Ended(x, t) == x # -1 /\ SatSub(t, x) >= AGE
Min(a, b) == IF a < b THEN a ELSE b
\* restore_held of a packet held at `at` for a member with no mark marks it asleep since then (a blob that kept no mark);
\* the caller passes the time at most the clock (mod.rs: a time ahead of now counts as now)
Derive(s, m, at) == IF s.sl[m] = -1 THEN [s EXCEPT !.sl[m] = at] ELSE s

\* an accepted sleep notice with a new clock (discovery.rs sleep_notice): the mark is set at now and SleepAccepted marks
\* the member for a write (a copy of a notice changes nothing and is not here: ConnectRelay.tla MarkKept)
Notice(s, m) == NoteMail([s EXCEPT !.sl[m] = s.now], m)

\* a packet held for member m (route.rs hold under the member's mark, or restore_held, which marks a member with no
\* mark; MailboxStored marks the member for a write)
Hold(s, m, id) ==
    LET r == PushAt(s, m, [id |-> id, at |-> s.now])
    IN [ok |-> r.ok, s |-> IF r.ok THEN NoteMail(Derive(r.s, m, s.now), m) ELSE r.s]

\* Core::on_heard of the member (route.rs udp_heard, release_held): deliver_held drains every live packet
\* (MailboxDelivered marks the member for a write) and the mark stays; the expired packets are dropped without a mark
Heard(s, m) ==
    LET live == Expire(s.mb[m], s.now)
        s1 == [s EXCEPT !.mb[m] = <<>>]
    IN IF live # <<>> THEN NoteMail(s1, m) ELSE s1
\* the member came back (clients.rs carrier_opened, route.rs member_returned): its mark ends (SleepEnded) and
\* deliver_held drains every live packet; either marks the member for a write
Return(s, m) ==
    LET live == Expire(s.mb[m], s.now)
        s1 == [s EXCEPT !.mb[m] = <<>>, !.sl[m] = -1]
    IN IF live # <<>> \/ s.sl[m] # -1 THEN NoteMail(s1, m) ELSE s1

\* clients.rs handle_timeout: the sweep runs when SWEEP_NS passed since the last one (a unit is longer); a mark past
\* AGE ends and the packets held under it end with it, without a write (a restore drops a kept blob whose mark ended)
Sweep(s) ==
    IF s.now <= s.ls THEN s
    ELSE [s EXCEPT !.ls = s.now,
                   !.rec = [n \in Nodes |-> IF s.rec[n].seq # 0 /\ SatSub(s.now, s.rec[n].rcv) >= TTL
                                            THEN NoRec ELSE s.rec[n]],
                   !.sl = [m \in Members |-> IF Ended(s.sl[m], s.now) THEN -1 ELSE s.sl[m]],
                   !.mb = [m \in Members |-> IF Ended(s.sl[m], s.now) THEN <<>> ELSE Expire(s.mb[m], s.now)],
                   !.slot = {m \in s.slot : ~Ended(s.sl[m], s.now) /\ Expire(s.mb[m], s.now) # <<>>}]
\* for the witness _w_mlife: the mark ends and the packets held under it stay
SweepKeepMail(s) ==
    IF s.now <= s.ls THEN s
    ELSE [s EXCEPT !.ls = s.now,
                   !.rec = [n \in Nodes |-> IF s.rec[n].seq # 0 /\ SatSub(s.now, s.rec[n].rcv) >= TTL
                                            THEN NoRec ELSE s.rec[n]],
                   !.sl = [m \in Members |-> IF Ended(s.sl[m], s.now) THEN -1 ELSE s.sl[m]],
                   !.mb = [m \in Members |-> Expire(s.mb[m], s.now)],
                   !.slot = {m \in s.slot : Expire(s.mb[m], s.now) # <<>>}]

\* keep.rs note_sweep: once per SWEEP_NS, whatever the count did (fix R4), the records the store holds that the
\* machine dropped are marked for removal; marks the table has no room for count one store error per check
NoteSweep(s) ==
    IF s.now <= s.kn THEN s
    ELSE LET gone == {x \in s.kh : s.rec[x].seq = 0}
             r == MarkRm(s.kx, gone)
         IN [s EXCEPT !.kn = s.now, !.kh = @ \ gone, !.kr = @ \ gone, !.kx = r.x,
                      !.errs = IF r.lost THEN @ + 1 ELSE @]

\* Core::on_timeout: last_now, the machine's timers, then note_sweep
Tick(s) == NoteSweep(Sweep(Called(s)))

\* next_job, the records loop: take the lowest key until a record is still stored
RECURSIVE PopRec(_)
PopRec(s) ==
    IF s.kr = {} THEN [job |-> NoJob, s |-> s]
    ELSE LET n == MinOf(s.kr)
             s1 == [s EXCEPT !.kr = @ \ {n}]
         IN IF s.rec[n].seq # 0
            THEN [job |-> [NoJob EXCEPT !.k = "put", !.n = n, !.seq = s.rec[n].seq, !.rcv = s.rec[n].rcv], s |-> s1]
            ELSE PopRec(s1)

\* the mark a member's blob keeps (its trailer)
MarkOf(s, m) == s.sl[m]
\* for the witness _w_mark: the blob keeps no mark (the code before the fix)
MarkOfNone(s, m) == -1
MailJob(s, m) == [NoJob EXCEPT !.k = "mail", !.n = m, !.pk = s.mb[m], !.mk = MarkOf(s, m)]

\* next_job, the failed loop: the oldest failed write, with its tries; a Put of a record the machine no longer holds
\* and a Remove of a record that came back are dropped
RECURSIVE PopFailed(_)
PopFailed(s) ==
    IF s.fq = <<>> THEN [job |-> NoJob, s |-> s]
    ELSE LET x == Head(s.fq)
             s1 == [s EXCEPT !.fq = Tail(@), !.tr = x.tr]
         IN CASE x.k = "put" /\ s.rec[x.n].seq # 0 ->
                   [job |-> [NoJob EXCEPT !.k = "put", !.n = x.n, !.seq = s.rec[x.n].seq, !.rcv = s.rec[x.n].rcv],
                    s |-> s1]
              [] x.k = "remove" /\ s.rec[x.n].seq = 0 -> [job |-> [NoJob EXCEPT !.k = "remove", !.n = x.n], s |-> s1]
              [] x.k = "mail" -> [job |-> MailJob(s, x.n), s |-> s1]
              [] OTHER -> PopFailed([s EXCEPT !.fq = Tail(@)])

\* keep.rs next_job: nothing while a failed write waits for its retry (last_now before retry_at, fix R3); else, with
\* the tries reset, a removal first, then a record, then a member's packets (the blob of held_packet 0, 1, ...), and
\* only then the oldest failed write
NextJob(s) ==
    IF s.ln <= s.ra THEN [job |-> NoJob, s |-> s]
    ELSE LET s0 == [s EXCEPT !.tr = 0] IN
    IF s0.kx # {}
    THEN [job |-> [NoJob EXCEPT !.k = "remove", !.n = MinOf(s0.kx)], s |-> [s0 EXCEPT !.kx = @ \ {MinOf(s0.kx)}]]
    ELSE LET r == PopRec(s0) IN
         IF r.job.k # "none" THEN r
         ELSE IF r.s.km # <<>> THEN [job |-> MailJob(r.s, Head(r.s.km)), s |-> [r.s EXCEPT !.km = Tail(@)]]
         ELSE PopFailed(r.s)

\* keep.rs requeue: the write of job j was dropped with its run (Part::end): a write tried before goes back to the
\* front of the failed writes with its tries while they have room; else its node is marked again (a record only in
\* records: held keeps it unless a sweep took it out); the next write of a record reads the newest from the machine
Requeue(s, j) ==
    LET s0 == [s EXCEPT !.tr = 0] IN
    IF s.tr > 0 /\ Len(s.fq) < FQ THEN [s0 EXCEPT !.fq = <<[k |-> j.k, n |-> j.n, tr |-> s.tr]>> \o @]
    ELSE CASE j.k = "put" -> [s0 EXCEPT !.kr = @ \cup {j.n}]
           [] j.k = "remove" -> MarkOne(s0, j.n)
           [] j.k = "mail" -> NoteMail(s0, j.n)
           [] OTHER -> s0

\* keep.rs write_failed: a failed write is given up when it was tried MAX_TRIES times or the failed writes are full
GivenUp(s) == s.tr + 1 >= MAXT \/ Len(s.fq) >= FQ
\* Part::store_written(false), keep.rs write_failed: counted, and the next write waits from the part's last_now (fix
\* R3); given up, counted once more; else queued behind the failed writes with one try more, unless its mark waits there
Failed(s, j) ==
    LET s1 == [s EXCEPT !.tr = 0, !.ra = s.ln, !.errs = @ + 1]
    IN IF GivenUp(s) THEN [s1 EXCEPT !.errs = @ + 1]
       ELSE IF \E x \in 1..Len(s.fq) : s.fq[x].k = j.k /\ s.fq[x].n = j.n THEN s1
       ELSE [s1 EXCEPT !.fq = Append(@, [k |-> j.k, n |-> j.n, tr |-> s.tr + 1])]

\* StoreWrite::run of a job on the store (an empty blob forgets the member)
Apply(st, j) ==
    CASE j.k = "put" -> [st EXCEPT !.rec[j.n] = [seq |-> j.seq, rcv |-> j.rcv, bad |-> "ok"]]
      [] j.k = "remove" -> [st EXCEPT !.rec[j.n] = NoSt]
      [] j.k = "mail" -> [st EXCEPT !.mail[j.n] = IF j.pk = <<>> /\ j.mk = -1 THEN NoMail
                                                ELSE [has |-> TRUE, pk |-> j.pk, mk |-> j.mk, gb |-> FALSE]]
      [] OTHER -> st

\* a write cut by a restart: "lost" (nothing landed), "whole" (all of it landed), "noparse" / "noverify" (a put
\* landed as bytes that do not parse / parse and do not verify), "prefix" (a blob landed short of its last byte: of
\* its mark trailer when it has one, which decode then finds torn, else of its last packet, which decode stops before;
\* either is a remainder restore counts), "trailer" (a blob landed whole up to its mark trailer and none of it: the old
\* form, nothing to count)
TearOk(j, mode) ==
    \/ mode \in {"lost", "whole"}
    \/ mode \in {"noparse", "noverify"} /\ j.k = "put"
    \/ mode = "prefix" /\ j.k = "mail" /\ (j.pk # <<>> \/ j.mk # -1)
    \/ mode = "trailer" /\ j.k = "mail" /\ j.mk # -1
Tear(st, j, mode) ==
    CASE mode = "lost" -> st
      [] mode = "whole" -> Apply(st, j)
      [] mode \in {"noparse", "noverify"} -> [st EXCEPT !.rec[j.n] = [seq |-> j.seq, rcv |-> j.rcv, bad |-> mode]]
      [] mode = "trailer" -> [st EXCEPT !.mail[j.n] = [has |-> TRUE, pk |-> j.pk, mk |-> -1, gb |-> FALSE]]
      [] OTHER -> [st EXCEPT !.mail[j.n] = [has |-> TRUE, pk |-> IF j.mk # -1 THEN j.pk ELSE Front(j.pk), mk |-> -1,
                                            gb |-> TRUE]]

\* keep.rs restore, the records loop over the kept records from node k on: parse, lifetime, restore_record
\* (verified like a replica, received at the kept time, no mark while restoring)
RECURSIVE RestRec(_, _, _, _)
RestRec(s, t, st, k) ==
    IF k > NR THEN s
    ELSE LET r == st.rec[k] IN
         IF r.seq = 0 THEN RestRec(s, t, st, k + 1)
         ELSE LET live == SatSub(t, r.rcv) < TTL
                  a == Accept(s, k, r.seq, r.rcv, FALSE)
                  try == live /\ r.bad = "ok"
                  s1 == IF try THEN a.s ELSE s
                  s2 == CASE r.bad = "noparse" -> [s1 EXCEPT !.errs = @ + 1]
                          [] try /\ a.ok -> [s1 EXCEPT !.kh = @ \cup {k}]
                          [] OTHER -> MarkOne(s1, k)
              IN RestRec(s2, t, st, k + 1)

\* restore_held for each packet of one blob, oldest first: [s, d], d when one was refused
RECURSIVE RestPk(_, _, _, _)
RestPk(s, m, l, d) ==
    IF l = <<>> THEN [s |-> s, d |-> d]
    ELSE IF SatSub(s.now, Head(l).at) >= AGE THEN RestPk(s, m, Tail(l), TRUE)
    ELSE LET r == PushAt(s, m, Head(l))
         IN RestPk(IF r.ok THEN Derive(r.s, m, Min(Head(l).at, s.now)) ELSE r.s, m, Tail(l), d \/ ~r.ok)

\* restore_sleep of a kept mark: the mark comes back with the time it was set at, or the restart's clock when that time
\* is ahead of it (a clock that went back): it then ends one AGE after the restart, never later than its own time would
RestMark(s, k, x) == [s EXCEPT !.sl[k] = Min(x, s.now)]
\* for the witness _w_mtime: the mark starts again at the restart
RestMarkNow(s, k, x) == [s EXCEPT !.sl[k] = s.now]

\* a kept mark that restore_sleep moved back to the clock (its time was ahead) is written again, so the store keeps the
\* mark the machine holds: the sweep that ends it writes nothing, and a later restart with the clock still behind the
\* kept time would bring it and its packets back for another AGE
Rewrite(x, t) == x > t
\* for the witness _w_clamp: the moved mark is not written (the store keeps the time ahead of the clock)
RewriteNone(x, t) == FALSE

\* the mailboxes loop, run twice (restore_mailbox): first over the blobs with a packet, then over the bare marks (w), so
\* the members that keep mail are restored and marked for a write before the marks that hold none; a remainder that is neither a packet nor a version 1 trailer counted once (Q6), a kept mark
\* first (with its time, at most the clock; one that ended takes its packets with it), then the packets; a member with a
\* refused packet, a blob that decodes to nothing, a mark that ended, a kept mark moved back to the clock, or packets
\* kept with no mark (the mark restore_held derived is written) is marked through the cap of the mailbox marks, a mark
\* past it counted (push_mail)
RECURSIVE RestMail(_, _, _, _)
RestMail(sb, st, k, w) ==
    IF k > NM THEN sb
    ELSE IF ~st.mail[k].has \/ (st.mail[k].pk # <<>>) # w THEN RestMail(sb, st, k + 1, w)
    ELSE LET s == IF st.mail[k].gb THEN [sb EXCEPT !.errs = @ + 1] ELSE sb
             x == st.mail[k].mk
             dead == Ended(x, s.now)
             s0 == IF x # -1 /\ ~dead THEN RestMark(s, k, x) ELSE s
             r == IF dead THEN [s |-> s, d |-> TRUE] ELSE RestPk(s0, k, st.mail[k].pk, FALSE)
             s1 == IF \/ r.d
                      \/ x = -1 /\ (st.mail[k].pk = <<>> \/ r.s.sl[k] # -1)
                      \/ x # -1 /\ ~dead /\ Rewrite(x, s.now)
                   THEN PushMail(r.s, k) ELSE r.s
         IN RestMail(s1, st, k + 1, w)

\* Core::restore at relay clock t into a fresh machine s (a second run of the same part does not restore: R2)
Restore(s, t, st) == RestMail(RestMail(RestRec([s EXCEPT !.now = t], t, st, 1), st, 1, TRUE), st, 1, FALSE)

\* the live packets of a list at time t
Live(l, t) == SelectSeq(l, LAMBDA p : SatSub(t, p.at) < AGE)
\* the mark x as a restart at t would bring it back: -1 when none or ended
MarkAt(x, t) == IF Ended(x, t) THEN -1 ELSE x
\* what a restart at t brings back of a kept blob b: nothing when its mark ended, else its live packets
KeptLive(b, t) == IF Ended(b.mk, t) THEN <<>> ELSE Live(b.pk, t)
=============================================================================
