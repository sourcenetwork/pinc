------------------------- MODULE FacadeRelayKeepOps -------------------------
(***************************************************************************)
(* What a node that carries the relay role keeps across a restart, step    *)
(* for step: crates/pinc/src/relay/state/keep.rs (Keep, note_record,       *)
(* note_mail, note_sweep, next_job, restore) over the parts of the state   *)
(* machine it reads (pinc-connect relay/records.rs accept and sweep,       *)
(* mailbox.rs push_at, expire, sweep and the drain of route.rs            *)
(* deliver_held), and the Store calls of relay/store.rs (put, remove,      *)
(* put_mailbox, load). FacadeRelayKeep.tla checks them over every         *)
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
(*   ls    the machine's last sweep (clients.rs last_sweep, 0 at start);   *)
(*   rec   per node [seq, rcv], seq 0 when no record is stored;            *)
(*   mb    per member the held packets [id, at], oldest first;             *)
(*   slot  the members holding a mailbox member slot;                      *)
(*   kr kh kx km kc   Keep.records, held, removed, mail, count;            *)
(*   errs  Counters.store_errors.                                          *)
(* Packets of one member have equal length, so MAILBOX_BYTES is MBP        *)
(* packets. The store st: per node [seq, rcv, bad] (bad: "ok", or a torn   *)
(* put that does not parse or does not verify), per member [has, pk] (pk  *)
(* the packets a blob decodes to, up to the first that does not parse).    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NR,    \* record nodes
          NM,    \* mailbox members
          RCAP,  \* the record table of the machine (limits.rs RECORDS)
          MCAP,  \* the mailbox member table (MAILBOX_MEMBERS)
          MBP,   \* the packets one member's mailbox holds (MAILBOX_BYTES over equal packets)
          MAILQ, \* the most members marked for a mailbox write (keep.rs: 4 * MAILBOX_MEMBERS)
          TTL,   \* RECORD_TTL_NS in units
          AGE    \* Limits.mailbox_max_age_ns in units

Nodes == 1..NR
Members == 1..NM

NoRec == [seq |-> 0, rcv |-> 0]
NoSt == [seq |-> 0, rcv |-> 0, bad |-> "ok"]
NoMail == [has |-> FALSE, pk |-> <<>>]
NoJob == [k |-> "none", n |-> 0, seq |-> 0, rcv |-> 0, pk |-> <<>>]

SatSub(a, b) == IF a > b THEN a - b ELSE 0
InSeq(x, q) == \E j \in 1..Len(q) : q[j] = x
Push1(q, x) == IF InSeq(x, q) THEN q ELSE Append(q, x)
Front(q) == SubSeq(q, 1, Len(q) - 1)
Last(q) == q[Len(q)]
Count(rec) == Cardinality({n \in Nodes : rec[n].seq # 0})

\* Core::new at relay clock t: an empty machine and an empty Keep
Machine0(t) == [now |-> t, ls |-> 0, rec |-> [n \in Nodes |-> NoRec], mb |-> [m \in Members |-> <<>>],
                slot |-> {}, kr |-> <<>>, kh |-> <<>>, kx |-> <<>>, km |-> <<>>, kc |-> 0, errs |-> 0]
St0 == [rec |-> [n \in Nodes |-> NoSt], mail |-> [m \in Members |-> NoMail]]

\* keep.rs note_record: skipped while restoring (the caller passes note = FALSE then)
NoteRecord(s, n) == [s EXCEPT !.kr = Push1(@, n), !.kh = Push1(@, n)]
\* keep.rs note_mail: a mark past 4 * MAILBOX_MEMBERS is dropped without a count
NoteMail(s, m) == IF ~InSeq(m, s.km) /\ Len(s.km) < MAILQ THEN [s EXCEPT !.km = Append(@, m)] ELSE s

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

\* a packet held for member m (route.rs hold, MailboxStored marks the member)
Hold(s, m, id) ==
    LET r == PushAt(s, m, [id |-> id, at |-> s.now])
    IN [ok |-> r.ok, s |-> IF r.ok THEN NoteMail(r.s, m) ELSE r.s]

\* Core::on_heard of the member: deliver_held drains every live packet (MailboxDelivered marks the member);
\* the expired ones are dropped without a mark
Heard(s, m) ==
    LET live == Expire(s.mb[m], s.now)
        s1 == [s EXCEPT !.mb[m] = <<>>]
    IN IF live # <<>> THEN NoteMail(s1, m) ELSE s1

\* clients.rs handle_timeout: the sweep runs when SWEEP_NS passed since the last one (a unit is longer)
Sweep(s) ==
    IF s.now <= s.ls THEN s
    ELSE [s EXCEPT !.ls = s.now,
                   !.rec = [n \in Nodes |-> IF s.rec[n].seq # 0 /\ SatSub(s.now, s.rec[n].rcv) >= TTL
                                            THEN NoRec ELSE s.rec[n]],
                   !.mb = [m \in Members |-> Expire(s.mb[m], s.now)],
                   !.slot = {m \in s.slot : Expire(s.mb[m], s.now) # <<>>}]

\* keep.rs note_sweep: only a drop in the count looks for records gone
NoteSweep(s) ==
    LET c == Count(s.rec) IN
    IF c >= s.kc THEN [s EXCEPT !.kc = c]
    ELSE LET gone == SelectSeq(s.kh, LAMBDA x : s.rec[x].seq = 0)
             alive == SelectSeq(s.kh, LAMBDA x : s.rec[x].seq # 0)
         IN [s EXCEPT !.kc = c, !.kh = alive, !.kr = SelectSeq(@, LAMBDA x : ~InSeq(x, gone)), !.kx = @ \o gone]

\* Core::on_timeout: the machine's timers, then note_sweep
Tick(s) == NoteSweep(Sweep(s))

\* next_job, the records loop: pop from the end until a record is still stored
RECURSIVE PopRec(_)
PopRec(s) ==
    IF s.kr = <<>> THEN [job |-> NoJob, s |-> s]
    ELSE LET n == Last(s.kr)
             s1 == [s EXCEPT !.kr = Front(@)]
         IN IF s.rec[n].seq # 0
            THEN [job |-> [NoJob EXCEPT !.k = "put", !.n = n, !.seq = s.rec[n].seq, !.rcv = s.rec[n].rcv], s |-> s1]
            ELSE PopRec(s1)

\* keep.rs next_job: a removal first, then a record, then a member's packets (the blob of held_packet 0, 1, ...)
NextJob(s) ==
    IF s.kx # <<>>
    THEN [job |-> [NoJob EXCEPT !.k = "remove", !.n = Last(s.kx)], s |-> [s EXCEPT !.kx = Front(@)]]
    ELSE LET r == PopRec(s) IN
         IF r.job.k # "none" \/ r.s.km = <<>> THEN r
         ELSE LET m == Last(r.s.km)
              IN [job |-> [NoJob EXCEPT !.k = "mail", !.n = m, !.pk = r.s.mb[m]], s |-> [r.s EXCEPT !.km = Front(@)]]

\* StoreWrite::run of a job on the store (an empty blob forgets the member)
Apply(st, j) ==
    CASE j.k = "put" -> [st EXCEPT !.rec[j.n] = [seq |-> j.seq, rcv |-> j.rcv, bad |-> "ok"]]
      [] j.k = "remove" -> [st EXCEPT !.rec[j.n] = NoSt]
      [] j.k = "mail" -> [st EXCEPT !.mail[j.n] = IF j.pk = <<>> THEN NoMail ELSE [has |-> TRUE, pk |-> j.pk]]
      [] OTHER -> st

\* a write cut by a restart: "lost" (nothing landed), "whole" (all of it landed), "noparse" / "noverify" (a put
\* landed as bytes that do not parse / parse and do not verify), "prefix" (a blob landed up to the middle of its last
\* packet, which decode then stops before)
TearOk(j, mode) ==
    \/ mode \in {"lost", "whole"}
    \/ mode \in {"noparse", "noverify"} /\ j.k = "put"
    \/ mode = "prefix" /\ j.k = "mail" /\ j.pk # <<>>
Tear(st, j, mode) ==
    CASE mode = "lost" -> st
      [] mode = "whole" -> Apply(st, j)
      [] mode \in {"noparse", "noverify"} -> [st EXCEPT !.rec[j.n] = [seq |-> j.seq, rcv |-> j.rcv, bad |-> mode]]
      [] OTHER -> [st EXCEPT !.mail[j.n] = [has |-> TRUE, pk |-> Front(j.pk)]]

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
                          [] try /\ a.ok -> [s1 EXCEPT !.kh = Append(@, k)]
                          [] OTHER -> [s1 EXCEPT !.kx = Append(@, k)]
              IN RestRec(s2, t, st, k + 1)

\* restore_held for each packet of one blob, oldest first: [s, d], d when one was refused
RECURSIVE RestPk(_, _, _, _)
RestPk(s, m, l, d) ==
    IF l = <<>> THEN [s |-> s, d |-> d]
    ELSE IF SatSub(s.now, Head(l).at) >= AGE THEN RestPk(s, m, Tail(l), TRUE)
    ELSE LET r == PushAt(s, m, Head(l)) IN RestPk(r.s, m, Tail(l), d \/ ~r.ok)

\* the mailboxes loop: a member with a refused packet, or a blob that decodes to nothing, is marked (no cap here)
RECURSIVE RestMail(_, _, _)
RestMail(s, st, k) ==
    IF k > NM THEN s
    ELSE IF ~st.mail[k].has THEN RestMail(s, st, k + 1)
    ELSE LET r == RestPk(s, k, st.mail[k].pk, FALSE)
             s1 == IF r.d \/ st.mail[k].pk = <<>> THEN [r.s EXCEPT !.km = Append(@, k)] ELSE r.s
         IN RestMail(s1, st, k + 1)

\* Core::restore at relay clock t into the machine s (a fresh one after a restart, the same one on a second run)
Restore(s, t, st) ==
    LET s0 == [s EXCEPT !.now = t]
        s2 == RestMail(RestRec(s0, t, st, 1), st, 1)
    IN [s2 EXCEPT !.kc = Count(s2.rec)]

\* the live packets of a list at time t
Live(l, t) == SelectSeq(l, LAMBDA p : SatSub(t, p.at) < AGE)
=============================================================================
