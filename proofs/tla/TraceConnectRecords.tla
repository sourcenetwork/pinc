---------------------------- MODULE TraceConnectRecords ----------------------------
(***************************************************************************)
(* Trace validation of the relay's record store: pinc-connect/src/relay/   *)
(* records.rs and the record part of discovery.rs and clients.rs.          *)
(*                                                                         *)
(* The Rust test tests/trace_connect_records.rs drives the real Relay      *)
(* through seeded schedules of every way a record arrives (PUB on a        *)
(* carrier, SYNC from a peer relay, restore_record, set_own_record), the   *)
(* timer, lookups over UDP, sync_record and peers added and removed, with  *)
(* really signed records (good, a flipped signature byte, the key of       *)
(* another node id, bytes that are no record) at times around the 5400 s   *)
(* lifetime, the 1800 s republish and the 1 s sweep. Every event must be   *)
(* the step the operators of ConnectRecordsOps.tla compute: the same       *)
(* answer, the same effects in the same order, and afterwards the same     *)
(* store (for each node: sequence number, home, tag, length, receive time) *)
(* and the same counters.                                                  *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds                       *)
(* connect_records.ndjson.                                                 *)
(***************************************************************************)
EXTENDS ConnectRecordsOps, Json, IOUtils

VARIABLES i, cf, R
vars == <<i, cf, R>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_records.ndjson")
Ev == Trace[i]

Init == i = 1 /\ cf = [R |-> 1, P |-> 1, me |-> 0] /\ R = NewStore(cf)

Rc == [node |-> Ev.rn, seq |-> Ev.rs, home |-> Ev.rh, tag |-> Ev.rt, len |-> Ev.rl, ok |-> Ev.rok = 1]

StoredSet(R1) == {<<n, R1.rec[n].r.seq, R1.rec[n].r.home, R1.rec[n].r.tag, R1.rec[n].r.len, R1.rec[n].rcv>> : n \in DOMAIN R1.rec}
Seen(R1) == /\ Len(Ev.st) = Cardinality(DOMAIN R1.rec)
            /\ {Ev.st[k] : k \in 1..Len(Ev.st)} = StoredSet(R1)
            /\ <<R1.cn.records, R1.cn.lookups, R1.cn.rejected>> = Ev.cn

Step(o) == /\ o.res = Ev.res /\ o.ef = Ev.out /\ Seen(o.R) /\ R' = o.R /\ cf' = cf /\ i' = i + 1

NewE == /\ Ev.t = "qnew"
        /\ cf' = [R |-> Ev.r, P |-> Ev.p, me |-> Ev.me]
        /\ R' = NewStore(cf') /\ i' = i + 1
AddE == /\ Ev.t = "qadd"
        /\ LET a == AddPeer(R, Ev.p) IN /\ (a.ok = (Ev.res = "ok")) /\ R' = a.R
        /\ cf' = cf /\ i' = i + 1
RemE == /\ Ev.t = "qrem" /\ R' = RemovePeer(R, Ev.p) /\ cf' = cf /\ i' = i + 1
PubE == /\ Ev.t = "qpub" /\ Step(Publish(cf, R, Ev.now, Ev.n, Rc))
RepE == /\ Ev.t = "qrep" /\ Step(Replica(cf, R, Ev.now, Rc))
RstE == /\ Ev.t = "qrst" /\ Step(Restore(cf, R, Ev.at, Rc))
OwnE == /\ Ev.t = "qown" /\ Step(SetOwn(cf, R, Ev.now, Rc))
TimeE == /\ Ev.t = "qtime" /\ Step(Timeout(cf, R, Ev.now))
LookE == /\ Ev.t = "qlook"
         /\ LET a == Answer(cf, R, Ev.now, Ev.peer) IN
            /\ a.ans = Ev.ans /\ a.ef = Ev.out
            /\ Ev.ans = "record" => /\ R.rec[Ev.peer].r.seq = Ev.as /\ R.rec[Ev.peer].r.tag = Ev.at
                                    /\ R.rec[Ev.peer].r.len = Ev.al
            /\ Seen(a.R) /\ R' = a.R /\ cf' = cf /\ i' = i + 1
SyncE == /\ Ev.t = "qsync"
         /\ LET s == SyncRecord(cf, R, Ev.to, Ev.node) IN
            /\ (s.ok = (Ev.res = "ok")) /\ s.ef = Ev.out /\ Seen(R)
         /\ R' = R /\ cf' = cf /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (NewE \/ AddE \/ RemE \/ PubE \/ RepE \/ RstE \/ OwnE \/ TimeE \/ LookE \/ SyncE)) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of ConnectRecordsOps.tla
TraceAccepted == <>(i = Len(Trace) + 1)
Inv == TRUE
=============================================================================
