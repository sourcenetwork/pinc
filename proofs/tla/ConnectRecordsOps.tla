------------------------- MODULE ConnectRecordsOps -------------------------
(***************************************************************************)
(* The record store of the relay (pinc-connect/src/relay/records.rs) as    *)
(* pure operators, step for step: RecordStore::accept and sweep,           *)
(* Relay::store, publish, replica, restore_record, set_own_record,         *)
(* republish_due, sync_record, lookup and answer, and the part of          *)
(* handle_timeout that touches records (the republish, then the sweep      *)
(* at most once per SWEEP). ConnectRecords.tla (the model check) and       *)
(* TraceConnectRecords.tla (the trace validation) both use these operators.*)
(*                                                                         *)
(* A record is the bytes the node signed, reduced to what the store sees:  *)
(*   node, seq, home   the fields the relay reads                          *)
(*   tag               stands for every other byte (addresses, hints,      *)
(*                     key, signature): two records with equal fields and  *)
(*                     different tags are different bytes                  *)
(*   len               the length of the bytes (the answer to a lookup     *)
(*                     depends on it)                                      *)
(*   ok                the signature verifies and the key belongs to the   *)
(*                     node id (Record::parse_verified succeeds): an       *)
(*                     ideal primitive, as in the other symbolic models,   *)
(*                     a predicate of the bytes. A record that is not      *)
(*                     well formed is one with ok = FALSE.                 *)
(* Two records are the same bytes exactly when they are equal as records.  *)
(*                                                                         *)
(* The table of the store is the finite function rec, full at cf.R (a new  *)
(* node is refused when full): ConnectTable.tla proves the real Table is   *)
(* that map. Peers are slots, as in the relay (cf.P of them, 32 in the     *)
(* code); a frame goes to every used slot in slot order. Time is in whole  *)
(* seconds, the unit of the trace; the constants are the real ones.        *)
(* The counters are the relay's `records`, `lookups` and `rejected`.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

REPUB == 1800     \* RECORD_REPUBLISH_NS
RECTTL == 5400    \* RECORD_TTL_NS = 3 * RECORD_REPUBLISH_NS
SWEEP == 1        \* SWEEP_NS
MAXDNS == 1389    \* MAX_DNS_DATAGRAM - 35 = 1452 - 28 - 35, the longest record a UDP lookup answers

Sat(x) == IF x < 0 THEN 0 ELSE x
Put(f, k, v) == [x \in DOMAIN f \cup {k} |-> IF x = k THEN v ELSE f[x]]
Min(a, b) == IF a < b THEN a ELSE b

NewStore(cf) == [rec |-> [x \in {} |-> 0], pr |-> [i \in 1..cf.P |-> 0], np |-> 0, ls |-> 0,
                 cn |-> [records |-> 0, lookups |-> 0, rejected |-> 0]]

IsPeer(R, n) == \E i \in 1..Len(R.pr) : R.pr[i] = n

(* Relay::reject: the counter and the trace transition *)
Fail(R, why, node) == [R |-> [R EXCEPT !.cn.rejected = @ + 1], res |-> why, ef |-> <<<<"t", "rej", why, node>>>>]

(* records.rs RecordStore::accept: how the store treats a verified record *)
Accept(cf, R, now, r) ==
    LET known == r.node \in DOMAIN R.rec
        s == R.rec[r.node]
    IN IF known /\ (r.seq < s.r.seq \/ (r.seq = s.r.seq /\ r # s.r)) THEN [kind |-> "stale", R |-> R]
       ELSE IF known /\ r.seq = s.r.seq THEN [kind |-> "refreshed", R |-> [R EXCEPT !.rec[r.node].rcv = now]]
       ELSE IF ~known /\ Cardinality(DOMAIN R.rec) >= cf.R THEN [kind |-> "full", R |-> R]
       ELSE [kind |-> "stored", R |-> [R EXCEPT !.rec = Put(R.rec, r.node, [r |-> r, rcv |-> now])]]

(* records.rs Relay::store; owner is 0 for none *)
Store(cf, R, now, r, owner, origin) ==
    IF ~r.ok THEN Fail(R, "badrecord", owner)
    ELSE IF owner # 0 /\ owner # r.node THEN Fail(R, "wrongowner", owner)
    ELSE LET a == Accept(cf, R, now, r) IN
         CASE a.kind = "stale" -> Fail(R, "stalerec", r.node)
           [] a.kind = "full" -> Fail(R, "storefull", r.node)
           [] a.kind = "refreshed" -> [R |-> a.R, res |-> "ok", ef |-> <<>>]
           [] OTHER -> [R |-> [a.R EXCEPT !.cn.records = @ + 1], res |-> "ok",
                        ef |-> <<<<"t", "rstored", r.node, r.seq, origin>>>>]

(* the frame to every peer, in slot order *)
Sync(R, len) == LET F[i \in 0..Len(R.pr)] ==
                        IF i = 0 THEN <<>>
                        ELSE IF R.pr[i] # 0 THEN Append(F[i - 1], <<"peer", R.pr[i], "sync", len>>) ELSE F[i - 1]
                IN F[Len(R.pr)]

(* a node published its record on its carrier: store it, replicate it *)
Publish(cf, R, now, node, r) ==
    LET s == Store(cf, R, now, r, node, "publish") IN
    IF s.res # "ok" THEN s ELSE [s EXCEPT !.ef = @ \o Sync(s.R, r.len)]

(* a peer relay replicated a record *)
Replica(cf, R, now, r) == Store(cf, R, now, r, 0, "replica")

(* restore_record is replica at the time the record was received *)
Restore(cf, R, received, r) == Replica(cf, R, received, r)

(* set_own_record: this relay's own record, replicated, and the republish timer armed *)
SetOwn(cf, R, now, r) ==
    LET s == Store(cf, R, now, r, cf.me, "own") IN
    IF s.res # "ok" THEN s
    ELSE [R |-> [s.R EXCEPT !.np = now + REPUB], res |-> "ok", ef |-> s.ef \o Sync(s.R, r.len)]

(* republish_due *)
RepublishDue(cf, R, now) ==
    IF R.np = 0 \/ now < R.np THEN [R |-> R, ef |-> <<>>]
    ELSE LET R1 == [R EXCEPT !.np = now + REPUB] IN
         IF cf.me \notin DOMAIN R1.rec THEN [R |-> R1, ef |-> <<>>]
         ELSE LET R2 == [R1 EXCEPT !.rec[cf.me].rcv = now]
                  n == Cardinality({i \in 1..Len(R2.pr) : R2.pr[i] # 0})
              IN [R |-> R2, ef |-> Sync(R2, R2.rec[cf.me].r.len) \o <<<<"t", "repub", n>>>>]

(* RecordStore::sweep: a record not received within RECORD_TTL_NS is dropped *)
SweepRecs(R, now) == [R EXCEPT !.rec = [x \in {y \in DOMAIN R.rec : Sat(now - R.rec[y].rcv) < RECTTL} |-> R.rec[x]]]

(* handle_timeout, the part that touches records: the republish, then the sweep unless one ran less than SWEEP ago *)
Timeout(cf, R, now) ==
    LET d == RepublishDue(cf, R, now) IN
    IF Sat(now - d.R.ls) < SWEEP THEN [R |-> d.R, res |-> "ok", ef |-> d.ef]
    ELSE [R |-> [SweepRecs(d.R, now) EXCEPT !.ls = now], res |-> "ok", ef |-> d.ef]

(* Relay::lookup: the stored record of peer if it is fresh *)
Fresh(R, now, peer) == peer \in DOMAIN R.rec /\ Sat(now - R.rec[peer].rcv) < RECTTL

(* Relay::answer, called for a DNSQ datagram: the counter, the trace transition and the answer *)
Answer(cf, R, now, peer) ==
    LET f == Fresh(R, now, peer)
        R1 == [R EXCEPT !.cn.lookups = @ + 1]
    IN [R |-> R1, ef |-> <<<<"t", "lookup", peer, IF f THEN 1 ELSE 0>>>>,
        ans |-> IF ~f THEN "absent" ELSE IF R.rec[peer].r.len > MAXDNS THEN "toolarge" ELSE "record"]

(* sync_record *)
SyncRecord(cf, R, to, node) ==
    IF node \in DOMAIN R.rec /\ R.rec[node].r.home = cf.me /\ IsPeer(R, to)
    THEN [ok |-> TRUE, ef |-> <<<<"peer", to, "sync", R.rec[node].r.len>>>>]
    ELSE [ok |-> FALSE, ef |-> <<>>]

(* add_peer and remove_peer *)
AddPeer(R, p) ==
    IF IsPeer(R, p) THEN [R |-> R, ok |-> TRUE]
    ELSE LET free == {i \in 1..Len(R.pr) : R.pr[i] = 0} IN
         IF free = {} THEN [R |-> R, ok |-> FALSE]
         ELSE LET m == CHOOSE i \in free : \A j \in free : i <= j IN [R |-> [R EXCEPT !.pr[m] = p], ok |-> TRUE]
RemovePeer(R, p) == [R EXCEPT !.pr = [i \in 1..Len(R.pr) |-> IF R.pr[i] = p THEN 0 ELSE R.pr[i]]]
=============================================================================
