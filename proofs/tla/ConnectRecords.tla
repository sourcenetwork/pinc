--------------------------- MODULE ConnectRecords ---------------------------
(***************************************************************************)
(* Model check of the relay's record store, lookup and own record          *)
(* (records.rs), over the operators of ConnectRecordsOps.tla. The steps    *)
(* are every way a record arrives (publish on a carrier, replica from a    *)
(* peer relay, restore_record after a restart, set_own_record), the        *)
(* timer (handle_timeout: the republish and the sweep), a lookup, the sync *)
(* of a record to a peer, and peers added and removed. Time is monotone    *)
(* and takes values of the finite set Times; a restored record was         *)
(* received at a time not after the clock. Records are verified or not     *)
(* (the signature check is a predicate of the bytes, see the Ops module).  *)
(*                                                                         *)
(* Invariants (Lean: Vinc/ConnectRecordsThm.lean):                         *)
(*  Bounded     at most cf.R records                                       *)
(*  Keyed       the store keeps at most one record per node id, and the    *)
(*              record under an id names that id                           *)
(*  OnlyGood    every stored record verified: no record whose signature or *)
(*              key binding fails is ever stored                           *)
(*  Highest     the stored record of a node is the one with the highest    *)
(*              sequence number accepted since the node had none stored    *)
(* Action properties (each is about one call):                             *)
(*  Lower, EqualDiff, EqualSame, Higher   the accept rule: a lower number  *)
(*              or an equal one with different bytes is refused and        *)
(*              changes nothing; an equal one with the same bytes only     *)
(*              renews its receive time; a higher one replaces             *)
(*  BadRefused  a record that does not verify is refused, nothing changes  *)
(*  WrongOwner  a node publishes only its own record                       *)
(*  Replicated  a published or own record goes once to every peer in slot  *)
(*              order, a replica or restored one to none, a refused one to *)
(*              none                                                       *)
(*  LookupFresh a lookup answers only with a stored, unexpired, verified   *)
(*              record, and changes nothing but its counter                *)
(*  SweepRule   the sweep drops exactly the expired records, and runs at   *)
(*              the first call at least SWEEP after the previous one       *)
(*  OwnArmed    set_own_record arms the republish at now + 1800 s; a       *)
(*              republish renews the own record and sends it once to each  *)
(*              peer, none before the timer                                *)
(***************************************************************************)
EXTENDS ConnectRecordsOps, TLC

CONSTANTS Nodes, Homes, Tags, MaxSeq, Times, Peers, Me, Cap, Slots, MaxCalls, BUG

cf == [R |-> Cap, P |-> Slots, me |-> Me]
TagLen(t) == IF t = 1 THEN 5 ELSE 1390
\* every record that verifies, and one that does not per node (the oracle says no)
Recs == {[node |-> n, seq |-> s, home |-> h, tag |-> t, len |-> TagLen(t), ok |-> TRUE] :
         n \in Nodes, s \in 1..MaxSeq, h \in Homes, t \in Tags}
        \cup {[node |-> n, seq |-> 1, home |-> CHOOSE h \in Homes : TRUE, tag |-> 1, len |-> TagLen(1), ok |-> FALSE] : n \in Nodes}

VARIABLES R, clock, hi, lc, calls
vars == <<R, clock, hi, lc, calls>>

NoCall == [op |-> "none", r |-> [node |-> 0, seq |-> 0, home |-> 0, tag |-> 0, len |-> 0, ok |-> FALSE], owner |-> 0,
           res |-> "none", ef |-> <<>>, now |-> 0, ans |-> "none", drop |-> 0, rep |-> FALSE]

Init == /\ R = NewStore(cf) /\ clock = 0 /\ hi = [n \in Nodes |-> 0] /\ lc = NoCall /\ calls = 0

Tick == \E t \in Times : t >= clock /\ clock' = t

Max2(a, b) == IF a > b THEN a ELSE b

(* the deliberately wrong rules the witness configs use *)
Replaced(R0, now, r) == [R |-> [R0 EXCEPT !.rec = Put(R0.rec, r.node, [r |-> r, rcv |-> now])], res |-> "ok",
                         ef |-> <<<<"t", "rstored", r.node, r.seq, "replica">>>>]
Known(R0, r) == r.node \in DOMAIN R0.rec
StoreBug(R0, now, r, owner, origin) ==
    LET good == Store(cf, R0, now, r, owner, origin) IN
    CASE BUG = "nocheck" /\ ~r.ok /\ (owner = 0 \/ owner = r.node) /\ (Known(R0, r) \/ Cardinality(DOMAIN R0.rec) < Cap) -> Replaced(R0, now, r)
      [] BUG = "equal" /\ r.ok /\ Known(R0, r) /\ r.seq = R0.rec[r.node].r.seq /\ r # R0.rec[r.node].r /\ (owner = 0 \/ owner = r.node) -> Replaced(R0, now, r)
      [] BUG = "lower" /\ r.ok /\ Known(R0, r) /\ r.seq < R0.rec[r.node].r.seq /\ (owner = 0 \/ owner = r.node) -> Replaced(R0, now, r)
      [] OTHER -> good

HiNext(r, res, R1) == [n \in Nodes |-> IF n \notin DOMAIN R1.rec THEN 0
                                       ELSE IF n = r.node /\ res = "ok" THEN Max2(hi[n], r.seq) ELSE hi[n]]

Arrive(op, r, owner, o, t) ==
    /\ R' = o.R /\ hi' = HiNext(r, o.res, o.R)
    /\ lc' = [op |-> op, r |-> r, owner |-> owner, res |-> o.res, ef |-> o.ef, now |-> t, ans |-> "none", drop |-> 0,
             rep |-> o.res = "ok" /\ r.node \in DOMAIN R.rec /\ r.seq > R.rec[r.node].r.seq]

DoPublish(node, r) == /\ Tick
                      /\ LET s == StoreBug(R, clock', r, node, "publish")
                             o == IF s.res # "ok" THEN s ELSE [s EXCEPT !.ef = @ \o Sync(s.R, r.len)]
                         IN Arrive("pub", r, node, o, clock')
DoReplica(r) == /\ Tick /\ Arrive("rep", r, 0, StoreBug(R, clock', r, 0, "replica"), clock')
DoRestore(t, r) == /\ t <= clock /\ clock' = clock /\ Arrive("rst", r, 0, StoreBug(R, t, r, 0, "replica"), t)
DoOwn(r) == /\ Tick
            /\ LET s == StoreBug(R, clock', r, Me, "own")
                   o == IF s.res # "ok" THEN s
                        ELSE [R |-> [s.R EXCEPT !.np = clock' + REPUB], res |-> "ok", ef |-> s.ef \o Sync(s.R, r.len)]
               IN Arrive("own", r, Me, o, clock')

DoTimeout == /\ Tick
             /\ LET d == RepublishDue(cf, R, clock')
                    o == IF Sat(clock' - d.R.ls) < SWEEP THEN [R |-> d.R, res |-> "ok", ef |-> d.ef]
                         ELSE IF BUG = "nosweep" THEN [R |-> [d.R EXCEPT !.ls = clock'], res |-> "ok", ef |-> d.ef]
                         ELSE Timeout(cf, R, clock')
                IN /\ R' = o.R
                   /\ hi' = [n \in Nodes |-> IF n \in DOMAIN o.R.rec THEN hi[n] ELSE 0]
                   /\ lc' = [NoCall EXCEPT !.op = "time", !.res = "ok", !.ef = o.ef, !.now = clock',
                                  !.drop = Cardinality(DOMAIN R.rec) - Cardinality(DOMAIN o.R.rec)]

DoLookup(peer) == /\ Tick
                  /\ LET a == Answer(cf, R, clock', peer)
                         fresh == IF BUG = "lookall" THEN peer \in DOMAIN R.rec ELSE Fresh(R, clock', peer)
                         ans == IF ~fresh THEN "absent" ELSE IF R.rec[peer].r.len > MAXDNS THEN "toolarge" ELSE "record"
                     IN /\ R' = a.R /\ hi' = hi
                        /\ lc' = [NoCall EXCEPT !.op = "look", !.r.node = peer, !.ans = ans, !.ef = a.ef, !.now = clock']

DoSync(to, node) == /\ LET s == SyncRecord(cf, R, to, node) IN
                       lc' = [NoCall EXCEPT !.op = "sync", !.r.node = node, !.owner = to, !.res = IF s.ok THEN "ok" ELSE "no",
                              !.ef = s.ef, !.now = clock]
                    /\ UNCHANGED <<R, clock, hi>>
DoAdd(p) == /\ R' = AddPeer(R, p).R /\ lc' = NoCall /\ UNCHANGED <<clock, hi>>
DoRem(p) == /\ R' = RemovePeer(R, p) /\ lc' = NoCall /\ UNCHANGED <<clock, hi>>

Next == /\ calls < MaxCalls /\ calls' = calls + 1
        /\ \/ \E n \in Nodes, r \in Recs : DoPublish(n, r)
           \/ \E r \in Recs : DoReplica(r)
           \/ \E t \in Times, r \in Recs : DoRestore(t, r)
           \/ \E r \in Recs : r.node = Me /\ DoOwn(r)
           \/ \E r \in Recs : r.node # Me /\ DoOwn(r)
           \/ DoTimeout
           \/ \E n \in Nodes : DoLookup(n)
           \/ \E p \in Peers, n \in Nodes : DoSync(p, n)
           \/ \E p \in Peers : DoAdd(p) \/ DoRem(p)

Spec == Init /\ [][Next]_vars

(* invariants *)
Bounded == Cardinality(DOMAIN R.rec) <= Cap
Keyed == \A k \in DOMAIN R.rec : R.rec[k].r.node = k
OnlyGood == \A k \in DOMAIN R.rec : R.rec[k].r.ok
Highest == \A k \in DOMAIN R.rec : hi[k] = R.rec[k].r.seq

(* action properties *)
StoreOp(c) == c.op \in {"pub", "rep", "rst", "own"}
Verified(c) == c.r.ok /\ (c.owner = 0 \/ c.owner = c.r.node)
Old(k) == R.rec[k]
Lower == [][StoreOp(lc') /\ Verified(lc') /\ lc'.r.node \in DOMAIN R.rec /\ lc'.r.seq < Old(lc'.r.node).r.seq
            => lc'.res = "stalerec" /\ R'.rec = R.rec]_vars
EqualDiff == [][StoreOp(lc') /\ Verified(lc') /\ lc'.r.node \in DOMAIN R.rec /\ lc'.r.seq = Old(lc'.r.node).r.seq
                /\ lc'.r # Old(lc'.r.node).r
            => lc'.res = "stalerec" /\ R'.rec = R.rec]_vars
EqualSame == [][StoreOp(lc') /\ Verified(lc') /\ lc'.r.node \in DOMAIN R.rec /\ lc'.r = Old(lc'.r.node).r
            => lc'.res = "ok" /\ R'.rec = [R.rec EXCEPT ![lc'.r.node].rcv = lc'.now]]_vars
Higher == [][StoreOp(lc') /\ Verified(lc') /\ lc'.r.node \in DOMAIN R.rec /\ lc'.r.seq > Old(lc'.r.node).r.seq
            => lc'.res = "ok" /\ R'.rec[lc'.r.node] = [r |-> lc'.r, rcv |-> lc'.now]
               /\ \A k \in DOMAIN R.rec \ {lc'.r.node} : R'.rec[k] = R.rec[k]]_vars
BadRefused == [][StoreOp(lc') /\ ~lc'.r.ok => lc'.res = "badrecord" /\ R'.rec = R.rec]_vars
WrongOwner == [][StoreOp(lc') /\ lc'.r.ok /\ lc'.owner # 0 /\ lc'.owner # lc'.r.node
                 => lc'.res = "wrongowner" /\ R'.rec = R.rec]_vars
FrameCount(ef) == Cardinality({i \in 1..Len(ef) : ef[i][1] = "peer"})
Used(pr) == LET F[i \in 0..Len(pr)] == IF i = 0 THEN <<>> ELSE IF pr[i] # 0 THEN Append(F[i - 1], pr[i]) ELSE F[i - 1] IN F[Len(pr)]
Targets(ef) == LET F[i \in 0..Len(ef)] == IF i = 0 THEN <<>> ELSE IF ef[i][1] = "peer" THEN Append(F[i - 1], ef[i][2]) ELSE F[i - 1]
               IN F[Len(ef)]
Replicated == [][/\ (lc'.op \in {"rep", "rst"} => FrameCount(lc'.ef) = 0)
                 /\ (StoreOp(lc') /\ lc'.res # "ok" => FrameCount(lc'.ef) = 0)
                 /\ (lc'.op \in {"pub", "own"} /\ lc'.res = "ok" => Targets(lc'.ef) = Used(R.pr))
                 /\ (StoreOp(lc') => R'.pr = R.pr)
                 /\ (StoreOp(lc') => \A j \in 1..Len(lc'.ef) : lc'.ef[j][1] = "peer" => lc'.ef[j][4] = lc'.r.len)]_vars
LookupFresh == [][lc'.op = "look" =>
                    /\ (lc'.ans # "absent" => lc'.r.node \in DOMAIN R.rec /\ Sat(lc'.now - R.rec[lc'.r.node].rcv) < RECTTL
                                               /\ R.rec[lc'.r.node].r.ok
                                               /\ (lc'.ans = "record") = (R.rec[lc'.r.node].r.len <= MAXDNS))
                    /\ (lc'.ans = "absent" => ~(lc'.r.node \in DOMAIN R.rec /\ Sat(lc'.now - R.rec[lc'.r.node].rcv) < RECTTL))
                    /\ R'.rec = R.rec]_vars
SweepRule == [][lc'.op = "time" =>
                  /\ (Sat(lc'.now - R.ls) >= SWEEP => R'.ls = lc'.now)
                  /\ (R'.ls # R.ls =>
                        /\ \A k \in DOMAIN R'.rec : Sat(lc'.now - R'.rec[k].rcv) < RECTTL
                        /\ \A k \in DOMAIN R.rec \ DOMAIN R'.rec : Sat(lc'.now - R.rec[k].rcv) >= RECTTL)
                  /\ DOMAIN R'.rec \subseteq DOMAIN R.rec]_vars
OwnArmed == [][/\ (lc'.op = "own" /\ lc'.res = "ok" => R'.np = lc'.now + REPUB /\ Me \in DOMAIN R'.rec)
               /\ (lc'.op = "time" /\ R.np # 0 /\ lc'.now >= R.np =>
                     /\ R'.np = lc'.now + REPUB
                     /\ (Me \in DOMAIN R.rec => R'.rec[Me].rcv = lc'.now /\ Me \in DOMAIN R'.rec
                                                /\ Targets(lc'.ef) = Used(R.pr)))
               /\ (lc'.op = "time" /\ (R.np = 0 \/ lc'.now < R.np) => FrameCount(lc'.ef) = 0 /\ R'.np = R.np)]_vars

\* reachability: the witnesses that the properties are not vacuous
NotStale == lc.res # "stalerec"
NotFull == lc.res # "storefull"
NotHit == lc.ans # "record"
NotToolarge == lc.ans # "toolarge"
NotAbsentStored == ~(lc.ans = "absent" /\ lc.r.node \in DOMAIN R.rec)
NotDropped == lc.drop = 0
NotRepub == \A i \in 1..Len(lc.ef) : lc.ef[i][1] # "t" \/ lc.ef[i][2] # "repub"
NotRefresh == ~(StoreOp(lc) /\ lc.res = "ok" /\ lc.ef = <<>> /\ lc.r.node \in DOMAIN R.rec)
NotReplaced == ~lc.rep
NotBad == lc.res # "badrecord"
NotWrong == lc.res # "wrongowner"
NotSyncOk == ~(lc.op = "sync" /\ lc.res = "ok")
=============================================================================
