-------------------------- MODULE ConnectRelayOps --------------------------
(***************************************************************************)
(* The relay of pinc-connect/src/relay (mod.rs, clients.rs, route.rs,      *)
(* records.rs, discovery.rs): carrier sessions, quota, forwarding, the     *)
(* reply route, the hub tunnel, record storage, sleep notices and the      *)
(* hold of packets for sleeping members, as pure operators: each takes the *)
(* configuration cf, the state R and the call, and returns the new state,  *)
(* the answer ("ok" or the reason of the refusal) and the effects in the   *)
(* order the code emits them (frames, closes, wake-ups and every Trace).   *)
(*                                                                         *)
(* A message held for a member is released when a packet from the member  *)
(* is heard (UdpHeard, and the SPU datagram through it) and its route is   *)
(* ready: the pass hands over, oldest first, every held message that fits  *)
(* the route, steps over one too long for the tunnel (it waits for the     *)
(* carrier) and stops at a hand-over the host refuses. Routing a packet    *)
(* (Route) starts no release, whatever the destination holds. For the     *)
(* witnesses only: cf.old (nothing is released), cf.hb (a packet for a     *)
(* member that holds messages is held behind them, the rule withdrawn)     *)
(* and cf.stop (the pass stops at the first message that does not fit).    *)
(*                                                                         *)
(* Time is in whole seconds, the unit of the trace; every rule constant is *)
(* a whole number of seconds in the code. Node ids are small naturals,     *)
(* 0 meaning none. Tables:                                                 *)
(*  - the session table is the exact Table of ConnectTableOps.tla (so the  *)
(*    sweep closes sessions in the order of the real slots); the sessions  *)
(*    themselves are in cd;                                                *)
(*  - sl (sleeping), udp, rec and the member table of the mailbox are     *)
(*    finite functions that are full at their capacity (a new key is       *)
(*    refused when full), which is all the code observes of them           *)
(*    (ConnectTable.tla proves the table is that map); a mark of sl is     *)
(*    [at, ts, woke]: when the notice was accepted, the notice's clock in  *)
(*    ms and the last wake-up asked for;                                   *)
(*  - gone is that function too, and gt the exact Table that holds the     *)
(*    same entries, so a full table drops the entry the code drops (the    *)
(*    first with the oldest time in slot order, record_gone);              *)
(*  - fb is the direct mapped Cache of the reply routes (bk gives the      *)
(*    bucket of each node: the hash of the code, as recorded).             *)
(* Seams, stated: signatures are an oracle (the call says whether the      *)
(* record or notice verifies for this relay), a record is identified by    *)
(* its node, seq and home (the bytes are a function of them), and the      *)
(* record and lookup answers, the relay's own record and the republish     *)
(* timer are outside this module (Records unit).                            *)
(***************************************************************************)
EXTENDS ConnectMailboxOps, ConnectTableOps

FRESH == 20      \* HUB_TUNNEL_FRESH_NS
STALE == 15      \* TUNNEL_STALE_NS
FWDB == 30       \* FWD_BACK_NS
SWIN == 10       \* SLEEP_WIN_NS
GONET == 600     \* GONE_TTL_NS
SWEEP == 1       \* SWEEP_NS
PING == 600      \* CLIENT_PING_NS
RECTTL == 5400   \* RECORD_TTL_NS = 3 * 1800 s
REARM == 30      \* WAKE_REARM_NS
SKEWMS == 10000  \* SKEW_MS
MAXTUN == 1424   \* MAX_TUNNEL_DATAGRAM = MAX_PACKET_LEN - 28
MAXPKT == 1452   \* MAX_PACKET_LEN
AM == 32         \* ALIAS_MAX
MAXPEERS == 32   \* MAX_PEERS

MC(cf) == [H |-> 52, B |-> cf.MB, N |-> cf.MN, MaxPkt |-> MAXPKT, Age |-> cf.Age, Rearm |-> REARM]

MinOf(S) == CHOOSE i \in S : \A j \in S : i <= j
Abs(x) == IF x < 0 THEN 0 - x ELSE x

(* AliasTable *)
NewAT == [len |-> 0, sl |-> [i \in 0..(AM - 1) |-> 0]]
Assign(a, node) ==
    LET P == {i \in 0..(a.len - 1) : a.sl[i] = node} IN
    IF P # {} THEN [a |-> a, known |-> TRUE, al |-> MinOf(P)]
    ELSE LET a1 == IF a.len >= AM THEN NewAT ELSE a IN
         [a |-> [len |-> a1.len + 1, sl |-> [a1.sl EXCEPT ![a1.len] = node]], known |-> FALSE, al |-> a1.len]
Learn(a, al, node) == IF al < AM THEN [a EXCEPT !.sl[al] = node] ELSE a
Resolve(a, al) == IF al < AM THEN a.sl[al] ELSE 0

NewRelay(cf) == [bk |-> [x \in {} |-> 0], tb |-> NewTable(cf.C), cd |-> [x \in {} |-> 0], gone |-> [x \in {} |-> 0],
                 gt |-> NewTable(cf.C),
                 sl |-> [x \in {} |-> 0], udp |-> [x \in {} |-> 0], nr |-> {},
                 fb |-> [i \in 0..(cf.C - 1) |-> [n |-> 0, rel |-> 0, at |-> 0]],
                 peers |-> [i \in 1..MAXPEERS |-> 0], rec |-> [x \in {} |-> 0], mb |-> Empty, ns |-> 0, ls |-> 0, np |-> 0]

HasC(cf, R, n) == Find(cf.C, R.bk, R.tb, n) >= 0

(* relay/mod.rs mark_live: a sleep mark lasts as long as the mailbox keeps a message (cf.Age, mailbox_max_age_ns),
   counted from the notice that set it; routing, the hold and the sweep read this one rule *)
Live(cf, R, now, n) == n \in DOMAIN R.sl /\ Sat(now - R.sl[n].at) < cf.Age
IsPeer(R, n) == \E i \in 1..MAXPEERS : R.peers[i] = n
CanPut(f, k, cap) == k \in DOMAIN f \/ Cardinality(DOMAIN f) < cap

\* the key of the first entry with the oldest time of a non-empty sequence of slots (Iterator::min_by_key)
OldestKey(es) == es[CHOOSE i \in 1..Len(es) : (\A j \in 1..Len(es) : es[i].v <= es[j].v) /\ \A j \in 1..(i - 1) : es[j].v > es[i].v].k

\* clients.rs record_gone: node closed at now; a full table first drops its entry with the oldest time (a node already in
\* it only has its time refreshed), so the close is never lost
RecordGone(cf, R, node, now) ==
    LET R1 == IF Find(cf.C, R.bk, R.gt, node) < 0 /\ R.gt.len >= cf.C
              THEN LET old == OldestKey(Entries(cf.C, R.gt, 0))
                   IN [R EXCEPT !.gone = Del(R.gone, old), !.gt = Remove(cf.C, R.bk, R.gt, old).t]
              ELSE R
    IN [R1 EXCEPT !.gone = Put(R1.gone, node, now), !.gt = Insert(cf.C, R1.bk, R1.gt, node, now).t]
\* the old rule, for the witness ConnectRelay_wgone (a definition override): a full table forgets the close
RecordGoneForget(cf, R, node, now) ==
    IF CanPut(R.gone, node, cf.C)
    THEN [R EXCEPT !.gone = Put(R.gone, node, now), !.gt = Insert(cf.C, R.bk, R.gt, node, now).t]
    ELSE R

\* the gone.retain of the sweep, on the slots: the entries closed GONET or more ago go
RECURSIVE RetainGone(_, _, _, _, _)
RetainGone(n, bk, t, i, now) ==
    IF i >= n THEN t
    ELSE IF t.s[i].k = 0 THEN RetainGone(n, bk, t, i + 1, now)
    ELSE IF Sat(now - t.s[i].v) < GONET THEN RetainGone(n, bk, t, i + 1, now)
    ELSE RetainGone(n, bk, RemoveAt(n, bk, t, i), i, now)

RoutedE(s, d, rt, b) == <<"t", "routed", s, d, rt, b>>
RejE(why, node) == <<"t", "rej", why, node>>
LocalEf(from, me, len) == <<RoutedE(from, me, "local", len), <<"local", from, len>>>>
Fail(R, why, node) == [R |-> R, res |-> why, ef |-> <<RejE(why, node)>>]

(* The host answers Sink::tunnel_ready from nr, the members with no validated direct route; it is an input of the
   call *)
SetReady(R, node, ok) == [R EXCEPT !.nr = IF ok = 1 THEN R.nr \ {node} ELSE R.nr \cup {node}]

(* route.rs fresh: the UDP session of the node was heard less than 20 s ago *)
Fresh(R, now, node) == node \in DOMAIN R.udp /\ Sat(now - R.udp[node]) < FRESH

(* route.rs tunnel_down *)
TunnelDown(R, now, dst, src, flag, len) ==
    IF ~Fresh(R, now, dst) \/ dst \in R.nr \/ len = 0 \/ 35 + len > MAXTUN THEN [ok |-> FALSE, ef |-> <<>>]
    ELSE [ok |-> TRUE, ef |-> <<<<"udp", dst, "spl", src, flag, len>>, RoutedE(src, dst, "tunnel", len)>>]

(* route.rs deliver_client *)
DeliverClient(cf, R, now, src, dst, flag, len, stalecopy) ==
    IF ~HasC(cf, R, dst) THEN [R |-> R, ok |-> FALSE, ef |-> <<>>]
    ELSE LET c == R.cd[dst]
             stale == Sat(now - c.lastRx) > STALE
             a == Assign(c.tx, src)
             R1 == [R EXCEPT !.cd[dst] = [c EXCEPT !.tx = a.a]]
             fe == IF a.known THEN <<"car", dst, "ra", a.al, flag, len>> ELSE <<"car", dst, "rn", src, a.al, flag, len>>
             t == IF stalecopy /\ stale THEN TunnelDown(R1, now, dst, src, flag, len) ELSE [ok |-> FALSE, ef |-> <<>>]
         IN [R |-> R1, ok |-> TRUE, ef |-> <<fe, RoutedE(src, dst, "carrier", len)>> \o t.ef]

(* route.rs hold: the packet goes into the mailbox, and a wake-up is requested on the first one or 30 s after the last,
   only while the member is still marked asleep (route reaches hold only for a member with a mark; the withdrawn rule
   of cf.hb holds a packet without one, and then requests none) *)
Hold(cf, R, now, dst, src, flag, len) ==
    LET p == Push(MC(cf), R.mb, now, dst, src, flag, len) IN
    IF p.res = "stored"
    THEN LET rearm == dst \in DOMAIN R.sl /\ ShouldWake(MC(cf), now, R.sl[dst], p.first)
             R1 == [R EXCEPT !.mb = p.mb, !.sl = IF rearm THEN [R.sl EXCEPT ![dst] = [R.sl[dst] EXCEPT !.woke = now]] ELSE R.sl]
             e == <<RoutedE(src, dst, "mailbox", len), <<"t", "mstored", dst, p.seq, p.dropped>>>>
                  \o (IF rearm THEN <<<<"t", "wakereq", dst>>, <<"wake", dst>>>> ELSE <<>>)
         IN [R |-> R1, res |-> "ok", ef |-> e]
    ELSE [R |-> [R EXCEPT !.mb = p.mb], res |-> "mbrefused", ef |-> <<RejE("mbrefused", src)>>]

(* route.rs forward: the relay `forward` sends dst's packets to: the reply route (the relay that forwarded dst's packets
   within 30 s, not this one), else the home of dst's stored record; 0 when there is none *)
HomeOf(cf, R, now, dst) ==
    LET slot == R.fb[R.bk[dst]]
        back == IF slot.n = dst /\ Sat(now - slot.at) < FWDB /\ slot.rel # cf.me THEN slot.rel ELSE 0
    IN IF back # 0 THEN back ELSE IF dst \in DOMAIN R.rec THEN R.rec[dst].home ELSE 0

(* route.rs forward: RELAY_FORWARD to the home relay, the reply route first *)
Forward(cf, R, now, src, dst, flag, len) ==
    LET home == HomeOf(cf, R, now, dst)
    IN IF home = 0 \/ home = cf.me THEN Fail(R, "noroute", src)
       ELSE IF ~IsPeer(R, home) THEN Fail(R, "nopeer", src)
       ELSE [R |-> R, res |-> "ok", ef |-> <<<<"peer", home, "fwd", src, dst, flag, len>>, RoutedE(src, dst, "peer", len)>>]

(* route.rs deliver_held: look for the oldest message that fits the route (a longer one is stepped over and stays
   held), hand it over, then remove it; the pass stops at the first hand-over the host refuses, which stays held with
   those behind it, and is counted once. A message that does not fit is no refusal. cf.stop: the first round's pass,
   which stops at a front message that does not fit *)
RECURSIVE DHLoop(_, _, _, _, _, _, _)
DHLoop(cf, R, now, node, open, fit, acc) ==
    LET p == IF cf.stop THEN Look(MC(cf), R.mb, now, node, fit) ELSE LookFit(MC(cf), R.mb, now, node, fit)
        R1 == [R EXCEPT !.mb = p.mb]
    IN IF ~p.got THEN [R |-> R1, ef |-> acc]
       ELSE LET m == p.m
                sent == IF open THEN DeliverClient(cf, R1, now, m.src, node, m.flag, m.len, FALSE)
                        ELSE TunnelDown(R1, now, node, m.src, m.flag, m.len)
                R2 == IF open THEN sent.R ELSE R1
            IN IF sent.ok
               THEN DHLoop(cf, [R2 EXCEPT !.mb = RemoveSeq(MC(cf), R2.mb, node, m.seq)], now, node, open, fit,
                           acc \o sent.ef \o <<<<"t", "mdeliv", node, m.seq>>>>)
               ELSE [R |-> R2, ef |-> acc \o sent.ef \o <<RejE("notunnel", node)>>]

DeliverHeld(cf, R, now, node) ==
    IF Pending(R.mb, node)[1] = 0 THEN [R |-> R, ef |-> <<>>]
    ELSE LET open == HasC(cf, R, node)
         IN IF ~open /\ ~Fresh(R, now, node) THEN [R |-> R, ef |-> <<>>]
            ELSE DHLoop(cf, R, now, node, open, IF open THEN MAXPKT ELSE MAXTUN - 35, <<>>)

(* route.rs release_held, called by udp_heard: nothing held returns at once; a member whose session is not fresh or
   whose route the host reports not ready keeps its messages and nothing is emitted; otherwise the pass of deliver_held
   runs. more says messages remain held (counted as pending, as the code does; only the withdrawn rule of cf.hb reads
   it). cf.old: nothing is released *)
ReleaseHeld(cf, R, now, node) ==
    IF cf.old \/ Pending(R.mb, node)[1] = 0 THEN [R |-> R, ef |-> <<>>, more |-> FALSE]
    ELSE IF ~Fresh(R, now, node) \/ node \in R.nr THEN [R |-> R, ef |-> <<>>, more |-> TRUE]
    ELSE LET dh == DeliverHeld(cf, R, now, node) IN [R |-> dh.R, ef |-> dh.ef, more |-> Pending(dh.R.mb, node)[1] > 0]

(* the answer o behind the effects of an earlier step of the same call *)
After(ef, o) == [o EXCEPT !.ef = ef \o o.ef]

(* The withdrawn rule, for its witness only (cf.hb): after the carrier, a destination that holds messages is released
   first and the packet is held behind what remains, so a packet for a member that holds mail is never forwarded *)
RouteBehind(cf, R, now, src, dst, flag, len, origin) ==
    LET dc == DeliverClient(cf, R, now, src, dst, flag, len, TRUE) IN
    IF dc.ok THEN [R |-> dc.R, res |-> "ok", ef |-> dc.ef]
    ELSE LET rh == ReleaseHeld(cf, R, now, dst)
             R2 == rh.R
             td == TunnelDown(R2, now, dst, src, flag, len)
         IN IF rh.more THEN After(rh.ef, Hold(cf, R2, now, dst, src, flag, len))
    ELSE IF td.ok THEN [R |-> R2, res |-> "ok", ef |-> rh.ef \o td.ef]
    ELSE IF Live(cf, R2, now, dst) THEN After(rh.ef, Hold(cf, R2, now, dst, src, flag, len))
    ELSE IF origin = "peer" THEN After(rh.ef, Fail(R2, "noroute", src))
    ELSE After(rh.ef, Forward(cf, R2, now, src, dst, flag, len))

(* route.rs route; origin is "client", "peer" or "tunnel". Whatever the destination holds, the packet goes down its
   carrier, or down its UDP session, or is held while its sleep mark lasts, or is forwarded to its home; routing starts
   no release *)
Route(cf, R, now, src, dst, flag, len, origin) ==
    IF dst = cf.me THEN [R |-> R, res |-> "ok", ef |-> LocalEf(src, cf.me, len)]
    ELSE IF cf.hb THEN RouteBehind(cf, R, now, src, dst, flag, len, origin)
    ELSE LET dc == DeliverClient(cf, R, now, src, dst, flag, len, TRUE) IN
    IF dc.ok THEN [R |-> dc.R, res |-> "ok", ef |-> dc.ef]
    ELSE LET td == TunnelDown(R, now, dst, src, flag, len) IN
    IF td.ok THEN [R |-> R, res |-> "ok", ef |-> td.ef]
    ELSE IF Live(cf, R, now, dst) THEN Hold(cf, R, now, dst, src, flag, len)
    ELSE IF origin = "peer" THEN Fail(R, "noroute", src)
    ELSE Forward(cf, R, now, src, dst, flag, len)

(* the end of a member's mark by its return (a carrier opened, or member_returned): traced, so the host writes it *)
SleepEnd(R, node) == IF node \in DOMAIN R.sl THEN <<<<"t", "sleepend", node>>>> ELSE <<>>

(* clients.rs carrier_opened *)
CarrierOpened(cf, R, now, node) ==
    LET id == R.ns
        had == HasC(cf, R, node)
        pre == IF had THEN <<<<"close", node, R.cd[node].id, "replaced">>>> ELSE <<>>
        cl == [id |-> id, opened |-> now, lastRx |-> now, ws |-> now, wb |-> 0, tx |-> NewAT, rx |-> NewAT]
        ins == Insert(cf.C, R.bk, R.tb, node, 0)
    IN IF ins.res = "full" THEN [R |-> R, res |-> "full", ef |-> pre \o <<RejE("full", node)>>]
       ELSE LET R1 == [R EXCEPT !.tb = ins.t, !.cd = Put(R.cd, node, cl), !.ns = id + 1,
                               !.gone = Del(R.gone, node), !.gt = Remove(cf.C, R.bk, R.gt, node).t, !.sl = Del(R.sl, node)]
                dh == DeliverHeld(cf, R1, now, node)
            IN [R |-> dh.R, res |-> "ok", ef |-> pre \o <<<<"t", "opened", node, id>>>> \o SleepEnd(R, node) \o dh.ef]

(* clients.rs carrier_closed *)
CarrierClosed(cf, R, now, node, sid) ==
    IF ~HasC(cf, R, node) \/ R.cd[node].id # sid THEN [R |-> R, res |-> "ok", ef |-> <<>>]
    ELSE LET rm == Remove(cf.C, R.bk, R.tb, node)
             R2 == RecordGone(cf, [R EXCEPT !.tb = rm.t, !.cd = Del(R.cd, node)], node, now)
             asleep == node \in DOMAIN R2.gone /\ node \in DOMAIN R.sl /\ R.sl[node].at >= Sat(now - SWIN)
         IN [R |-> R2, res |-> "ok",
             ef |-> <<<<"t", "closed", node, IF asleep THEN 1 ELSE 0>>>>]

(* clients.rs charge *)
Charge(cf, R, now, node, bytes) ==
    LET c == R.cd[node]
        c1 == IF Sat(now - c.ws) >= cf.Window THEN [c EXCEPT !.ws = now, !.wb = 0] ELSE c
        nxt == c1.wb + bytes
    IN IF nxt > cf.Bytes THEN [R |-> [R EXCEPT !.cd[node] = c1], ok |-> FALSE, ef |-> <<<<"t", "quota", node>>>>]
       ELSE [R |-> [R EXCEPT !.cd[node] = [c1 EXCEPT !.wb = nxt]], ok |-> TRUE, ef |-> <<>>]

(* records.rs RecordStore::accept and Relay::store (the signature is an oracle: the calls here are validly signed) *)
Accept(cf, R, now, k, seq, home, origin) ==
    LET known == k \in DOMAIN R.rec
        s == R.rec[k]
        store == [R |-> [R EXCEPT !.rec = Put(R.rec, k, [seq |-> seq, home |-> home, rcv |-> now])], res |-> "ok",
                  ef |-> <<<<"t", "rstored", k, seq, origin>>>>]
    IN IF known /\ (seq < s.seq \/ (seq = s.seq /\ home # s.home)) THEN Fail(R, "stalerec", k)
       ELSE IF known /\ seq = s.seq THEN [R |-> [R EXCEPT !.rec[k].rcv = now], res |-> "ok", ef |-> <<>>]
       ELSE IF ~known /\ Cardinality(DOMAIN R.rec) >= cf.R THEN Fail(R, "storefull", k)
       ELSE store

RECURSIVE Replicate(_, _, _, _)
Replicate(R, i, rlen, acc) ==
    IF i > MAXPEERS THEN acc
    ELSE Replicate(R, i + 1, rlen, IF R.peers[i] # 0 THEN Append(acc, <<"peer", R.peers[i], "sync", rlen>>) ELSE acc)

Publish(cf, R, now, node, k, seq, home, rlen) ==
    IF node # k THEN Fail(R, "wrongowner", node)
    ELSE LET a == Accept(cf, R, now, k, seq, home, "publish") IN
         IF a.res # "ok" THEN a ELSE [R |-> a.R, res |-> "ok", ef |-> a.ef \o Replicate(a.R, 1, rlen, <<>>)]

(* discovery.rs sleep_notice; sender is 0 for a notice over UDP; ts is the notice's clock in ms. A copy of the notice
   that set a live mark (the same clock) is accepted and changes nothing: the mark keeps its time and its wake-up; a
   mark past its life is no mark (a copy of its notice sets a new one, with no wake-up kept). The eviction of a mark
   with no mail from a full table (put_sleeper: the oldest goes, traced sleepend and counted in marks_evicted; the
   notice is refused only when every mark holds mail) is not modelled: with C 2 and two clients no config fills the
   table, and no notice of the recorded trace (C 3) evicts one *)
SleepNotice(cf, R, now, k, ts, good, sender) ==
    IF sender # 0 /\ sender # k THEN Fail(R, "wrongsender", k)
    ELSE IF Abs(now * 1000 - ts) >= SKEWMS THEN Fail(R, "skew", k)
    ELSE IF ~(HasC(cf, R, k) \/ k \in DOMAIN R.gone) THEN Fail(R, "unknown", k)
    ELSE IF good = 0 THEN Fail(R, "sig", k)
    ELSE IF Live(cf, R, now, k) /\ R.sl[k].ts = ts THEN [R |-> R, res |-> "ok", ef |-> <<>>]
    ELSE IF ~CanPut(R.sl, k, cf.C) THEN Fail(R, "full", k)
    ELSE [R |-> [R EXCEPT !.sl = Put(R.sl, k, [at |-> now, ts |-> ts,
                                              woke |-> IF Live(cf, R, now, k) THEN R.sl[k].woke ELSE 0])],
          res |-> "ok", ef |-> <<<<"t", "sleepok", k>>>>]
(* the old rule, for the witness ConnectRelay_wcopy (a definition override): every accepted notice sets the mark at now,
   so a copy of it moves the mark and a crash after the copy reads as a suspension *)
SleepNoticeMove(cf, R, now, k, ts, good, sender) ==
    IF sender # 0 /\ sender # k THEN Fail(R, "wrongsender", k)
    ELSE IF Abs(now * 1000 - ts) >= SKEWMS THEN Fail(R, "skew", k)
    ELSE IF ~(HasC(cf, R, k) \/ k \in DOMAIN R.gone) THEN Fail(R, "unknown", k)
    ELSE IF good = 0 THEN Fail(R, "sig", k)
    ELSE IF ~CanPut(R.sl, k, cf.C) THEN Fail(R, "full", k)
    ELSE [R |-> [R EXCEPT !.sl = Put(R.sl, k, [at |-> now, ts |-> ts,
                                              woke |-> IF k \in DOMAIN R.sl THEN R.sl[k].woke ELSE 0])],
          res |-> "ok", ef |-> <<<<"t", "sleepok", k>>>>]

(* the packet bytes a frame is charged for *)
Weight(f) == CASE f[1] = "send" -> f[4]
               [] f[1] = "sendnew" -> f[5]
               [] f[1] = "sendalias" -> f[4]
               [] f[1] = "selfsend" -> f[2]
               [] f[1] = "other" -> f[2]
               [] f[1] = "pub" -> f[5]
               [] f[1] = "sleep" -> f[5]
               [] OTHER -> 0

(* clients.rs client_frame, after the charge *)
Dispatch(cf, R, now, node, f) ==
    CASE f[1] = "send" -> Route(cf, R, now, node, f[2], f[3], f[4], "client")
      [] f[1] = "sendnew" ->
           LET R1 == [R EXCEPT !.cd[node].rx = Learn(R.cd[node].rx, f[3], f[2])] IN
           Route(cf, R1, now, node, f[2], f[4], f[5], "client")
      [] f[1] = "sendalias" ->
           LET dst == Resolve(R.cd[node].rx, f[2]) IN
           IF dst = 0 THEN Fail(R, "unkalias", node) ELSE Route(cf, R, now, node, dst, f[3], f[4], "client")
      [] f[1] = "selfsend" -> [R |-> R, res |-> "ok", ef |-> LocalEf(node, cf.me, f[2])]
      [] f[1] = "ping" -> [R |-> R, res |-> "ok", ef |-> <<<<"t", "pulse", node>>, <<"car", node, "pong">>>>]
      [] f[1] = "pong" -> [R |-> R, res |-> "ok", ef |-> <<>>]
      [] f[1] = "pub" -> Publish(cf, R, now, node, f[2], f[3], f[4], f[5])
      [] f[1] = "sleep" -> SleepNotice(cf, R, now, f[2], f[3], f[4], node)
      [] OTHER -> Fail(R, "unexpected", node)

(* clients.rs carrier_frame *)
CarrierFrame(cf, R, now, node, sid, f) ==
    IF ~HasC(cf, R, node) \/ R.cd[node].id # sid THEN Fail(R, "stale", node)
    ELSE LET R1 == [R EXCEPT !.cd[node].lastRx = now]
             w == Weight(f)
             ch == Charge(cf, R1, now, node, w)
         IN IF w > 0 /\ ~ch.ok THEN [R |-> ch.R, res |-> "quota", ef |-> ch.ef]
            ELSE Dispatch(cf, IF w > 0 THEN ch.R ELSE R1, now, node, f)

(* clients.rs peer_frame *)
PeerFrame(cf, R, now, from, f) ==
    IF ~IsPeer(R, from) THEN Fail(R, "unauth", from)
    ELSE CASE f[1] = "fwd" ->
              LET src == f[2]
                  learn == ~HasC(cf, R, src)
                  R1 == IF learn THEN [R EXCEPT !.fb[R.bk[src]] = [n |-> src, rel |-> from, at |-> now]] ELSE R
                  rt == Route(cf, R1, now, src, f[3], f[4], f[5], "peer")
              IN [R |-> rt.R, res |-> rt.res, ef |-> (IF learn THEN <<<<"t", "fwdback", src, from>>>> ELSE <<>>) \o rt.ef]
           [] f[1] = "sync" -> Accept(cf, R, now, f[2], f[3], f[4], "replica")
           [] f[1] = "ping" -> [R |-> R, res |-> "ok", ef |-> <<<<"peer", from, "pong">>>>]
           [] f[1] = "pong" -> [R |-> R, res |-> "ok", ef |-> <<>>]
           [] OTHER -> Fail(R, "unexpected", from)

AddPeer(R, p) ==
    IF IsPeer(R, p) THEN [R |-> R, ok |-> TRUE]
    ELSE LET free == {i \in 1..MAXPEERS : R.peers[i] = 0} IN
         IF free = {} THEN [R |-> R, ok |-> FALSE] ELSE [R |-> [R EXCEPT !.peers[MinOf(free)] = p], ok |-> TRUE]
RemovePeer(R, p) == [R EXCEPT !.peers = [i \in 1..MAXPEERS |-> IF R.peers[i] = p THEN 0 ELSE R.peers[i]]]

(* route.rs udp_heard: the host heard the member on its validated route at now; the time is stamped, then the member's
   held messages are released. A full table is reported (cf.old: silently, with no release) *)
UdpHeard(cf, R, now, node) ==
    IF CanPut(R.udp, node, cf.C)
    THEN LET R1 == [R EXCEPT !.udp = Put(R.udp, node, now)]
             rh == ReleaseHeld(cf, R1, now, node)
         IN [R |-> rh.R, res |-> "ok", ef |-> rh.ef]
    ELSE IF cf.old THEN [R |-> R, res |-> "full", ef |-> <<>>] ELSE Fail(R, "full", node)
UdpGone(R, node) == [R EXCEPT !.udp = Del(R.udp, node)]

MemberReturned(cf, R, now, node) ==
    LET R1 == [R EXCEPT !.sl = Del(R.sl, node)]
        dh == DeliverHeld(cf, R1, now, node)
    IN [R |-> dh.R, res |-> "ok", ef |-> SleepEnd(R, node) \o dh.ef]

(* discovery.rs datagram, the SPU case; m is the validated member or 0. The member is heard first (its effects come
   first, a full table is traced and the datagram goes on) *)
Spu(cf, R, now, m, dst, flag, len) ==
    IF len = 0 \/ 35 + len > MAXTUN THEN Fail(R, "baddg", m)
    ELSE IF m = 0 THEN Fail(R, "unauth", 0)
    ELSE LET uh == IF CanPut(R.udp, m, cf.C) THEN UdpHeard(cf, R, now, m) ELSE [R |-> R, res |-> "ok", ef |-> <<>>] IN
         IF dst = cf.me THEN After(uh.ef, Fail(uh.R, "noroute", m))
         ELSE After(uh.ef, Route(cf, uh.R, now, m, dst, flag, len, "tunnel"))

(* clients.rs handle_timeout: the session sweep walks the real slots; an expired session is removed and the slot looked at again *)
RECURSIVE SweepC(_, _, _, _, _, _)
SweepC(cf, R, now, i, acc, dummy) ==
    IF i >= cf.C THEN [R |-> R, ef |-> acc]
    ELSE LET k == R.tb.s[i].k IN
         IF k = 0 THEN SweepC(cf, R, now, i + 1, acc, 0)
         ELSE LET c == R.cd[k] IN
              IF Sat(now - c.opened) < cf.SessT THEN SweepC(cf, R, now, i + 1, acc, 0)
              ELSE LET R1 == RecordGone(cf, [R EXCEPT !.tb = RemoveAt(cf.C, R.bk, R.tb, i), !.cd = Del(R.cd, k)], k, now)
                   IN SweepC(cf, R1, now, i, acc \o <<<<"t", "expired", k>>, <<"close", k, c.id, "session">>>>, 0)

(* clients.rs handle_timeout: every client carrier is written a PING, in slot order, every PING seconds *)
RECURSIVE PingC(_, _, _, _)
PingC(cf, R, i, acc) ==
    IF i >= cf.C THEN acc
    ELSE LET k == R.tb.s[i].k IN PingC(cf, R, i + 1, IF k = 0 THEN acc ELSE Append(acc, <<"car", k, "ping">>))

RECURSIVE ClearSet(_, _)
ClearSet(mb, S) == IF S = {} THEN mb ELSE LET x == CHOOSE y \in S : TRUE IN ClearSet(Clear(mb, x), S \ {x})

(* clients.rs handle_timeout, the marks: a mark past its life (Live) ends, and the messages held under it end with it
   (Mailbox::clear, counted expired), so no message outlives the mark it was held under *)
MarkSweep(cf, R, now) ==
    LET ended == {y \in DOMAIN R.sl : ~Live(cf, R, now, y)}
    IN [sl |-> [x \in DOMAIN R.sl \ ended |-> R.sl[x]], mb |-> ClearSet(R.mb, ended)]
(* the old rule's shape, for the witness ConnectRelay_wlife: a mark lives less than the mailbox keeps a message (the
   gone life of 600 s against a day; 16 s against cf.Age here) *)
MarkSweepShort(cf, R, now) ==
    [sl |-> [x \in {y \in DOMAIN R.sl : Sat(now - R.sl[y].at) < 16} |-> R.sl[x]], mb |-> R.mb]
(* for the witness ConnectRelay_wmail: the mark ends at its life and the messages held under it stay *)
MarkSweepKeepMail(cf, R, now) ==
    [sl |-> [x \in {y \in DOMAIN R.sl : Live(cf, R, now, y)} |-> R.sl[x]], mb |-> R.mb]

Timeout(cf, R0, now) ==
    LET due == now >= R0.np
        pf == IF due THEN PingC(cf, R0, 0, <<>>) ELSE <<>>
        R == IF due THEN [R0 EXCEPT !.np = now + PING] ELSE R0
    IN
    IF Sat(now - R.ls) < SWEEP THEN [R |-> R, res |-> "ok", ef |-> pf]
    ELSE LET sw == SweepC(cf, R, now, 0, pf, 0)
             R1 == sw.R
             ms == MarkSweep(cf, R1, now)
             R2 == [R1 EXCEPT !.ls = now,
                    !.gone = [x \in {y \in DOMAIN R1.gone : Sat(now - R1.gone[y]) < GONET} |-> R1.gone[x]],
                    !.gt = RetainGone(cf.C, R1.bk, R1.gt, 0, now),
                    !.sl = ms.sl,
                    !.rec = [x \in {y \in DOMAIN R1.rec : Sat(now - R1.rec[y].rcv) < RECTTL} |-> R1.rec[x]],
                    !.mb = Sweep(MC(cf), ms.mb, now)]
         IN [R |-> R2, res |-> "ok", ef |-> sw.ef]
=============================================================================
