-------------------------- MODULE ConnectRelayOps --------------------------
(***************************************************************************)
(* The relay of vinc-connect/src/relay (mod.rs, clients.rs, route.rs,      *)
(* records.rs, discovery.rs): carrier sessions, quota, forwarding, the     *)
(* reply route, the hub tunnel, record storage, sleep notices and the      *)
(* hold of packets for sleeping members, as pure operators: each takes the *)
(* configuration cf, the state R and the call, and returns the new state,  *)
(* the answer ("ok" or the reason of the refusal) and the effects in the   *)
(* order the code emits them (frames, closes, wake-ups and every Trace).   *)
(*                                                                         *)
(* Time is in whole seconds, the unit of the trace; every rule constant is *)
(* a whole number of seconds in the code. Node ids are small naturals,     *)
(* 0 meaning none. Tables:                                                 *)
(*  - the session table is the exact Table of ConnectTableOps.tla (so the  *)
(*    sweep closes sessions in the order of the real slots); the sessions  *)
(*    themselves are in cd;                                                *)
(*  - gone, sl (sleeping), udp, rec and the member table of the mailbox    *)
(*    are finite functions that are full at their capacity (a new key is   *)
(*    refused when full), which is all the code observes of them           *)
(*    (ConnectTable.tla proves the table is that map);                     *)
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
                 sl |-> [x \in {} |-> 0], udp |-> [x \in {} |-> 0], nr |-> {},
                 fb |-> [i \in 0..(cf.C - 1) |-> [n |-> 0, rel |-> 0, at |-> 0]],
                 peers |-> [i \in 1..MAXPEERS |-> 0], rec |-> [x \in {} |-> 0], mb |-> Empty, ns |-> 0, ls |-> 0, np |-> 0]

HasC(cf, R, n) == Find(cf.C, R.bk, R.tb, n) >= 0
IsPeer(R, n) == \E i \in 1..MAXPEERS : R.peers[i] = n
CanPut(f, k, cap) == k \in DOMAIN f \/ Cardinality(DOMAIN f) < cap

RoutedE(s, d, rt, b) == <<"t", "routed", s, d, rt, b>>
RejE(why, node) == <<"t", "rej", why, node>>
LocalEf(from, me, len) == <<RoutedE(from, me, "local", len), <<"local", from, len>>>>
Fail(R, why, node) == [R |-> R, res |-> why, ef |-> <<RejE(why, node)>>]

(* The host answers Sink::tunnel_ready from nr, the members with no validated direct route; it is an input of the
   call *)
SetReady(R, node, ok) == [R EXCEPT !.nr = IF ok = 1 THEN R.nr \ {node} ELSE R.nr \cup {node}]

(* route.rs tunnel_down *)
TunnelDown(R, now, dst, src, flag, len) ==
    LET fresh == dst \in DOMAIN R.udp /\ Sat(now - R.udp[dst]) < FRESH IN
    IF ~fresh \/ dst \in R.nr \/ len = 0 \/ 35 + len > MAXTUN THEN [ok |-> FALSE, ef |-> <<>>]
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

(* route.rs hold: the packet goes into the mailbox, and a wake-up is requested on the first one or 30 s after the last *)
Hold(cf, R, now, dst, src, flag, len) ==
    LET p == Push(MC(cf), R.mb, now, dst, src, flag, len) IN
    IF p.res = "stored"
    THEN LET s == R.sl[dst]
             rearm == ShouldWake(MC(cf), now, s, p.first)
             R1 == [R EXCEPT !.mb = p.mb, !.sl[dst] = IF rearm THEN [s EXCEPT !.woke = now] ELSE s]
             e == <<RoutedE(src, dst, "mailbox", len), <<"t", "mstored", dst, p.seq, p.dropped>>>>
                  \o (IF rearm THEN <<<<"t", "wakereq", dst>>, <<"wake", dst>>>> ELSE <<>>)
         IN [R |-> R1, res |-> "ok", ef |-> e]
    ELSE [R |-> [R EXCEPT !.mb = p.mb], res |-> "mbrefused", ef |-> <<RejE("mbrefused", src)>>]

(* route.rs forward: RELAY_FORWARD to the home relay, the reply route first *)
Forward(cf, R, now, src, dst, flag, len) ==
    LET slot == R.fb[R.bk[dst]]
        back == IF slot.n = dst /\ Sat(now - slot.at) < FWDB /\ slot.rel # cf.me THEN slot.rel ELSE 0
        home == IF back # 0 THEN back ELSE IF dst \in DOMAIN R.rec THEN R.rec[dst].home ELSE 0
    IN IF home = 0 \/ home = cf.me THEN Fail(R, "noroute", src)
       ELSE IF ~IsPeer(R, home) THEN Fail(R, "nopeer", src)
       ELSE [R |-> R, res |-> "ok", ef |-> <<<<"peer", home, "fwd", src, dst, flag, len>>, RoutedE(src, dst, "peer", len)>>]

(* route.rs route; origin is "client", "peer" or "tunnel" *)
Route(cf, R, now, src, dst, flag, len, origin) ==
    IF dst = cf.me THEN [R |-> R, res |-> "ok", ef |-> LocalEf(src, cf.me, len)]
    ELSE LET dc == DeliverClient(cf, R, now, src, dst, flag, len, TRUE) IN
    IF dc.ok THEN [R |-> dc.R, res |-> "ok", ef |-> dc.ef]
    ELSE LET td == TunnelDown(R, now, dst, src, flag, len) IN
    IF td.ok THEN [R |-> R, res |-> "ok", ef |-> td.ef]
    ELSE IF dst \in DOMAIN R.sl THEN Hold(cf, R, now, dst, src, flag, len)
    ELSE IF origin = "peer" THEN Fail(R, "noroute", src)
    ELSE Forward(cf, R, now, src, dst, flag, len)

(* route.rs deliver_held: look, hand over, then remove; the pass stops at the first message that cannot be handed over,
   which stays held, and is counted once *)
RECURSIVE DHLoop(_, _, _, _, _, _, _)
DHLoop(cf, R, now, node, open, fit, acc) ==
    LET p == Look(MC(cf), R.mb, now, node, fit)
        R1 == [R EXCEPT !.mb = p.mb]
    IN IF ~p.got THEN [R |-> R1, ef |-> acc]
       ELSE LET m == p.m
                sent == IF open THEN DeliverClient(cf, R1, now, m.src, node, m.flag, m.len, FALSE)
                        ELSE TunnelDown(R1, now, node, m.src, m.flag, m.len)
                R2 == IF open THEN sent.R ELSE R1
            IN IF sent.ok
               THEN DHLoop(cf, [R2 EXCEPT !.mb = MbRemove(MC(cf), R2.mb, node, m.seq)], now, node, open, fit,
                           acc \o sent.ef \o <<<<"t", "mdeliv", node, m.seq>>>>)
               ELSE [R |-> R2, ef |-> acc \o sent.ef \o <<RejE("notunnel", node)>>]

DeliverHeld(cf, R, now, node) ==
    IF Pending(R.mb, node)[1] = 0 THEN [R |-> R, ef |-> <<>>]
    ELSE LET open == HasC(cf, R, node)
             fresh == node \in DOMAIN R.udp /\ Sat(now - R.udp[node]) < FRESH
         IN IF ~open /\ ~fresh THEN [R |-> R, ef |-> <<>>]
            ELSE DHLoop(cf, R, now, node, open, IF open THEN MAXPKT ELSE MAXTUN - 35, <<>>)

(* clients.rs carrier_opened *)
CarrierOpened(cf, R, now, node) ==
    LET id == R.ns
        had == HasC(cf, R, node)
        pre == IF had THEN <<<<"close", node, R.cd[node].id, "replaced">>>> ELSE <<>>
        cl == [id |-> id, opened |-> now, lastRx |-> now, ws |-> now, wb |-> 0, tx |-> NewAT, rx |-> NewAT]
        ins == Insert(cf.C, R.bk, R.tb, node, 0)
    IN IF ins.res = "full" THEN [R |-> R, res |-> "full", ef |-> pre \o <<RejE("full", node)>>]
       ELSE LET R1 == [R EXCEPT !.tb = ins.t, !.cd = Put(R.cd, node, cl), !.ns = id + 1,
                               !.gone = Del(R.gone, node), !.sl = Del(R.sl, node)]
                dh == DeliverHeld(cf, R1, now, node)
            IN [R |-> dh.R, res |-> "ok", ef |-> pre \o <<<<"t", "opened", node, id>>>> \o dh.ef]

(* clients.rs carrier_closed *)
CarrierClosed(cf, R, now, node, sid) ==
    IF ~HasC(cf, R, node) \/ R.cd[node].id # sid THEN [R |-> R, res |-> "ok", ef |-> <<>>]
    ELSE LET rm == Remove(cf.C, R.bk, R.tb, node)
             gone1 == IF CanPut(R.gone, node, cf.C) THEN Put(R.gone, node, now) ELSE R.gone
             asleep == node \in DOMAIN gone1 /\ node \in DOMAIN R.sl /\ R.sl[node].at >= Sat(now - SWIN)
         IN [R |-> [R EXCEPT !.tb = rm.t, !.cd = Del(R.cd, node), !.gone = gone1], res |-> "ok",
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

(* discovery.rs sleep_notice; sender is 0 for a notice over UDP; ts is the notice's clock in ms *)
SleepNotice(cf, R, now, k, ts, good, sender) ==
    IF sender # 0 /\ sender # k THEN Fail(R, "wrongsender", k)
    ELSE IF Abs(now * 1000 - ts) >= SKEWMS THEN Fail(R, "skew", k)
    ELSE IF ~(HasC(cf, R, k) \/ k \in DOMAIN R.gone) THEN Fail(R, "unknown", k)
    ELSE IF good = 0 THEN Fail(R, "sig", k)
    ELSE IF ~CanPut(R.sl, k, cf.C) THEN Fail(R, "full", k)
    ELSE [R |-> [R EXCEPT !.sl = Put(R.sl, k, [at |-> now, woke |-> IF k \in DOMAIN R.sl THEN R.sl[k].woke ELSE 0])],
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

UdpHeard(cf, R, node, at) ==
    IF CanPut(R.udp, node, cf.C) THEN [R |-> [R EXCEPT !.udp = Put(R.udp, node, at)], res |-> "ok", ef |-> <<>>]
    ELSE [R |-> R, res |-> "full", ef |-> <<>>]
UdpGone(R, node) == [R EXCEPT !.udp = Del(R.udp, node)]

MemberReturned(cf, R, now, node) ==
    LET R1 == [R EXCEPT !.sl = Del(R.sl, node)]
        dh == DeliverHeld(cf, R1, now, node)
    IN [R |-> dh.R, res |-> "ok", ef |-> dh.ef]

(* discovery.rs datagram, the SPU case; m is the validated member or 0 *)
Spu(cf, R, now, m, dst, flag, len) ==
    IF len = 0 \/ 35 + len > MAXTUN THEN Fail(R, "baddg", m)
    ELSE LET R1 == IF m # 0 /\ CanPut(R.udp, m, cf.C) THEN [R EXCEPT !.udp = Put(R.udp, m, now)] ELSE R IN
         IF m = 0 THEN Fail(R1, "unauth", 0)
         ELSE IF dst = cf.me THEN Fail(R1, "noroute", m)
         ELSE Route(cf, R1, now, m, dst, flag, len, "tunnel")

(* clients.rs handle_timeout: the session sweep walks the real slots; an expired session is removed and the slot looked at again *)
RECURSIVE SweepC(_, _, _, _, _, _)
SweepC(cf, R, now, i, acc, dummy) ==
    IF i >= cf.C THEN [R |-> R, ef |-> acc]
    ELSE LET k == R.tb.s[i].k IN
         IF k = 0 THEN SweepC(cf, R, now, i + 1, acc, 0)
         ELSE LET c == R.cd[k] IN
              IF Sat(now - c.opened) < cf.SessT THEN SweepC(cf, R, now, i + 1, acc, 0)
              ELSE LET R1 == [R EXCEPT !.tb = RemoveAt(cf.C, R.bk, R.tb, i), !.cd = Del(R.cd, k),
                                       !.gone = IF CanPut(R.gone, k, cf.C) THEN Put(R.gone, k, now) ELSE R.gone]
                   IN SweepC(cf, R1, now, i, acc \o <<<<"t", "expired", k>>, <<"close", k, c.id, "session">>>>, 0)

(* clients.rs handle_timeout: every client carrier is written a PING, in slot order, every PING seconds *)
RECURSIVE PingC(_, _, _, _)
PingC(cf, R, i, acc) ==
    IF i >= cf.C THEN acc
    ELSE LET k == R.tb.s[i].k IN PingC(cf, R, i + 1, IF k = 0 THEN acc ELSE Append(acc, <<"car", k, "ping">>))

Timeout(cf, R0, now) ==
    LET due == now >= R0.np
        pf == IF due THEN PingC(cf, R0, 0, <<>>) ELSE <<>>
        R == IF due THEN [R0 EXCEPT !.np = now + PING] ELSE R0
    IN
    IF Sat(now - R.ls) < SWEEP THEN [R |-> R, res |-> "ok", ef |-> pf]
    ELSE LET sw == SweepC(cf, R, now, 0, pf, 0)
             R1 == sw.R
             R2 == [R1 EXCEPT !.ls = now,
                    !.gone = [x \in {y \in DOMAIN R1.gone : Sat(now - R1.gone[y]) < GONET} |-> R1.gone[x]],
                    !.sl = [x \in {y \in DOMAIN R1.sl : Sat(now - R1.sl[y].at) < GONET} |-> R1.sl[x]],
                    !.rec = [x \in {y \in DOMAIN R1.rec : Sat(now - R1.rec[y].rcv) < RECTTL} |-> R1.rec[x]],
                    !.mb = Sweep(MC(cf), R1.mb, now)]
         IN [R |-> R2, res |-> "ok", ef |-> sw.ef]
=============================================================================
