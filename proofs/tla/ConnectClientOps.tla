---------------------------- MODULE ConnectClientOps ----------------------------
(***************************************************************************)
(* The client rules of vinc-connect/src/client as pure operators: the      *)
(* punch timer and probe gaps (punch.rs), the hub tunnel decisions and     *)
(* splice tables (tunnel.rs), the first-flight selection and pending dials *)
(* (dial.rs), the lookup table (lookup.rs) and the probe state with the    *)
(* classification (netcheck.rs).                                           *)
(*                                                                         *)
(* Time is in microseconds (TLC's integers are 32 bits wide; the code      *)
(* counts nanoseconds, every rule constant is a whole number of            *)
(* microseconds and the traces read the clock in whole milliseconds, so    *)
(* every division of the code is exact). A deadline of the code one        *)
(* nanosecond past a whole microsecond is the next microsecond here: the   *)
(* clock is only read on whole microseconds. -1 stands for none. Nodes,    *)
(* relays, sessions and addresses are small numbers; tables are sequences  *)
(* of fixed length, as the arrays of the code.                             *)
(* Lean counterpart: Vinc/ConnectClient.lean, ConnectClientThm.lean.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

SEC == 1000000
Max(a, b) == IF a > b THEN a ELSE b
Min(a, b) == IF a < b THEN a ELSE b
SatSub(a, b) == IF a < b THEN 0 ELSE a - b

(* ---- punch.rs ---- *)
PROBEBASE == 33300
PROBECAP == 2 * SEC
UPGRADE == 60 * SEC
GOOD == 10000
FIRSTDELAY == 1000
ACTIVEKEEP == 20 * SEC

RECURSIVE GapsFrom(_, _)
GapsFrom(n, g) == IF n = 0 THEN <<>> ELSE <<g>> \o GapsFrom(n - 1, Min(g * 2, PROBECAP))
ProbeGaps(srtt) == GapsFrom(9, Max(PROBEBASE, srtt \div 8))

\* the timer is at (0 is off); v is [idle, direct, rtt, quiet]
PDue(at, now, v) ==
    IF at = 0 \/ now < at THEN [res |-> "wait", at |-> at]
    ELSE IF now < v.quiet /\ v.direct THEN [res |-> "wait", at |-> v.quiet + 1]
    ELSE IF v.idle >= ACTIVEKEEP THEN [res |-> "wait", at |-> now + UPGRADE]
    ELSE [res |-> "punch", at |-> IF v.direct /\ v.rtt # 0 /\ v.rtt <= GOOD THEN 0 ELSE now + UPGRADE]
PObs(at) == IF at = 0 THEN -1 ELSE at

(* ---- tunnel.rs ---- *)
TSTALE == 15 * SEC
HUBFRESH == 20 * SEC
SPLLIVE == 30 * SEC
SPLICESPAN == 4 * SEC

HubOk(valid, heard, now) == valid /\ SatSub(now, heard) < HUBFRESH

Decide(open, silent, s, tunnel) ==
    IF ~tunnel THEN "carrier"
    ELSE IF ~open THEN "tunnel"
    ELSE IF silent > TSTALE THEN "both"
    ELSE IF ~s.has THEN "carrier"
    ELSE LET loss == s.pto >= (IF s.thin THEN 2 ELSE 1)
             hs == s.hs /\ (s.tries >= 2 \/ ~s.thin)
         IN IF loss \/ hs THEN "both" ELSE "carrier"

ThinSplice(t) ==
    IF ~(t.thin /\ t.est /\ t.took /\ ~t.fresh /\ t.pto < 2) THEN FALSE
    ELSE LET span == IF t.rtt * 2 > SPLICESPAN THEN t.rtt * 2 ELSE SPLICESPAN IN
         t.age >= 0 /\ t.age < span

\* a splice table: peers is a sequence of [e, peer, relay, at], live a sequence of [e, at, addr]
NewSplices(p, r) == [peers |-> [i \in 1..p |-> [e |-> FALSE, peer |-> 0, relay |-> 0, at |-> 0]], next |-> 0,
                     live |-> [i \in 1..r |-> [e |-> FALSE, at |-> 0, addr |-> 0]]]
FindPeer(peers, peer) ==
    LET S == {i \in 1..Len(peers) : peers[i].e /\ peers[i].peer = peer} IN
    IF S = {} THEN -1 ELSE (CHOOSE i \in S : \A j \in S : i <= j) - 1
Seen(T, now, relay, peer, frm) ==
    LET live == IF relay < Len(T.live) THEN [T.live EXCEPT ![relay + 1] = [e |-> TRUE, at |-> now, addr |-> frm]] ELSE T.live
        f == FindPeer(T.peers, peer)
        slot == IF f >= 0 THEN f ELSE T.next
        peers == IF slot < Len(T.peers) THEN [T.peers EXCEPT ![slot + 1] = [e |-> TRUE, peer |-> peer, relay |-> relay, at |-> now]] ELSE T.peers
    IN [peers |-> peers, next |-> IF slot = T.next THEN (T.next + 1) % Max(Len(T.peers), 1) ELSE T.next, live |-> live]
Age(T, now, relay, peer) ==
    LET S == {i \in 1..Len(T.peers) : T.peers[i].e /\ T.peers[i].peer = peer /\ T.peers[i].relay = relay} IN
    IF S = {} THEN -1 ELSE SatSub(now, T.peers[CHOOSE i \in S : \A j \in S : i <= j].at)
LiveAt(T, now, relay, rtt) ==
    IF relay >= Len(T.live) THEN -1
    ELSE LET l == T.live[relay + 1] IN
         IF ~l.e THEN -1
         ELSE LET span == IF rtt * 2 > SPLLIVE THEN rtt * 2 ELSE SPLLIVE IN IF SatSub(now, l.at) < span THEN l.addr ELSE -1

(* ---- dial.rs ---- *)
LATESTART == 10 * SEC
TGSLOW == 250000
RLYONCE == 30 * SEC
RLYMIN == 4 * SEC

DirectFirst(first, hub, fd, started) == first /\ hub /\ SatSub(fd, started) > LATESTART

\* a candidate is <<"u", addr>> or <<"r", relay>>; views is a sequence of [some, live, gen]
KeepCand(t, views, c) ==
    IF c[1] = "u" THEN ~(t.hs0 /\ t.dialer)
    ELSE LET v == IF c[2] < Len(views) THEN views[c[2] + 1] ELSE [some |-> FALSE, live |-> FALSE, gen |-> 0] IN
         ~(t.dialer /\ t.rtt >= TGSLOW /\ v.some /\ v.live /\ t.haslast /\ t.last[1] = c[2] /\ t.last[2] = v.gen
           /\ SatSub(t.now, t.last[3]) < Min(RLYONCE, Max(RLYMIN, t.rtt * 3)))

RECURSIVE KeepAll(_, _, _)
KeepAll(t, views, cs) == IF cs = <<>> THEN <<>>
                         ELSE (IF KeepCand(t, views, Head(cs)) THEN <<Head(cs)>> ELSE <<>>) \o KeepAll(t, views, Tail(cs))

RECURSIVE Carried(_, _, _)
Carried(views, out, acc) ==
    IF out = <<>> THEN acc
    ELSE IF Head(out)[1] = "r"
         THEN Carried(views, Tail(out), <<Head(out)[2], IF Head(out)[2] < Len(views) /\ views[Head(out)[2] + 1].some THEN views[Head(out)[2] + 1].gen ELSE 0>>)
         ELSE Carried(views, Tail(out), acc)

Select(cands, t, views, cap) ==
    LET kept == KeepAll(t, views, SubSeq(cands, 1, Min(Len(cands), 16)))
        n == Len(kept)
        slow == t.rtt >= TGSLOW
        thin == t.dialer /\ n > 1 /\ (slow \/ (t.tries >= 2 /\ t.nortt))
        picked == IF thin THEN <<kept[(t.tries % n) + 1]>> ELSE kept
        out == SubSeq(picked, 1, Min(Len(picked), cap))
    IN [out |-> out, carried |-> Carried(views, out, <<>>)]

\* pending dials: items is a sequence of [e, peer, ws] with ws a sequence of H sessions (-1 empty)
NewPending(n, h) == [items |-> [i \in 1..n |-> [e |-> FALSE, peer |-> 0, ws |-> [k \in 1..h |-> -1]]], h |-> h]
SlotOf(items, peer) ==
    LET S == {i \in 1..Len(items) : items[i].e /\ items[i].peer = peer} IN
    IF S # {} THEN CHOOSE i \in S : \A j \in S : i <= j
    ELSE LET F == {i \in 1..Len(items) : ~items[i].e} IN IF F = {} THEN -1 ELSE CHOOSE i \in F : \A j \in F : i <= j
FirstFree(ws) == LET F == {k \in 1..Len(ws) : ws[k] = -1} IN IF F = {} THEN -1 ELSE CHOOSE k \in F : \A j \in F : k <= j
PAdd(P, peer, s) ==
    LET i == SlotOf(P.items, peer) IN
    IF i < 0 THEN [ok |-> FALSE, P |-> P]
    ELSE LET cur == IF P.items[i].e THEN P.items[i] ELSE [e |-> TRUE, peer |-> peer, ws |-> [k \in 1..P.h |-> -1]]
             hasS == \E k \in 1..Len(cur.ws) : cur.ws[k] = s
             f == FirstFree(cur.ws)
         IN IF hasS THEN [ok |-> TRUE, P |-> [P EXCEPT !.items[i] = cur]]
            ELSE IF f < 0 THEN [ok |-> FALSE, P |-> [P EXCEPT !.items[i] = cur]]
            ELSE [ok |-> TRUE, P |-> [P EXCEPT !.items[i] = [cur EXCEPT !.ws[f] = s]]]
PTake(P, peer) ==
    LET S == {i \in 1..Len(P.items) : P.items[i].e /\ P.items[i].peer = peer} IN
    IF S = {} THEN [res |-> [k \in 1..P.h |-> -1], P |-> P]
    ELSE LET i == CHOOSE i \in S : \A j \in S : i <= j IN
         [res |-> P.items[i].ws, P |-> [P EXCEPT !.items[i] = [e |-> FALSE, peer |-> 0, ws |-> [k \in 1..P.h |-> -1]]]]
\* keep the sessions s with s % 4 # keep; the peers left with none are dropped, in slot order
RECURSIVE PruneAll(_, _, _, _)
PruneAll(items, i, keep, dropped) ==
    IF i > Len(items) THEN [items |-> items, dropped |-> dropped]
    ELSE IF ~items[i].e THEN PruneAll(items, i + 1, keep, dropped)
    ELSE LET ws == [k \in 1..Len(items[i].ws) |-> IF items[i].ws[k] >= 0 /\ items[i].ws[k] % 4 = keep THEN -1 ELSE items[i].ws[k]]
         IN IF \A k \in 1..Len(ws) : ws[k] = -1
            THEN PruneAll([items EXCEPT ![i] = [e |-> FALSE, peer |-> 0, ws |-> ws]], i + 1, keep, Append(dropped, items[i].peer))
            ELSE PruneAll([items EXCEPT ![i].ws = ws], i + 1, keep, dropped)
PPeers(P) == LET RECURSIVE F(_, _) F(i, acc) == IF i > Len(P.items) THEN acc ELSE F(i + 1, IF P.items[i].e THEN Append(acc, P.items[i].peer) ELSE acc) IN F(1, <<>>)
PHas(P, k) == \E i \in 1..Len(P.items) : P.items[i].e /\ P.items[i].peer = k

(* ---- lookup.rs ---- *)
LRETRY == 300000
CWAIT == 2 * SEC
THINMAX == 8 * SEC
NewLookups(n) == [items |-> [i \in 1..n |-> [e |-> FALSE, peer |-> 0, at |-> 0, tried |-> FALSE, conly |-> FALSE, again |-> FALSE, wait |-> LRETRY]]]
LSlot(items, peer) == SlotOf(items, peer)
LAsk(T, now, peer, udp, car, thin) ==
    LET i == LSlot(T.items, peer) IN
    IF i < 0 THEN [res |-> "skip", T |-> T]
    ELSE LET cur == T.items[i]
             item == IF cur.e THEN cur ELSE [e |-> TRUE, peer |-> peer, at |-> 0, tried |-> FALSE, conly |-> FALSE, again |-> FALSE, wait |-> LRETRY]
         IN IF cur.e /\ ~item.again /\ now < item.at + item.wait THEN [res |-> "skip", T |-> T]
            ELSE LET retry == item.tried
                     thinWait == IF thin = 0 THEN 0 ELSE IF 2 * thin < THINMAX THEN 2 * thin ELSE THINMAX
                     i1 == [item EXCEPT !.again = FALSE, !.tried = TRUE, !.at = now, !.wait = IF thinWait > LRETRY THEN thinWait ELSE LRETRY]
                     byCar == ~udp \/ i1.conly
                     r == IF byCar
                          THEN LET i2 == [i1 EXCEPT !.at = now + (CWAIT - LRETRY)] IN
                               IF car THEN [res |-> "carrier", item |-> i2]
                               ELSE IF retry THEN [res |-> "later", item |-> i2]
                               ELSE [res |-> "udp", item |-> [i2 EXCEPT !.at = now]]
                          ELSE [res |-> IF retry THEN "udpall" ELSE "udp", item |-> i1]
                 IN [res |-> r.res, T |-> [items |-> [T.items EXCEPT ![i] = r.item]]]
LAnswered(T, peer) == [items |-> [i \in 1..Len(T.items) |-> IF T.items[i].e /\ T.items[i].peer = peer THEN [T.items[i] EXCEPT !.e = FALSE] ELSE T.items[i]]]
LTooLarge(T, peer) == [items |-> [i \in 1..Len(T.items) |->
                         IF T.items[i].e /\ T.items[i].peer = peer THEN [T.items[i] EXCEPT !.conly = TRUE, !.again = TRUE] ELSE T.items[i]]]
LClear(T) == [items |-> [i \in 1..Len(T.items) |-> [T.items[i] EXCEPT !.e = FALSE]]]
LLen(T) == Cardinality({i \in 1..Len(T.items) : T.items[i].e})
LHas(T, k) == \E i \in 1..Len(T.items) : T.items[i].e /\ T.items[i].peer = k
LDue(T, now) == LET RECURSIVE F(_, _) F(i, acc) == IF i > Len(T.items) THEN acc ELSE F(i + 1, IF T.items[i].e /\ now > T.items[i].at + T.items[i].wait THEN Append(acc, T.items[i].peer) ELSE acc) IN F(1, <<>>)
LNext(T) == LET S == {i \in 1..Len(T.items) : T.items[i].e} IN
            IF S = {} THEN -1 ELSE (CHOOSE m \in {T.items[i].at + T.items[i].wait + 1 : i \in S} : \A x \in {T.items[i].at + T.items[i].wait + 1 : i \in S} : m <= x)

(* ---- netcheck.rs ---- *)
MISSLIMIT == 3
HOMETRIES == 3
\* addresses are <<ip octets, port>>
IsShared(ip) == Len(ip) = 4 /\ ip[1] = 100 /\ ip[2] >= 64 /\ ip[2] < 128
Classify(local, refl, mapped, heard, since, wd) ==
    IF refl = <<>> THEN (IF ~heard /\ since >= wd THEN 5 ELSE 0)
    ELSE IF \E i \in 1..Len(refl) : \E j \in 1..Len(local) : refl[i] = local[j] THEN 1
    ELSE IF \E i \in 1..Len(refl) : \E j \in 1..Len(mapped) : refl[i] = mapped[j] THEN 2
    ELSE IF (\E i \in 1..Len(refl) : IsShared(refl[i][1])) \/ (\E i \in 1..Len(refl) : refl[i] # refl[1]) THEN 4
    ELSE 3

NewNet(r) == [probes |-> [i \in 1..r |-> [e |-> FALSE, nonce |-> <<>>, sent |-> 0]], rtt |-> [i \in 1..r |-> 0],
              refl |-> [i \in 1..r |-> -1], home |-> -1, missed |-> [i \in 1..r |-> 0], tries |-> 0, fp |-> -1]
Unhealthy(N, i) == N.missed[i + 1] >= MISSLIMIT
NFailed(N, i) == IF i < Len(N.missed) THEN [N EXCEPT !.missed[i + 1] = Min(255, N.missed[i + 1] + 1)] ELSE N
NHealthy(N, i) == IF i < Len(N.missed) THEN [N EXCEPT !.missed[i + 1] = 0] ELSE N
NProbeSent(N, now, relay, nonce, works) ==
    LET N1 == IF works /\ relay < Len(N.probes) /\ N.probes[relay + 1].e THEN NFailed(N, relay) ELSE N IN
    IF relay < Len(N1.probes)
    THEN [N1 EXCEPT !.probes[relay + 1] = [e |-> TRUE, nonce |-> nonce, sent |-> now], !.fp = IF N1.fp < 0 THEN now ELSE N1.fp]
    ELSE N1
ArgMin(S, key) == IF S = {} THEN -1 ELSE CHOOSE m \in S : \A x \in S : key[m + 1] < key[x + 1] \/ (key[m + 1] = key[x + 1] /\ m <= x)
NAnswered(N, now, relay, nonce, addr) ==
    IF relay >= Len(N.probes) \/ ~N.probes[relay + 1].e \/ N.probes[relay + 1].nonce # nonce THEN [res |-> -1, N |-> N]
    ELSE LET rtt == SatSub(now, N.probes[relay + 1].sent)
             N1 == [N EXCEPT !.probes[relay + 1].e = FALSE, !.missed[relay + 1] = 0, !.rtt[relay + 1] = rtt, !.refl[relay + 1] = addr]
             cands == {i \in 0..(Len(N1.probes) - 1) : N1.refl[i + 1] >= 0 /\ ~Unhealthy(N1, i)}
             best == ArgMin(cands, N1.rtt)
             N2 == IF best >= 0 /\ N1.home # best /\ (N1.home < 0 \/ Unhealthy(N1, N1.home) \/ N1.rtt[best + 1] < N1.rtt[N1.home + 1])
                   THEN [N1 EXCEPT !.home = best] ELSE N1
         IN [res |-> rtt, N |-> N2]
NFailover(N, usable, open) ==
    IF N.home < 0 \/ ~Unhealthy(N, N.home) THEN [res |-> -1, N |-> N]
    ELSE LET rn == Len(N.probes)
             meas == ArgMin({i \in 0..(rn - 1) : i # N.home /\ usable[i + 1] /\ N.missed[i + 1] = 0 /\ N.refl[i + 1] >= 0}, N.rtt)
             ring == {(N.home + k) % rn : k \in 1..(rn - 1)}
             cand == {k \in 1..(rn - 1) : usable[((N.home + k) % rn) + 1] /\ open[((N.home + k) % rn) + 1] /\ ~Unhealthy(N, (N.home + k) % rn)}
             nxt == IF meas >= 0 THEN meas
                    ELSE IF cand = {} THEN -1
                    ELSE (N.home + (CHOOSE k \in cand : \A x \in cand : k <= x)) % rn
         IN IF nxt < 0 THEN [res |-> -1, N |-> N] ELSE [res |-> nxt, N |-> [N EXCEPT !.home = nxt]]
NRestart(N) == [N EXCEPT !.probes = [i \in 1..Len(N.probes) |-> [N.probes[i] EXCEPT !.e = FALSE]],
                         !.refl = [i \in 1..Len(N.refl) |-> -1], !.fp = -1, !.tries = 0]
NMissing(N, first) ==
    IF N.home >= 0 THEN [res |-> "done", N |-> N]
    ELSE LET N1 == [N EXCEPT !.tries = Min(255, N.tries + 1)] IN
         IF first >= 0 /\ N1.tries >= HOMETRIES THEN [res |-> "fb" \o ToString(first), N |-> [N1 EXCEPT !.home = first]]
         ELSE [res |-> "again", N |-> N1]
NRtt(N, i) == IF N.refl[i + 1] >= 0 THEN N.rtt[i + 1] ELSE -1
NBest(N) == LET S == {i \in 0..(Len(N.probes) - 1) : N.refl[i + 1] >= 0} IN
            IF S = {} THEN 0 ELSE (CHOOSE m \in {N.rtt[i + 1] : i \in S} : \A x \in {N.rtt[i + 1] : i \in S} : m <= x)
=============================================================================
