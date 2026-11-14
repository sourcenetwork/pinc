------------------------------ MODULE ConnectClient ------------------------------
(***************************************************************************)
(* Model check of the client rules (ConnectClientOps.tla).                 *)
(*                                                                         *)
(* Mode "pure": the decisions are checked over a finite domain of every    *)
(* argument that matters (a single state):                                 *)
(*  PunchOK     the probe gaps are nine, the first at least 33.3 ms and    *)
(*              the others at most 2 s; the punch timer is never left in   *)
(*              the past; it punches only when due; it stops for a good    *)
(*              direct path; an idle session only waits                    *)
(*  TunnelOK    no tunnel means the carrier, a closed carrier means the    *)
(*              tunnel, a stale carrier gets both; THIN_SPLICE needs a     *)
(*              thin node, an established session and a splice younger     *)
(*              than the span                                              *)
(*  SelectOK    the selection is a subsequence of the candidates, at most  *)
(*              cap long, one on a thin try, and the carried relay is one  *)
(*              of those selected                                          *)
(*  ClassifyOK  the class is UDP blocked only with no UDP heard, no        *)
(*              reflexive address and the watchdog passed; public wins     *)
(*              over port-mapped over carrier-grade over behind NAT        *)
(* Mode "pending", "lookups", "net": the table or the probe state under    *)
(* every sequence of its calls:                                            *)
(*  PendingOK   the table keeps its size, a peer is in at most one slot,   *)
(*              a session waits in at most one place, an accepted session  *)
(*              is in the table, prune keeps only the sessions asked to    *)
(*  LookupsOK   the table keeps its size and a peer is in at most one      *)
(*              slot; a query within the retry wait is skipped; a peer is  *)
(*              due only after the wait; nothing waits forever             *)
(*  NetOK       the home is a valid relay; after an answer it is the       *)
(*              relay with the lowest last round trip among those that     *)
(*              ever answered and are not unhealthy, a tie to the one that *)
(*              answered first (so a fallback home that never answered     *)
(*              moves to the first relay that does); the places in the     *)
(*              order of first answers are 1..k, each once; a link change  *)
(*              keeps the home, that order and the count of rounds without *)
(*              a home; a failover lands on a relay known to work (it      *)
(*              answered a probe since it last failed, or its carrier is   *)
(*              open); a relay is unhealthy after three misses in a row    *)
(*              and healthy again after an answer; at the third round      *)
(*              without a home, counted across link changes, the relay     *)
(*              given (the lowest id) is the home                          *)
(* Witnesses of the rules the code had before (TLC must violate them):     *)
(*  ConnectClient_w_homelower  HomeOnlyLower: the home moves only to a     *)
(*              strictly lower round trip or away from an unhealthy relay  *)
(* Lean: Vinc/ConnectClientThm.lean.                                       *)
(***************************************************************************)
EXTENDS ConnectClientOps

CONSTANTS Mode, Times, Peers, Sess
VARIABLES P, LK, NC
vars == <<P, LK, NC>>

RECURSIVE Subseq(_, _)
Subseq(a, b) == IF a = <<>> THEN TRUE ELSE IF b = <<>> THEN FALSE
                ELSE IF Head(a) = Head(b) THEN Subseq(Tail(a), Tail(b)) ELSE Subseq(a, Tail(b))

(* ---- pure ---- *)
Views == {[idle |-> a, direct |-> d, rtt |-> r, quiet |-> q] : a \in {0, ACTIVEKEEP - 1, ACTIVEKEEP}, d \in BOOLEAN,
                                                                r \in {0, 5000, GOOD, GOOD + 1}, q \in {0, 5 * SEC, 20 * SEC}}
PunchOK ==
    /\ \A srtt \in {0, 8000, 264000, 2 * SEC, 20 * SEC} :
         LET g == ProbeGaps(srtt) IN
         /\ Len(g) = 9 /\ g[1] >= PROBEBASE /\ g[1] >= srtt \div 8
         /\ \A k \in 2..9 : g[k] <= PROBECAP
         /\ \A k \in 2..9 : g[k - 1] <= PROBECAP => g[k - 1] <= g[k]
    /\ \A at \in {0, 3 * SEC, 10 * SEC}, now \in {0, 3 * SEC, 4 * SEC, 10 * SEC, 30 * SEC}, v \in Views :
         LET r == PDue(at, now, v) IN
         /\ (r.at = 0 \/ r.at > now)
         /\ (r.res = "punch" => at # 0 /\ at <= now)
         /\ (r.res = "punch" /\ v.direct /\ v.rtt # 0 /\ v.rtt <= GOOD => r.at = 0)
         /\ (at # 0 /\ at <= now /\ v.idle >= ACTIVEKEEP /\ ~(now < v.quiet /\ v.direct) => r = [res |-> "wait", at |-> now + UPGRADE])
         /\ ((at = 0 \/ now < at) => r = [res |-> "wait", at |-> at])

Sessions == {[has |-> FALSE, pto |-> 0, hs |-> FALSE, tries |-> 0, thin |-> FALSE]}
            \cup {[has |-> TRUE, pto |-> p, hs |-> h, tries |-> t, thin |-> th] : p \in 0..2, h \in BOOLEAN, t \in 0..2, th \in BOOLEAN}
TunnelOK ==
    /\ \A o \in BOOLEAN, silent \in {0, TSTALE, TSTALE + 1}, s \in Sessions :
         /\ Decide(o, silent, s, FALSE) = "carrier"
         /\ (~o => Decide(o, silent, s, TRUE) = "tunnel")
         /\ (o /\ silent > TSTALE => Decide(o, silent, s, TRUE) = "both")
         /\ (o /\ silent <= TSTALE /\ ~s.has => Decide(o, silent, s, TRUE) = "carrier")
    /\ \A th \in BOOLEAN, es \in BOOLEAN, age \in {-1, 0, SPLICESPAN - 1, SPLICESPAN, 5 * SEC}, rtt \in {0, 3 * SEC}, fr \in BOOLEAN, tk \in BOOLEAN, pto \in 0..3 :
         LET t == [thin |-> th, est |-> es, age |-> age, rtt |-> rtt, fresh |-> fr, took |-> tk, pto |-> pto] IN
         ThinSplice(t) => (th /\ es /\ tk /\ ~fr /\ pto < 2 /\ age >= 0 /\ age < Max(SPLICESPAN, rtt * 2))
    /\ \A valid \in BOOLEAN, heard \in {0, 5 * SEC}, now \in {0, 10 * SEC, 25 * SEC, 26 * SEC} :
         HubOk(valid, heard, now) = (valid /\ SatSub(now, heard) < HUBFRESH)

CandSets == {<<>>} \cup {<<c>> : c \in {<<"u", 1>>, <<"r", 0>>, <<"r", 1>>}}
            \cup {<<a, b>> : a \in {<<"u", 1>>, <<"r", 0>>}, b \in {<<"u", 2>>, <<"r", 1>>}}
            \cup {<<<<"u", 1>>, <<"r", 0>>, <<"r", 1>>>>}
ViewSets == {<<[some |-> a, live |-> l, gen |-> g], [some |-> TRUE, live |-> TRUE, gen |-> 0]>> : a \in BOOLEAN, l \in BOOLEAN, g \in 0..1}
SelectOK ==
    \A cs \in CandSets, views \in ViewSets, dialer \in BOOLEAN, tries \in 0..2, rtt \in {0, TGSLOW, 5 * SEC}, nr \in BOOLEAN, hs0 \in BOOLEAN,
       hl \in BOOLEAN, cap \in 1..3 :
       LET t == [now |-> 10 * SEC, dialer |-> dialer, tries |-> tries, rtt |-> rtt, nortt |-> nr, hs0 |-> hs0, haslast |-> hl, last |-> <<0, 0, 9 * SEC>>]
           r == Select(cs, t, views, cap) IN
       /\ Subseq(r.out, cs) /\ Len(r.out) <= cap
       /\ (dialer /\ Len(KeepAll(t, views, cs)) > 1 /\ (rtt >= TGSLOW \/ (tries >= 2 /\ nr)) => Len(r.out) <= 1)
       /\ (~dialer => r.out = SubSeq(cs, 1, Min(Len(cs), cap)))
       /\ (r.carried # <<>> => \E k \in 1..Len(r.out) : r.out[k] = <<"r", r.carried[1]>>)

Addr1 == <<<<10, 0, 0, 1>>, 1>>
Addr2 == <<<<10, 0, 0, 2>>, 1>>
Shared1 == <<<<100, 64, 0, 1>>, 1>>
Shared2 == <<<<100, 128, 0, 1>>, 1>>
ClassifyOK ==
    /\ \A refl \in {<<>>, <<Addr1>>, <<Shared1>>, <<Shared2>>, <<Addr1, Addr2>>, <<Shared2, Shared2>>},
          local \in {<<>>, <<Addr1>>}, mapped \in {<<>>, <<Addr2>>}, heard \in BOOLEAN, since \in {0, 5 * SEC}, wd \in {5 * SEC} :
         LET c == Classify(local, refl, mapped, heard, since, wd) IN
         /\ (c = 5 => ~heard /\ refl = <<>> /\ since >= wd)
         /\ (refl = <<>> => c \in {0, 5})
         /\ ((refl # <<>> /\ \E i \in 1..Len(refl) : refl[i] \in {local[j] : j \in 1..Len(local)}) => c = 1)
         /\ (refl # <<>> => c \in 1..4)
    /\ IsShared(<<100, 64, 0, 1>>) /\ IsShared(<<100, 127, 255, 1>>) /\ ~IsShared(<<100, 128, 0, 1>>) /\ ~IsShared(<<100, 63, 0, 1>>)
    /\ ~IsShared(<<10, 0, 0, 1>>)

(* ---- state machines ---- *)
Init == /\ P = NewPending(2, 2) /\ LK = NewLookups(2) /\ NC = NewNet(2)

DoPending ==
    \/ \E pe \in Peers, s \in Sess : LET r == PAdd(P, pe, s) IN P' = r.P
    \/ \E pe \in Peers : P' = PTake(P, pe).P
    \/ \E k \in 0..1 : P' = [P EXCEPT !.items = PruneAll(P.items, 1, k, <<>>).items]

DoLookups ==
    \/ \E pe \in Peers, now \in Times, u \in BOOLEAN, c \in BOOLEAN, th \in {0, 500000} : LK' = LAsk(LK, now, pe, u, c, th).T
    \/ \E pe \in Peers : LK' = LAnswered(LK, pe)
    \/ \E pe \in Peers : LK' = LTooLarge(LK, pe)
    \/ LK' = LClear(LK)

DoNet ==
    \/ \E now \in Times, rl \in 0..1, nc \in 1..1, w \in BOOLEAN : NC' = NProbeSent(NC, now, rl, <<nc>>, w) 
    \/ \E now \in Times, rl \in 0..1, nc \in 1..1, a \in 1..2 : NC' = NAnswered(NC, now, rl, <<nc>>, a).N 
    \/ \E rl \in 0..1 : NC' = NFailed(NC, rl)
    \/ \E rl \in 0..1 : NC' = NHealthy(NC, rl)
    \/ \E us \in {<<TRUE, TRUE>>, <<TRUE, FALSE>>, <<FALSE, TRUE>>}, op \in BOOLEAN \X BOOLEAN : NC' = NFailover(NC, us, op).N
    \/ NC' = NRestart(NC)
    \/ \E fr \in -1..1 : NC' = NMissing(NC, fr).N

Next == \/ (Mode = "pending" /\ DoPending /\ UNCHANGED <<LK, NC>>)
        \/ (Mode = "lookups" /\ DoLookups /\ UNCHANGED <<P, NC>>)
        \/ (Mode = "net" /\ DoNet /\ UNCHANGED <<P, LK>>)
        \/ (Mode = "pure" /\ UNCHANGED vars)
Spec == Init /\ [][Next]_vars

PendingOK ==
    /\ Len(P.items) = 2 /\ \A i \in 1..2 : Len(P.items[i].ws) = 2
    /\ \A i, j \in 1..2 : (i # j /\ P.items[i].e /\ P.items[j].e) => P.items[i].peer # P.items[j].peer

LookupsOK ==
    /\ Len(LK.items) = 2
    /\ \A i, j \in 1..2 : (i # j /\ LK.items[i].e /\ LK.items[j].e) => LK.items[i].peer # LK.items[j].peer
    /\ \A pe \in Peers, now \in Times :
         LET a == LAsk(LK, now, pe, TRUE, TRUE, 0) IN
         (\E i \in 1..2 : LK.items[i].e /\ LK.items[i].peer = pe /\ ~LK.items[i].again /\ now < LK.items[i].at + LK.items[i].wait) => a.res = "skip"
    /\ \A now \in Times : \A pe \in {LDue(LK, now)[k] : k \in 1..Len(LDue(LK, now))} :
         \E i \in 1..2 : LK.items[i].e /\ LK.items[i].peer = pe /\ now > LK.items[i].at + LK.items[i].wait
    /\ \A now \in Times : (LNext(LK) >= 0 /\ LNext(LK) <= now) => LDue(LK, now) # <<>>

\* the answers the net configs can take in a state: every relay, address and time, the one nonce
Answers == {NAnswered(NC, now, rl, <<1>>, a) : now \in Times, rl \in 0..1, a \in 1..2}

NetOK ==
    /\ NC.home \in -1..1
    /\ \A i \in 0..1 : Unhealthy(NC, i) = (NC.missed[i + 1] >= MISSLIMIT)
    /\ \A us \in {<<TRUE, TRUE>>, <<TRUE, FALSE>>}, op \in BOOLEAN \X BOOLEAN :
         LET f == NFailover(NC, us, op) IN
         f.res >= 0 => (f.res # NC.home /\ ~Unhealthy(NC, f.res) /\ us[f.res + 1] /\ f.N.home = f.res
                        /\ ((NC.missed[f.res + 1] = 0 /\ NC.refl[f.res + 1] >= 0) \/ op[f.res + 1]))
    \* the relays that answered hold the places 1..k of the order of first answers, each once
    /\ LET A == {i \in 1..2 : NC.order[i] > 0} IN {NC.order[i] : i \in A} = 1..Cardinality(A)
    \* after an answer the home is the relay with the lowest last round trip among those that ever answered and are not
    \* unhealthy, a tie to the one that answered first
    /\ \A r \in Answers : r.res >= 0 =>
         LET h == r.N.home IN
         /\ h \in Answered(r.N)
         /\ \A i \in Answered(r.N) : \/ r.N.rtt[h + 1] < r.N.rtt[i + 1]
                                     \/ r.N.rtt[h + 1] = r.N.rtt[i + 1] /\ r.N.order[h + 1] <= r.N.order[i + 1]
    \* a link change forgets the round's answers and keeps the home, the order and the rounds without a home
    /\ LET s == NRestart(NC) IN
       /\ s.home = NC.home /\ s.order = NC.order /\ s.tries = NC.tries /\ s.rtt = NC.rtt /\ s.missed = NC.missed
       /\ \A i \in 1..2 : s.refl[i] = -1 /\ ~s.probes[i].e
    \* a round without a home is counted; at the third the relay given is the home
    /\ \A fr \in 0..1 :
         LET m == NMissing(NC, fr) IN
         /\ NC.home >= 0 => m.res = "done" /\ m.N = NC
         /\ (NC.home < 0 /\ NC.tries + 1 >= HOMETRIES) => m.N.home = fr
         /\ (NC.home < 0 /\ NC.tries + 1 < HOMETRIES) => m.N.home = -1 /\ m.N.tries = NC.tries + 1

\* the old rule: an answer moves the home only to a strictly lower round trip, or away from an unhealthy home
HomeOnlyLower ==
    \A r \in Answers : (r.res >= 0 /\ r.N.home # NC.home) =>
        (NC.home < 0 \/ Unhealthy(r.N, NC.home) \/ r.N.rtt[r.N.home + 1] < r.N.rtt[NC.home + 1])

\* the miss and try counters saturate at 255 in the code; one past the threshold covers every branch
Bounded == (\A i \in 1..2 : NC.missed[i] <= MISSLIMIT + 1) /\ NC.tries <= HOMETRIES + 1
=============================================================================
