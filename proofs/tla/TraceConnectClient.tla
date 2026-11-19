---------------------------- MODULE TraceConnectClient ----------------------------
(***************************************************************************)
(* Trace validation of the client rules of connectivity: pinc-connect      *)
(* client/{punch,tunnel,dial,lookup,netcheck}.rs.                          *)
(*                                                                         *)
(* The Rust test tests/trace_connect_client.rs drives the real punch       *)
(* timer, tunnel rules and splice tables, first-flight selection, pending  *)
(* dials, lookup table, answer verification, classification and probe     *)
(* state with seeded random calls and records each call with its answer    *)
(* and the state read back through the public accessors. Every event must  *)
(* be the step the operators of ConnectClientOps.tla compute (and, for     *)
(* verify, ConnectCodecOps.tla for the record). Times are microseconds.   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds connect_client.ndjson.*)
(***************************************************************************)
EXTENDS ConnectClientOps, ConnectCodecOps, Json, IOUtils

VARIABLES i, P, T, PE, LK, NC
vars == <<i, P, T, PE, LK, NC>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/connect_client.ndjson")
Ev == Trace[i]

Init == /\ i = 1 /\ P = 0 /\ T = NewSplices(3, 2) /\ PE = NewPending(3, 2) /\ LK = NewLookups(3) /\ NC = NewNet(3)

Num(bs) == LET RECURSIVE F(_) F(b) == IF b = <<>> THEN 0 ELSE F(SubSeq(b, 1, Len(b) - 1)) * 256 + b[Len(b)] IN F(bs)
Step == i' = i + 1

Keep(a, b, c, d, e) == TRUE

PuncherE ==
    CASE Ev.c = "est" -> /\ P' = Ev.now + FIRSTDELAY /\ PObs(P') = Ev.at /\ Ev.res = "none"
      [] Ev.c = "arm" -> /\ P' = Ev.arg /\ PObs(P') = Ev.at /\ Ev.res = "none"
      [] Ev.c = "due" -> LET r == PDue(P, Ev.now, Ev.view) IN /\ r.res = Ev.res /\ P' = r.at /\ PObs(r.at) = Ev.at

SpliceView == /\ Ev.ages = [k \in 1..10 |-> Age(T, Ev.now, (k - 1) % 2, ((k - 1) \div 2) + 1)]
              /\ Ev.lives = [r \in 1..2 |-> LiveAt(T, Ev.now, r - 1, Ev.rtt)]

PendView(Q) == /\ PPeers(Q) = Ev.peers /\ Ev.has = [k \in 1..5 |-> PHas(Q, k)]
LookView(Q) == /\ LLen(Q) = Ev.len /\ LDue(Q, Ev.now) = Ev.due /\ LNext(Q) = Ev.next /\ Ev.has = [k \in 1..5 |-> LHas(Q, k)]
NetView(Q) == /\ Ev.home = Q.home /\ Ev.rtts = [k \in 1..3 |-> NRtt(Q, k - 1)] /\ Ev.refl = Q.refl
              /\ Ev.unh = [k \in 1..3 |-> Unhealthy(Q, k - 1)] /\ Ev.best = NBest(Q) /\ Ev.first = Q.fp

\* the bytes of an address of a record as <<ip, port>>
AddrOf(a) == <<SubSeq(a, 2, Len(a) - 2), a[Len(a) - 1] * 256 + a[Len(a)]>>

VerifyOK ==
    IF Ev.k = "abs" THEN Ev.res = "none"
    ELSE IF Ev.k = "big" THEN Ev.res = "toolarge"
    ELSE LET r == RecParse(Ev.b) IN
         IF ~r.ok THEN Ev.res = "rec:" \o r.e
         ELSE IF ~Ev.sig THEN Ev.res = "rec:sig"
         ELSE IF r.v.node # Ev.peer THEN Ev.res = "wrongnode"
         ELSE /\ Ev.res.found.home = r.v.home /\ Ev.res.found.reach = r.v.reach /\ Ev.res.found.seq = Num(r.v.seq)
              /\ Ev.res.found.addrs = [k \in 1..Len(r.v.addrs) |-> AddrOf(r.v.addrs[k])]

Ev1 ==
    CASE Ev.m = "gaps" -> /\ ProbeGaps(Ev.srtt) = Ev.out /\ Step /\ UNCHANGED <<P, T, PE, LK, NC>>
      [] Ev.m = "pnew" -> /\ P' = 0 /\ Step /\ UNCHANGED <<T, PE, LK, NC>>
      [] Ev.m = "puncher" -> /\ PuncherE /\ Step /\ UNCHANGED <<T, PE, LK, NC>>
      [] Ev.m = "decide" -> /\ Decide(Ev.open, Ev.silent, Ev.session, Ev.tunnel) = Ev.res /\ Step /\ UNCHANGED <<P, T, PE, LK, NC>>
      [] Ev.m = "thin" -> /\ ThinSplice([thin |-> Ev.thin, est |-> Ev.est, age |-> Ev.age, rtt |-> Ev.rtt, fresh |-> Ev.fresh,
                                         took |-> Ev.took, pto |-> Ev.pto]) = Ev.res /\ Step /\ UNCHANGED <<P, T, PE, LK, NC>>
      [] Ev.m = "hubok" -> /\ HubOk(Ev.valid, Ev.heard, Ev.now) = Ev.res /\ Step /\ UNCHANGED <<P, T, PE, LK, NC>>
      [] Ev.m = "snew" -> /\ T' = NewSplices(Ev.p, Ev.r) /\ Step /\ UNCHANGED <<P, PE, LK, NC>>
      [] Ev.m = "seen" -> /\ T' = Seen(T, Ev.now, Ev.relay, Ev.peer, Ev.from) /\ Step /\ UNCHANGED <<P, PE, LK, NC>>
      [] Ev.m = "sview" -> /\ SpliceView /\ Step /\ UNCHANGED <<P, T, PE, LK, NC>>
      [] Ev.m = "direct" -> /\ DirectFirst(Ev.first, Ev.hub, Ev.fd, Ev.started) = Ev.res /\ Step /\ UNCHANGED <<P, T, PE, LK, NC>>
      [] Ev.m = "select" ->
           LET r == Select(Ev.cands, [now |-> Ev.try.now, dialer |-> Ev.try.dialer, tries |-> Ev.try.tries, rtt |-> Ev.try.rtt,
                                      nortt |-> Ev.try.nortt, hs0 |-> Ev.try.hs0, haslast |-> Ev.try.haslast, last |-> Ev.try.last],
                           Ev.views, Ev.cap) IN
           /\ r.out = Ev.out /\ r.carried = Ev.carried /\ Step /\ UNCHANGED <<P, T, PE, LK, NC>>
      [] Ev.m = "pnew3" -> /\ PE' = NewPending(Ev.n, Ev.h) /\ Step /\ UNCHANGED <<P, T, LK, NC>>
      [] Ev.m = "padd" -> LET r == PAdd(PE, Ev.peer, Ev.s) IN /\ r.ok = Ev.res /\ PendView(r.P) /\ PE' = r.P /\ Step /\ UNCHANGED <<P, T, LK, NC>>
      [] Ev.m = "ptake" -> LET r == PTake(PE, Ev.peer) IN /\ r.res = Ev.res /\ PendView(r.P) /\ PE' = r.P /\ Step /\ UNCHANGED <<P, T, LK, NC>>
      [] Ev.m = "pprune" -> LET r == PruneAll(PE.items, 1, Ev.keep, <<>>) IN
                            /\ r.dropped = Ev.res /\ PendView([PE EXCEPT !.items = r.items]) /\ PE' = [PE EXCEPT !.items = r.items]
                            /\ Step /\ UNCHANGED <<P, T, LK, NC>>
      [] Ev.m = "lnew" -> /\ LK' = NewLookups(Ev.n) /\ Step /\ UNCHANGED <<P, T, PE, NC>>
      [] Ev.m = "ask" -> LET r == LAsk(LK, Ev.now, Ev.peer, Ev.udp, Ev.car, Ev.thin) IN
                         /\ r.res = Ev.res /\ LookView(r.T) /\ LK' = r.T /\ Step /\ UNCHANGED <<P, T, PE, NC>>
      [] Ev.m = "answered" /\ "relay" \notin DOMAIN Ev ->
           /\ LookView(LAnswered(LK, Ev.peer)) /\ LK' = LAnswered(LK, Ev.peer) /\ Step /\ UNCHANGED <<P, T, PE, NC>>
      [] Ev.m = "toolarge" -> /\ LookView(LTooLarge(LK, Ev.peer)) /\ LK' = LTooLarge(LK, Ev.peer) /\ Step /\ UNCHANGED <<P, T, PE, NC>>
      [] Ev.m = "lclear" -> /\ LookView(LClear(LK)) /\ LK' = LClear(LK) /\ Step /\ UNCHANGED <<P, T, PE, NC>>
      [] Ev.m = "lview" -> /\ LookView(LK) /\ Step /\ UNCHANGED <<P, T, PE, LK, NC>>
      [] Ev.m = "verify" -> /\ VerifyOK /\ Step /\ UNCHANGED <<P, T, PE, LK, NC>>
      [] Ev.m = "classify" -> /\ Classify(Ev.local, Ev.refl, Ev.mapped, Ev.heard, Ev.since, Ev.wd) = Ev.res /\ Step /\ UNCHANGED <<P, T, PE, LK, NC>>
      [] Ev.m = "nnew" -> /\ NC' = NPin(NewNet(Ev.r), Ev.pin) /\ Step /\ UNCHANGED <<P, T, PE, LK>>
      [] Ev.m = "psent" -> LET n == NProbeSent(NC, Ev.now, Ev.relay, Ev.nonce, Ev.works) IN
                           /\ NetView(n) /\ NC' = n /\ Step /\ UNCHANGED <<P, T, PE, LK>>
      [] Ev.m = "answered" -> LET r == NAnswered(NC, Ev.now, Ev.relay, Ev.nonce, Ev.addr) IN
                              /\ r.res = Ev.res /\ NetView(r.N) /\ NC' = r.N /\ Step /\ UNCHANGED <<P, T, PE, LK>>
      [] Ev.m = "failed" -> /\ NetView(NFailed(NC, Ev.relay)) /\ NC' = NFailed(NC, Ev.relay) /\ Step /\ UNCHANGED <<P, T, PE, LK>>
      [] Ev.m = "healthy" -> /\ NetView(NHealthy(NC, Ev.relay)) /\ NC' = NHealthy(NC, Ev.relay) /\ Step /\ UNCHANGED <<P, T, PE, LK>>
      [] Ev.m = "failover" -> LET r == NFailover(NC, Ev.usable, Ev.open) IN
                              /\ r.res = Ev.res /\ NetView(r.N) /\ NC' = r.N /\ Step /\ UNCHANGED <<P, T, PE, LK>>
      [] Ev.m = "restart" -> /\ NetView(NRestart(NC)) /\ NC' = NRestart(NC) /\ Step /\ UNCHANGED <<P, T, PE, LK>>
      [] Ev.m = "missing" -> LET r == NMissing(NC, Ev.fr) IN
                             /\ r.res = Ev.res /\ NetView(r.N) /\ NC' = r.N /\ Step /\ UNCHANGED <<P, T, PE, LK>>

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ Ev.t = "cl" /\ Ev1) \/ Done

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

\* the whole recorded trace is a behaviour of ConnectClientOps.tla
TraceAccepted == <>(i = Len(Trace) + 1)
Inv == TRUE
=============================================================================
