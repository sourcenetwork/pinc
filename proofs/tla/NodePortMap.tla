------------------------------ MODULE NodePortMap ------------------------------
(***************************************************************************)
(* The node's port-mapping client (pinc-node portmap.rs: Pm,               *)
(* start_port_mapping, pm_seed, stop_port_mapping, pm_restart,             *)
(* pm_datagram, pm_timeout, pm_poll_udp, handle_http, pm_apply,            *)
(* port_mapping_done, Pm::sending and Pm::reap).                           *)
(*                                                                         *)
(* pm is the node's Pm (on = FALSE is None): cur the client (0 = none      *)
(* until a nonce is drawn), ret the R retiring slots (0 = empty), ovf the  *)
(* releases replaced, halted, retry the time of the next draw, nf the      *)
(* failed draws, given the address the connectivity client was last given. *)
(* ph is each client's phase, decided by pinc-portmap (its own models):   *)
(* "run" asking, "map" holding a mapping, "rel" stopped with its release  *)
(* unsent, "wait" its release sent and not answered, "done" stopped,     *)
(* "lost" replaced in a full queue. A client's address is its id; conn is *)
(* the address the connectivity client holds (0 = none). The HTTP carrier *)
(* (UPnP) is folded into the answers; the protocol bytes are not modelled. *)
(*                                                                         *)
(* Checked, from the module documentation and the comments:                *)
(*  Inv: ConnHolds (the connectivity client holds exactly the address the  *)
(*   client holds), Kept (a client with a release unsent or unanswered is  *)
(*   the client or in the queue), Slots (the queue holds distinct clients);*)
(*  StepProps: NoPmNothing (with port mapping never turned on nothing is   *)
(*   sent and no timer is armed), ReleaseFirst (the new client sends       *)
(*   nothing while a retiring client's release is unsent), HaltedStays (a *)
(*   stop before any nonce starts nothing later), Counted (each release    *)
(*   replaced is counted once), RetrySat (a failed draw is tried again     *)
(*   NR later, saturating at the clock's maximum TMAX).                    *)
(* Findings: ReplacesOldest (the documentation: a full queue "replaces the *)
(* oldest release"; the code replaces slot 1, which a reap and a later     *)
(* start can refill with the newest), config NodePortMap_woldest.          *)
(* Witnesses: NeverOverflow, NeverSaturated.                               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS R, NIDS, TMAX, NR
VARIABLES pm, ph, conn, now, ids, sent, wrongv, sat
vars == <<pm, ph, conn, now, ids, sent, wrongv, sat>>

Ids == 1..NIDS
Off == [on |-> FALSE, cur |-> 0, ret |-> [k \in 1..R |-> 0], ovf |-> 0, halted |-> FALSE, retry |-> 0, nf |-> 0,
        given |-> 0]
Min2(a, b) == IF a < b THEN a ELSE b
RetIds(p) == {p.ret[k] : k \in 1..R} \ {0}
Held(p, h) == IF p.cur # 0 /\ h[p.cur] = "map" THEN p.cur ELSE 0
\* pm_apply: the connectivity client is given what the client holds, if it changed
Apply(p, h) == IF ~p.on THEN [p |-> p, conn |-> conn] ELSE [p |-> [p EXCEPT !.given = Held(p, h)], conn |-> Held(p, h)]
\* PortMap::stop of a client in phase x: a held mapping is released; one still asking may have nothing to release
StopTo(x) == CASE x = "map" -> {"rel"} [] x = "run" -> {"rel", "done"} [] OTHER -> {x}
Stopped(x) == x \in {"done", "lost"}
\* Pm::reap: a retiring client whose release is done leaves its slot
Reap(p, h) == [p EXCEPT !.ret = [k \in 1..R |-> IF p.ret[k] # 0 /\ Stopped(h[p.ret[k]]) THEN 0 ELSE p.ret[k]]]
\* pm_seed: draw a nonce; a client starts, or the failure is counted and the draw is due NR later
Seed(p, h, t, ok) ==
    IF ~p.on \/ p.cur # 0 \/ p.halted THEN [p |-> p, h |-> h, ids |-> ids]
    ELSE IF ok /\ ids < NIDS
         THEN [p |-> [p EXCEPT !.cur = ids + 1], h |-> [h EXCEPT ![ids + 1] = "run"], ids |-> ids + 1]
         ELSE [p |-> [p EXCEPT !.nf = @ + 1, !.retry = Min2(t + NR, TMAX)], h |-> h, ids |-> ids]

Init == pm = Off /\ ph = [c \in Ids |-> "none"] /\ conn = 0 /\ now = 0 /\ ids = 0 /\ sent = 0 /\ wrongv = FALSE
        /\ sat = FALSE

\* start_port_mapping: the old client is stopped; unless that ends it, it takes the first empty slot, or slot 1 of a
\* full queue, whose client is replaced unsent and counted; then a new Pm, the draw, and pm_apply
Start(ok) ==
    \E x \in IF pm.cur # 0 THEN StopTo(ph[pm.cur]) ELSE {"none"} :
      LET c == pm.cur
          h1 == IF c # 0 THEN [ph EXCEPT ![c] = x] ELSE ph
          keep == c # 0 /\ ~Stopped(x)
          free == {k \in 1..R : pm.ret[k] = 0}
          slot == IF free # {} THEN CHOOSE k \in free : \A j \in free : k <= j ELSE 1
          full == keep /\ free = {}
          victim == pm.ret[1]
          h2 == IF full THEN [h1 EXCEPT ![victim] = "lost"] ELSE h1
          q == [on |-> TRUE, cur |-> 0, ret |-> IF keep THEN [pm.ret EXCEPT ![slot] = c] ELSE pm.ret,
                ovf |-> IF full THEN pm.ovf + 1 ELSE pm.ovf, halted |-> FALSE, retry |-> now, nf |-> 0,
                given |-> pm.given]
          s == Seed(q, h2, now, ok)
          a == Apply(s.p, s.h)
      IN /\ pm' = a.p /\ ph' = s.h /\ conn' = a.conn /\ ids' = s.ids
         /\ wrongv' = (wrongv \/ (full /\ \E k \in 1..R : pm.ret[k] < victim))
         /\ sat' = (sat \/ (~ok /\ now = TMAX))
         /\ UNCHANGED now /\ sent' = 0
\* stop_port_mapping: the client is stopped; a Pm that never drew its nonce halts, and goes when nothing retires
Stop ==
    /\ pm.on
    /\ IF pm.cur # 0
       THEN \E x \in StopTo(ph[pm.cur]) : LET h == [ph EXCEPT ![pm.cur] = x] a == Apply(pm, h)
                                         IN pm' = a.p /\ ph' = h /\ conn' = a.conn
       ELSE LET p == IF RetIds(pm) = {} THEN Off ELSE [pm EXCEPT !.halted = TRUE] a == Apply(p, ph)
            IN pm' = a.p /\ conn' = a.conn /\ UNCHANGED ph
    /\ sent' = 0 /\ UNCHANGED <<now, ids, wrongv, sat>>
\* pm_restart (the network changed): the client drops its mapping and asks again
Restart ==
    /\ pm.on /\ pm.cur # 0 /\ ph[pm.cur] = "map"
    /\ LET h == [ph EXCEPT ![pm.cur] = "run"] a == Apply(pm, h) IN pm' = a.p /\ ph' = h /\ conn' = a.conn
    /\ sent' = 0 /\ UNCHANGED <<now, ids, wrongv, sat>>
\* pm_datagram or handle_http: an answer for client c (the client first, then the queue); a grant, a lost mapping,
\* or the answer to a release; handle_http also reaps
Answer(c, y, http) ==
    /\ pm.on /\ c # 0 /\ (c = pm.cur \/ c \in RetIds(pm))
    /\ \/ c = pm.cur /\ ph[c] = "run" /\ y = "map"
       \/ c = pm.cur /\ ph[c] = "map" /\ y = "run"
       \/ ph[c] = "wait" /\ y = "done"
    /\ LET h == [ph EXCEPT ![c] = y] p == IF http THEN Reap(pm, h) ELSE pm a == Apply(p, h)
       IN pm' = a.p /\ ph' = h /\ conn' = a.conn
    /\ sent' = 0 /\ UNCHANGED <<now, ids, wrongv, sat>>
\* pm_poll_udp: the retiring clients first, in slot order, then the client; then reap. A client that has nothing to
\* send (one asking may wait for its timer) is the environment's choice (sends = FALSE).
PollUdp(sends) ==
    /\ IF ~pm.on THEN sent' = 0 /\ UNCHANGED <<pm, ph>>
       ELSE LET rel == {k \in 1..R : pm.ret[k] # 0 /\ ph[pm.ret[k]] = "rel"}
            IN IF rel # {}
               THEN LET k == CHOOSE k \in rel : \A j \in rel : k <= j
                        h == [ph EXCEPT ![pm.ret[k]] = "wait"]
                    IN sent' = pm.ret[k] /\ ph' = h /\ pm' = Reap(pm, h)
               ELSE IF pm.cur # 0 /\ sends /\ ph[pm.cur] \in {"run", "rel"}
               THEN LET h == IF ph[pm.cur] = "rel" THEN [ph EXCEPT ![pm.cur] = "wait"] ELSE ph
                    IN sent' = pm.cur /\ ph' = h /\ pm' = Reap(pm, h)
               ELSE sent' = 0 /\ ph' = ph /\ pm' = Reap(pm, ph)
    /\ UNCHANGED <<conn, now, ids, wrongv, sat>>
\* handle_timeout at t: the draw if due, then each sending client's timer (a release given up on is done, a lease
\* that ran out is dropped), reap,
\* and pm_apply after each
Timeout(t, ok, gu) ==
    /\ t \in now..TMAX
    /\ LET s == IF pm.on /\ pm.cur = 0 /\ pm.retry <= t THEN Seed(pm, ph, t, ok) ELSE [p |-> pm, h |-> ph, ids |-> ids]
           a1 == Apply(s.p, s.h)
           mine == gu # 0 /\ s.p.on /\ (gu = s.p.cur \/ gu \in RetIds(s.p))
           h == CASE mine /\ s.h[gu] = "wait" -> [s.h EXCEPT ![gu] = "done"]
                  [] mine /\ gu = s.p.cur /\ s.h[gu] = "map" -> [s.h EXCEPT ![gu] = "run"]
                  [] OTHER -> s.h
           p == IF a1.p.on THEN Reap(a1.p, h) ELSE a1.p
           a2 == Apply(p, h)
       IN /\ pm' = a2.p /\ ph' = h /\ conn' = a2.conn /\ ids' = s.ids
          /\ sat' = (sat \/ (pm.on /\ pm.cur = 0 /\ ~pm.halted /\ pm.retry <= t /\ ~ok /\ t = TMAX))
    /\ now' = t /\ sent' = 0 /\ UNCHANGED wrongv

Next == \/ \E ok \in BOOLEAN : Start(ok) /\ ids < NIDS
        \/ Stop \/ Restart
        \/ \E c \in Ids, y \in {"map", "run", "done"}, http \in BOOLEAN : Answer(c, y, http)
        \/ \E b \in BOOLEAN : PollUdp(b)
        \/ \E t \in 0..TMAX, ok \in BOOLEAN, gu \in 0..NIDS : Timeout(t, ok, gu)
Spec == Init /\ [][Next]_vars
Bound == pm.nf <= 2

ConnHolds == /\ pm.on => conn = Held(pm, ph) /\ pm.given = conn
             /\ ~pm.on => conn = 0
Kept == \A c \in Ids : ph[c] \in {"rel", "wait"} => c = pm.cur \/ c \in RetIds(pm)
Slots == \A j, k \in 1..R : j # k /\ pm.ret[j] # 0 => pm.ret[j] # pm.ret[k]
Inv == ConnHolds /\ Kept /\ Slots /\ (pm.cur # 0 => pm.cur \notin RetIds(pm))

NoPmNothing == [][~pm.on /\ ~pm'.on => sent' = 0]_vars
ReleaseFirst == [][sent' # 0 /\ sent' = pm.cur => \A k \in 1..R : pm.ret[k] = 0 \/ ph[pm.ret[k]] # "rel"]_vars
HaltedStays == [][pm.halted /\ pm'.on /\ pm'.halted => pm'.cur = 0]_vars
Counted == [][pm'.on => pm'.ovf = (IF pm.on THEN pm.ovf ELSE 0)
                                   + Cardinality({c \in Ids : ph'[c] = "lost" /\ ph[c] # "lost"})]_vars
RetrySat == [][pm'.on /\ pm'.cur = 0 /\ pm'.nf > pm.nf /\ pm.on => pm'.retry = Min2(now' + NR, TMAX)]_vars
StepProps == NoPmNothing /\ ReleaseFirst /\ HaltedStays /\ Counted /\ RetrySat

ReplacesOldest == ~wrongv
NeverOverflow == pm.ovf = 0
NeverSaturated == ~sat
=============================================================================
