--------------------------- MODULE ConnectRelay ---------------------------
(***************************************************************************)
(* Model check of the relay (ConnectRelayOps.tla): every call, with every  *)
(* argument of a small universe, in every order, at the instants of the    *)
(* finite set Times, which holds values around the rule constants (10, 15, *)
(* 20, 30 s). Nodes 1 and 2 open carriers; 3 never does (it is only        *)
(* forwarded); 5 and 6 are peer relays that may be added and removed; 9 is *)
(* this relay.                                                             *)
(*                                                                         *)
(*  CallsOk        for every call: NoReforward (a packet that came from a  *)
(*                 peer relay produces no relay frame), FwdToPeers (every  *)
(*                 relay frame goes to an authenticated peer), TunnelOk    *)
(*                 (a tunnelled packet goes down a session heard less than *)
(*                 20 s ago and fits 1452 - 28 bytes), ReplyRoute (a reply *)
(*                 route is learnt only for the sender of the frame and    *)
(*                 for a node without a carrier here); a refused hand-over *)
(*                 of a held message (a member the host reports not ready) *)
(*                 ends the pass and the member still holds messages       *)
(*  QuotaOk        no node's window total exceeds the quota                *)
(*  SessionLimit   after a sweep, no session is older than the limit       *)
(*  SessionsBound  at most C sessions, one per node, and the mailbox keeps *)
(*                 its quota                                               *)
(*  Forwarded      a packet for a member that is not asleep here, has no  *)
(*                 carrier and no ready route here and is homed at        *)
(*                 another relay is forwarded to that relay, whatever     *)
(*                 this relay holds for it                                *)
(*  HeardDelivers  an accepted heard packet leaves a member whose route    *)
(*                 is ready holding no message that fits the route        *)
(*  StepsOver      the same pass leaves exactly the messages that do not   *)
(*                 fit, in their order: a message too long for the        *)
(*                 tunnel does not stop the ones behind it                *)
(*  MailboxOk      each member's bytes and count are those of its queue,  *)
(*                 and every stored message is delivered, dropped,        *)
(*                 expired or held                                        *)
(* The witness configs put a rule back and each violates the property it  *)
(* names: OldHeld (nothing is released) ConnectRelay_wheard, HoldBehind   *)
(* (a packet for a member that holds messages is held behind them, the    *)
(* rule withdrawn) ConnectRelay_wfwd, StopFirst (the pass stops at the    *)
(* first message that does not fit) ConnectRelay_wstop. Seed is a peer    *)
(* relay present at the start that is also the home of node 2's record    *)
(* (0: none), Lens the lengths a peer relay may forward (a length over    *)
(* 1389 does not fit the tunnel) and MBytes the byte quota of a member's  *)
(* mailbox; ConnectRelay_fwd and ConnectRelay_long reach a member that    *)
(* holds mail and is homed elsewhere, and one that holds a long message.  *)
(*  SpuSilent      an uploaded packet from a member whose UDP stamp finds   *)
(*                 the table full is no refusal: nothing is traced        *)
(* FullUdp starts with the UDP table full of other nodes (ConnectRelay_full) *)
(* and LoudSpu puts the traced refusal back (ConnectRelay_wfull).          *)
(* Lean: Pinc/ConnectRelayThm.lean (peer_unauth, forward_peer, no_reforward,*)
(* back_window, charge_inv, tunnel_spec, spu_member, heard_idle,           *)
(* heard_unready_quiet, forwarded, sleep_spec, ...).                       *)
(***************************************************************************)
EXTENDS ConnectRelayOps

CONSTANTS Times, MaxNs, Depth, WithSleep, WithReady, OldHeld, HoldBehind, StopFirst, Seed, Lens, MBytes, FullUdp, LoudSpu
cf == [me |-> 9, C |-> 2, R |-> 2, MN |-> 1, MB |-> MBytes, Bytes |-> 3, Window |-> 3, SessT |-> 4, Age |-> 40,
       old |-> OldHeld, hb |-> HoldBehind, stop |-> StopFirst]
Cl == {1, 2}

\* the earlier SPU, for a witness only (LoudSpu): a full UDP table is traced as a refusal and the datagram goes on
SpuLoud(cf0, R0, now, m, dst, flag, len) ==
    IF len = 0 \/ 35 + len > MAXTUN THEN Fail(R0, "baddg", m)
    ELSE IF m = 0 THEN Fail(R0, "unauth", 0)
    ELSE LET uh == UdpHeard(cf0, R0, now, m) IN
         IF dst = cf0.me THEN After(uh.ef, Fail(uh.R, "noroute", m))
         ELSE After(uh.ef, Route(cf0, uh.R, now, m, dst, flag, len, "tunnel"))
Peers == {5, 6}
VARIABLES R, clock, last, steps, ref, fw, heard, step, quiet
vars == <<R, clock, last, steps, ref, fw, heard, step, quiet>>

SeedRelay == [NewRelay(cf) EXCEPT !.bk = [x \in {1, 2, 3, 5, 6, 9} |-> x % 2],
                  !.peers = [i \in 1..MAXPEERS |-> IF i = 1 THEN Seed ELSE 0],
                  !.udp = IF FullUdp THEN [x \in {3, 4} |-> 0] ELSE [x \in {} |-> 0],
                  !.rec = IF Seed = 0 THEN [x \in {} |-> 0] ELSE [x \in {2} |-> [seq |-> 1, home |-> Seed, rcv |-> 0]]]

Init == /\ R = SeedRelay
        /\ clock = 0 /\ steps = 0 /\ last = TRUE /\ ref = FALSE /\ fw = TRUE /\ heard = TRUE /\ step = TRUE /\ quiet = TRUE

IsFwd(e) == Len(e) >= 3 /\ e[1] = "peer" /\ e[3] = "fwd"
IsUdp(e) == Len(e) >= 3 /\ e[1] = "udp"
IsNoTunnel(e) == Len(e) >= 4 /\ e[1] = "t" /\ e[2] = "rej" /\ e[3] = "notunnel"
IsLearn(e) == Len(e) >= 4 /\ e[1] = "t" /\ e[2] = "fwdback"

\* the destination of a carrier frame (0 when it routes nothing)
FDst(nd, f) == IF f[1] = "send" THEN f[2]
               ELSE IF f[1] = "sendalias" /\ nd \in DOMAIN R.cd THEN Resolve(R.cd[nd].rx, f[2]) ELSE 0

\* the properties of one call, checked on its effects: the peers are those before the call, the UDP sessions and sessions
\* those after it
Checks(kind, o, from, tm) ==
    LET E == o.ef IN
    /\ kind = "peer" => \A k \in 1..Len(E) : ~ IsFwd(E[k])
    /\ \A k \in 1..Len(E) : IsFwd(E[k]) => \E i \in 1..MAXPEERS : R.peers[i] = E[k][2]
    /\ \A k \in 1..Len(E) : IsUdp(E[k]) =>
           E[k][2] \in DOMAIN o.R.udp /\ Sat(tm - o.R.udp[E[k][2]]) < FRESH /\ 35 + E[k][6] <= MAXTUN
    /\ \A k \in 1..Len(E) : IsLearn(E[k]) => E[k][4] = from /\ E[k][3] \notin DOMAIN o.R.cd
    \* a refused hand-over ends the pass and the member still holds messages
    /\ \A k \in 1..Len(E) : IsNoTunnel(E[k]) => k = Len(E) /\ E[k][4] \in DOMAIN o.R.mb.held

\* the answers of a call that never reached the routing of a packet
Unrouted == {"stale", "quota", "unauth", "baddg", "unkalias"}

\* Forwarded on one call, dst the destination it routes (R is the state before the call, tm its time): a packet from a
\* carrier or a UDP session for a node that is not asleep, has no carrier and no ready route here and has a home relay
\* that is a peer is forwarded to it, whatever the node's mailbox holds. A packet that came from a peer relay is
\* never forwarded again.
FwdOk(kind, o, dst, tm) ==
    (/\ kind \in {"frame", "spu"} /\ dst \notin {0, cf.me} /\ o.res \notin Unrouted
     /\ ~HasC(cf, R, dst) /\ dst \notin DOMAIN R.sl /\ ~(Fresh(R, tm, dst) /\ dst \notin R.nr)
     /\ HomeOf(cf, R, tm, dst) \notin {0, cf.me} /\ IsPeer(R, HomeOf(cf, R, tm, dst)))
    => \E k \in 1..Len(o.ef) : IsFwd(o.ef[k]) /\ o.ef[k][2] = HomeOf(cf, R, tm, dst)

\* the messages of q longer than fit, in their order
RECURSIVE Over(_, _)
Over(q, fit) == IF q = <<>> THEN <<>>
                ELSE IF Head(q).len > fit THEN <<Head(q)>> \o Over(Tail(q), fit) ELSE Over(Tail(q), fit)
\* the longest body the member's route takes: the carrier takes a whole packet, the tunnel what is left of its datagram
Fit(Rx, n) == IF HasC(cf, Rx, n) THEN MAXPKT ELSE MAXTUN - 35
Queue(Rx, n) == IF n \in DOMAIN Rx.mb.held THEN Rx.mb.held[n].q ELSE <<>>

\* HeardDelivers on one call: node is the member heard
HeardOk(kind, o, node) ==
    kind = "udp" /\ o.res = "ok" => (node \in o.R.nr \/ Over(Queue(o.R, node), Fit(o.R, node)) = Queue(o.R, node))

\* StepsOver on one call: a heard member whose route is ready keeps exactly the live messages that do not fit
StepsOk(kind, o, node, tm) ==
    kind = "udp" /\ o.res = "ok" /\ node \notin o.R.nr =>
        Queue(o.R, node) = Over(IF node \in DOMAIN R.mb.held THEN ExpireH(MC(cf), tm, R.mb.held[node]).h.q ELSE <<>>,
                               Fit(o.R, node))

\* SpuSilent on one call: an uploaded packet from a member whose UDP stamp does not fit the full table is no refusal
SpuQuiet(kind, o) == kind = "spu" => \A k \in 1..Len(o.ef) : o.ef[k] # RejE("full", 1)

Do(kind, o, from, dst) == /\ R' = o.R /\ last' = Checks(kind, o, from, clock') /\ steps' = steps + 1
                          /\ fw' = FwdOk(kind, o, dst, clock') /\ heard' = HeardOk(kind, o, dst)
                          /\ step' = StepsOk(kind, o, dst, clock')
                          /\ quiet' = SpuQuiet(kind, o)
                          /\ ref' = (ref \/ \E k \in 1..Len(o.ef) : IsNoTunnel(o.ef[k]))

Frames(nd, tm) == {<<"send", d, 0, 1>> : d \in {1, 2, 3}}
             \cup {<<"sendalias", 0, 0, 1>>}
             \cup (IF WithSleep THEN {<<"sleep", nd, tm * 1000, 1, 1>>} ELSE {})

Next == \/ \E t \in Times : t >= clock /\ clock' = t /\
            ( (\E n \in Cl : R.ns < MaxNs /\ Do("open", CarrierOpened(cf, R, t, n), 0, 0))
            \/ (\E n \in Cl, s \in 0..MaxNs : Do("close", CarrierClosed(cf, R, t, n, s), 0, 0))
            \/ (\E nd \in Cl : \E s \in 0..MaxNs : \E f \in Frames(nd, t) : Do("frame", CarrierFrame(cf, R, t, nd, s, f), 0, FDst(nd, f)))
            \/ (\E p \in Peers \cup {1}, s \in {3}, d \in {1, 3}, ln \in Lens :
                    Do("peer", PeerFrame(cf, R, t, p, <<"fwd", s, d, 0, ln>>), p, d))
            \/ (\E n \in Cl : Do("udp", UdpHeard(cf, R, t, n), 0, n))
            \/ (\E m \in {0, 1}, d \in {2, 3} : Do("spu", IF LoudSpu THEN SpuLoud(cf, R, t, m, d, 0, 1) ELSE Spu(cf, R, t, m, d, 0, 1), 0, d))
            \/ (WithReady /\ \E n \in Cl : Do("ret", MemberReturned(cf, R, t, n), 0, 0))
            \/ Do("time", Timeout(cf, R, t), 0, 0) )
        \/ (\E p \in Peers : R' = AddPeer(R, p).R /\ UNCHANGED <<clock, last, ref, fw, heard, step, quiet>>
                          /\ steps' = steps + 1)
        \/ (\E p \in Peers : R' = RemovePeer(R, p) /\ UNCHANGED <<clock, last, ref, fw, heard, step, quiet>>
                          /\ steps' = steps + 1)
        \/ (WithReady /\ \E n \in Cl, o \in {0, 1} :
                R' = SetReady(R, n, o) /\ UNCHANGED <<clock, last, ref, fw, heard, step, quiet>> /\ steps' = steps + 1)

Spec == Init /\ [][Next]_vars

\* the checks of the last call: NoReforward, FwdToPeers, TunnelOk, ReplyRoute and the refused hand-over (see Checks)
CallsOk == last
QuotaOk == \A n \in DOMAIN R.cd : R.cd[n].wb <= cf.Bytes
SessionLimit == R.ls = clock /\ clock > 0 => \A n \in DOMAIN R.cd : Sat(clock - R.cd[n].opened) < cf.SessT
SessionsBound == /\ Cardinality(DOMAIN R.cd) <= cf.C /\ DOMAIN R.cd = Keys(R.tb, cf.C)
                 /\ \A n \in DOMAIN R.mb.held : R.mb.held[n].used <= cf.MB
\* the books of the mailbox, as ConnectMailbox.tla's Bounds and Conserved state them
Sum(q) == LET F[i \in 0..Len(q)] == IF i = 0 THEN 0 ELSE F[i - 1] + Size(MC(cf), q[i]) IN F[Len(q)]
Total == LET G[S \in SUBSET DOMAIN R.mb.held] ==
                IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN R.mb.held[x].count + G[S \ {x}]
         IN G[DOMAIN R.mb.held]
MailboxOk == /\ \A n \in DOMAIN R.mb.held : LET h == R.mb.held[n] IN
                  h.used = Sum(h.q) /\ h.count = Len(h.q) /\ h.count > 0
             /\ R.mb.st.stored = R.mb.st.delivered + R.mb.st.dropped + R.mb.st.expired + Total
\* the checks of the last call: a packet is forwarded to the home of a member that has no other way, and a heard packet
\* releases what its route can take and keeps what does not fit
Forwarded == fw
HeardDelivers == heard
StepsOver == step
\* the uploaded packet of a member is answered, with the table full, as without a stamp and not as a refusal
SpuSilent == quiet
\* a bounded model check: calls up to a depth of Depth
SmallMb == steps <= Depth
\* witness: some call refused the hand-over of a held message (only possible when the host reports a member not ready)
NoRefusal == ~ref
=============================================================================
