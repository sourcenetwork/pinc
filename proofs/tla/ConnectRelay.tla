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
(*  HeldFirst      nothing overtakes a held message: a packet is tunnelled *)
(*                 or sent on a carrier to a member that still holds       *)
(*                 messages only as one of the hand-overs of a pass (each  *)
(*                 followed by its delivery), and a destination that held  *)
(*                 messages is never answered NoRoute                      *)
(*  HeardDelivers  an accepted heard packet leaves a member whose route    *)
(*                 is ready holding nothing                                *)
(* OldHeld restores the rule before the release (nothing is released and   *)
(* packets overtake): the witness configs ConnectRelay_wheard and          *)
(* ConnectRelay_wfirst violate the two invariants with it.                 *)
(* Lean: Vinc/ConnectRelayThm.lean (peer_unauth, forward_peer, no_reforward,*)
(* back_window, charge_inv, tunnel_spec, spu_member, heard_idle,           *)
(* heard_unready_quiet, held_first, sleep_spec, ...).                      *)
(***************************************************************************)
EXTENDS ConnectRelayOps

CONSTANTS Times, MaxNs, Depth, WithSleep, WithReady, OldHeld
cf == [me |-> 9, C |-> 2, R |-> 2, MN |-> 1, MB |-> 120, Bytes |-> 3, Window |-> 3, SessT |-> 4, Age |-> 40,
       old |-> OldHeld]
Cl == {1, 2}
Peers == {5, 6}
VARIABLES R, clock, last, steps, ref, first, heard
vars == <<R, clock, last, steps, ref, first, heard>>

Init == /\ R = [NewRelay(cf) EXCEPT !.bk = [x \in {1, 2, 3, 5, 6, 9} |-> x % 2]]
        /\ clock = 0 /\ steps = 0 /\ last = TRUE /\ ref = FALSE /\ first = TRUE /\ heard = TRUE

IsFwd(e) == Len(e) >= 3 /\ e[1] = "peer" /\ e[3] = "fwd"
IsUdp(e) == Len(e) >= 3 /\ e[1] = "udp"
IsNoTunnel(e) == Len(e) >= 4 /\ e[1] = "t" /\ e[2] = "rej" /\ e[3] = "notunnel"
IsLearn(e) == Len(e) >= 4 /\ e[1] = "t" /\ e[2] = "fwdback"
IsRoutedOut(e) == Len(e) >= 6 /\ e[1] = "t" /\ e[2] = "routed" /\ (e[5] = "tunnel" \/ e[5] = "carrier")
IsMdeliv(e, d) == Len(e) >= 3 /\ e[1] = "t" /\ e[2] = "mdeliv" /\ e[3] = d
IsNoRoute(e) == Len(e) >= 4 /\ e[1] = "t" /\ e[2] = "rej" /\ e[3] = "noroute"

\* the destination of a carrier frame (0 when it routes nothing)
FDst(nd, f) == IF f[1] = "send" THEN f[2]
               ELSE IF f[1] = "sendalias" /\ nd \in DOMAIN R.cd THEN Resolve(R.cd[nd].rx, f[2]) ELSE 0
\* the member holds a live message at tm (the front one has not expired)
HeldLive(Rx, d, tm) == d \in DOMAIN Rx.mb.held /\ Sat(tm - Head(Rx.mb.held[d].q).t) < cf.Age

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

\* HeldFirst on one call, dst the destination it routes (R is the state before, o.R after): a tunnel or carrier hand-over
\* to a member left holding messages is followed by its delivery, and a destination that held a live message is not
\* answered NoRoute
FirstOk(o, dst, tm) ==
    LET E == o.ef IN
    /\ \A k \in 1..Len(E) :
           (IsRoutedOut(E[k]) /\ E[k][4] \in DOMAIN o.R.mb.held) => (k < Len(E) /\ IsMdeliv(E[k + 1], E[k][4]))
    /\ \A k \in 1..Len(E) : IsNoRoute(E[k]) => ~HeldLive(R, dst, tm)

\* HeardDelivers on one call: node is the member heard
HeardOk(kind, o, node) ==
    kind = "udp" /\ o.res = "ok" => (node \in o.R.nr \/ node \notin DOMAIN o.R.mb.held)

Do(kind, o, from, dst) == /\ R' = o.R /\ last' = Checks(kind, o, from, clock') /\ steps' = steps + 1
                          /\ first' = FirstOk(o, dst, clock') /\ heard' = HeardOk(kind, o, dst)
                          /\ ref' = (ref \/ \E k \in 1..Len(o.ef) : IsNoTunnel(o.ef[k]))

Frames(nd, tm) == {<<"send", d, 0, 1>> : d \in {1, 2, 3}}
             \cup {<<"sendalias", 0, 0, 1>>}
             \cup (IF WithSleep THEN {<<"sleep", nd, tm * 1000, 1, 1>>} ELSE {})

Next == \/ \E t \in Times : t >= clock /\ clock' = t /\
            ( (\E n \in Cl : R.ns < MaxNs /\ Do("open", CarrierOpened(cf, R, t, n), 0, 0))
            \/ (\E n \in Cl, s \in 0..MaxNs : Do("close", CarrierClosed(cf, R, t, n, s), 0, 0))
            \/ (\E nd \in Cl : \E s \in 0..MaxNs : \E f \in Frames(nd, t) : Do("frame", CarrierFrame(cf, R, t, nd, s, f), 0, FDst(nd, f)))
            \/ (\E p \in Peers \cup {1}, s \in {3}, d \in {1, 3} :
                    Do("peer", PeerFrame(cf, R, t, p, <<"fwd", s, d, 0, 1>>), p, d))
            \/ (\E n \in Cl : Do("udp", UdpHeard(cf, R, t, n), 0, n))
            \/ (\E m \in {0, 1}, d \in {2, 3} : Do("spu", Spu(cf, R, t, m, d, 0, 1), 0, d))
            \/ (WithReady /\ \E n \in Cl : Do("ret", MemberReturned(cf, R, t, n), 0, 0))
            \/ Do("time", Timeout(cf, R, t), 0, 0) )
        \/ (\E p \in Peers : R' = AddPeer(R, p).R /\ UNCHANGED <<clock, last, ref, first, heard>> /\ steps' = steps + 1)
        \/ (\E p \in Peers : R' = RemovePeer(R, p) /\ UNCHANGED <<clock, last, ref, first, heard>> /\ steps' = steps + 1)
        \/ (WithReady /\ \E n \in Cl, o \in {0, 1} :
                R' = SetReady(R, n, o) /\ UNCHANGED <<clock, last, ref, first, heard>> /\ steps' = steps + 1)

Spec == Init /\ [][Next]_vars

\* the checks of the last call: NoReforward, FwdToPeers, TunnelOk, ReplyRoute and the refused hand-over (see Checks)
CallsOk == last
QuotaOk == \A n \in DOMAIN R.cd : R.cd[n].wb <= cf.Bytes
SessionLimit == R.ls = clock /\ clock > 0 => \A n \in DOMAIN R.cd : Sat(clock - R.cd[n].opened) < cf.SessT
SessionsBound == /\ Cardinality(DOMAIN R.cd) <= cf.C /\ DOMAIN R.cd = Keys(R.tb, cf.C)
                 /\ \A n \in DOMAIN R.mb.held : R.mb.held[n].used <= cf.MB
\* the checks of the last call: nothing overtakes a held message, and a heard packet releases what its route can take
HeldFirst == first
HeardDelivers == heard
\* a bounded model check: calls up to a depth of Depth
SmallMb == steps <= Depth
\* witness: some call refused the hand-over of a held message (only possible when the host reports a member not ready)
NoRefusal == ~ref
=============================================================================
