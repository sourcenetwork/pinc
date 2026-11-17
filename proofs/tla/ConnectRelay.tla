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
(* Lean: Vinc/ConnectRelayThm.lean (peer_unauth, forward_peer, no_reforward,*)
(* back_window, charge_inv, tunnel_spec, spu_member, sleep_spec, ...).     *)
(***************************************************************************)
EXTENDS ConnectRelayOps

CONSTANTS Times, MaxNs, Depth, WithSleep, WithReady
cf == [me |-> 9, C |-> 2, R |-> 2, MN |-> 1, MB |-> 120, Bytes |-> 3, Window |-> 3, SessT |-> 4, Age |-> 40]
Cl == {1, 2}
Peers == {5, 6}
VARIABLES R, clock, last, steps, ref
vars == <<R, clock, last, steps, ref>>

Init == /\ R = [NewRelay(cf) EXCEPT !.bk = [x \in {1, 2, 3, 5, 6, 9} |-> x % 2]]
        /\ clock = 0 /\ steps = 0 /\ last = TRUE /\ ref = FALSE

IsFwd(e) == Len(e) >= 3 /\ e[1] = "peer" /\ e[3] = "fwd"
IsUdp(e) == Len(e) >= 3 /\ e[1] = "udp"
IsNoTunnel(e) == Len(e) >= 4 /\ e[1] = "t" /\ e[2] = "rej" /\ e[3] = "notunnel"
IsLearn(e) == Len(e) >= 4 /\ e[1] = "t" /\ e[2] = "fwdback"

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

Do(kind, o, from) == /\ R' = o.R /\ last' = Checks(kind, o, from, clock') /\ steps' = steps + 1
                     /\ ref' = (ref \/ \E k \in 1..Len(o.ef) : IsNoTunnel(o.ef[k]))

Frames(nd, tm) == {<<"send", d, 0, 1>> : d \in {1, 2, 3}}
             \cup {<<"sendalias", 0, 0, 1>>}
             \cup (IF WithSleep THEN {<<"sleep", nd, tm * 1000, 1, 1>>} ELSE {})

Next == \/ \E t \in Times : t >= clock /\ clock' = t /\
            ( (\E n \in Cl : R.ns < MaxNs /\ Do("open", CarrierOpened(cf, R, t, n), 0))
            \/ (\E n \in Cl, s \in 0..MaxNs : Do("close", CarrierClosed(cf, R, t, n, s), 0))
            \/ (\E nd \in Cl : \E s \in 0..MaxNs : \E f \in Frames(nd, t) : Do("frame", CarrierFrame(cf, R, t, nd, s, f), 0))
            \/ (\E p \in Peers \cup {1}, s \in {3}, d \in {1, 3} :
                    Do("peer", PeerFrame(cf, R, t, p, <<"fwd", s, d, 0, 1>>), p))
            \/ (\E n \in Cl : Do("udp", UdpHeard(cf, R, n, t), 0))
            \/ (\E m \in {0, 1}, d \in {2, 3} : Do("spu", Spu(cf, R, t, m, d, 0, 1), 0))
            \/ (WithReady /\ \E n \in Cl : Do("ret", MemberReturned(cf, R, t, n), 0))
            \/ Do("time", Timeout(cf, R, t), 0) )
        \/ (\E p \in Peers : R' = AddPeer(R, p).R /\ UNCHANGED <<clock, last, ref>> /\ steps' = steps + 1)
        \/ (\E p \in Peers : R' = RemovePeer(R, p) /\ UNCHANGED <<clock, last, ref>> /\ steps' = steps + 1)
        \/ (WithReady /\ \E n \in Cl, o \in {0, 1} :
                R' = SetReady(R, n, o) /\ UNCHANGED <<clock, last, ref>> /\ steps' = steps + 1)

Spec == Init /\ [][Next]_vars

\* the checks of the last call: NoReforward, FwdToPeers, TunnelOk, ReplyRoute and the refused hand-over (see Checks)
CallsOk == last
QuotaOk == \A n \in DOMAIN R.cd : R.cd[n].wb <= cf.Bytes
SessionLimit == R.ls = clock /\ clock > 0 => \A n \in DOMAIN R.cd : Sat(clock - R.cd[n].opened) < cf.SessT
SessionsBound == /\ Cardinality(DOMAIN R.cd) <= cf.C /\ DOMAIN R.cd = Keys(R.tb, cf.C)
                 /\ \A n \in DOMAIN R.mb.held : R.mb.held[n].used <= cf.MB
\* a bounded model check: calls up to a depth of Depth
SmallMb == steps <= Depth
\* witness: some call refused the hand-over of a held message (only possible when the host reports a member not ready)
NoRefusal == ~ref
=============================================================================
