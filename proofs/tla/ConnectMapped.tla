----------------------------- MODULE ConnectMapped -----------------------------
(***************************************************************************)
(* Model check of the port mappings the connectivity layer holds:          *)
(* pinc-connect client/mapped.rs (set_mapped, refresh_mapped, candidates)  *)
(* with the update_class of conn.rs and the restart of link_changed and    *)
(* resume (ConnectMappedOps.tla), over every interleaving of: a mapping    *)
(* set of 0 to 3 addresses (two IPs, the same address twice, a third one   *)
(* past the two slots), a reflexive address from either of 2 relays (at    *)
(* the mapping's IP with another port or its own port, at another public   *)
(* IP, at a shared-range IP, at the node's local address), a link change,  *)
(* and a tick with and without the UDP watchdog run out. The node has one  *)
(* local address.                                                          *)
(*                                                                         *)
(* Checked, in every state reached (the module doc of mapped.rs and the    *)
(* docs of set_mapped and candidates):                                     *)
(*  - HeldNotOffered: a mapped address no relay vouches for (no reflexive  *)
(*    address at its IP) is never offered, unless it is itself a           *)
(*    reflexive or local address;                                          *)
(*  - OfferedFirst: the vouched mapped addresses lead the candidates, in   *)
(*    the order of the mapping;                                            *)
(*  - MappedOnlyWhileSeen: the class is PortMapped only while a relay      *)
(*    vouches for a mapping;                                               *)
(*  - LiveSync: what the layer holds as vouched is what the reflexive      *)
(*    addresses vouch for now;                                             *)
(* and in every step:                                                      *)
(*  - ClassKept: a node with a class never loses it ("a withdrawn mapping  *)
(*    never leaves the node without a class");                             *)
(*  - AskedAtOnce: a change in what is vouched for asks for the record at  *)
(*    once; a fallback takes a class that is not PortMapped and sets the   *)
(*    publication to now.                                                  *)
(* Witness ConnectMapped_w_fallback: NoFallback is violated, so a mapping  *)
(* that made the node port-mapped is withdrawn in some behaviour.          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, ConnectMappedOps

VARIABLES S, eff
vars == <<S, eff>>

IPL == <<192, 168, 1, 2>>
IPP == <<198, 51, 100, 5>>
IPQ == <<203, 0, 113, 9>>
IPS == <<100, 64, 0, 1>>
LA == <<IPL, 4433>>
MP == <<IPP, 7777>>
MQ == <<IPQ, 7777>>

MS == {<<>>, <<MP>>, <<MQ>>, <<MP, MQ>>, <<MQ, MP>>, <<MP, MP>>, <<MP, MQ, LA>>}
AS == {<<IPP, 20000>>, <<IPP, 7777>>, <<IPP, 20001>>, <<IPQ, 20000>>, <<IPS, 20000>>, LA}

Init == S = New(<<LA>>, 2) /\ eff = Did(0, FALSE, FALSE, FALSE)

Apply(r) == S' = r.s /\ eff' = [r EXCEPT !.s = 0]

Next == \/ \E ms \in MS, q \in BOOLEAN : Apply(SetMapped(S, ms, q))
        \/ \E i \in 1..2, a \in AS : Apply(Answer(S, i, a))
        \/ Apply(Restart(S))
        \/ \E q \in BOOLEAN : Apply(Tick(S, q))
Spec == Init /\ [][Next]_vars

RL == ReflList(S)

HeldNotOffered == \A j \in 1..2 :
    LET m == S.mapped[j]
    IN (m # NOA /\ ~Seen(RL, m) /\ InSeqA(Cands(S), m)) => (InSeqA(RL, m) \/ InSeqA(S.local, m))

OfferedFirst == LET lv == DedupCap(Flat(LiveOf(S, RL)), <<>>, MAXADDRS)
                IN \A i \in 1..Len(lv) : i <= Len(Cands(S)) /\ Cands(S)[i] = lv[i]

MappedOnlyWhileSeen == S.cls = 2 => AnyLive(LiveOf(S, RL))

LiveSync == S.live = LiveOf(S, RL)

ClassKept == [][S.cls # 0 => S'.cls # 0]_vars

AskedAtOnce == [][/\ S'.live # S.live => eff'.want
                  /\ eff'.fb => (eff'.pub /\ S'.cls # 2)]_vars

\* the reachability witness: a port-mapped node loses its mapping
NoFallback == ~eff.fb
=============================================================================
