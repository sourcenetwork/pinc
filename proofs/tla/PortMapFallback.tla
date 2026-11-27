---------------------------- MODULE PortMapFallback ----------------------------
(***************************************************************************)
(* The order in which the port-mapping client tries PCP, NAT-PMP and       *)
(* UPnP-IGD: pinc-portmap client.rs (`PortMap`), on the operators of       *)
(* PortMapFallbackOps.tla. Every state the calls reach from `new`, for     *)
(* every configuration (gateway known or not; a private IPv4 socket,       *)
(* another specified one, an unspecified one).                             *)
(*                                                                         *)
(* What the module documentation of client.rs claims, stated apart from    *)
(* the code (each a state invariant that quantifies over every call from   *)
(* the state, so no ghost is needed):                                      *)
(*  - FirstStep: with the gateway known the client asks with PCP, but a    *)
(*    socket on the unspecified address with NAT-PMP only; with none known *)
(*    only UPnP is tried, and only from a private IPv4 address.            *)
(*  - Allowed: PCP is used only with a gateway and a specified socket,     *)
(*    NAT-PMP only with a gateway, UPnP only from a private IPv4 socket    *)
(*    (asking, held or deleted).                                           *)
(*  - Order: no call but stop, restart and the expiry of a lease takes an  *)
(*    asking client back to an earlier protocol or an earlier request of   *)
(*    one (PCP, NAT-PMP address, NAT-PMP map, search, description,         *)
(*    external address, AddPortMapping).                                   *)
(*  - FallbackNext: when a first ask leaves its protocol without a         *)
(*    mapping, it goes to the next documented one: PCP to NAT-PMP,         *)
(*    NAT-PMP to UPnP (when it may search, else to the retry after RETRY), *)
(*    UPnP to the retry. IdleRetry: the retry begins again from the first. *)
(*  - Renewal: a renewal asks with the protocol that granted the mapping,  *)
(*    and one that fails goes back to holding it (tried again half way).   *)
(*  - PrivateRefused: a grant of an external address no internet peer can *)
(*    reach is not held (PCP, NAT-PMP, and UPnP's external address).       *)
(*  - StopFinal: after stop no mapping is held, the client only releases   *)
(*    and deletes, and no call makes it ask again; StopReleases: stop      *)
(*    releases the mapping held or the request in flight that may have     *)
(*    made one (UPnP by DeletePortMapping); restart releases a PCP or      *)
(*    NAT-PMP mapping held.                                                *)
(*  - AnswerScope: an answer changes the client only when it answers the   *)
(*    request in flight (PCP by nonce, protocol and port; NAT-PMP by       *)
(*    opcode and port; a search answer only while searching; HTTP only     *)
(*    when sent), and a PCP or NAT-PMP answer that does not is counted.    *)
(*                                                                         *)
(* Bounds: none on the configurations or the calls; rf <= 2 (CONSTRAINT)   *)
(* keeps the abstraction of time sound (PortMapFallbackOps.tla). Both      *)
(* release slots are free to fill, so a stop or restart with both full     *)
(* (the third release takes the last slot) is in the domain. About 3300    *)
(* states.                                                                 *)
(*                                                                         *)
(* PortMapFallback_full.cfg is a witness: a UPnP mapping held with a       *)
(* gateway known, so the whole chain PCP, NAT-PMP, UPnP is reachable.      *)
(***************************************************************************)
EXTENDS PortMapFallbackOps

VARIABLES s, rf
vars == <<s, rf>>

Init == s = Blank /\ rf = 0
Do(o) == s' = o.s /\ rf' = RfNext(rf, o)
Next ==
    \/ s.st = "none" /\ \E g \in BOOLEAN, l \in Locals : s' = New(g, l).s /\ rf' = 0
    \/ s.st # "none" /\ \E o \in Outs(s) : Do(o)
Spec == Init /\ [][Next]_vars

Bound == rf <= 2

(* ---- the documented rule ---- *)
\* the step `new` documents
DocFirst(g, l) == IF g THEN (IF l = "unspec" THEN "nataddr" ELSE "pcp") ELSE IF l = "priv" THEN "ssdp" ELSE "stopped"
\* asking steps in the documented order
Level(st) == CASE st = "pcp" -> 1 [] st = "nataddr" -> 2 [] st = "natmap" -> 3 [] st = "ssdp" -> 4 [] st = "desc" -> 5
               [] st = "extip" -> 6 [] st = "add" -> 7 [] OTHER -> 0
Asking(st) == Level(st) > 0
\* where a protocol that gave no mapping goes on
DocNext(x) ==
    CASE ProtoOf(x.st) = "pcp" -> "nataddr"
      [] ProtoOf(x.st) = "natpmp" -> (IF x.cfg.l = "priv" THEN "ssdp" ELSE "idle")
      [] OTHER -> "idle"

TypeOK ==
    /\ s.cfg \in [g : BOOLEAN, l : Locals] /\ s.st \in Steps /\ s.tr \in 0..3 /\ s.sd \in BOOLEAN
    /\ s.ht \in {"none", "due", "sent"} /\ s.hd \in Protos \cup {"none"} /\ s.rn \in BOOLEAN
    /\ s.ig \in [on : BOOLEAN, ctl : BOOLEAN, pm : BOOLEAN, cf : 0..3]
    /\ s.rl \in {<<a, b>> : a, b \in {"none", "pcp", "natpmp"}} /\ s.hl \in BOOLEAN
    /\ rf \in 0..3

FirstStep == \A g \in BOOLEAN, l \in Locals : New(g, l).s.st = DocFirst(g, l)

Allowed ==
    /\ ProtoOf(s.st) = "pcp" \/ s.hd = "pcp" => s.cfg.g /\ s.cfg.l # "unspec"
    /\ ProtoOf(s.st) = "natpmp" \/ s.hd = "natpmp" => s.cfg.g
    /\ ProtoOf(s.st) = "upnp" \/ s.hd = "upnp" \/ s.st = "delete" => s.cfg.l = "priv"

Order == Asking(s.st) => \A o \in Moves(s) : Asking(o.s.st) => Level(o.s.st) >= Level(s.st)

FallbackNext ==
    (Asking(s.st) /\ ~s.rn) =>
        \A o \in Moves(s) : (o.s.st # "held" /\ ProtoOf(o.s.st) # ProtoOf(s.st)) => o.s.st = DocNext(s)
IdleRetry == s.st = "idle" => Tick(s).s.st = First(s.cfg) /\ First(s.cfg) = DocFirst(s.cfg.g, s.cfg.l)

Renewal ==
    /\ s.rn => s.hd # "none" /\ ProtoOf(s.st) = s.hd
    /\ s.hd # "none" => s.st = "held" \/ s.rn
    /\ s.st = "held" => ProtoOf(Tick(s).s.st) = s.hd /\ Tick(s).s.rn
    /\ s.rn => \A o \in Moves(s) : ProtoOf(o.s.st) # s.hd => o.s.st = "held" /\ o.s.hd = s.hd

PrivateRefused ==
    \* a private address does not move the machine to the mapping step (in it already, the answer is out of scope)
    /\ s.cfg.g => Pcp(s, "grantpriv").ev # "grant" /\ (s.st # "natmap" => NatStep(s, "addrpriv").s.st # "natmap")
    /\ s.st = "extip" => Http(s, "ippriv").s.st # "add" /\ Http(s, "ippriv").ev # "grant"

StopFinal ==
    s.hl => /\ s.hd = "none" /\ s.st \in {"delete", "stopped"}
            /\ Dgram(s).r \in {"none", "pcprel", "natrel"}
            /\ HttpPoll(s).r \in {"none", "delete"}
            /\ \A o \in Outs(s) : o.s.hl /\ o.s.hd = "none" /\ o.s.st \in {"delete", "stopped"}
\* the mapping stop must release: the one held, else what the request in flight may have made
Owed(x) == IF x.hd # "none" THEN x.hd ELSE InFlight(x)
StopReleases ==
    /\ LET o == Stop(s).s
       IN /\ Owed(s) \in {"pcp", "natpmp"} => Owed(s) \in {o.rl[1], o.rl[2]} /\ o.st = "stopped"
          /\ Owed(s) = "upnp" => o.st = "delete" /\ o.ht = "due"
          /\ Owed(s) = "none" => o.st = "stopped"
    /\ ~s.hl /\ s.hd \in {"pcp", "natpmp"} => s.hd \in {Restart(s).s.rl[1], Restart(s).s.rl[2]}

PcpMatch(k) ==
    s.st = "pcp" /\ (k \in {"grant", "grantpriv", "unsupp", "err"} \/ (k \in {"hunsupp", "herr"} /\ s.hd = "none"))
NatMatch(k) ==
    \/ k \in {"err0", "err1"} /\ s.st = "pcp" /\ ~s.rn
    \/ k \in {"addr", "addrpriv", "addrerr", "err0"} /\ s.st = "nataddr"
    \/ k \in {"map", "maperr", "err1"} /\ s.st = "natmap"
AnswerScope ==
    /\ s.cfg.g =>
         /\ \A k \in PcpKinds : Pcp(s, k).s # s => PcpMatch(k)
         /\ \A k \in NatKinds : NatStep(s, k).s # s => NatMatch(k)
         /\ s.st \notin {"ssdp", "stopped"} =>
              /\ \A k \in PcpKinds \ {"announce"} : ~PcpMatch(k) => Pcp(s, k).r # "none"
              /\ \A k \in NatKinds : ~NatMatch(k) => NatStep(s, k).r # "none"
    /\ \A k \in SsdpKinds : Ssdp(s, k).s # s => s.st = "ssdp" /\ k = "ok"
    /\ \A k \in HttpKinds : Http(s, k).s # s => s.ht = "sent"

Inv ==
    /\ TypeOK
    /\ FirstStep
    /\ s.st # "none" => (Allowed /\ Order /\ FallbackNext /\ IdleRetry /\ Renewal /\ PrivateRefused /\ StopFinal
                         /\ StopReleases /\ AnswerScope)

\* Witness (PortMapFallback_full.cfg, which TLC must violate): no UPnP mapping is held with a gateway known.
NoUpnpWithGateway == ~(s.hd = "upnp" /\ s.cfg.g)
=============================================================================
