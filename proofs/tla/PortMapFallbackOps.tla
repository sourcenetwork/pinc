--------------------------- MODULE PortMapFallbackOps ---------------------------
(***************************************************************************)
(* The calls of the port-mapping client as pure operators: pinc-portmap    *)
(* client.rs, `PortMap` (`new`, `handle_timeout`, `handle_datagram` with   *)
(* `pcp_answer`, `natpmp_answer` and the SSDP leg, `poll_datagram`,        *)
(* `poll_http`, `handle_http`, `stop`, `restart`, and the private `first`, *)
(* `enter`, `fail`, `grant`, `in_flight`, `queue_release` they use).       *)
(* PortMapFallback.tla checks the documented order on them and             *)
(* MbtPortMapFallback.tla turns them into model-based tests.               *)
(*                                                                         *)
(* A client state is a record:                                             *)
(*   cfg  [g: a gateway is known, l: "priv" (a private IPv4 socket),       *)
(*        "pub" (a specified socket that is not private IPv4, IPv4 or      *)
(*        IPv6: the code treats both alike), "unspec" (0.0.0.0 or ::)]     *)
(*   st   the step ("none" before `new`)                                   *)
(*   tr   tries of the request asked (0 outside an asking step)            *)
(*   sd   a datagram is due (`send`)                                       *)
(*   ht   the HTTP exchange: "none", "due", "sent"                         *)
(*   hd   the protocol of the mapping held, "none" for no mapping          *)
(*   rn   a renewal is in flight (`renewing`)                              *)
(*   ig   what the client knows of the gateway's UPnP service: on (an      *)
(*        `igd`), ctl (its control URL is known), pm (it keeps only leases *)
(*        of duration 0), cf (conflicts met, 0..3)                         *)
(*   rl   the two release slots, each "none", "pcp" or "natpmp"            *)
(*   hl   `halted`: stop was called                                        *)
(* A call returns [s: the state after, r: the counter of Stats it bumps    *)
(* ("none" for none) or what it gives out, ev: "grant" for a grant,        *)
(* "rfail" for a failed renewal, else "none"].                             *)
(*                                                                         *)
(* Abstractions, each sound for the steps the calls take:                  *)
(*  - Time is not kept: a timer call is handle_timeout at poll_timeout(),  *)
(*    the earliest deadline; a lease expiry is a separate call (Late, two  *)
(*    days on). poll_timeout() is the step's own deadline and never the    *)
(*    expiry while a lease of LIFETIME (7200 s) has had at most two failed *)
(*    renewals (each halves what is left: at least 900 s remain, a round   *)
(*    takes at most 6 s); the specs bound this with rf.                    *)
(*  - The gateway's epoch is always consistent (a gateway that restarted   *)
(*    is PortMapLease.tla's), so note_epoch never drops a mapping.         *)
(*  - An announce changes only times (the renewal is brought forward,      *)
(*    which the timer call reaches in the same step), so it changes no     *)
(*    field here; with no mapping held it is counted.                      *)
(*  - nat_ip is always set in NatMap and is not kept; the external port    *)
(*    of UPnP is a function of cf (ExtPort).                               *)
(*  - ig is cleared (NoIg) when no step can read it again: outside the     *)
(*    HTTP steps with no UPnP mapping held, the next igd is a new one made *)
(*    by an SSDP answer. The code keeps the old one; nothing reads it.     *)
(*  - The answers are the kinds below, each one fixed datagram or HTTP     *)
(*    answer (MbtPortMapFallback.tla lists the bytes for the test).        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

Locals == {"priv", "pub", "unspec"}
Steps == {"none", "pcp", "nataddr", "natmap", "ssdp", "desc", "extip", "add", "delete", "held", "idle", "stopped"}
Protos == {"pcp", "natpmp", "upnp"}
PcpKinds == {"grant", "grantpriv", "unsupp", "err", "hunsupp", "herr", "announce", "nonce", "port"}
NatKinds == {"addr", "addrpriv", "addrerr", "map", "maperr", "err0", "err1", "port", "garbage"}
SsdpKinds == {"ok", "foreign", "other", "bad"}
HttpKinds == {"fail", "desc", "ip", "ippriv", "ok", "perm", "conflict", "fault"}
\* what an answer or a timer call bumps
Counters == {"none", "unexpected", "wrong_nonce", "wrong_source", "refused", "timeouts", "http"}
DgramRes == {"none", "pcp", "pcprel", "natrel", "nataddr", "natmap", "search"}
PollRes == {"none", "get", "extip", "add", "addperm", "delete"}

NoIg == [on |-> FALSE, ctl |-> FALSE, pm |-> FALSE, cf |-> 0]
Blank == [cfg |-> [g |-> FALSE, l |-> "unspec"], st |-> "none", tr |-> 0, sd |-> FALSE, ht |-> "none", hd |-> "none",
          rn |-> FALSE, ig |-> NoIg, rl |-> <<"none", "none">>, hl |-> FALSE]

\* the first external port AddPortMapping asks for is the socket's port (the test's is 65534); a conflict asks the next,
\* and checked_add(1).unwrap_or(1024) wraps 65535 to 1024
ExtPort(cf) == CASE cf = 0 -> 65534 [] cf = 1 -> 65535 [] cf = 2 -> 1024 [] OTHER -> 1025

AskStep(st) == st \in {"pcp", "nataddr", "natmap", "ssdp"}
HttpStep(st) == st \in {"desc", "extip", "add", "delete"}
\* the protocol a step asks with
ProtoOf(st) ==
    CASE st = "pcp" -> "pcp"
      [] st \in {"nataddr", "natmap"} -> "natpmp"
      [] st \in {"ssdp", "desc", "extip", "add"} -> "upnp"
      [] OTHER -> "none"

(* ---- the code ---- *)
\* PortMap::searchable
Searchable(s) == s.cfg.l = "priv"
\* PortMap::first
First(cfg) ==
    IF cfg.g /\ cfg.l # "unspec" THEN "pcp"
    ELSE IF cfg.g THEN "nataddr"
    ELSE IF cfg.l = "priv" THEN "ssdp"
    ELSE "stopped"
\* PortMap::enter
Enter(s, st) ==
    [s EXCEPT !.st = st, !.tr = IF AskStep(st) THEN 1 ELSE 0, !.sd = AskStep(st),
              !.ht = IF HttpStep(st) THEN "due" ELSE "none"]
Norm(s) == [s EXCEPT !.ig = IF HttpStep(s.st) \/ s.hd = "upnp" THEN @ ELSE NoIg]
Out(s, r, ev) == [s |-> Norm(s), r |-> r, ev |-> ev]
Same(s, r) == Out(s, r, "none")

\* PortMap::fail
FailState(s) ==
    IF s.rn /\ s.hd # "none" THEN Enter([s EXCEPT !.rn = FALSE], "held")
    ELSE LET n == CASE s.st = "pcp" -> "nataddr"
                    [] s.st \in {"nataddr", "natmap"} /\ Searchable(s) -> "ssdp"
                    [] s.st \in {"delete", "stopped"} -> "stopped"
                    [] OTHER -> "idle"
         IN Enter([s EXCEPT !.rn = FALSE], n)
Fail(s, r) == Out(FailState(s), r, IF s.rn /\ s.hd # "none" THEN "rfail" ELSE "none")
\* PortMap::grant
Grant(s, p) == Out(Enter([s EXCEPT !.hd = p, !.rn = FALSE], "held"), "none", "grant")
\* PortMap::renew: the step a renewal of protocol p asks in
RenewStep(p) == CASE p = "pcp" -> "pcp" [] p = "natpmp" -> "nataddr" [] OTHER -> "extip"

\* PortMap::new
New(g, l) == Same(Enter([Blank EXCEPT !.cfg = [g |-> g, l |-> l]], First([g |-> g, l |-> l])), "none")

\* handle_timeout(poll_timeout()): the earliest deadline, which is never the expiry (see the header)
Tick(s) ==
    CASE s.st = "held" -> Same(Enter([s EXCEPT !.rn = TRUE], RenewStep(s.hd)), "none")
      [] AskStep(s.st) /\ s.tr < 3 -> Same([s EXCEPT !.tr = @ + 1, !.sd = TRUE], "none")
      [] s.st = "idle" -> Same(Enter(s, First(s.cfg)), "none")
      [] s.st = "stopped" -> Same(s, "none")
      [] OTHER -> Fail(s, "timeouts")
\* handle_timeout past the expiry of the mapping held (hd # "none")
Late(s) == Same(Enter([s EXCEPT !.hd = "none", !.rn = FALSE], First(s.cfg)), "none")

\* PortMap::poll_datagram: a release first, then the request due
RelRes(p) == IF p = "pcp" THEN "pcprel" ELSE "natrel"
SendRes(st) == CASE st = "pcp" -> "pcp" [] st = "nataddr" -> "nataddr" [] st = "natmap" -> "natmap"
                 [] st = "ssdp" -> "search" [] OTHER -> "none"
Dgram(s) ==
    IF s.rl[1] # "none" THEN Same([s EXCEPT !.rl[1] = "none"], RelRes(s.rl[1]))
    ELSE IF s.rl[2] # "none" THEN Same([s EXCEPT !.rl[2] = "none"], RelRes(s.rl[2]))
    ELSE IF ~s.sd THEN Same(s, "none")
    ELSE Same([s EXCEPT !.sd = FALSE], SendRes(s.st))

\* PortMap::poll_http (ht is "due" only in an HTTP step, where the igd and, past Desc, its control URL are known)
PollOf(s) == CASE s.st = "desc" -> "get" [] s.st = "extip" -> "extip"
               [] s.st = "add" -> (IF s.ig.pm THEN "addperm" ELSE "add") [] OTHER -> "delete"
HttpPoll(s) == IF s.ht # "due" THEN Same(s, "none") ELSE Same([s EXCEPT !.ht = "sent"], PollOf(s))

\* PortMap::handle_datagram of a PCP datagram from the gateway's port (pcp_answer); stopped, or searching (it is not a
\* search answer with a location), it is counted as unexpected
Unexp(s) == Same(s, "unexpected")
Pcp(s, k) ==
    IF s.st \in {"stopped", "ssdp"} THEN Unexp(s)
    ELSE CASE k = "nonce" -> Same(s, "wrong_nonce")
           [] k \in {"grant", "grantpriv", "unsupp", "err", "port"} ->
                IF s.st # "pcp" \/ k = "port" THEN Unexp(s)
                ELSE (CASE k = "grant" -> Grant(s, "pcp")
                        [] k = "grantpriv" -> Fail(s, "refused")
                        [] k = "unsupp" -> (IF s.rn THEN Fail(s, "none") ELSE Same(Enter(s, "nataddr"), "none"))
                        [] OTHER -> Fail(s, "none"))
           [] k \in {"hunsupp", "herr"} ->
                IF s.st # "pcp" THEN Unexp(s)
                ELSE IF k = "hunsupp" /\ ~s.rn THEN Same(Enter(s, "nataddr"), "none")
                ELSE Fail(s, "none")
           [] OTHER -> IF s.hd = "none" THEN Unexp(s) ELSE Same(s, "none")      \* announce

\* PortMap::handle_datagram of a NAT-PMP datagram from the gateway's port (natpmp_answer); stopped or searching as Pcp
NatStep(s, k) ==
    IF s.st \in {"stopped", "ssdp"} THEN Unexp(s)
    ELSE CASE k \in {"err0", "err1"} ->
                IF s.st = "pcp" /\ ~s.rn THEN Same(Enter(s, "nataddr"), "none")
                ELSE IF (k = "err0" /\ s.st = "nataddr") \/ (k = "err1" /\ s.st = "natmap") THEN Fail(s, "none")
                ELSE Unexp(s)
           [] k \in {"addr", "addrpriv", "addrerr"} ->
                IF s.st # "nataddr" THEN Unexp(s)
                ELSE (CASE k = "addr" -> Same(Enter(s, "natmap"), "none")
                        [] k = "addrpriv" -> Fail(s, "refused")
                        [] OTHER -> Fail(s, "none"))
           [] k \in {"map", "maperr", "port"} ->
                IF s.st # "natmap" \/ k = "port" THEN Unexp(s)
                ELSE IF k = "map" THEN Grant(s, "natpmp") ELSE Fail(s, "none")
           [] OTHER -> Unexp(s)                                                  \* garbage

\* PortMap::handle_datagram of a datagram from port 1900 of the host the test searches (the gateway when one is known)
Ssdp(s, k) ==
    IF s.st # "ssdp" \/ k \in {"foreign", "bad"} THEN Same(s, "wrong_source")
    ELSE IF k = "ok" THEN Same(Enter([s EXCEPT !.ig = [on |-> TRUE, ctl |-> FALSE, pm |-> FALSE, cf |-> 0]], "desc"), "none")
    ELSE Unexp(s)                                                                 \* other: a 404, no location

\* PortMap::handle_http
Http(s, k) ==
    IF s.ht # "sent" THEN Same(s, "none")
    ELSE LET s1 == [s EXCEPT !.ht = "none"]
         IN IF k = "fail" THEN Fail(s1, "http")
            ELSE CASE s.st = "desc" ->
                        IF k = "desc" THEN Same(Enter([s1 EXCEPT !.ig.ctl = TRUE], "extip"), "none") ELSE Fail(s1, "http")
                   [] s.st = "extip" ->
                        (CASE k = "ip" -> Same(Enter(s1, "add"), "none")
                           [] k = "ippriv" -> Fail(s1, "refused")
                           [] OTHER -> Fail(s1, "http"))
                   [] s.st = "add" ->
                        (CASE k \in {"desc", "ip", "ippriv", "ok"} -> Grant(s1, "upnp")
                           [] k = "perm" /\ ~s.ig.pm -> Same(Enter([s1 EXCEPT !.ig.pm = TRUE], "add"), "none")
                           [] k = "conflict" /\ s.ig.cf < 3 /\ ~s.rn ->
                                Same(Enter([s1 EXCEPT !.ig.cf = @ + 1], "add"), "none")
                           [] OTHER -> Fail(s1, "http"))
                   [] OTHER -> Same(Enter(s1, "stopped"), "none")                 \* delete

\* PortMap::in_flight and queue_release
InFlight(s) == CASE s.st = "pcp" -> "pcp" [] s.st = "natmap" -> "natpmp"
                 [] s.st = "add" /\ s.ig.on /\ s.ig.ctl -> "upnp" [] OTHER -> "none"
Queue(rl, p) == IF rl[1] = "none" THEN <<p, rl[2]>> ELSE <<rl[1], p>>
\* PortMap::stop
Stop(s) ==
    LET lease == IF s.hd # "none" THEN s.hd ELSE InFlight(s)
        s1 == [s EXCEPT !.hl = TRUE, !.hd = "none", !.rn = FALSE]
    IN IF lease = "upnp" /\ s.ig.on /\ s.ig.ctl THEN Same(Enter(s1, "delete"), "none")
       ELSE IF lease # "none" THEN Same(Enter([s1 EXCEPT !.rl = Queue(s.rl, lease)], "stopped"), "none")
       ELSE Same(Enter(s1, "stopped"), "none")
\* PortMap::restart
Restart(s) ==
    IF s.hl THEN Same(s, "none")
    ELSE LET rl == IF s.hd \in {"pcp", "natpmp"} THEN Queue(s.rl, s.hd) ELSE s.rl
         IN Same(Enter([s EXCEPT !.rl = rl, !.hd = "none", !.rn = FALSE, !.ig = NoIg], First(s.cfg)), "none")

\* failed renewals since the last grant, 0 with no mapping held
RfNext(rf, o) == IF o.s.hd = "none" \/ o.ev = "grant" THEN 0 ELSE IF o.ev = "rfail" THEN rf + 1 ELSE rf

\* every call from a state of the code (after new), with the answers a known gateway can send only when one is known
Outs(s) ==
    {Dgram(s), HttpPoll(s), Tick(s), Stop(s), Restart(s)}
    \cup (IF s.hd # "none" THEN {Late(s)} ELSE {})
    \cup (IF s.cfg.g THEN {Pcp(s, k) : k \in PcpKinds} \cup {NatStep(s, k) : k \in NatKinds} ELSE {})
    \cup {Ssdp(s, k) : k \in SsdpKinds} \cup {Http(s, k) : k \in HttpKinds}
\* the same without stop, restart and the expiry, which begin again by design
Moves(s) ==
    {Dgram(s), HttpPoll(s), Tick(s)}
    \cup (IF s.cfg.g THEN {Pcp(s, k) : k \in PcpKinds} \cup {NatStep(s, k) : k \in NatKinds} ELSE {})
    \cup {Ssdp(s, k) : k \in SsdpKinds} \cup {Http(s, k) : k \in HttpKinds}
=============================================================================
