-------------------------- MODULE MbtPortMapFallback --------------------------
(***************************************************************************)
(* Model-based tests of the port-mapping client's fallback order:          *)
(* pinc-portmap client.rs (`PortMap`), the state graph of the operators of *)
(* PortMapFallbackOps.tla, whose properties PortMapFallback.tla checks.    *)
(*                                                                         *)
(* TLC writes the graph (-dump dot,actionlabels,constrained); an edge is   *)
(* one call of the client with what it returns, as TLC labels it:          *)
(*   CallNew(g, l)      PortMap::new for a configuration (the only call    *)
(*                      from the initial state)                            *)
(*   CallDgram(r)       poll_datagram: r the datagram given out            *)
(*   CallHttpPoll(r)    poll_http: r the request given out                 *)
(*   CallTick(r)        handle_timeout(poll_timeout()), r the counter      *)
(*   CallLate           handle_timeout two days on (a mapping is held)     *)
(*   CallPcp(k, r)      handle_datagram of the PCP answer k from the       *)
(*                      gateway's port, r the counter                      *)
(*   CallNat(k, r)      the same for the NAT-PMP answer k                  *)
(*   CallSsdp(k, r)     handle_datagram of the search answer k from port   *)
(*                      1900 of the searched host                          *)
(*   CallHttp(k, r)     handle_http of the HTTP answer k                   *)
(*   CallStop           stop                                               *)
(*   CallRestart        restart                                            *)
(* The result is an argument, so the graph has one node per state          *)
(* (Complete checks each result is in its set). scripts/mbt.py turns the   *)
(* graph into paths from the initial state that take every edge, and       *)
(* tests/mbt_portmap_fallback.rs drives a real PortMap along each path,    *)
(* comparing after every call the result (the datagram or request given    *)
(* out, the Stats counter bumped, none for no counter) and the state the   *)
(* crate's `trace` probe reports against the node.                         *)
(*                                                                         *)
(* To keep the graph small (each step of a case is a line of the cases     *)
(* file): every answer kind is an edge from every state, except that a     *)
(* stopped client gets one PCP, one NAT-PMP and one search answer (each    *)
(* returns at once) and a client with no HTTP exchange sent gets one HTTP  *)
(* answer (it is dropped at once); the PCP and NAT-PMP answers need a      *)
(* gateway. MbtBound makes a state with both release slots full before a   *)
(* stop a leaf (the third release, which takes the last slot, is checked   *)
(* by PortMapFallback.cfg, not here), and one past two failed renewals a   *)
(* leaf (the timer abstraction). About 1300 states and 35,000 edges.       *)
(***************************************************************************)
EXTENDS PortMapFallbackOps

VARIABLES s, rf
vars == <<s, rf>>

Init == s = Blank /\ rf = 0

Do(o, r) == r = o.r /\ s' = o.s /\ rf' = RfNext(rf, o)
Live == s.st # "none"

CallNew(g, l) == s.st = "none" /\ s' = New(g, l).s /\ rf' = 0
CallDgram(r) == Live /\ Do(Dgram(s), r)
CallHttpPoll(r) == Live /\ Do(HttpPoll(s), r)
CallTick(r) == Live /\ Do(Tick(s), r)
CallLate == Live /\ s.hd # "none" /\ Do(Late(s), "none")
CallPcp(k, r) == Live /\ s.cfg.g /\ (s.st # "stopped" \/ k = "grant") /\ Do(Pcp(s, k), r)
CallNat(k, r) == Live /\ s.cfg.g /\ (s.st # "stopped" \/ k = "addr") /\ Do(Nat(s, k), r)
CallSsdp(k, r) == Live /\ (s.st # "stopped" \/ k = "ok") /\ Do(Ssdp(s, k), r)
CallHttp(k, r) == Live /\ (s.ht = "sent" \/ k = "ok") /\ Do(Http(s, k), r)
CallStop == Live /\ Do(Stop(s), "none")
CallRestart == Live /\ Do(Restart(s), "none")

Next ==
    \/ \E g \in BOOLEAN, l \in Locals : CallNew(g, l)
    \/ \E r \in DgramRes : CallDgram(r)
    \/ \E r \in PollRes : CallHttpPoll(r)
    \/ \E r \in Counters : CallTick(r)
    \/ CallLate
    \/ \E k \in PcpKinds, r \in Counters : CallPcp(k, r)
    \/ \E k \in NatKinds, r \in Counters : CallNat(k, r)
    \/ \E k \in SsdpKinds, r \in Counters : CallSsdp(k, r)
    \/ \E k \in HttpKinds, r \in Counters : CallHttp(k, r)
    \/ CallStop
    \/ CallRestart
Spec == Init /\ [][Next]_vars

MbtBound == rf <= 2 /\ (s.rl[2] = "none" \/ s.hl)

\* every call of a state in the graph has a result in the set Next ranges over
Complete ==
    Live =>
        /\ Dgram(s).r \in DgramRes /\ HttpPoll(s).r \in PollRes /\ Tick(s).r \in Counters
        /\ Stop(s).r = "none" /\ Restart(s).r = "none" /\ (s.hd # "none" => Late(s).r = "none")
        /\ \A k \in PcpKinds : Pcp(s, k).r \in Counters
        /\ \A k \in NatKinds : Nat(s, k).r \in Counters
        /\ \A k \in SsdpKinds : Ssdp(s, k).r \in Counters
        /\ \A k \in HttpKinds : Http(s, k).r \in Counters
=============================================================================
