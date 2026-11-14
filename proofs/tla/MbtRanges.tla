----------------------------- MODULE MbtRanges ------------------------------
(***************************************************************************)
(* Model-based tests of the received-packet tracker's range set and the    *)
(* ACK ranges it reports (vinc-transport recovery/recv.rs,                 *)
(* ReceivedPackets<RANGES>): the state graph of the operators of           *)
(* RxOps.tla at a small capacity, for a Rust test to walk.                 *)
(*                                                                         *)
(* TLC enumerates every state reachable by the calls below and writes the  *)
(* graph (-dump dot,actionlabels,constrained): a node is the whole tracker *)
(* (RxOps' record x: the ranges, the floor, our acknowledgements sent, the *)
(* peer's confirmations and the floor they made) and an edge is one call   *)
(* with what it returns, as the label TLC gives it, the action and its     *)
(* arguments:                                                              *)
(*   CallRecv(pn, new)           on_packet_received of a packet number pn  *)
(*                               that is not ack-eliciting; new is TRUE    *)
(*                               for New, FALSE for Duplicate;             *)
(*   CallContains(pn, seen)      contains(pn);                             *)
(*   CallAckRanges(now, rgs)     ack_ranges(now) as inclusive pairs,       *)
(*                               largest first;                            *)
(*   CallAckSent(apn, now)       on_ack_sent: an acknowledgement went out  *)
(*                               in our packet apn at now;                 *)
(*   CallPeerAck(now, rgs)       on_peer_ack: the peer acknowledged the    *)
(*                               inclusive ranges rgs at now.              *)
(* The result is an argument so that the graph has one node per tracker:   *)
(* TLC makes one action per value of every bounded \E of Next, and the     *)
(* result is a bounded \E over the one value the operators compute, so     *)
(* every call has exactly one edge from a node (Complete checks that the   *)
(* values are of the shape the test reads). scripts/mbt.py turns the graph *)
(* into paths from the empty tracker that take every edge, and             *)
(* tests/mbt_ranges.rs drives a real tracker along each path, comparing    *)
(* the result and the whole tracker (trace_view, largest, range_count and  *)
(* contains of every number) after every call.                             *)
(*                                                                         *)
(* Scope: the range set and the report of it. Every packet is not          *)
(* ack-eliciting, so the acknowledgement policy (pending, due, every,      *)
(* min_rtt: the component "acknowledgement thinning", checked by Rx.tla    *)
(* and TraceRx.tla) stays at its start. CAP is the const generic RANGES,   *)
(* small so that the table fills; MAXACK is the code's MAX_ACK_RANGES, 32, *)
(* a constant of the module that a test cannot scale, and a graph that     *)
(* holds 33 ranges would be every set of 33 non-adjacent numbers, so the   *)
(* limit of 32 is not reached here (CAP is below it). SENTN and CONFN are  *)
(* the code's 48 and 32, too large to fill: the graph stops at SMAX        *)
(* acknowledgements recorded and CMAX confirmations queued, states past    *)
(* it are leaves, reached and compared but not left. The clock is the      *)
(* argument of each call, any of TS; the confirmation hold is 2 s, 2000    *)
(* with MS = 1 and SEC = 1000.                                             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS MS, SEC, TOP, MAXPN, U32MAX, SENTN, CONFN, MAXACK, CAP, PN, TS, APNS, SMAX, CMAX
VARIABLES x
vars == <<x>>

INSTANCE RxOps

Init == x = Init0(CAP)

RecvRes(pn) == Receive(x, [pn |-> pn, now |-> 0, elic |-> FALSE, bytes |-> 0])

\* the peer's acknowledgements: none, our packet 0 alone, a range of other packets, and both (the first range
\* misses, the second holds the packet)
PeerRgs == {<<>>, <<<<0, 0>>>>, <<<<1, 1>>>>, <<<<1, 1>>, <<0, 0>>>>}

CallRecv(pn, new) == LET r == RecvRes(pn) IN new = (r.out = "New") /\ x' = r.x
CallContains(pn, seen) == seen = Contains(x, pn) /\ x' = x
CallAckRanges(now, rgs) == rgs = AckRanges(x, now) /\ x' = x
CallAckSent(apn, now) == x' = AckSent(x, apn, now)
CallPeerAck(now, rgs) == x' = PeerAck(x, now, rgs)

\* the reports a call can return, which TLC needs as a set that does not depend on the state to split the action on
\* it: at most CAP inclusive pairs over the packet numbers, largest first and not touching
Pairs == {p \in (0..PN) \X (0..PN) : p[1] <= p[2]}
Reports == {s \in UNION {[1..k -> Pairs] : k \in 0..CAP} : \A j \in 1..(Len(s) - 1) : s[j + 1][2] + 1 < s[j][1]}

Next == \/ \E pn \in 0..PN, new \in BOOLEAN : CallRecv(pn, new)
        \/ \E pn \in 0..(PN + 1), seen \in BOOLEAN : CallContains(pn, seen)
        \/ \E now \in TS, rgs \in Reports : CallAckRanges(now, rgs)
        \/ \E apn \in APNS, now \in TS : CallAckSent(apn, now)
        \/ \E now \in TS, rgs \in PeerRgs : CallPeerAck(now, rgs)
Spec == Init /\ [][Next]_vars

Held == Len(x.sent) <= SMAX /\ Len(x.conf) <= CMAX

\* every call of a state in the graph has its result in the set Next ranges over, so no call is lost; a report is at
\* most MAXACK inclusive pairs, largest first
Complete ==
    /\ \A pn \in 0..PN : RecvRes(pn).out \in {"New", "Duplicate"}
    /\ \A now \in TS : LET r == AckRanges(x, now)
                       IN /\ r \in Reports
                          /\ Len(r) <= MAXACK
                          /\ \A k \in DOMAIN r : r[k][1] <= r[k][2]
                          /\ \A k \in 1..(Len(r) - 1) : r[k + 1][2] < r[k][1]
=============================================================================
