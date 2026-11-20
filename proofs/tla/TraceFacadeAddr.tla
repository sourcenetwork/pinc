--------------------------- MODULE TraceFacadeAddr ---------------------------
(***************************************************************************)
(* Trace validation of crates/pinc/src/addr.rs (`node_to_string`,          *)
(* `node_from_str`, `NodeAddr::with_relay`, `ticket`, `parse`) against the *)
(* operators of FacadeAddrOps.tla at the real width (NB = 32 bytes).       *)
(*                                                                         *)
(* The unit test `addr::tests::trace_addr` (both builds of the crate       *)
(* `pinc`, file facade_addr.ndjson) records every text as an array of byte *)
(* codes: ids of every algorithm and their text read back; the texts of    *)
(* the model's "str" cases at 32 bytes and random mutations; every url of  *)
(* at most 4 characters over h : / , @ and what `with_relay` says; each    *)
(* address given to `with_direct` and the one the value holds (op          *)
(* "direct"); NodeAddr                                                     *)
(* values (built through the API, with flowinfo 0 and 1, and through the   *)
(* public fields) with their ticket; and parses of tickets and of mutated  *)
(* tickets. The core library's SocketAddr parse is an oracle the test      *)
(* records for every item of a parsed text that has no "://": accepted or  *)
(* not, the Display text and flowinfo of what it gives. Every answer must  *)
(* be the model's.                                                         *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds facade_addr.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils
VARIABLE x

A == INSTANCE FacadeAddrOps WITH NB <- 32

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/facade_addr.ndjson")

Id(r) == [alg |-> r.alg, bytes |-> r.bytes]
Val(r) == [node |-> Id(r.node), direct |-> [k \in 1..Len(r.direct) |-> [txt |-> r.direct[k].txt,
                                                                          flow |-> r.direct[k].flow]],
           relays |-> r.relays]
\* the recorded oracle of the core library's parse: the texts it accepted and what it gave
CPOf(ev) == LET acc == {e \in {ev.cp[k] : k \in 1..Len(ev.cp)} : e.ok}
            IN [t \in {e.t : e \in acc} |-> [txt |-> (CHOOSE e \in acc : e.t = t).txt,
                                             flow |-> (CHOOSE e \in acc : e.t = t).flow]]
\* every item of the text the model hands to the oracle was recorded
Covered(ev) == LET k == A!First(ev.s, A!At)
                   rest == IF k > 0 THEN A!After(ev.s, k) ELSE <<>>
                   items == A!Split(rest, A!Comma)
               IN \A j \in 1..Len(items) :
                    (items[j] # <<>> /\ ~A!Contains(items[j], A!Sep)) => \E e \in 1..Len(ev.cp) : ev.cp[e].t = items[j]

EvOK(ev) ==
    CASE ev.op = "id" -> /\ A!NodeToString(Id(ev)) = ev.text
                         /\ A!NodeFromStr(ev.text) = [ok |-> TRUE, v |-> Id(ev)]
      [] ev.op = "str" -> LET r == A!NodeFromStr(ev.s)
                          IN r.ok = ev.ok /\ (ev.ok => r.v = Id(ev))
      [] ev.op = "relay" -> A!RelayOK(ev.u) = ev.ok
      \* with_direct of one address: what the value holds (the flow label dropped, fix F12)
      [] ev.op = "direct" -> A!WithDirect([txt |-> ev.a.txt, flow |-> ev.a.flow])
                             = [txt |-> ev.held.txt, flow |-> ev.held.flow]
      [] ev.op = "ticket" -> A!Ticket(Val(ev.v)) = ev.text
      [] ev.op = "parse" -> LET r == A!Parse(ev.s, CPOf(ev))
                            IN Covered(ev) /\ r.ok = ev.ok /\ (ev.ok => r.v = Val(ev.v))
      [] OTHER -> FALSE

Init == x = 0
Next == UNCHANGED x
TraceSpec == Init /\ [][Next]_x

AllOK == /\ \A k \in DOMAIN Trace : Trace[k].t = "addr" /\ EvOK(Trace[k])
         \* an address with a flow label was given to with_direct
         /\ \E k \in DOMAIN Trace : Trace[k].op = "direct" /\ Trace[k].a.flow # 0
=============================================================================
