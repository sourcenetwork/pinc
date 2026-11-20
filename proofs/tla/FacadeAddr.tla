------------------------------- MODULE FacadeAddr -------------------------------
(***************************************************************************)
(* Node ids as text and the one-line ticket of a node's address:           *)
(* crates/pinc/src/addr.rs (`node_to_string`, `node_from_str`,             *)
(* `NodeAddr::with_direct`, `with_relay`, `ticket`, `parse`), with the     *)
(* operators of FacadeAddrOps.tla at NB = 1 byte a node id (32 scaled).    *)
(*                                                                         *)
(* Cases (a machine whose root has one successor per case):                *)
(*  - "id": every algorithm tag 1..4 with node bytes from a sample:        *)
(*    NodeRT (node_from_str(node_to_string(id)) = id);                     *)
(*  - "str": texts made of a tag part (none, "00." .. "05.", "0a.", "0A.", *)
(*    "1.", "+1.") and a hex part (lower, upper, short, long, signed, not  *)
(*    hex): NodeCanon, the doc of node_from_str ("exactly what             *)
(*    node_to_string prints, so one id has one text"): an accepted text is *)
(*    the text of the id it gives;                                         *)
(*  - "relay": every url of at most 4 characters over h : / , @ (781):     *)
(*    GuardExact (with_relay accepts a url exactly when a ticket with that *)
(*    one relay reads back the same value);                                *)
(*  - "addr": NodeAddr values of two ids, up to two direct addresses (an   *)
(*    IPv4 and an IPv6 one given to with_direct with IPv6 flowinfo in      *)
(*    FLOWS) and up to two relays accepted by with_relay: RoundTrip (the   *)
(*    module doc: "printing then parsing returns the same value for a      *)
(*    NodeAddr built through its functions"); with RAW also struct         *)
(*    literals (public fields: any string as a relay, a flow label kept),  *)
(*    which the doc excepts ("a struct literal can hold what the text form *)
(*    cannot carry").                                                      *)
(* The core library's SocketAddr parse is cp: the two address texts, read  *)
(* with flowinfo 0 (the text of a SocketAddrV6 has no flowinfo).           *)
(*                                                                         *)
(* FacadeAddr.cfg checks NodeRT, NodeCanon, NodeAccepts (what              *)
(* node_from_str accepts, written apart from it), GuardExact and RoundTrip *)
(* on values built through the API with flowinfo 0 and 1. Before the       *)
(* facade fixes (F11, F12) "01.<hex>" was a second text of an Ed25519 id   *)
(* (NodeCanon failed, and NodeAccepts, written to the code, accepted it)   *)
(* and with_direct kept the flow label the ticket drops (RoundTrip failed  *)
(* at flowinfo 1). Witness FacadeAddr_raw (TLC must violate RoundTrip): a  *)
(* struct literal can hold what the text form cannot carry, the exception  *)
(* the doc states since F13.                                               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS FLOWS, RAW
ASSUME FLOWS \subseteq {0, 1} /\ 0 \in FLOWS /\ RAW \in BOOLEAN

A == INSTANCE FacadeAddrOps WITH NB <- 1

\* texts
Addr4 == <<49, 58, 50>>                     \* "1:2"
Addr6 == <<91, 58, 58, 49, 93, 58, 50>>     \* "[::1]:2"
CP == [t \in {Addr4, Addr6} |-> [txt |-> t, flow |-> 0]]

IdSample == {[alg |-> a, bytes |-> <<b>>] : a \in 1..4, b \in {0, 9, 10, 171, 255}}
TagParts == {<<>>} \cup {t \o <<46>> : t \in {<<48, 48>>, <<48, 49>>, <<48, 50>>, <<48, 52>>, <<48, 53>>,
                                              <<48, 97>>, <<48, 65>>, <<49>>, <<43, 49>>}}
HexParts == {<<48, 48>>, <<97, 98>>, <<65, 66>>, <<97>>, <<97, 98, 99>>, <<43, 97>>, <<103, 48>>, <<57, 102>>}
Strs == {t \o x : t \in TagParts, x \in HexParts} \cup {<<46>>, <<46, 97, 98>>, <<>>}

Alpha == {104, 58, 47, 44, 64}
Urls == UNION {[1..n -> Alpha] : n \in 0..4}

N1 == [alg |-> 1, bytes |-> <<171>>]
N2 == [alg |-> 2, bytes |-> <<9>>]
Directs == {[txt |-> Addr4, flow |-> 0]} \cup {[txt |-> Addr6, flow |-> f] : f \in FLOWS}
\* what with_direct holds of them
ApiDirects == {A!WithDirect(d) : d \in Directs}
\* relays with_relay accepts: "h://", "://@", "h://h"; RAW adds what the public field may hold: "", "h", "h://,h"
Relays == {<<104, 58, 47, 47>>, <<58, 47, 47, 64>>, <<104, 58, 47, 47, 104>>}
          \cup (IF RAW THEN {<<>>, <<104>>, <<104, 58, 47, 47, 44, 104>>} ELSE {})
Upto2(S) == {<<>>} \cup {<<x>> : x \in S} \cup {<<x, y>> : x, y \in S}
Values == {[node |-> n, direct |-> d, relays |-> r] :
              n \in {N1, N2}, d \in Upto2(IF RAW THEN Directs ELSE ApiDirects), r \in Upto2(Relays)}

Cases == {[k |-> "id", id |-> i] : i \in IdSample}
         \cup {[k |-> "str", s |-> s] : s \in Strs}
         \cup {[k |-> "relay", u |-> u] : u \in Urls}
         \cup {[k |-> "addr", v |-> v] : v \in Values}

VARIABLE cs
Init == cs = [k |-> "root"]
Next == cs.k = "root" /\ \E c \in Cases : cs' = c
Spec == Init /\ [][Next]_cs

NodeRT == cs.k = "id" => A!NodeFromStr(A!NodeToString(cs.id)) = [ok |-> TRUE, v |-> cs.id]
NodeCanon == cs.k = "str" =>
    LET r == A!NodeFromStr(cs.s) IN r.ok => A!NodeToString(r.v) = cs.s
\* what the code accepts, written apart from it: a 2-digit lowercase tag of a known algorithm other than Ed25519 and
\* a dot, or none, then 2 * NB lowercase hex digits
NodeAccepts == cs.k = "str" =>
    LET s == cs.s
        ok == \/ A!IsLowerHex(s, 2)
              \/ Len(s) = 5 /\ s[3] = 46 /\ SubSeq(s, 1, 2) \in {A!Hex2(t) : t \in 2..4} /\ A!IsLowerHex(SubSeq(s, 4, 5), 2)
    IN A!NodeFromStr(s).ok = ok
GuardExact == cs.k = "relay" =>
    LET v == [node |-> N1, direct |-> <<>>, relays |-> <<cs.u>>]
    IN A!RelayOK(cs.u) = (A!Parse(A!Ticket(v), CP) = [ok |-> TRUE, v |-> v])
RoundTrip == cs.k = "addr" => A!Parse(A!Ticket(cs.v), CP) = [ok |-> TRUE, v |-> cs.v]
=============================================================================
