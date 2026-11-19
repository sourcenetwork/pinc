----------------------------- MODULE ConnectFlight -----------------------------
(***************************************************************************)
(* Model check of the candidate paths of a flight: pinc-connect            *)
(* client/flight.rs, Connectivity::candidates_for (with dial.rs            *)
(* flight_relays), on a systematic domain of what it reads: caller hints   *)
(* (none, one, a repeat, one that a beacon or the record also lists, 4,    *)
(* 12, 16 and 17 distinct), a beacon (none, one, one shared with a hint,   *)
(* the full 4), a record (none; or no, one, overlapping and the full 8     *)
(* addresses, fresh or stale, homed on no known relay, on relay 0 or on    *)
(* relay 1), the node itself a relay or not, the home relay none, 1, or    *)
(* at position 300 (past a u8), and fwd either way. The list is the code's *)
(* own: 16 entries at most (`[Cand; 16]`).                                 *)
(*                                                                         *)
(* Checked for every case (the docs of candidates_for and flight_relays):  *)
(*  - NoDupCap: at most 16 candidates, none twice (a relay named twice is  *)
(*    listed once);                                                        *)
(*  - UdpFirst: every address comes before every relay ("the caller's      *)
(*    addresses, then the peer's relay, then our home relay");             *)
(*  - HintsFirst: the list starts with the caller's distinct addresses in  *)
(*    their order;                                                         *)
(*  - Sources: every candidate is a hint, a beacon address, an address of  *)
(*    a usable record, the peer's relay (the node itself, or the record's  *)
(*    home) or, for a dial with fwd, our home relay;                       *)
(*  - StaleLeftOut: with fresh_at set, the addresses of a stale record are *)
(*    left out (only hints and beacon addresses remain);                   *)
(*  - Complete: when the distinct candidates fit in 16, every one is       *)
(*    listed, so a stale or missing record still leaves the relay paths;   *)
(*  - RelayOrder: the peer's relay comes before ours.                      *)
(* Witness ConnectFlight_w_cut: RelayKept (a relay that applies is listed) *)
(* is violated: 16 caller addresses fill the list and the relay paths fall *)
(* off. The docs do not promise the relays a place; the witness shows the  *)
(* cap is reached and what it cuts.                                        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, ConnectFlightOps

VARIABLE x

Hn(p, lo, hi) == [i \in 1..(hi - lo + 1) |-> p \o ToString(lo + i - 1)]

HINTS == {<<>>, <<"a1">>, <<"a1", "a1">>, <<"a2", "a1">>, <<"b1">>, <<"r1">>,
          Hn("h", 1, 4), Hn("h", 1, 12), Hn("h", 1, 16), Hn("h", 1, 17)}
BEACONS == {<<>>, <<"b1">>, <<"b1", "a1">>, Hn("b", 1, 4)}
RECS == {<<>>, <<"r1">>, <<"r1", "b1", "a1">>, Hn("r", 1, 8)}

NoRec == [hasRec : {FALSE}, rec : {<<>>}, fresh : {TRUE}, recHome : {NOREL}]
SomeRec == [hasRec : {TRUE}, rec : RECS, fresh : BOOLEAN, recHome : {NOREL, 0, 1}]

Ins == {[hints |-> h, beacon |-> b, hasRec |-> r.hasRec, rec |-> r.rec, fresh |-> r.fresh, recHome |-> r.recHome,
         peer |-> p, home |-> hm, fwd |-> f] :
        h \in HINTS, b \in BEACONS, r \in NoRec \cup SomeRec, p \in {NOREL, 2}, hm \in {NOREL, 1, 300}, f \in BOOLEAN}

Init == x = [t |-> "root"]
Next == x.t = "root" /\ \E i \in Ins : x' = [t |-> "case", v |-> i]
Spec == Init /\ [][Next]_x

Range(s) == {s[i] : i \in 1..Len(s)}
Out == CandidatesFor(x.v)

RECURSIVE Dedup(_, _)
Dedup(s, acc) == IF s = <<>> THEN acc ELSE Dedup(Tail(s), IF InSeq(acc, Head(s)) THEN acc ELSE Append(acc, Head(s)))

RelSpec(v) == (IF PeerRelay(v) # NOREL THEN {PeerRelay(v)} ELSE {}) \cup (IF OwnRelay(v) # NOREL THEN {OwnRelay(v)} ELSE {})
AllIn(v) == {U(a) : a \in Range(v.hints) \cup Range(v.beacon) \cup Range(UsableRec(v))} \cup {Rl(r) : r \in RelSpec(v)}

NoDupCap == x.t = "case" =>
    /\ Len(Out) <= CAP
    /\ \A i, j \in 1..Len(Out) : i # j => Out[i] # Out[j]

UdpFirst == x.t = "case" =>
    \A i, j \in 1..Len(Out) : (i < j /\ Out[i].k = "r") => Out[j].k = "r"

HintsFirst == x.t = "case" =>
    LET dh == Dedup(x.v.hints, <<>>)
    IN \A i \in 1..Len(dh) : i <= CAP => (i <= Len(Out) /\ Out[i] = U(dh[i]))

Sources == x.t = "case" =>
    \A i \in 1..Len(Out) :
        IF Out[i].k = "u" THEN Out[i].a \in Range(x.v.hints) \cup Range(x.v.beacon) \cup Range(UsableRec(x.v))
        ELSE Out[i].r \in RelSpec(x.v)

StaleLeftOut == x.t = "case" =>
    ((x.v.hasRec /\ ~x.v.fresh) =>
        \A i \in 1..Len(Out) : Out[i].k = "u" => Out[i].a \in Range(x.v.hints) \cup Range(x.v.beacon))

Complete == x.t = "case" =>
    (Cardinality(AllIn(x.v)) <= CAP => AllIn(x.v) \subseteq Range(Out))

RelayOrder == x.t = "case" =>
    \A i, j \in 1..Len(Out) :
        (Out[i].k = "r" /\ Out[j].k = "r" /\ Out[i].r = OwnRelay(x.v) /\ Out[j].r = PeerRelay(x.v)
         /\ PeerRelay(x.v) # OwnRelay(x.v)) => j < i

\* the reachability witness of the cap
RelayKept == x.t = "case" => (RelSpec(x.v) # {} => \E i \in 1..Len(Out) : Out[i].k = "r")
=============================================================================
