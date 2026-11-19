---------------------------- MODULE ConnectFlightOps ----------------------------
(***************************************************************************)
(* The candidate paths of a flight (pinc-connect client/flight.rs,         *)
(* Connectivity::candidates_for, with dial.rs flight_relays) as pure       *)
(* operators over the tables the function reads. ConnectFlight.tla (the    *)
(* model check) and TraceConnectFlight.tla (the trace validation) use      *)
(* them.                                                                   *)
(*                                                                         *)
(* The input `v` is what candidates_for reads:                            *)
(*   hints    the caller's addresses, in order                             *)
(*   beacon   the addresses of the local beacon heard from the node, in    *)
(*            order (<<>> when none was heard)                             *)
(*   hasRec   whether a record was found for the node (`found`)            *)
(*   rec      that record's addresses, in order                            *)
(*   fresh    fresh_at is none, or the record is fresh at it (found_fresh) *)
(*   peer     relay_of(node): the node's position in the relay table, -1   *)
(*   recHome  relay_of(found.home), -1 when no record or not a relay we    *)
(*            know; read from the record whether or not it is fresh        *)
(*   home     the home relay, -1 when none                                 *)
(*   fwd      the dial started without a usable record (RELAY_FWD)         *)
(* An address is a non-empty string (a name in the model, the address's    *)
(* text in the trace; TLC refuses to compare a string with a number, so    *)
(* every field keeps one type). A candidate is a record: k "u" with the    *)
(* address a, or k "r" with the relay position r.                          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CAP == 16
NOREL == -1

U(a) == [k |-> "u", a |-> a, r |-> NOREL]
Rl(r) == [k |-> "r", a |-> "", r |-> r]

InSeq(s, v) == \E i \in 1..Len(s) : s[i] = v

(* the `add` closure: append when there is room and the candidate is not listed yet *)
Add(out, c) == IF Len(out) < CAP /\ ~InSeq(out, c) THEN Append(out, c) ELSE out
RECURSIVE AddAll(_, _)
AddAll(out, cs) == IF cs = <<>> THEN out ELSE AddAll(Add(out, Head(cs)), Tail(cs))

Udps(as) == [i \in 1..Len(as) |-> U(as[i])]
Rls(rs) == [i \in 1..Len(rs) |-> Rl(rs[i])]

(* u8::try_from(r).ok() *)
Byte(r) == IF r >= 0 /\ r < 256 THEN r ELSE NOREL

(* dial.rs flight_relays: the peer's relay, then ours when it differs; a relay named twice once *)
FlightRelays(peer, own) ==
    IF peer # NOREL /\ own # NOREL /\ peer # own THEN <<peer, own>>
    ELSE IF peer # NOREL THEN <<peer>>
    ELSE IF own # NOREL THEN <<own>>
    ELSE <<>>

PeerRelay(v) == Byte(IF v.peer # NOREL THEN v.peer ELSE v.recHome)
OwnRelay(v) == IF v.fwd THEN Byte(v.home) ELSE NOREL
UsableRec(v) == IF v.hasRec /\ v.fresh THEN v.rec ELSE <<>>

(* Connectivity::candidates_for *)
CandidatesFor(v) ==
    LET s1 == AddAll(<<>>, Udps(v.hints))
        s2 == AddAll(s1, Udps(v.beacon))
        s3 == AddAll(s2, Udps(UsableRec(v)))
    IN AddAll(s3, Rls(FlightRelays(PeerRelay(v), OwnRelay(v))))
=============================================================================
