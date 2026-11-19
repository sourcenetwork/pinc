------------------------------ MODULE EarlyOps ------------------------------
(***************************************************************************)
(* The buffer of packets that arrive before their keys, as the real code   *)
(* works it: pinc-transport conn/recv.rs (on_packet, on_short, hold_early, *)
(* handle_inner), conn/drive.rs (on_hs_event, drain_early), conn/life.rs   *)
(* (begin_close, release_buffers) and stream/datagram.rs (EarlyData).      *)
(* Early.tla checks them over every interleaving at small sizes;           *)
(* TraceEarly.tla replays the recorded calls of real connections and of    *)
(* the real buffer.                                                        *)
(*                                                                         *)
(* The state c of one connection: client (it dialed), ph (the phase:      *)
(* "hs" handshaking, "up" connected, "closed" for both Closing and         *)
(* Closed, which refuse alike), er (the 0-RTT receive keys exist), rv (the *)
(* 1-RTT receive keys exist), q (the packets held, oldest first), and the  *)
(* counters nb (early_buffered), nd (early_dropped), nu (undecryptable),   *)
(* nr (early_refused) and rx (bytes_received). A packet p has an id (its   *)
(* place in the order of arrival), a kind ("z" a 0-RTT long packet, "s" a  *)
(* 1-RTT short one) and a fate when it is opened: "open" (it               *)
(* authenticates), "fail" (it does not), "close" (it authenticates and its *)
(* frames close the connection) or, for a 0-RTT packet, "estonly" (it      *)
(* authenticates and carries ACK, CLOSE, REKEY, NEW_TICKETS or             *)
(* PATH_RESPONSE, a frame only an established session sends, which the     *)
(* frame scan of process_payload marks). Which keys open it is not         *)
(* modelled: a packet is opened by the keys its kind needs when they       *)
(* exist, and then its fate decides. The bytes are not modelled either,    *)
(* only dlen, the length of the datagram, which counts toward the          *)
(* amplification budget on arrival.                                        *)
(*                                                                         *)
(* Recv returns the result out: "held" (kept for later), "full" (it        *)
(* should have been kept and was refused), "undec" (not opened), "ok"      *)
(* (opened), "refused" (opened and dropped whole for a frame only an       *)
(* established session sends, #295) and "closed" (the connection was       *)
(* over), and the new state.                                               *)
(* room says whether the pool can hold the packet (a chunk is free and it  *)
(* fits one); a packet that is refused for want of room is counted as one  *)
(* that found the buffer full.                                             *)
(***************************************************************************)
EXTENDS Integers, Sequences

Early0(client) == [client |-> client, ph |-> "hs", er |-> FALSE, rv |-> FALSE, q |-> <<>>,
                   nb |-> 0, nd |-> 0, nu |-> 0, nr |-> 0, rx |-> 0]

\* begin_close and silent_close: release_buffers lets go of every packet held
Shut(c) == [c EXCEPT !.ph = "closed", !.q = <<>>]

\* hold_early: EarlyData::push keeps the packet while fewer than cap are held and the pool has room
HoldPkt(c, cap, room, p) ==
    IF Len(c.q) < cap /\ room
    THEN [out |-> "held", c |-> [c EXCEPT !.q = Append(c.q, p), !.nb = c.nb + 1]]
    ELSE [out |-> "full", c |-> [c EXCEPT !.nd = c.nd + 1]]

\* on_zero_rtt, and on_short with the 1-RTT keys in place: opened or refused, never held. A 0-RTT packet that opens
\* and carries a frame only an established session sends is dropped whole before any of its frames is applied, and
\* counted; the connection stays open (process_payload). A 1-RTT packet that opens ends the use of the early keys,
\* whatever its frames; one that fails is counted as undecryptable, a 0-RTT one is not.
Direct(c, p) ==
    IF p.kind = "z"
    THEN IF ~c.er \/ p.fate = "fail" THEN [out |-> "undec", c |-> c]
         ELSE IF p.fate = "estonly" THEN [out |-> "refused", c |-> [c EXCEPT !.nr = c.nr + 1]]
         ELSE [out |-> "ok", c |-> IF p.fate = "close" THEN Shut(c) ELSE c]
    ELSE IF p.fate = "fail" THEN [out |-> "undec", c |-> [c EXCEPT !.nu = c.nu + 1]]
         ELSE LET c1 == [c EXCEPT !.er = FALSE]
              IN [out |-> "ok", c |-> IF p.fate = "close" THEN Shut(c1) ELSE c1]

\* Whether on_packet keeps the packet for want of keys: a 0-RTT packet on a server in its handshake that has no
\* early keys yet, a 1-RTT packet in a handshake before the 1-RTT keys exist.
Eligible(c, p) ==
    /\ c.ph = "hs"
    /\ IF p.kind = "z" THEN ~c.er /\ ~c.client ELSE ~c.rv

\* handle_inner counts the datagram before any packet of it is looked at; a closed connection refuses it first
Recv(c, cap, room, p, dlen) ==
    IF c.ph = "closed" THEN [out |-> "closed", c |-> c]
    ELSE LET c1 == [c EXCEPT !.rx = c.rx + dlen]
         IN IF Eligible(c1, p) THEN HoldPkt(c1, cap, room, p)
            ELSE IF p.kind = "s" /\ ~c1.rv THEN [out |-> "undec", c |-> c1]
            ELSE Direct(c1, p)

\* on_hs_event, EarlyKeys: the server has the 0-RTT receive keys
EarlyKeys(c) == [c EXCEPT !.er = TRUE]

\* drain_early: the packets held, oldest first, each taken out and tried once; a close ends it and the packets
\* still held go with the rest. done lists the ids tried.
RECURSIVE DrainQ(_, _)
DrainQ(c, l) ==
    IF l = <<>> THEN [c |-> [c EXCEPT !.q = <<>>], done |-> <<>>]
    ELSE LET p == Head(l)
             x == Direct(c, p)
         IN IF x.c.ph = "closed" THEN [c |-> x.c, done |-> <<p.id>>]
            ELSE LET r == DrainQ(x.c, Tail(l)) IN [c |-> r.c, done |-> <<p.id>> \o r.done]

\* on_hs_event, Established: the 1-RTT keys are installed, then the held packets are drained. Only the
\* datagrams counted already (rx) are counted: a drained packet is not counted again.
Established(c) == DrainQ([c EXCEPT !.ph = "up", !.rv = TRUE], c.q)

Ids(l) == [i \in DOMAIN l |-> l[i].id]
=============================================================================
