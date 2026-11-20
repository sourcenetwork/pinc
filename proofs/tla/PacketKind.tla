----------------------------- MODULE PacketKind -----------------------------
(***************************************************************************)
(* Which frames go in which kind of packet, as the receiver classifies a   *)
(* packet's frames and the builder chooses the kind of packet it seals     *)
(* (pinc-transport conn/recv.rs scan and Props, process_payload's early    *)
(* refusal and its follow_peer gate; conn/send.rs build_app's kind,        *)
(* can_build_app, early_client, fill_frames' gates).                       *)
(*                                                                         *)
(* Not restated here: the buffer of early packets and the fate of a 0-RTT  *)
(* packet once classified (Early.tla, which takes "carries a frame only an *)
(* established session sends" as an input), what a fill holds and in what *)
(* order, and that a handshake packet carries no frames (FramePack.tla).   *)
(* This module is the classification itself, frame by frame, and the      *)
(* agreement of the two ends on it.                                        *)
(*                                                                         *)
(* A packet is the sequence of its frames' kinds (Frames, the 19 variants  *)
(* of Frame). Scan folds recv.rs scan's arms over it. Decide is            *)
(* process_payload's first decision on a packet that opened: a 0-RTT       *)
(* packet (early) that carries ACK, CLOSE, REKEY, NEW_TICKETS or           *)
(* PATH_RESPONSE is refused whole (EarlyFrame), anything else goes on.     *)
(*                                                                         *)
(* The builder: a packet of the application space is 1-RTT (Short) when    *)
(* the 1-RTT send keys exist, 0-RTT for a dialing side in its handshake    *)
(* with early send keys, and none is built otherwise; the CLOSE packet is  *)
(* built only with the 1-RTT send keys. Fill(st) is what fill_frames may   *)
(* write in a state: never CLOSE or PADDING, ACK only with an             *)
(* acknowledgement pending, PATH_RESPONSE only with a challenge to answer, *)
(* NEW_TICKETS only with tickets to send, REKEY only with a key roll to    *)
(* send. Facts of every reachable state (FACTS), each read off the code:   *)
(* a dialing side has an acknowledgement or a response pending only after  *)
(* a 1-RTT packet opened (it is never handed 0-RTT packets: it holds no    *)
(* early receive keys), so only with the 1-RTT receive keys; keys.install  *)
(* sets the 1-RTT send and receive keys together; only a responder holds   *)
(* tickets to send; a key roll is sent only with the 1-RTT send keys; only *)
(* a dialing side holds early send keys (drive.rs on_hs_event).            *)
(*                                                                         *)
(* Checked over every packet of at most 2 frames and every state of the    *)
(* builder (2^8 x 2 of them):                                              *)
(*  EarlyRule     a 0-RTT packet is refused exactly when it carries one of *)
(*                the five frames (Props.established_only's doc);          *)
(*  ShortTakesAll a 1-RTT packet is never refused for its frames;          *)
(*  MoversRule    follow_peer runs exactly for a packet with STREAM,       *)
(*                DATAGRAM or WAKE, and takes it as a WAKE exactly when it *)
(*                carries one (Props.nonprobing's doc, path.rs module doc);*)
(*  OrderFree     the classification does not depend on the frames' order;*)
(*  SenderAgrees  in every reachable state where the builder seals a 0-RTT *)
(*                packet, no frame its fill may write makes the receiver   *)
(*                refuse it (with EarlyRule: no packet it builds is).      *)
(* Witness PacketKind_facts: without the facts SenderAgrees is violated (a *)
(* dialing side with an acknowledgement pending and no 1-RTT keys would    *)
(* put an ACK in a 0-RTT packet): the facts are what the agreement rests   *)
(* on, and the trace test checks them on real sessions.                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS FACTS

VARIABLE c

Frames == {"PADDING", "PING", "ACK", "RESET_STREAM", "STOP_SENDING", "STREAM", "MAX_STREAM_DATA", "MAX_STREAMS",
           "PATH_CHALLENGE", "PATH_RESPONSE", "CLOSE", "DATAGRAM", "MTU_ECHO", "SLEEP", "WAKE", "REKEY", "READY",
           "NEW_TICKETS", "EXTENSION"}
EstOnly == {"ACK", "CLOSE", "REKEY", "NEW_TICKETS", "PATH_RESPONSE"}
Movers == {"STREAM", "DATAGRAM", "WAKE"}

NoProps == [eliciting |-> FALSE, ping |-> FALSE, padding |-> FALSE, nonprobing |-> FALSE, wake |-> FALSE,
            est |-> FALSE]
\* scan, arm by arm
Arm(p, f) ==
    CASE f = "PADDING" -> [p EXCEPT !.padding = TRUE]
      [] f = "ACK" -> [p EXCEPT !.est = TRUE]
      [] f \in {"CLOSE", "REKEY", "NEW_TICKETS", "PATH_RESPONSE"} -> [p EXCEPT !.eliciting = TRUE, !.est = TRUE]
      [] f = "PING" -> [p EXCEPT !.eliciting = TRUE, !.ping = TRUE]
      [] f \in {"STREAM", "DATAGRAM"} -> [p EXCEPT !.eliciting = TRUE, !.nonprobing = TRUE]
      [] f = "WAKE" -> [p EXCEPT !.eliciting = TRUE, !.nonprobing = TRUE, !.wake = TRUE]
      [] OTHER -> [p EXCEPT !.eliciting = TRUE]
RECURSIVE ScanFrom(_, _, _)
ScanFrom(s, k, p) == IF k > Len(s) THEN p ELSE ScanFrom(s, k + 1, Arm(p, s[k]))
Scan(s) == ScanFrom(s, 1, NoProps)

\* process_payload on a packet that opened: "refused" is Drop::EarlyFrame (counted in early_refused)
Decide(early, s) == IF early /\ Scan(s).est THEN "refused" ELSE "applied"

Has(s, S) == \E k \in 1..Len(s) : s[k] \in S
Seqs == {<<>>} \cup {<<a>> : a \in Frames} \cup {<<a, b>> : a \in Frames, b \in Frames}

\* the builder's state: role, phase, the 1-RTT send and receive keys, early send keys, and what is pending
States == [client : BOOLEAN, phase : {"hs", "up"}, send : BOOLEAN, recv : BOOLEAN, esend : BOOLEAN,
           ackp : BOOLEAN, resp : BOOLEAN, tickets : BOOLEAN, rekey : BOOLEAN]
Reach(st) ==
    ~FACTS \/ (/\ (st.client /\ (st.ackp \/ st.resp)) => st.recv
               /\ st.recv = st.send
               /\ st.tickets => ~st.client
               /\ st.rekey => st.send
               /\ st.esend => st.client)
\* build_app's kind; "none" when can_build_app is false
Kind(st) == IF st.send THEN "short" ELSE IF st.client /\ st.phase = "hs" /\ st.esend THEN "zrtt" ELSE "none"
Fill(st) ==
    Frames \ ({"CLOSE", "PADDING"}
              \cup (IF st.ackp THEN {} ELSE {"ACK"})
              \cup (IF st.resp THEN {} ELSE {"PATH_RESPONSE"})
              \cup (IF st.tickets THEN {} ELSE {"NEW_TICKETS"})
              \cup (IF st.rekey THEN {} ELSE {"REKEY"}))

Init == c = 0
Next == UNCHANGED c
Spec == Init /\ [][Next]_c

EarlyRule == \A s \in Seqs : (Decide(TRUE, s) = "refused") = Has(s, EstOnly)
ShortTakesAll == \A s \in Seqs : Decide(FALSE, s) = "applied"
MoversRule == \A s \in Seqs : Scan(s).nonprobing = Has(s, Movers) /\ Scan(s).wake = Has(s, {"WAKE"})
OrderFree == \A a, b \in Frames : Scan(<<a, b>>) = Scan(<<b, a>>)
\* `c = 0` holds in every state; it makes this a state invariant, which TLC reports as violated (the witness
\* PacketKind_facts looks for that) instead of a constant found FALSE at start-up
SenderAgrees == c = 0 /\
    \A st \in States : (Reach(st) /\ Kind(st) = "zrtt") => \A f \in Fill(st) : Decide(TRUE, <<f>>) = "applied"
=============================================================================
