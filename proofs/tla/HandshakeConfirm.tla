---------------------------- MODULE HandshakeConfirm ----------------------------
(***************************************************************************)
(* A dialing side's wait for the peer to confirm a session (pinc#385).     *)
(* Code: crates/pinc-transport/src/conn/handshake.rs (Handshake::on_event  *)
(* arms `confirm_at` when a dialing side establishes; Handshake::on_timer  *)
(* ends it as `unconfirmed`; Handshake::confirm clears it on the first     *)
(* 1-RTT packet), crates/pinc-transport/src/conn/drive.rs Connection::pump *)
(* (closes with CloseReason::Unconfirmed).                                 *)
(*                                                                         *)
(* The story. A dialer sends a Hello; the responder opens a half-done      *)
(* handshake, replies, and gives up after RLimit. The dialer, on the       *)
(* reply, counts the session established and sends its Finish; the        *)
(* responder, on the Finish while it still waits, holds the session and    *)
(* answers with a 1-RTT packet, which confirms it to the dialer. Any       *)
(* message can be lost or take up to MaxDelay ticks. The dialer resends    *)
(* its Finish while it waits.                                              *)
(*                                                                         *)
(* What must never happen (HalfOpenBounded): the dialer holds a session    *)
(* the peer has not confirmed for longer than Limit ticks after it         *)
(* established. And the dialer ends a session as unconfirmed only when no  *)
(* confirmation ever reached it (ClosedOnlyUnconfirmed).                   *)
(*                                                                         *)
(* Guard switched off by the RED configuration HandshakeConfirm_nobound:   *)
(* Bound - the dialer ends the session Limit ticks after it established    *)
(* with no confirmation. Without it, a Finish that reaches the responder   *)
(* after its handshake ran out leaves the dialer holding a session nobody  *)
(* else holds until the (unmodelled) idle timeout.                         *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

\* Limit: the dialer's wait for confirmation; RLimit: the responder's handshake limit; MaxDelay: the longest a message
\* takes; MaxT: the last tick checked; Bound: the guard (TRUE in the code).
CONSTANTS Limit, RLimit, MaxDelay, MaxT, Bound

\* t: the clock; d: the dialer ("open" before the reply, "est" established, "conf" confirmed, "closed" ended
\* unconfirmed); dEst: when it established; r: the responder ("none", "open" waiting for the Finish, "done" holding the
\* session, "gone" its handshake ran out); rStart: when it opened; net: the messages on their way, each with the tick it
\* arrives at; acked: some confirmation ever reached the dialer.
VARIABLES t, d, dEst, r, rStart, net, acked
vars == <<t, d, dEst, r, rStart, net, acked>>

\* A message of kind k arriving at tick a.
Msg(k, a) == [k |-> k, a |-> a]
\* The possible arrival ticks of a message sent now.
Arrivals == {t + x : x \in 1..MaxDelay}

Init == /\ t = 0 /\ d = "open" /\ dEst = 0 /\ r = "none" /\ rStart = 0 /\ acked = FALSE
        \* the Hello is on its way (or lost: then nothing ever happens, which no property forbids)
        /\ net \in {{}} \cup {{Msg("hello", a)} : a \in {x : x \in 1..MaxDelay}}

\* Send a message of kind k: it arrives at some tick within MaxDelay, or is lost.
Send(k) == net' \in {net} \cup {net \cup {Msg(k, a)} : a \in Arrivals}

\* The clock moves on, unless a message is due now.
Tick == /\ t < MaxT
        /\ \A m \in net : m.a > t
        /\ t' = t + 1
        /\ UNCHANGED <<d, dEst, r, rStart, net, acked>>

\* A message due now arrives.
Deliver == \E m \in net : m.a = t /\
    LET rest == net \ {m} IN
    \/ /\ m.k = "hello" /\ r = "none"
       \* the responder opens and replies
       /\ r' = "open" /\ rStart' = t
       /\ net' \in {rest} \cup {rest \cup {Msg("reply", a)} : a \in Arrivals}
       /\ UNCHANGED <<t, d, dEst, acked>>
    \/ /\ m.k = "reply" /\ d = "open"
       \* the dialer establishes and sends its Finish (handshake.rs on_event: Stage::Finish, confirm_at)
       /\ d' = "est" /\ dEst' = t
       /\ net' \in {rest} \cup {rest \cup {Msg("finish", a)} : a \in Arrivals}
       /\ UNCHANGED <<t, r, rStart, acked>>
    \/ /\ m.k = "finish" /\ r \in {"open", "done"}
       \* the responder holds the session and answers with a 1-RTT packet
       /\ r' = "done"
       /\ net' \in {rest} \cup {rest \cup {Msg("ack", a)} : a \in Arrivals}
       /\ UNCHANGED <<t, d, dEst, rStart, acked>>
    \/ /\ m.k = "ack"
       \* a 1-RTT packet confirms the session to a dialer still waiting (handshake.rs confirm); one reaching a dialer
       \* that already ended changes nothing
       /\ acked' = (acked \/ d = "est")
       /\ d' = IF d = "est" THEN "conf" ELSE d
       /\ net' = rest
       /\ UNCHANGED <<t, dEst, r, rStart>>
    \/ /\ ~(m.k = "hello" /\ r = "none") /\ ~(m.k = "reply" /\ d = "open")
       /\ ~(m.k = "finish" /\ r \in {"open", "done"}) /\ m.k # "ack"
       \* anything else finds no one waiting for it and is dropped (a Finish after the responder gave up)
       /\ net' = rest
       /\ UNCHANGED <<t, d, dEst, r, rStart, acked>>

\* The responder's handshake runs out RLimit ticks after it opened.
RGiveUp == /\ r = "open" /\ t - rStart > RLimit /\ r' = "gone"
           /\ UNCHANGED <<t, d, dEst, rStart, net, acked>>

\* The dialer resends its Finish while it waits.
Resend == /\ d = "est" /\ Send("finish") /\ net' # net
          /\ UNCHANGED <<t, d, dEst, r, rStart, acked>>

\* handshake.rs on_timer: past Limit after it established with no confirmation, the dialer ends the session.
GiveUp == /\ Bound /\ d = "est" /\ t - dEst > Limit /\ d' = "closed"
          /\ UNCHANGED <<t, dEst, r, rStart, net, acked>>

\* Timers fire before the clock moves past them: a due give-up is taken at its tick.
Next == Deliver \/ RGiveUp \/ Resend \/ GiveUp
        \/ (Tick /\ ~ENABLED GiveUp /\ ~ENABLED RGiveUp)
Spec == Init /\ [][Next]_vars

\* Every variable holds what it should.
TypeOK == /\ t \in 0..MaxT /\ d \in {"open", "est", "conf", "closed"} /\ r \in {"none", "open", "done", "gone"}
          /\ acked \in BOOLEAN /\ \A m \in net : m.k \in {"hello", "reply", "finish", "ack"}

\* The dialer never holds an unconfirmed session past Limit ticks after it established, the tick that passes the
\* limit included (connect_deadline: the limit is exceeded, not reached, and the timer fires at that tick).
HalfOpenBounded == d = "est" => t - dEst <= Limit + 1

\* The dialer ends a session as unconfirmed only when no confirmation ever reached it.
ClosedOnlyUnconfirmed == d = "closed" => ~acked
=============================================================================
