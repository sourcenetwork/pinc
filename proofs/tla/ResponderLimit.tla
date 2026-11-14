---------------------------- MODULE ResponderLimit ----------------------------
(***************************************************************************)
(* How long a responder holds a half-open handshake once it has answered   *)
(* (vinc#387).                                                             *)
(* Code: crates/vinc-transport/src/conn/handshake.rs (RESPONDER_HOLD,      *)
(* Timing::connect_timeout, Handshake::step: the hold is set when the      *)
(* responder's flight first goes out), crates/vinc-core/src/slot.rs        *)
(* (Slot::half_open_life) and timers.rs (settle_core, run_timer: the       *)
(* endpoint's own half-open sweep follows the same life).                  *)
(*                                                                         *)
(* The story. A dialer behind a slow link starts a handshake. The          *)
(* responder makes a half-open session at tick 0 and gives up when its     *)
(* limit is exceeded. It answers (its flight goes out) at once, a little   *)
(* later (a key host that takes its time), or never. The Finish reaches it *)
(* after one path round trip, two, two plus a retransmission timeout as    *)
(* long as the base limit, or never (a dialer that only holds the session  *)
(* open). A responder that has answered holds the session Hold ticks from  *)
(* its creation, longer than the base limit; one that never answered keeps *)
(* the base limit. The hold is one fixed constant: nothing the peer sends  *)
(* moves it, so a stranger can make a half-open session cost at most Hold, *)
(* and the half-open cap bounds the table at the cap times Hold.           *)
(*                                                                         *)
(* What must never happen:                                                 *)
(*  HalfOpenBounded - a half-open session outlives Hold, whatever the      *)
(*  dialer does;                                                           *)
(*  SlowFinishHolds - a responder that answered drops a Finish that        *)
(*  arrives within Hold;                                                   *)
(*  UnansweredKeepsBase - a responder that never answered holds the        *)
(*  session past the base limit.                                           *)
(*                                                                         *)
(* Guards, each switched off by one RED configuration:                     *)
(*  Fixed - the hold counts from the session's creation and nothing moves  *)
(*  it (ResponderLimit_nocap: the hold is armed again at every resend of   *)
(*  the flight, so a dialer that keeps the responder resending holds the   *)
(*  session past Hold, HalfOpenBounded fails);                             *)
(*  Held - a responder that answered holds Hold, not the base              *)
(*  (ResponderLimit_nohold: the base limit expires before a slow dialer's  *)
(*  Finish delayed by one retransmission timeout, SlowFinishHolds fails).  *)
(***************************************************************************)
EXTENDS Integers

\* Base: the connect limit (CONNECT_TIMEOUT, HALF_OPEN_LIFE); Hold: RESPONDER_HOLD, HALF_OPEN_HOLD; Resend: the
\* responder's resend period; MaxRtt: the largest path round trip; MaxT: the last tick checked; Fixed, Held: the
\* guards (TRUE in the code).
CONSTANTS Base, Hold, Resend, MaxRtt, MaxT, Fixed, Held

\* t: the clock; rtt: the path round trip; answerAt: when the responder's flight first goes out; finishAt: when the
\* Finish arrives; armed: the instant the hold counts from; r: the responder ("open", "done" holding the session,
\* "gone" its handshake ran out).
VARIABLES t, rtt, answerAt, finishAt, armed, r
vars == <<t, rtt, answerAt, finishAt, armed, r>>

\* Never: an instant past every run.
Never == MaxT + 1

\* The responder has answered by now.
Answered == answerAt <= t

\* The responder's limit (Timing::connect_timeout, Slot::half_open_life): the base until it answered, then the hold
\* counted from creation (armed stays 0); without Held, the base throughout.
Limit == IF Answered /\ Held THEN armed + Hold ELSE Base

Init == /\ t = 0 /\ r = "open" /\ armed = 0
        /\ rtt \in 1..MaxRtt
        \* the flight goes out at once, a tick later (a slow key host), or never
        /\ answerAt \in {0, 1, Never}
        \* the Finish after one round trip, two, two plus a retransmission timeout as long as the base, or never
        /\ finishAt \in {rtt, 2 * rtt, Base + 2 * rtt, Never}

\* The clock moves on, unless the Finish or the expiry is due now. Without Fixed, every resend of an answered
\* responder arms the hold again from that instant.
Tick == /\ t < MaxT
        /\ ~(r = "open" /\ t = finishAt)
        /\ ~(r = "open" /\ t > Limit)
        /\ t' = t + 1
        /\ armed' = IF ~Fixed /\ Answered /\ r = "open" /\ t > answerAt /\ (t - answerAt) % Resend = 0
                    THEN t ELSE armed
        /\ UNCHANGED <<rtt, answerAt, finishAt, r>>

\* The Finish arrives while the handshake waits, after the responder answered: it holds the session.
Finish == /\ r = "open" /\ t = finishAt /\ Answered /\ t <= Limit
          /\ r' = "done" /\ UNCHANGED <<t, rtt, answerAt, finishAt, armed>>

\* The handshake runs out past its limit (the limit is exceeded, not reached).
Expire == /\ r = "open" /\ t > Limit
          /\ r' = "gone" /\ UNCHANGED <<t, rtt, answerAt, finishAt, armed>>

\* A Finish that comes before the responder answered is not one (the dialer cannot finish what it was never sent).
Ignore == /\ r = "open" /\ t = finishAt /\ ~Answered /\ t <= Limit /\ t < MaxT
          /\ t' = t + 1 /\ UNCHANGED <<rtt, answerAt, finishAt, armed, r>>

Next == Tick \/ Finish \/ Expire \/ Ignore
Spec == Init /\ [][Next]_vars

\* Every variable holds what it should.
TypeOK == /\ t \in 0..MaxT /\ rtt \in 1..MaxRtt /\ answerAt \in {0, 1, Never} /\ armed \in 0..MaxT
          /\ r \in {"open", "done", "gone"}

\* A half-open session never outlives the hold, the tick that passes it included.
HalfOpenBounded == r = "open" => t <= Hold + 1

\* A responder that answered takes a Finish that arrives within the hold.
SlowFinishHolds == (answerAt <= finishAt /\ finishAt <= Hold) => r # "gone"

\* A responder that never answered is not held past the base limit.
UnansweredKeepsBase == (answerAt = Never /\ r = "open") => t <= Base + 1
=============================================================================
