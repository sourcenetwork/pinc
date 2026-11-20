-------------------------- MODULE TraceResponderLimit --------------------------
(***************************************************************************)
(* Trace validation of the responder's handshake limit and hold            *)
(* (pinc-transport conn/handshake.rs RESPONDER_HOLD, handshake_limit,      *)
(* handshake_end, the hold set in `step`) against ResponderLimit.tla.      *)
(*                                                                         *)
(* The Rust test tests/trace_responder_limit.rs makes a real responder     *)
(* connection at tick 0 and drives it in ticks of 10 s (the model's        *)
(* tick: the connect limit of 30 s is Base = 3, RESPONDER_HOLD of 60 s is  *)
(* Hold = 6). The dialer's first flight reaches it at tick 0, at tick 1 or *)
(* never (answerAt); or only a short Initial of a prekey it does not hold  *)
(* does, which it rejects (rejectAt); the dialer's Finish is held back and *)
(* handed over at tick finishAt (one round trip, two, the base plus two,   *)
(* or never). Each run starts with an "init" event giving those inputs in  *)
(* ticks (-1 for never) and then, for every tick 0..12, an "obs" event:    *)
(* after the inputs due at that tick and the responder's timers due by     *)
(* then, its state (open, done when the Finish was taken, gone when the    *)
(* handshake ran out) and whether it has answered.                         *)
(*                                                                         *)
(* The trace spec runs ResponderLimit's own actions from the recorded      *)
(* Init and requires every observation to be the model's state at that     *)
(* tick once the model has settled (no Finish or Expire is due); every     *)
(* state satisfies the invariants of ResponderLimit.cfg.                   *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds                       *)
(* responder_limit.ndjson.                                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLES t, rtt, answerAt, rejectAt, finishAt, armed, r, i
mvars == <<t, rtt, answerAt, rejectAt, finishAt, armed, r>>
vars == <<t, rtt, answerAt, rejectAt, finishAt, armed, r, i>>

\* The code's limits in ticks of 10 s, as ResponderLimit.cfg; the code's hold is fixed, held, and a reject starts none.
R == INSTANCE ResponderLimit WITH Base <- 3, Hold <- 6, Resend <- 2, MaxRtt <- 3, MaxT <- 12, Fixed <- TRUE,
                                  Held <- TRUE, RejectFree <- TRUE

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/responder_limit.ndjson")
Ev == Trace[i]

\* A recorded tick, -1 standing for never.
Tk(n) == IF n = -1 THEN R!Never ELSE n

Init == /\ i = 1 /\ t = 0 /\ rtt = 1 /\ answerAt = R!Never /\ rejectAt = R!Never /\ finishAt = R!Never /\ armed = 0
        /\ r = "open"

\* A run starts: ResponderLimit's Init with the recorded inputs, which must be among the ones it allows.
Start == /\ Ev.t = "init"
         /\ Ev.rtt \in 1..3
         /\ Tk(Ev.ans) \in {0, 1, R!Never} /\ Tk(Ev.rej) \in {0, 1, R!Never}
         /\ Tk(Ev.fin) \in {Ev.rtt, 2 * Ev.rtt, 3 + 2 * Ev.rtt, R!Never}
         /\ t' = 0 /\ r' = "open" /\ armed' = 0 /\ rtt' = Ev.rtt
         /\ answerAt' = Tk(Ev.ans) /\ rejectAt' = Tk(Ev.rej) /\ finishAt' = Tk(Ev.fin)
         /\ i' = i + 1

\* The model moves towards the next observation: a Finish or an expiry at this tick, or the next tick while the
\* observation is of a later one. At the end instant both may be due; the code hands the input over before the timers
\* due at that instant, so the expiry is taken there only when no Finish is due.
Model == /\ Ev.t = "obs"
         /\ \/ R!Finish \/ (R!Expire /\ ~R!FinishDue)
            \/ (R!Tick \/ R!Ignore) /\ Ev.tk > t
         /\ UNCHANGED i

\* Nothing more is due at this tick: neither a Finish (at the end instant too: an input there goes before the timers)
\* nor an expiry.
Settled == ~(R!FinishDue \/ R!ExpireDue)

\* The responder at tick t is the model's.
Obs == /\ Ev.t = "obs"
       /\ Ev.tk = t /\ Settled
       /\ Ev.r = r
       /\ (Ev.answered = 1) = R!Answered
       /\ UNCHANGED mvars /\ i' = i + 1

Done == i > Len(Trace) /\ UNCHANGED vars

TNext == (i <= Len(Trace) /\ (Start \/ Model \/ Obs)) \/ Done
TraceSpec == Init /\ [][TNext]_vars

\* the invariants of ResponderLimit.cfg, on every state of every run
Inv == R!HalfOpenBounded /\ R!SlowFinishHolds /\ R!UnansweredKeepsBase /\ R!RejectedKeepsBase
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
