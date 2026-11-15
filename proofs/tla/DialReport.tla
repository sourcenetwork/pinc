----------------------------- MODULE DialReport -----------------------------
(***************************************************************************)
(* How long a dial reported before its handshake may stay up unanswered,   *)
(* and why the early end never closes a dial to a peer that is running.    *)
(*                                                                         *)
(* Who acts. One peer, which can stop without a word (a killed process)    *)
(* and come back on the same address and identity as a new incarnation    *)
(* that holds none of the old sessions or tickets. Our endpoint, which     *)
(* dials it one dial at a time, may hold a cached allow from the access    *)
(* check (the dial is then "optimistic", reported at once) and may hold a  *)
(* ticket from an incarnation (the dial then resumes). The network, which  *)
(* loses any flight. The host, which keeps or drops sessions and may hold  *)
(* a dial's resends while it looks the peer's address up. Time moves in   *)
(* ticks; a first resend delay is First ticks and a round trip Rtt < First *)
(* (the first delay is at least twice the remembered round trip).          *)
(*                                                                         *)
(* What can happen. A dial sends its first flight and resends it after    *)
(* First, 2 First, 4 First ... ticks (the code's doubling). A resumed      *)
(* dial falls back to a full handshake at its third send, which restarts   *)
(* the schedule. A peer that answers with a reject (it lost our ticket)    *)
(* restarts the schedule too, with a fresh full flight. A held dial sends  *)
(* nothing; its timer looks again every tick. An optimistic dial on a node *)
(* that is not thin ends as "unanswered" when its timer fires after        *)
(* Flights flights went out with nothing heard from the peer; any dial     *)
(* ends once Limit ticks are exceeded, not when they are reached (the      *)
(* handshake's 30 s; twice that on a thin node: the code's deadline is the *)
(* start plus the limit plus one nanosecond, connect_deadline).            *)
(* Only the Limit end raises the node's handshake floor.                   *)
(*                                                                         *)
(* What must never happen:                                                 *)
(*  NoLingering    an optimistic dial to a peer that never answered, on a  *)
(*                 node that is not thin and never held, is still up past  *)
(*                 Promise ticks;                                          *)
(*  ReachLive      a dial to a peer that ran the whole time ends early     *)
(*                 although fewer than Flights of its flights since the    *)
(*                 peer was last heard were lost;                          *)
(*  ThinKeepsLimit a dial on a thin node ends early;                       *)
(*  FloorOnLimit   the floor moves for anything but a Limit end;           *)
(*  SubAtOnce      a dial over a held session waits;                       *)
(*  AnsweredOnlyHeard  the host is told the peer answered a dial whose     *)
(*                 peer it never heard (Connection::answered returns for a *)
(*                 peer that stopped);                                     *)
(*  AnsweredWhenDone   a dial whose handshake finished, or a sub-session   *)
(*                 whose peer was heard, is not told answered (answered    *)
(*                 waits for a peer that answered).                        *)
(*                                                                         *)
(* The answered report: a dial reported before its peer answered (the     *)
(* optimistic one, a sub-session) is told so, and told again with          *)
(* Event::Answered once the peer is heard on it; a dial reported after its *)
(* handshake is answered when it is reported. crates/vinc-core/src/        *)
(* events.rs `announce` (the first value) and `on_established` (the        *)
(* handshake of a reported dial ends), crates/vinc-core/src/rx.rs          *)
(* `deliver` (the first packet on an established, reported session),       *)
(* crates/vinc/src/conn.rs `Connection::answered`.                         *)
(*                                                                         *)
(* Rust: crates/vinc-core/src/commands.rs `connect` (the optimistic report *)
(* calls `end_unanswered`); crates/vinc-transport/src/conn/hooks.rs        *)
(* `end_unanswered`; crates/vinc-transport/src/conn/handshake.rs           *)
(* `EARLY_FLIGHTS`, `on_timer` (held, then early, then resend), `step`     *)
(* (a queued first flight counts), `feed` (a message from the peer resets  *)
(* the count), `on_event` (`ResumeRejected` restarts the schedule);        *)
(* crates/vinc-transport/src/conn/drive.rs `pump` (`Unanswered` or         *)
(* `HandshakeTimeout`); crates/vinc-core/src/events.rs `on_closed` (only   *)
(* `HandshakeTimeout` calls `note_timeout`, the floor).                    *)
(* Lean: none (no data structure changes; the decision is this machine).   *)
(*                                                                         *)
(* Witnesses (scripts/proofs.sh witness_tlc), one per guard:               *)
(*  _nobound   no early end, the code before #76: an optimistic dial to a  *)
(*             stopped peer stays up until Limit; NoLingering fails.       *)
(*  _fixed     the first fix: an end at a fixed time after the dial,       *)
(*             blind to the schedule; lost flights or a hold push a        *)
(*             running peer's answer past it; ReachLive fails.             *)
(*  _countheld a held timer counts as a flight: a long lookup ends a dial  *)
(*             that sent nothing; ReachLive fails.                         *)
(*  _noreset   a reject does not start the count again: the restarted     *)
(*             peer's dial ends while its full handshake is under way;     *)
(*             ReachLive fails.                                            *)
(*  _thin      the early end applies on a thin node; ThinKeepsLimit fails. *)
(*  _floor     the early end raises the floor; FloorOnLimit fails.         *)
(*  _answeratreport  the code before #493: a reported dial counts as       *)
(*             answered from the start, so a dial to a stopped peer looks  *)
(*             answered; AnsweredOnlyHeard fails.                          *)
(*  _noanswer  no Answered event: an optimistic dial whose handshake ends  *)
(*             stays unanswered; AnsweredWhenDone fails.                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    First,        \* the first resend delay, in ticks
    Rtt,          \* the round trip, in ticks (below First)
    Flights,      \* the unanswered flights after which an optimistic dial ends (the code's EARLY_FLIGHTS, 4)
    Promise,      \* the most ticks an optimistic dial to a silent peer is promised to last
    Limit,        \* the ticks any handshake waits before it gives up (the 30 s), twice that on a thin node
    MaxNow,       \* the last tick explored
    MaxInc,       \* the most incarnations of the peer explored
    Early,        \* the early end is built (FALSE: the code before #76)
    FixedBound,   \* 0, or the early end happens this many ticks after the dial whatever was sent (the first fix)
    CountHeld,    \* a held timer counts as a flight (a planted bug)
    HeardResets,  \* a message from the peer starts the count again (FALSE: a planted bug)
    EarlyOnThin,  \* the early end applies on a thin node too (a planted bug)
    FloorEarly,   \* the early end raises the floor (a planted bug)
    AnswerAtReport, \* a reported dial counts as answered from its report (the code before the answered report)
    AnswerEvent   \* the host is told when a dial reported early is answered (FALSE: a planted bug)

\* Assumption: the round trip is shorter than the first resend delay, as the code makes it (2 x the remembered RTT).
ASSUME Rtt < First

VARIABLES
    now,      \* the current tick, from 1
    alive,    \* whether the peer runs
    inc,      \* the incarnation of the peer that runs (or ran last)
    ticket,   \* the incarnation that gave us our ticket, 0 for none
    cached,   \* whether our endpoint holds a cached allow for the peer
    held,     \* whether the host holds a session with the peer
    d,        \* the dial (fields below)
    steady,   \* the peer ran without a break since the dial started
    floor,    \* how many times the node's handshake floor was raised
    limits    \* how many dials ended at Limit

vars == <<now, alive, inc, ticket, cached, held, d, steady, floor, limits>>

\* 2 to the power k, for the doubling of the resend delay.
RECURSIVE Pow2(_)
\* 1 for k = 0, else twice the power one lower.
Pow2(k) == IF k = 0 THEN 1 ELSE 2 * Pow2(k - 1)

\* How long a handshake on a thin node, or any other, waits before it gives up.
LimitOf(thin) == IF thin THEN 2 * Limit ELSE Limit

\* A dial that is idle: nothing started.
Idle == [st |-> "idle", at |-> 1, sub |-> FALSE, told |-> FALSE, early |-> FALSE, thin |-> FALSE, sends |-> 0,
         unheard |-> 0, lost |-> 0, next |-> 0, ans |-> 0, hold |-> FALSE, wasHeld |-> FALSE, resume |-> FALSE,
         tinc |-> 0, heard |-> FALSE, answered |-> FALSE, why |-> "none", told_ans |-> FALSE]

\* Every variable has the shape it should.
TypeOK ==
    /\ now \in 1..MaxNow
    /\ alive \in BOOLEAN /\ inc \in 1..MaxInc /\ ticket \in 0..MaxInc
    /\ cached \in BOOLEAN /\ held \in BOOLEAN /\ steady \in BOOLEAN
    /\ d.st \in {"idle", "hs", "up", "failed", "closed"}
    /\ d.why \in {"none", "early", "limit"}
    /\ floor \in Nat /\ limits \in Nat

Init ==
    /\ now = 1              \* time starts
    /\ alive = TRUE         \* the peer runs
    /\ inc = 1              \* as its first incarnation
    /\ ticket \in {0, 1}    \* we may hold a ticket it gave us, or not
    /\ cached \in BOOLEAN   \* we may hold a cached allow for it, or not
    /\ held = FALSE         \* the host holds no session yet
    /\ d = Idle             \* no dial yet
    /\ steady = TRUE        \* nothing has stopped
    /\ floor = 0            \* the floor was never raised
    /\ limits = 0           \* no dial ended at Limit

\* Whether the dial's handshake is still waiting for the peer.
Waiting == d.st \in {"hs", "up"} /\ ~d.sub /\ ~d.answered

\* Whether this dial may end early: built, asked for (optimistic), and not on a thin node unless the bug is planted.
MayEndEarly == Early /\ d.early /\ (~d.thin \/ EarlyOnThin)

\* The first fix's end: a fixed time after the dial, whatever the schedule did.
FixedDue == FixedBound > 0 /\ MayEndEarly /\ now >= d.at + FixedBound

\* The flight `dd` sends now, lost by the network (`lose`) or not: it counts as unheard; one that is not lost and
\* reaches a running peer brings an answer Rtt ticks later (the earliest pending answer is the one kept).
Send(dd, lose) ==
    [dd EXCEPT !.unheard = @ + 1,                                       \* one more flight with nothing heard
               !.lost = IF lose THEN @ + 1 ELSE @,                     \* the network lost it
               !.ans = IF ~lose /\ alive /\ @ = 0 THEN now + Rtt ELSE @]  \* else a running peer answers it

\* A tick passes. Pending events happen on time: time does not pass a due timer, answer, Limit or fixed end.
Tick ==
    /\ now < MaxNow                                   \* within the explored time
    /\ ~(Waiting /\ now >= d.next)                    \* the resend timer is not due
    /\ ~(Waiting /\ d.ans > 0 /\ now >= d.ans)        \* no answer is due
    /\ ~(Waiting /\ now > d.at + LimitOf(d.thin))     \* Limit is not exceeded
    /\ ~(Waiting /\ FixedDue)                         \* the fixed end is not due
    /\ now' = now + 1                                 \* one tick on
    /\ UNCHANGED <<alive, inc, ticket, cached, held, d, steady, floor, limits>>

\* The peer stops without closing anything; an answer it had not sent yet never comes.
Stop ==
    /\ alive                                          \* it runs
    /\ alive' = FALSE                                 \* and stops
    /\ steady' = FALSE                                \* so the dial no longer faces a steady peer
    /\ d' = [d EXCEPT !.ans = 0]                      \* its pending answer is gone
    /\ UNCHANGED <<now, inc, ticket, cached, held, floor, limits>>

\* The peer comes back as a new incarnation, which holds none of our sessions or tickets.
Restart ==
    /\ ~alive /\ inc < MaxInc                         \* it is down, and we explore one more incarnation
    /\ alive' = TRUE                                  \* it runs again
    /\ inc' = inc + 1                                 \* as a new incarnation
    /\ held' = FALSE                                  \* a session the host held is dead (the host learns it later)
    /\ UNCHANGED <<now, ticket, cached, d, steady, floor, limits>>

\* Our cached allow lapses, or a check answers and is cached again.
Cache ==
    /\ cached' = ~cached                              \* flips
    /\ UNCHANGED <<now, alive, inc, ticket, held, d, steady, floor, limits>>

\* The host drops the session it held.
DropHeld ==
    /\ held                                           \* it holds one
    /\ held' = FALSE                                  \* and lets it go
    /\ UNCHANGED <<now, alive, inc, ticket, cached, d, steady, floor, limits>>

\* The host holds a waiting dial's resends while it looks the address up, or lets them go.
Hold ==
    /\ Waiting                                        \* only a waiting dial
    /\ d' = [d EXCEPT !.hold = ~@, !.wasHeld = TRUE]  \* flips the hold, and remembers there was one
    /\ UNCHANGED <<now, alive, inc, ticket, cached, held, steady, floor, limits>>

\* A dial starts. Over a held session: a sub-session, handed over at once. Otherwise a handshake that sends its first
\* flight now (the network may lose it): reported at once when optimistic, resumed when we hold a ticket, on a node
\* that is thin or not.
Start ==
    /\ d.st = "idle"                                  \* no dial running
    /\ steady' = alive                                \* the peer is steady from here only if it runs now
    /\ \E thin \in BOOLEAN, lose \in BOOLEAN :        \* the node may be thin; the first flight may be lost
        d' = IF held
             THEN [Idle EXCEPT !.st = "up", !.at = now, !.sub = TRUE, !.told = TRUE,  \* a sub-session, at once
                               !.told_ans = AnswerAtReport]  \* not answered yet, unless the old rule is planted
             ELSE Send([Idle EXCEPT !.st = IF cached THEN "up" ELSE "hs",  \* optimistic: handed over now
                                    !.at = now,                             \* when it began
                                    !.told = cached,                        \* the host has it if optimistic
                                    !.early = cached,                       \* and then it may end early
                                    !.told_ans = cached /\ AnswerAtReport,  \* reported unanswered (old rule: answered)
                                    !.thin = thin,                          \* the node's kind
                                    !.sends = 1,                            \* one send so far
                                    !.next = now + First,                   \* the first resend
                                    !.resume = ticket > 0,                  \* a resume if we hold a ticket
                                    !.tinc = ticket], lose)                 \* from that incarnation
    /\ UNCHANGED <<now, alive, inc, ticket, cached, held, floor, limits>>

\* An answer arrives. From an incarnation that lost our ticket: a reject, which counts as heard, sends a full flight
\* now and restarts the schedule. Otherwise the handshake is done and the host has the session.
Answer ==
    /\ Waiting /\ d.ans > 0 /\ now >= d.ans /\ alive  \* a pending answer is due and the peer runs
    /\ IF d.resume /\ d.tinc /= inc
       THEN \E lose \in BOOLEAN :                     \* the reject; the fresh flight may be lost
                d' = Send([d EXCEPT !.ans = 0,                                  \* the answer is used
                                    !.heard = TRUE,                             \* the peer was heard
                                    !.lost = 0,                                 \* losses count from here
                                    !.unheard = IF HeardResets THEN 0 ELSE @,   \* the count starts again
                                    !.sends = 1,                                \* the schedule restarts
                                    !.next = now + First,                       \* with the first delay
                                    !.resume = FALSE], lose)                    \* now a full handshake
            /\ UNCHANGED <<ticket, held>>
       ELSE /\ d' = [d EXCEPT !.st = "up", !.told = TRUE, !.answered = TRUE, !.heard = TRUE, !.ans = 0,  \* done
                              \* a dial reported now is answered with its report; one reported early hears Answered
                              !.told_ans = IF d.told THEN (@ \/ AnswerEvent) ELSE TRUE]
            /\ held' = TRUE                           \* the host holds the session
            /\ ticket' = inc                          \* and the peer gives us a ticket
    /\ UNCHANGED <<now, alive, inc, cached, steady, floor, limits>>

\* The resend timer fires (the code's `on_timer`, in its order). Held: look again next tick (a planted bug counts it
\* as a flight). Else, an optimistic dial with Flights unheard flights ends early. Else the flight goes again; the
\* third send of a resume is the fallback to a full handshake, which restarts the schedule.
Fire ==
    /\ Waiting /\ now >= d.next /\ ~FixedDue          \* the timer is due
    /\ IF d.hold
       THEN /\ d' = [d EXCEPT !.next = now + 1,                             \* look again
                              !.unheard = IF CountHeld THEN @ + 1 ELSE @]  \* nothing sent, nothing counted
            /\ UNCHANGED <<floor>>
       ELSE IF FixedBound = 0 /\ MayEndEarly /\ d.unheard >= Flights
       THEN /\ d' = [d EXCEPT !.st = "closed", !.why = "early"]            \* ends as unanswered
            /\ floor' = IF FloorEarly THEN floor + 1 ELSE floor             \* the floor stays (unless planted)
       ELSE /\ \E lose \in BOOLEAN :                                        \* the resend may be lost
                LET fb == d.resume /\ d.sends + 1 = 3 IN                    \* the resume's fallback send
                d' = Send([d EXCEPT !.sends = IF fb THEN 1 ELSE @ + 1,      \* a fallback restarts the count
                                    !.next = now + (IF fb THEN First ELSE First * Pow2(d.sends)),  \* doubles
                                    !.resume = IF fb THEN FALSE ELSE @], lose)  \* now full after a fallback
            /\ UNCHANGED <<floor>>
    /\ UNCHANGED <<now, alive, inc, ticket, cached, held, steady, limits>>

\* The peer answers what a sub-session sends: its first packet on the sub-session arrives. Only a peer that runs, and
\* still holds the session the sub-session was opened over (a restart lost it), answers.
SubHeard ==
    /\ d.sub /\ d.st = "up" /\ ~d.heard               \* a sub-session not heard from yet
    /\ alive /\ held                                  \* its peer runs and holds the parent
    /\ d' = [d EXCEPT !.heard = TRUE,                  \* the peer was heard
                      !.told_ans = @ \/ AnswerEvent]    \* and the host is told it answered
    /\ UNCHANGED <<now, alive, inc, ticket, cached, held, steady, floor, limits>>

\* The first fix's end: at its fixed time, before anything else, held or not.
FixedEnd ==
    /\ Waiting /\ FixedDue                            \* the fixed time came
    /\ d' = [d EXCEPT !.st = "closed", !.why = "early"]  \* the dial ends
    /\ UNCHANGED <<now, alive, inc, ticket, cached, held, steady, floor, limits>>

\* Limit: a handshake still waiting gives up. A dial handed over closes, any other fails; the floor goes up.
GiveUp ==
    /\ Waiting /\ now > d.at + LimitOf(d.thin)        \* Limit was exceeded
    /\ d' = [d EXCEPT !.st = IF d.told THEN "closed" ELSE "failed", !.why = "limit"]  \* it ends
    /\ floor' = floor + 1                             \* the floor goes up
    /\ limits' = limits + 1                           \* counted as a Limit end
    /\ UNCHANGED <<now, alive, inc, ticket, cached, held, steady>>

\* The host takes the result and may dial again.
Done ==
    /\ d.st \in {"up", "failed", "closed"} /\ ~Waiting  \* the dial is over
    /\ d' = Idle                                      \* ready for the next
    /\ UNCHANGED <<now, alive, inc, ticket, cached, held, steady, floor, limits>>

Next == Tick \/ Stop \/ Restart \/ Cache \/ DropHeld \/ Hold \/ Start \/ Answer \/ SubHeard \/ Fire \/ FixedEnd \/ GiveUp \/ Done

Spec == Init /\ [][Next]_vars

\* An optimistic dial to a peer that never answered, on a node that is not thin and never held, is over by Promise
\* ticks after it began.
NoLingering ==
    (d.st = "up" /\ d.early /\ ~d.thin /\ ~d.heard /\ ~d.wasHeld /\ ~d.answered) => now <= d.at + Promise

\* A dial to a peer that ran the whole time ends early only if every one of its last Flights flights was lost.
ReachLive == (d.why = "early" /\ steady) => d.lost >= Flights

\* A thin node keeps its own Limit: no early end.
ThinKeepsLimit == d.why = "early" => ~d.thin

\* Only a Limit end raises the floor.
FloorOnLimit == floor = limits

\* A dial over a held session is handed over in the step it starts.
SubAtOnce == d.sub => d.st \in {"up", "idle"}

\* The host is told a dial was answered only once its peer was heard on it.
AnsweredOnlyHeard == d.told_ans => d.heard

\* A dial whose handshake finished, or a sub-session whose peer was heard, is told answered.
AnsweredWhenDone == (d.st = "up" /\ (d.answered \/ (d.sub /\ d.heard))) => d.told_ans
=============================================================================
