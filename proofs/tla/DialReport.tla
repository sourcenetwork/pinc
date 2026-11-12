----------------------------- MODULE DialReport -----------------------------
(***************************************************************************)
(* How long a dial reported before its handshake may stay up unanswered.   *)
(*                                                                         *)
(* Who acts. One peer, which can stop without a word (a killed process)    *)
(* and come back on the same address and identity as a new incarnation    *)
(* that holds none of the old sessions. Our endpoint, which dials it one   *)
(* dial at a time and may hold a cached allow from the access check (the   *)
(* dial is then "optimistic"). The host may keep the session a dial gave   *)
(* it, or drop it. Time moves in ticks.                                    *)
(*                                                                         *)
(* What can happen. A dial while the host holds a session rides it as a    *)
(* sub-session, reported at once (no round trip: the G-SURFACE gate). An   *)
(* optimistic dial is reported at once too, before its handshake, so its   *)
(* first data leaves in the first flight. Any other dial is reported when  *)
(* its handshake is done. A handshake to a running peer is done within Hs  *)
(* ticks. An optimistic connection whose handshake is not done within      *)
(* Bound ticks closes as timed out; an ordinary handshake gives up at      *)
(* Limit (the handshake's own 30 s).                                       *)
(*                                                                         *)
(* What must never happen:                                                 *)
(*  NoLingering  a connection reported to the host and never answered by   *)
(*               the peer is still up past Promise ticks after its dial;   *)
(*  ReachLive    a dial without a held session to a peer that ran the     *)
(*               whole time fails, or its connection is closed;            *)
(*  SubAtOnce    a dial over a held session waits.                         *)
(* What is not promised: a sub-session over a held session the peer no     *)
(* longer holds is reported and stays up until the idle timeout (telling   *)
(* would cost the round trip G-SURFACE forbids).                           *)
(*                                                                         *)
(* Rust: crates/vinc-core/src/commands.rs `connect` (the parent branch,    *)
(* the optimistic report and its bound: `EARLY_BOUND_*`,                   *)
(* `set_connect_deadline`); crates/vinc-transport/src/conn/hooks.rs        *)
(* `set_connect_deadline`, crates/vinc-transport/src/conn/handshake.rs     *)
(* `cap_connect_at`, `on_timer` (the deadline closes the handshake with    *)
(* `HandshakeTimeout`); crates/vinc-core/src/events.rs `on_closed` (a      *)
(* reported session that ends raises `Closed`).                            *)
(* Lean: none (no data structure changes; the decision is this machine).   *)
(*                                                                         *)
(* Witnesses (scripts/proofs.sh witness_tlc), one per guard:               *)
(*  _nobound  Bound = Limit, the code before the fix: an optimistic        *)
(*            connection to a stopped peer stays up for the handshake's    *)
(*            whole 30 s; NoLingering fails.                               *)
(*  _tight    Bound below the handshake time Hs: a running peer's          *)
(*            optimistic connection is closed before its handshake could   *)
(*            finish; ReachLive fails.                                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Hs,       \* the most ticks a handshake to a running peer takes
    Bound,    \* the ticks an optimistic connection waits for its handshake (8 round trips, 2 s to 10 s)
    Promise,  \* the ticks the host is promised an unanswered connection lasts at most (the documented bound)
    Limit,    \* the ticks any handshake waits before it gives up (30 s)
    MaxNow,   \* the last tick explored
    MaxInc    \* the most incarnations of the peer explored

VARIABLES
    now,      \* the current tick, from 1
    alive,    \* whether the peer runs
    inc,      \* the incarnation of the peer that runs (or ran last)
    cached,   \* whether our endpoint holds a cached allow for the peer
    held,     \* whether the host holds a session with the peer
    dial,     \* the dial: [st, at, sub, told, answered]
    steady    \* the peer ran without a break since the dial started

vars == <<now, alive, inc, cached, held, dial, steady>>

\* Every variable has the shape it should.
TypeOK ==
    /\ now \in 1..MaxNow
    /\ alive \in BOOLEAN /\ inc \in 1..MaxInc /\ cached \in BOOLEAN /\ held \in BOOLEAN
    /\ dial.st \in {"idle", "hs", "up", "failed", "closed"}
    /\ dial.at \in 1..MaxNow
    /\ dial.sub \in BOOLEAN /\ dial.told \in BOOLEAN /\ dial.answered \in BOOLEAN
    /\ steady \in BOOLEAN

Init ==
    /\ now = 1
    /\ alive = TRUE
    /\ inc = 1
    /\ cached = FALSE
    /\ held = FALSE
    \* `st`: "hs" handshaking, "up" a connection the host has, "failed" a dial error, "closed" the connection ended.
    \* `told`: the host was handed the connection; `answered`: the peer answered its handshake.
    /\ dial = [st |-> "idle", at |-> 1, sub |-> FALSE, told |-> FALSE, answered |-> FALSE]
    /\ steady = TRUE

\* Whether the dial's handshake is still waiting for the peer.
Waiting == dial.st \in {"hs", "up"} /\ ~dial.sub /\ ~dial.answered

\* The deadline of the waiting handshake: Bound ticks for one reported early, Limit for any other.
GiveUpAt == dial.at + (IF dial.told THEN Bound ELSE Limit)

\* A tick passes. A handshake to a running peer is done within Hs ticks, and the handshake's deadline fires on time,
\* so time does not pass either point while it is pending.
Tick ==
    /\ now < MaxNow
    /\ ~(Waiting /\ alive /\ now >= dial.at + Hs)
    /\ ~(Waiting /\ now >= GiveUpAt)
    /\ now' = now + 1
    /\ UNCHANGED <<alive, inc, cached, held, dial, steady>>

\* The peer stops without closing anything.
Stop ==
    /\ alive
    /\ alive' = FALSE
    /\ steady' = FALSE
    /\ UNCHANGED <<now, inc, cached, held, dial>>

\* The peer comes back on the same address and identity: a new incarnation, which holds none of our sessions.
Restart ==
    /\ ~alive /\ inc < MaxInc
    /\ alive' = TRUE
    /\ inc' = inc + 1
    /\ UNCHANGED <<now, cached, held, dial, steady>>

\* Our cached allow lapses, or a check answers and is cached again.
Cache ==
    /\ cached' = ~cached
    /\ UNCHANGED <<now, alive, inc, held, dial, steady>>

\* The host drops the session it held (or the idle timeout closes it).
DropHeld ==
    /\ held
    /\ held' = FALSE
    /\ UNCHANGED <<now, alive, inc, cached, dial, steady>>

\* A dial starts. Over a held session: a sub-session, handed over at once. Otherwise a handshake; an optimistic one is
\* handed over at once too.
Start ==
    /\ dial.st = "idle"
    /\ steady' = alive
    /\ dial' = [st |-> IF held \/ cached THEN "up" ELSE "hs", at |-> now, sub |-> held, told |-> held \/ cached,
                answered |-> FALSE]
    /\ UNCHANGED <<now, alive, inc, cached, held>>

\* The running peer answers the handshake: the connection is handed over (if it was not already) and is held.
HsDone ==
    /\ Waiting /\ alive
    /\ dial' = [dial EXCEPT !.st = "up", !.told = TRUE, !.answered = TRUE]
    /\ held' = TRUE
    /\ UNCHANGED <<now, alive, inc, cached, steady>>

\* The handshake reached its deadline unanswered: a connection handed over closes as timed out, a dial not handed
\* over fails.
GiveUp ==
    /\ Waiting /\ now >= GiveUpAt
    /\ dial' = [dial EXCEPT !.st = IF dial.told THEN "closed" ELSE "failed"]
    /\ UNCHANGED <<now, alive, inc, cached, held, steady>>

\* The host takes the result and may dial again.
Done ==
    /\ dial.st \in {"up", "failed", "closed"} /\ ~Waiting
    /\ dial' = [dial EXCEPT !.st = "idle"]
    /\ UNCHANGED <<now, alive, inc, cached, held, steady>>

Next == Tick \/ Stop \/ Restart \/ Cache \/ DropHeld \/ Start \/ HsDone \/ GiveUp \/ Done

Spec == Init /\ [][Next]_vars

\* A connection the host has, through a handshake the peer never answered, is gone by Promise ticks after its dial.
NoLingering == (dial.st = "up" /\ ~dial.sub /\ ~dial.answered) => now <= dial.at + Promise

\* A dial without a held session to a peer that ran the whole time neither fails nor has its connection closed.
ReachLive == (dial.st \in {"failed", "closed"} /\ ~dial.sub) => ~steady

\* A dial over a held session is handed over in the step it starts.
SubAtOnce == dial.sub => dial.st \in {"up", "idle"}
=============================================================================
