----------------------------- MODULE DialReport -----------------------------
(***************************************************************************)
(* When a dial may say "connected".                                        *)
(*                                                                         *)
(* Who acts. One peer, which can stop without a word (a killed process)    *)
(* and come back on the same address and identity as a new incarnation    *)
(* that holds none of the old sessions. Our endpoint, which dials it one   *)
(* dial at a time and remembers an allow from the access check (the 30 s   *)
(* cache: a dial with it is "optimistic"). The host may keep the session   *)
(* a dial gave it, or drop it. Time moves in ticks.                        *)
(*                                                                         *)
(* What can happen. A dial while the host holds a session with the peer    *)
(* rides it as a sub-session and is reported at once (no round trip, the   *)
(* G-SURFACE gate). Any other dial runs a handshake. The handshake ends    *)
(* within Hs ticks when the peer runs; the peer's access check may refuse  *)
(* us; the connect timeout ends a dial that got nowhere. With EarlyReport  *)
(* (the endpoint's `early_report`, on in the core, off in the facade) an   *)
(* optimistic dial is reported before its handshake.                       *)
(*                                                                         *)
(* What must never happen, with `early_report` off:                        *)
(*  HandshakeEvidence  a handshake dial is reported without the peer       *)
(*                     having answered it;                                 *)
(*  ReachInDial        a dial with no held session fails although the     *)
(*                     peer ran and admitted us the whole time;            *)
(*  NoStuck            a dial whose handshake ended is left pending;      *)
(*  SubAtOnce          a dial over a held session waits.                   *)
(* What is not promised: a sub-session over a held session the peer no     *)
(* longer holds is reported (only a round trip could tell, and G-SURFACE   *)
(* forbids one); the host learns at the idle timeout.                      *)
(*                                                                         *)
(* Rust: crates/vinc-core/src/commands.rs `connect` (the early report,    *)
(* `optimistic && self.cfg.early_report`, and the parent branch);          *)
(* crates/vinc-core/src/acp.rs `allow_session` (the report once allowed,   *)
(* `client && !announced`) and `deny_session` (`announce_failure`);        *)
(* crates/vinc-core/src/events.rs `on_ready` (`!announced`), `on_closed`;  *)
(* crates/vinc-core/src/endpoint.rs `EndpointConfig::early_report`;        *)
(* crates/vinc/src/start.rs (the facade turns it off).                     *)
(* Lean: none (no data structure changes; the decision is this machine).   *)
(*                                                                         *)
(* Witnesses (scripts/proofs.sh witness_tlc), one per guard:               *)
(*  _early      EarlyReport = TRUE, the code before the fix: an optimistic *)
(*              dial to a stopped peer is reported, and nothing ever       *)
(*              answers it; HandshakeEvidence fails.                       *)
(*  _reportflag ReportByFlag = TRUE: the report after the handshake keyed  *)
(*              on "not optimistic" (the old `client && !optimistic`) and  *)
(*              not on "not reported yet"; with the early report off an    *)
(*              optimistic dial is never reported and times out against a  *)
(*              running peer; ReachInDial fails.                           *)
(*  _denyflag   DenyByFlag = TRUE: a refusal tells the dial only when it   *)
(*              was not optimistic (the old `!optimistic`); a refused      *)
(*              optimistic dial stays pending; NoStuck fails.             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Hs,            \* the most ticks a handshake to a running peer takes
    Deadline,      \* the connect timeout, in ticks
    MaxNow,        \* the last tick explored
    MaxInc,        \* the most incarnations of the peer explored
    EarlyReport,   \* the endpoint's early_report (TRUE in _early)
    ReportByFlag,  \* TRUE: the old report condition (the planted bug of _reportflag)
    DenyByFlag     \* TRUE: the old refusal condition (the planted bug of _denyflag)

\* "No answer": the evidence of a dial reported before anything was heard.
Never == 0

VARIABLES
    now,      \* the current tick, from 1
    alive,    \* whether the peer runs
    inc,      \* the incarnation of the peer that runs (or ran last)
    admits,   \* whether the peer's access check admits us
    cached,   \* whether our endpoint holds a cached allow for the peer (the dial is optimistic)
    held,     \* the session the host holds: [has, inc (the incarnation that made it)]
    dial,     \* the dial: [st, at, opt, sub, ev, told]
    steady    \* the peer ran and admitted us without a break since the dial started

vars == <<now, alive, inc, admits, cached, held, dial, steady>>

\* Every variable has the shape it should.
TypeOK ==
    /\ now \in 1..MaxNow
    /\ alive \in BOOLEAN /\ inc \in 1..MaxInc /\ admits \in BOOLEAN /\ cached \in BOOLEAN
    /\ held.has \in BOOLEAN /\ held.inc \in 1..MaxInc
    /\ dial.st \in {"idle", "hs", "reported", "failed"}
    /\ dial.opt \in BOOLEAN /\ dial.sub \in BOOLEAN /\ dial.ev \in 0..MaxNow /\ dial.told \in BOOLEAN
    /\ steady \in BOOLEAN

Init ==
    /\ now = 1
    /\ alive = TRUE
    /\ inc = 1
    /\ admits = TRUE
    /\ cached = FALSE
    /\ held = [has |-> FALSE, inc |-> 1]
    \* `told`: the application was told Connected for this dial (the code's `announced`).
    /\ dial = [st |-> "idle", at |-> 1, opt |-> FALSE, sub |-> FALSE, ev |-> Never, told |-> FALSE]
    /\ steady = TRUE

\* A tick passes. A handshake to a running peer that admits us ends within Hs ticks, so time does not pass that
\* point while it is pending.
Tick ==
    /\ now < MaxNow
    /\ ~(dial.st = "hs" /\ dial.ev = Never /\ alive /\ now >= dial.at + Hs)
    /\ now' = now + 1
    /\ UNCHANGED <<alive, inc, admits, cached, held, dial, steady>>

\* The peer stops without closing anything.
Stop ==
    /\ alive
    /\ alive' = FALSE
    /\ steady' = FALSE
    /\ UNCHANGED <<now, inc, admits, cached, held, dial>>

\* The peer comes back on the same address and identity: a new incarnation, which holds none of our sessions.
Restart ==
    /\ ~alive /\ inc < MaxInc
    /\ alive' = TRUE
    /\ inc' = inc + 1
    /\ UNCHANGED <<now, admits, cached, held, dial, steady>>

\* The peer's application starts or stops admitting us.
Admit ==
    /\ admits' = ~admits
    /\ steady' = (steady /\ admits')
    /\ UNCHANGED <<now, alive, inc, cached, held, dial>>

\* Our cached allow lapses, or a check answers and is cached again.
Cache ==
    /\ cached' = ~cached
    /\ UNCHANGED <<now, alive, inc, admits, held, dial, steady>>

\* The host drops the session it held (or the idle timeout closes it).
DropHeld ==
    /\ held.has
    /\ held' = [held EXCEPT !.has = FALSE]
    /\ UNCHANGED <<now, alive, inc, admits, cached, dial, steady>>

\* A dial starts. Over a held session: a sub-session, reported at once. Otherwise a handshake, reported at once only
\* when it is optimistic and the early report is on.
Start ==
    /\ dial.st = "idle"
    /\ steady' = (alive /\ admits)
    /\ IF held.has
       THEN dial' = [st |-> "reported", at |-> now, opt |-> cached, sub |-> TRUE, ev |-> Never, told |-> TRUE]
       ELSE LET early == cached /\ EarlyReport
            IN dial' = [st |-> IF early THEN "reported" ELSE "hs", at |-> now, opt |-> cached, sub |-> FALSE,
                        ev |-> Never, told |-> early]
    /\ UNCHANGED <<now, alive, inc, admits, cached, held>>

\* The handshake is done and the peer's check admitted us: the application is told, unless it was told already. With
\* the planted ReportByFlag the test is "not optimistic" instead, which skips an optimistic dial that was not told.
HsDone ==
    /\ dial.st \in {"hs", "reported"} /\ ~dial.sub /\ dial.ev = Never
    /\ alive /\ admits
    /\ LET report == IF ReportByFlag THEN ~dial.opt ELSE ~dial.told
       IN dial' = [dial EXCEPT !.ev = now,
                               !.st = IF report \/ dial.told THEN "reported" ELSE "hs",
                               !.told = dial.told \/ report]
    /\ held' = [has |-> TRUE, inc |-> inc]
    /\ UNCHANGED <<now, alive, inc, admits, cached, steady>>

\* The peer's check refuses us during the handshake: the dial fails, or the session closes if the application was
\* told. With the planted DenyByFlag the failure is told only to a dial that was not optimistic.
Deny ==
    /\ dial.st \in {"hs", "reported"} /\ ~dial.sub /\ dial.ev = Never
    /\ alive /\ ~admits
    /\ LET tell == IF DenyByFlag THEN ~dial.opt ELSE ~dial.told
       IN dial' = IF dial.told THEN [dial EXCEPT !.st = "failed"]
                  ELSE IF tell THEN [dial EXCEPT !.st = "failed"]
                  ELSE [dial EXCEPT !.ev = now]   \* refused, closed, and nobody is told: the dial stays pending
    /\ UNCHANGED <<now, alive, inc, admits, cached, held, steady>>

\* The connect timeout passes with the dial still pending: it fails.
Timeout ==
    /\ dial.st = "hs" /\ now >= dial.at + Deadline
    /\ dial' = [dial EXCEPT !.st = "failed"]
    /\ UNCHANGED <<now, alive, inc, admits, cached, held, steady>>

\* The host takes the result and may dial again.
Done ==
    /\ dial.st \in {"reported", "failed"}
    /\ dial' = [dial EXCEPT !.st = "idle"]
    /\ UNCHANGED <<now, alive, inc, admits, cached, held, steady>>

Next == Tick \/ Stop \/ Restart \/ Admit \/ Cache \/ DropHeld \/ Start \/ HsDone \/ Deny \/ Timeout \/ Done

Spec == Init /\ [][Next]_vars

\* A handshake dial the application was told about heard the peer: its handshake finished.
HandshakeEvidence == (dial.st = "reported" /\ ~dial.sub) => dial.ev # Never

\* A handshake dial fails only if the peer stopped or refused us while it ran.
ReachInDial == (dial.st = "failed" /\ ~dial.sub) => ~steady

\* A dial is not left pending once its handshake ended (admitted or refused): it was reported or it failed.
NoStuck == (dial.st = "hs" /\ dial.ev # Never) => FALSE

\* A dial over a held session is reported in the step it starts.
SubAtOnce == dial.sub => dial.st \in {"reported", "idle"}
=============================================================================
