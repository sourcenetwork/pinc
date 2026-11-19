---------------------------- MODULE FacadeEventsOps ----------------------------
(***************************************************************************)
(* The bounded queue of topic events the facade keeps for the host, as the *)
(* code computes it: crates/pinc/src/engine/topics.rs `EVENTS`,            *)
(* `push_event`, `poll_event` and the `NodeEvent::Lost` arm of             *)
(* `on_node_event`; the fields `events: VecDeque<Event>`, `lost: u32`,     *)
(* `stopped: Option<Error>` of `Core` (engine.rs).                         *)
(*                                                                         *)
(* A state is [q |-> the queued events (an id each), lost |-> the drop     *)
(* count as a U64.tla word, stopped |-> BOOLEAN]. The count saturates at   *)
(* TOPW (u32::MAX in the trace check, a small word in the model check), so *)
(* the same operators serve both. A poll answers a record                  *)
(* [r |-> "lost" | "event" | "none" | "wait", n |-> the count (a word),    *)
(* e |-> the event (0 when none), s |-> the state after].                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, U64
CONSTANTS CAP, TOPW
ASSUME CAP \in Nat \ {0}

\* lost.saturating_add(c) on a u32 whose largest value is TOPW
SatAddW(a, c) == IF Lt(TOPW, Add(a, c)) THEN TOPW ELSE Add(a, c)

Empty == [q |-> <<>>, lost |-> Zero, stopped |-> FALSE]

\* push_event: a full queue counts the new event and drops it; else it goes to the back
Full(s) == Len(s.q) >= CAP
Enq(s, e) == IF Full(s) THEN [s EXCEPT !.lost = SatAddW(s.lost, One)] ELSE [s EXCEPT !.q = Append(s.q, e)]

\* on_node_event(NodeEvent::Lost { count }): the node's drops join the count
NodeLost(s, c) == [s EXCEPT !.lost = SatAddW(s.lost, c)]

\* poll_event: the count first, then the oldest event, then None once stopped, else a wait
PollOf(s) ==
    IF s.lost # Zero THEN [r |-> "lost", n |-> s.lost, e |-> 0, s |-> [s EXCEPT !.lost = Zero]]
    ELSE IF Len(s.q) > 0 THEN [r |-> "event", n |-> Zero, e |-> Head(s.q), s |-> [s EXCEPT !.q = Tail(s.q)]]
    ELSE IF s.stopped THEN [r |-> "none", n |-> Zero, e |-> 0, s |-> s]
    ELSE [r |-> "wait", n |-> Zero, e |-> 0, s |-> s]

\* the endpoint stops (`stopped` set); the queue and the count stay
Stop(s) == [s EXCEPT !.stopped = TRUE]
=============================================================================
