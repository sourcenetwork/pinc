---------------------------- MODULE TraceFacadeWaits ----------------------------
(***************************************************************************)
(* Trace validation of the waiters of one session of the facade, the       *)
(* steps of FacadeWaits.tla on the real code: crates/pinc/src/engine.rs    *)
(* (Core::on_event, wake_s, stream_opened, send_failed, session_down,      *)
(* stop, end_session, the notify_all of service, kick), engine/ops.rs (the *)
(* attempts) and drive.rs (Shared::run_as, Turn::drop).                    *)
(*                                                                         *)
(* The Rust test tests/trace_facade_waits.rs runs two real endpoints over  *)
(* an in-memory wire, a virtual clock and a manual executor whose wakers   *)
(* record which future they wake. The subject endpoint (built with the     *)
(* cargo feature `trace`) logs, in one sequence with those wakes: each     *)
(* event its core handles for the session (with the accept queues and the  *)
(* stopped streams after it), each notify_all, each end of the session,    *)
(* each attempt that ended (Done) or registered a wait (its key), each     *)
(* kick (also the one a waiting future that does not drive makes, fix F3,  *)
(* for a deadline it added) and each baton offered when a future's turn    *)
(* ends. The test adds the futures it starts, polls, drops, the results    *)
(* they return and the wakes                                               *)
(* of the host (a delivered packet, a timer). Each record carries the      *)
(* futures woken after it and before the next record.                      *)
(*                                                                         *)
(* Checked on every record: an event wakes exactly the armed futures       *)
(* registered on its key (plus futures waiting on an endpoint-wide key,    *)
(* which other parts of the same service may wake) and unregisters every   *)
(* entry of that key; notify_all wakes every armed future; the end of the  *)
(* session wakes every future registered on it and sets its reason once;   *)
(* an attempt waits only when the model's attempt would (the queue empty,  *)
(* the session live, no stop recorded) and ends as the model's would (the  *)
(* oldest accepted stream, the session's reason); a future that returns    *)
(* Pending is armed and registered, so it cannot be forgotten; kick and    *)
(* baton wake at most one armed future. Only the subject's futures are     *)
(* logged; the peer's run unobserved.                                      *)
(*                                                                         *)
(* Codes. Keys: 1 AcceptBi, 2 AcceptUni, 3 Datagram, 4 Closed, 5 and 6     *)
(* Open (never in this test), 7 Read, 8 Write, 9 Answered, 16 and above an *)
(* endpoint-wide key; a key without a stream records stream 0. Calls use   *)
(* the code of the key they wait on (16 for a future of the endpoint:      *)
(* run, connect). Events: 1 Connected, 2 Incoming, 4 Closed, 5             *)
(* StreamOpened, 6 StreamReadable, 7 StreamReset, 8 StreamWritable, 9      *)
(* OpenReady, 10 Answered, 12 StreamStopped, 14 DatagramReceived, 0 any    *)
(* other. Error kinds: 1 Stopped, 2 Reset, 3 Closed by the peer, 4 Closed  *)
(* by this side, 5 TooLarge, 6 TimedOut, 7 Refused, 8 Unreachable, 9 Busy, *)
(* 10 Config, 11 Shutdown.                                                 *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR.                                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd

CONSTANTS
    FILE,   \* the ndjson under PINC_TRACE_DIR
    NF,     \* future ids are 0 .. NF - 1
    ACAP,   \* Limits::accept_streams of the subject
    TRK     \* TRACKED

VARIABLES
    i,
    live,   \* the session is in Core::sessions
    ended,  \* the error kind of SessInfo::ended, 0 until set
    acc,    \* Sess::accept_bi
    accu,   \* Sess::accept_uni
    fail,   \* the stream ids of Sess::send_fail
    ans,    \* SessInfo::answered
    pend,   \* futures started and not finished or dropped
    call,   \* each future's call code
    sid,    \* each future's stream
    wkey,   \* each future's registration: [k, s], k = 0 for none
    armed,  \* futures whose ticket holds their waker
    cur,    \* the future being polled, -1 between polls
    out     \* what a future that ended must return: r -1 not ended, 0 any, 1 ok with v (0 any), 2 error kind e

vars == <<i, live, ended, acc, accu, fail, ans, pend, call, sid, wkey, armed, cur, out>>

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/" \o FILE)
Ev == Trace[i]
Futs == 0..(NF - 1)
Range(q) == {q[j] : j \in DOMAIN q}
Woke == Range(Ev.woke)

GLOBAL == 16
NoKey == [k |-> 0, s |-> 0]
Key(k, s) == [k |-> k, s |-> s]
NoOut == [r |-> -1, e |-> 0, v |-> 0]
AnyOut == [r |-> 0, e |-> 0, v |-> 0]
OkV(v) == [r |-> 1, e |-> 0, v |-> v]
ErrE(e) == [r |-> 2, e |-> e, v |-> 0]
IsGlobal(f) == wkey[f].k >= GLOBAL
SessWait(f) == wkey[f].k \in 1..(GLOBAL - 1)
Uni(id) == (id \div 2) % 2 = 1

\* send_failed: the stream's entry replaces an older one; at TRK entries the oldest goes
SendFailed(q, id) ==
    LET g == SelectSeq(q, LAMBDA x : x # id)
    IN Append(IF Len(g) >= TRK THEN Tail(g) ELSE g, id)

\* the futures registered on key k of stream s: wake_s notifies them and takes the key off the list
Hit(k, s) == {f \in Futs : wkey[f] = Key(k, s)}
ClearKey(set) == [f \in Futs |-> IF f \in set THEN NoKey ELSE wkey[f]]
\* the woken futures are armed; the session's ones are exactly the armed among exp; the rest wait endpoint-wide
WokeIs(exp) ==
    /\ Woke \subseteq armed
    /\ {f \in Woke : ~IsGlobal(f)} = exp \cap armed
\* wakes no record names a reason for: only armed futures waiting endpoint-wide
Stray == Woke \subseteq {f \in armed : IsGlobal(f)}

Fresh ==
    /\ live' = FALSE /\ ended' = 0 /\ acc' = <<>> /\ accu' = <<>> /\ fail' = <<>> /\ ans' = FALSE
    /\ pend' = {} /\ call' = [f \in Futs |-> 0] /\ sid' = [f \in Futs |-> 0]
    /\ wkey' = [f \in Futs |-> NoKey] /\ armed' = {} /\ cur' = -1 /\ out' = [f \in Futs |-> NoOut]

-----------------------------------------------------------------------------
(* The core's records.                                                      *)

\* an event the core handled for the session; Connected and Incoming bring the session up
Active == live /\ Ev.k \notin {1, 2}
EvExp ==
    CASE Ev.k = 5 -> IF Uni(Ev.s) THEN (IF Len(accu) < ACAP THEN Hit(2, 0) ELSE {})
                                  ELSE (IF Len(acc) < ACAP THEN Hit(1, 0) ELSE {})
      [] Ev.k \in {6, 7} -> Hit(7, Ev.s)
      [] Ev.k \in {8, 12} -> Hit(8, Ev.s)
      [] Ev.k = 10 -> Hit(9, 0)
      [] Ev.k = 14 -> Hit(3, 0)
      [] OTHER -> {}
Refused == Ev.k = 5 /\ ~Uni(Ev.s) /\ Len(acc) >= ACAP
EvStep ==
    /\ Ev.op = "ev"
    /\ LET exp == IF Active THEN EvExp ELSE {}
       IN /\ WokeIs(exp) /\ armed' = armed \ Woke /\ wkey' = ClearKey(exp)
    /\ live' = (live \/ Ev.k \in {1, 2})
    /\ acc' = IF Active /\ Ev.k = 5 /\ ~Uni(Ev.s) /\ Len(acc) < ACAP THEN Append(acc, Ev.s) ELSE acc
    /\ accu' = IF Active /\ Ev.k = 5 /\ Uni(Ev.s) /\ Len(accu) < ACAP THEN Append(accu, Ev.s) ELSE accu
    \* only a stream the peer stopped: a refused one has no writer to read an entry (fix F6)
    /\ fail' = IF Active /\ Ev.k = 12 THEN SendFailed(fail, Ev.s) ELSE fail
    \* a session comes up answered when it was accepted or its peer was already heard (session_up: !dialer ||
    \* peer_answered); the record does not show the second, so a dialed session may come up either way
    /\ IF ~live /\ Ev.k \in {1, 2} THEN ans' \in IF Ev.k = 2 THEN {TRUE} ELSE BOOLEAN
       ELSE ans' = (ans \/ (Active /\ Ev.k = 10))
    \* the lists are read after the event (waits_probe.rs); Closed ends the session inside it (session_down, whose
    \* "end" record follows), so they are the ended session's: none
    /\ IF Ev.k = 4 THEN Ev.acc = <<>> /\ Ev.accu = <<>> /\ Ev.fail = <<>>
       ELSE Ev.acc = acc' /\ Ev.accu = accu' /\ Ev.fail = fail'
    /\ UNCHANGED <<ended, pend, call, sid, cur, out>>

\* notify_all: the drop counter moved; every armed future is woken
AllStep ==
    /\ Ev.op = "all"
    /\ Woke = armed /\ armed' = {}
    /\ UNCHANGED <<live, ended, acc, accu, fail, ans, pend, call, sid, wkey, cur, out>>

\* end_session (from session_down or stop): the reason once, then every future registered on the session
EndStep ==
    /\ Ev.op = "end" /\ live
    /\ LET exp == {f \in Futs : SessWait(f)}
       IN /\ WokeIs(exp) /\ armed' = armed \ Woke /\ wkey' = ClearKey(exp)
    /\ live' = FALSE
    /\ ended' = IF ended = 0 THEN Ev.e ELSE ended
    /\ acc' = <<>> /\ accu' = <<>> /\ fail' = <<>>
    /\ UNCHANGED <<ans, pend, call, sid, cur, out>>

\* kick or baton: at most one armed future, which loses its waker
WakeStep ==
    /\ Ev.op = "wake"
    /\ IF Ev.why = 1
       THEN UNCHANGED armed                                  \* the host's own wakers: a packet, a timer
       ELSE Cardinality(Woke) <= 1 /\ Woke \subseteq armed /\ armed' = armed \ Woke
    /\ UNCHANGED <<live, ended, acc, accu, fail, ans, pend, call, sid, wkey, cur, out>>

-----------------------------------------------------------------------------
(* The attempts and the futures.                                            *)

\* Done: what the attempt must return, from the state the records built
DoneOut(f) ==
    LET c == call[f] IN
    CASE c = 1 -> IF live THEN OkV(Head(acc)) ELSE ErrE(ended)
      [] c = 2 -> IF live THEN OkV(Head(accu)) ELSE ErrE(ended)
      [] c = 4 -> ErrE(ended)
      [] c = 9 -> IF ans THEN AnyOut ELSE ErrE(ended)
      [] c = 8 -> IF ~live THEN ErrE(ended) ELSE IF sid[f] \in Range(fail) THEN ErrE(1) ELSE AnyOut
      [] c \in {3, 7} -> IF live THEN AnyOut ELSE ErrE(ended)
      [] OTHER -> AnyOut
\* where Done is allowed at all
DoneOk(f) ==
    LET c == call[f] IN
    CASE c = 1 -> ~live \/ acc # <<>>
      [] c = 2 -> ~live \/ accu # <<>>
      [] c = 4 -> ~live
      [] c = 9 -> ans \/ ~live
      [] OTHER -> TRUE
\* where a wait is allowed: the model's attempt would wait
WaitOk(f) ==
    LET c == call[f] IN
    CASE c = 1 -> live /\ acc = <<>>
      [] c = 2 -> live /\ accu = <<>>
      [] c = 9 -> live /\ ~ans
      [] c = 8 -> live /\ sid[f] \notin Range(fail)
      [] c \in {3, 4, 7} -> live
      [] OTHER -> TRUE
WaitKey(f) ==
    IF call[f] >= GLOBAL THEN Ev.key >= GLOBAL
    ELSE Ev.key = call[f] /\ Ev.s = (IF call[f] \in {7, 8} THEN sid[f] ELSE 0)

TryStep ==
    /\ Ev.op = "try" /\ cur = Ev.f /\ Ev.f \in pend /\ Stray
    /\ LET f == Ev.f IN
       IF Ev.key = 0
       THEN \* Done: kick, then the Turn forgets the wait and releases the ticket
            /\ DoneOk(f)
            /\ out' = [out EXCEPT ![f] = DoneOut(f)]
            /\ acc' = IF call[f] = 1 /\ live THEN Tail(acc) ELSE acc
            /\ accu' = IF call[f] = 2 /\ live THEN Tail(accu) ELSE accu
            /\ wkey' = [wkey EXCEPT ![f] = NoKey]
            /\ armed' = (armed \ {f}) \ Woke
       ELSE \* Wait: forget the old key, add_wait (nothing on a session not in the table), arm
            /\ WaitOk(f) /\ WaitKey(f)
            /\ wkey' = [wkey EXCEPT ![f] = IF Ev.key >= GLOBAL \/ live THEN Key(Ev.key, Ev.s) ELSE NoKey]
            /\ armed' = (armed \cup {f}) \ Woke
            /\ UNCHANGED <<out, acc, accu>>
    /\ UNCHANGED <<live, ended, fail, ans, pend, call, sid, cur>>

PollStep ==
    /\ Ev.op = "poll" /\ cur = -1 /\ Ev.f \in pend /\ Stray
    /\ cur' = Ev.f /\ armed' = armed \ Woke
    /\ UNCHANGED <<live, ended, acc, accu, fail, ans, pend, call, sid, wkey, out>>

\* the poll returned: Pending only for a future armed and registered; Ready with the result the attempt fixed
Matches(o) ==
    \/ o.r = 0
    \/ /\ o.r = Ev.r
       /\ o.r = 1 => (o.v = 0 \/ o.v = Ev.v)
       /\ o.r = 2 => o.e = Ev.e
\* the wakes a return carries happen after it, in the peer's polls, which make no record: only Stray ones
RetStep ==
    /\ Ev.op = "ret" /\ cur = Ev.f /\ Stray
    /\ cur' = -1
    /\ IF Ev.r = 0
       THEN Ev.f \in armed /\ wkey[Ev.f] # NoKey /\ armed' = armed \ Woke /\ UNCHANGED <<pend, out, wkey>>
       ELSE /\ out[Ev.f] # NoOut /\ Matches(out[Ev.f])
            /\ pend' = pend \ {Ev.f} /\ armed' = (armed \ {Ev.f}) \ Woke
            /\ wkey' = [wkey EXCEPT ![Ev.f] = NoKey]
            /\ UNCHANGED out
    /\ UNCHANGED <<live, ended, acc, accu, fail, ans, call, sid>>

\* a future dropped between polls: its Turn forgets the wait and releases the ticket
DropStep ==
    /\ Ev.op = "drop" /\ cur = -1 /\ Ev.f \in pend /\ Woke = {}
    /\ pend' = pend \ {Ev.f} /\ armed' = armed \ {Ev.f} /\ wkey' = [wkey EXCEPT ![Ev.f] = NoKey]
    /\ UNCHANGED <<live, ended, acc, accu, fail, ans, call, sid, cur, out>>

SpawnStep ==
    /\ Ev.op = "spawn" /\ Ev.f \in Futs /\ Ev.f \notin pend /\ Woke = {}
    /\ pend' = pend \cup {Ev.f}
    /\ call' = [call EXCEPT ![Ev.f] = Ev.call] /\ sid' = [sid EXCEPT ![Ev.f] = Ev.s]
    /\ wkey' = [wkey EXCEPT ![Ev.f] = NoKey] /\ out' = [out EXCEPT ![Ev.f] = NoOut]
    /\ UNCHANGED <<live, ended, acc, accu, fail, ans, armed, cur>>

\* the test found nothing to do: its own check (every pending future polled once more stays Pending) follows
RestStep == Ev.op = "rest" /\ cur = -1 /\ Woke = {} /\ UNCHANGED <<live, ended, acc, accu, fail, ans, pend, call, sid, wkey, armed, cur, out>>
InitStep == Ev.op = "init" /\ Woke = {} /\ Fresh

Init == i = 1 /\ live = FALSE /\ ended = 0 /\ acc = <<>> /\ accu = <<>> /\ fail = <<>> /\ ans = FALSE
        /\ pend = {} /\ call = [f \in Futs |-> 0] /\ sid = [f \in Futs |-> 0]
        /\ wkey = [f \in Futs |-> NoKey] /\ armed = {} /\ cur = -1 /\ out = [f \in Futs |-> NoOut]
Step == /\ i <= Len(Trace) /\ Ev.t = "fw"
        /\ \/ InitStep \/ SpawnStep \/ PollStep \/ TryStep \/ RetStep \/ DropStep
           \/ EvStep \/ AllStep \/ EndStep \/ WakeStep \/ RestStep
        /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* on every recorded state: only running futures are armed; a session wait only on a live session; the bounds
Inv ==
    /\ armed \subseteq pend
    /\ \A f \in Futs : SessWait(f) => live /\ f \in pend
    /\ Len(acc) <= ACAP /\ Len(accu) <= ACAP
    /\ Len(fail) <= TRK
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
