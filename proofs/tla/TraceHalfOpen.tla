---------------------------- MODULE TraceHalfOpen ----------------------------
(***************************************************************************)
(* Trace validation of the endpoint's half-open cap and the lifetime of an *)
(* unauthenticated session: pinc-core rx.rs, events.rs, endpoint.rs,       *)
(* timers.rs.                                                              *)
(*                                                                         *)
(* The Rust test tests/trace_halfopen.rs drives real endpoints (built with *)
(* the cargo feature `trace`) with first flights of every type at and      *)
(* around the size floors, floods past the cap, genuine full handshakes    *)
(* and resumptions, replays, closes, a missing protocol, a full slot       *)
(* table, a stalled event queue and timer calls before, at and after the   *)
(* ends of the sessions, the clock stepping back too. One line per call:   *)
(* the inputs the decisions used (the message type and length read off the *)
(* datagram, whether the test sent it as a genuine dialer would, how many  *)
(* sessions held its id, the stall), the decisions the                     *)
(* endpoint recorded in its own trace ring (admissions with the count, the *)
(* room the host left to accept sessions and the sessions owed, and the    *)
(* ticket's verdict they used, sessions made, established, expired and     *)
(* freed), and the slots whose bookkeeping changed, with the count, the    *)
(* stall and poll_timeout after the call. Every decision must be the one   *)
(* the operators of HalfOpenOps.tla make, in that order, and the slots and *)
(* the count they compute must be the recorded ones; the deadlines a       *)
(* session's connection asks for are the endpoint's own, and must keep an  *)
(* unauthenticated session within its own life, which is the base life or *)
(* the hold once it answered, never shorter than before. The cap a first   *)
(* flight meets is the smaller of the code's and half the room, rounded    *)
(* up, and no flight starts a session while the owed sessions fill the     *)
(* room. A first packet the responder would only reject, or not answer at  *)
(* all, is recorded as decided without a session: answered with a reject   *)
(* because its prekey or ticket is not held (admitted 2) or dropped        *)
(* without an answer (admitted 3), only a short Initial or a Hello of the  *)
(* floor's size or more, no resumption, that finds room to be decided on,  *)
(* and never a packet the test sent as a genuine dialer does when no       *)
(* session holds its id: that first packet is admitted or refused, never   *)
(* rejected or dropped (a copy of it that finds its session may be). A     *)
(* reject is counted once at most in the call (a refusal by the ledger, or *)
(* a full queue of rejects); one that is queued is counted when it is      *)
(* sent. A first flight goes to the admission only while its id has fewer  *)
(* holders than the endpoint allows (Room), and a datagram whose first     *)
(* flight went to the admission frees no session that was in use before    *)
(* it, only one it made itself: an arrival never frees the session that    *)
(* holds its id. Times are in                                              *)
(* milliseconds (a deadline rounded up, so every comparison is the one the *)
(* code makes).                                                            *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds halfopen.ndjson.      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, TraceEnd
VARIABLES i, e, p
vars == <<i, e, p>>
INSTANCE HalfOpenOps

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/halfopen.ndjson")
Ev == Trace[i]

\* a recorded slot: <<slot, in use, created, unauthenticated, counted, has a deadline, the deadline, its life>>
SlotOf(r) == IF r[2] = 0 THEN Free
             ELSE [use |-> TRUE, created |-> r[3], unauth |-> r[4] = 1, counted |-> r[5] = 1, life |-> r[8],
                   dl |-> IF r[6] = 1 THEN r[7] ELSE NoDl]
\* the slots after the call: the recorded changes over the slots before it
After(sl, diff) == [j \in DOMAIN sl |->
                      IF \E k \in DOMAIN diff : diff[k][1] = j
                      THEN SlotOf(diff[CHOOSE k \in DOMAIN diff : diff[k][1] = j]) ELSE sl[j]]
\* the deadline and the life are the endpoint's own (the life rises to the hold when the session answers)
Bare(s) == [s EXCEPT !.dl = NoDl, !.life = 0]
\* the cap the counted sessions meet: the code's, or half the room the host left, rounded up, when that is less
HalfCapOf(max, room) == IF Half(room) < max THEN Half(room) ELSE max

\* the decisions of one call, in the order the endpoint recorded them, from the state before it: st = [e, ok, adm],
\* adm the last admission <<admitted, resume>> (<<>> once a session took it); a step is <<code, a, b, c, d, f>>: 0 an
\* admission <<0, admitted, count, resume, room, owed>> (admitted 1 made a session, 0 was refused, 2 was answered with a
\* reject without a session, 3 was dropped; Ev.n sessions held the datagram's id), 1 a session made in slot a (b = 1 for a
\* dial), 2 established, 3 expired, 4 freed
RECURSIVE Fold(_, _, _)
Fold(st, steps, k) ==
    IF k > Len(steps) THEN st
    ELSE LET s == steps[k]
             x == st.e
             j == s[2]
             nxt == CASE s[1] = 0 ->
                          [e |-> x, adm |-> <<s[2], s[4]>>,
                           ok |-> /\ st.ok /\ Ev.op = "dgram" /\ First(Ev.kind) /\ s[3] = x.count
                                  /\ Room(Ev.n, p.holders)
                                  /\ (s[4] = 1 => Ev.kind = 6)
                                  /\ s[2] \in 0..3
                                  \* a first packet answered with a reject or dropped, without a session, is a short
                                  \* Initial or a Hello of the floor's size or more that finds room to be decided on, no
                                  \* resumption, and not one the test sent as a genuine dialer does while no session
                                  \* holds its id
                                  /\ (s[2] >= 2 => /\ Forged(Ev.kind) /\ s[4] = 0 /\ s[6] < s[5]
                                                  /\ Ev.len >= Floor(Ev.kind, p.full, p.short, p.hello)
                                                  /\ (Ev.genuine = 0 \/ Ev.n > 0))
                                  /\ (s[2] < 2 => (s[2] = 1) = (s[6] < s[5]
                                          /\ Admit(x.count, Ev.kind, Ev.len, s[4] = 1, HalfCapOf(p.max, s[5]),
                                                   p.full, p.short, p.hello)))]
                      [] s[1] = 1 /\ s[3] = 1 ->
                          [e |-> Dial(x, j, Ev.now, p.life), adm |-> st.adm,
                           ok |-> st.ok /\ j \in DOMAIN x.slots /\ ~x.slots[j].use]
                      [] s[1] = 1 ->
                          [e |-> Make(x, j, Ev.now, st.adm = <<1, 1>>, p.life), adm |-> <<>>,
                           ok |-> /\ st.ok /\ j \in DOMAIN x.slots /\ ~x.slots[j].use
                                  /\ st.adm \in {<<1, 0>>, <<1, 1>>}]
                      [] s[1] = 2 ->
                          [e |-> Establish(x, j), adm |-> st.adm, ok |-> st.ok /\ j \in DOMAIN x.slots /\ x.slots[j].use]
                      [] s[1] = 3 ->
                          [e |-> x, adm |-> st.adm,
                           ok |-> /\ st.ok /\ Ev.op = "timer" /\ j \in DOMAIN x.slots
                                  /\ Expired(x.slots[j], Ev.now)
                                  /\ k < Len(steps) /\ steps[k + 1] = <<4, j, 0, 0, 0, 0>>]
                      [] s[1] = 4 ->
                          [e |-> Release(x, j), adm |-> st.adm, ok |-> st.ok /\ j \in DOMAIN x.slots]
                      [] OTHER -> [st EXCEPT !.ok = FALSE]
         IN Fold(nxt, steps, k + 1)

InitEv == /\ Ev.op = "init"
          /\ p' = [k |-> Ev.k, max |-> Ev.max, life |-> Ev.life, hold |-> Ev.hold, full |-> Ev.full,
                   short |-> Ev.short, hello |-> Ev.hello, holders |-> Ev.holders]
          /\ e' = [slots |-> Table0(Ev.k), count |-> 0]

CallEv ==
    LET st == Fold([e |-> e, ok |-> TRUE, adm |-> <<>>], Ev.steps, 1)
        sl == After(e.slots, Ev.diff)
        made == \E k \in DOMAIN Ev.steps : Ev.steps[k][1] = 1
        decided == Len(Ev.steps) > 0 /\ Ev.steps[1][1] = 0
        timeout == IF Ev.timeout = <<>> THEN NoDl ELSE Ev.timeout[1]
    IN /\ Ev.op \in {"dgram", "timer", "other"}
       /\ st.ok
       \* the slots and the count the model computes are the endpoint's; the deadlines are the endpoint's own
       /\ \A j \in DOMAIN sl : Bare(sl[j]) = Bare(st.e.slots[j])
       \* a session lives the base life or the hold, and its life never falls while it holds the slot
       /\ \A j \in DOMAIN sl : sl[j].use => /\ sl[j].life \in {p.life, p.hold}
                                         /\ (e.slots[j].use /\ e.slots[j].created = sl[j].created
                                               => sl[j].life >= e.slots[j].life)
       /\ st.e.count = Ev.count
       /\ e' = [slots |-> sl, count |-> Ev.count]
       \* poll_timeout is the earliest deadline, none while the event queue is stalled
       /\ timeout = Poll(sl, Ev.stalled = 1)
       \* a timer call the queue did not stop leaves no unauthenticated session at or past its end; a stalled one runs
       \* nothing
       /\ Ev.op = "timer" /\ Ev.stalled = 0 => \A j \in DOMAIN sl : ~Expired(sl[j], Ev.now)
       /\ Ev.op = "timer" /\ Ev.stalled0 = 1 => Ev.steps = <<>> /\ Ev.diff = <<>>
       \* an arrival never frees a session: a datagram whose first flight went to the admission frees only a session
       \* that was not in use before it or that it made itself (the id table full, or a session that ended at once)
       /\ Ev.op = "dgram" /\ (\E k \in DOMAIN Ev.steps : Ev.steps[k][1] = 0) =>
            \A k \in DOMAIN Ev.steps : Ev.steps[k][1] = 4 =>
                 \/ Ev.steps[k][2] \notin DOMAIN e.slots
                 \/ ~e.slots[Ev.steps[k][2]].use
                 \/ \E m \in 1..(k - 1) : Ev.steps[m][1] = 1 /\ Ev.steps[m][2] = Ev.steps[k][2]
       \* a datagram for an id no session holds: a stalled queue or a type that starts no session decides nothing, a first
       \* message type is decided, and what makes no session changes no slot and counts one dropped or stalled datagram
       /\ Ev.op = "dgram" /\ Ev.n = 0 =>
            /\ Ev.stalled0 = 1 => Ev.steps = <<>> /\ Ev.stalledIn = 1 /\ Ev.dropped = 0
            /\ Ev.stalled0 = 0 /\ ~First(Ev.kind) => Ev.steps = <<>> /\ (Ev.kind # 0 => Ev.dropped = 1)
            /\ Ev.stalled0 = 0 /\ First(Ev.kind) => decided
            /\ ~made => Ev.diff = <<>>
            \* what decides and makes no session is counted once: dropped, or (otherwise) a reject the ledger refused, or
            \* refused for want of room; a reject that is queued is counted when it is sent, not in this call
            /\ decided /\ ~made =>
                 IF Ev.steps[1][2] = 2 THEN Ev.dropped + Ev.otherwise <= 1 ELSE Ev.dropped + Ev.otherwise = 1
       /\ UNCHANGED p

Init == /\ i = 1 /\ e = [slots |-> Table0(1), count |-> 0]
        /\ p = [k |-> 1, max |-> 0, life |-> 0, hold |-> 0, full |-> 0, short |-> 0, hello |-> 0, holders |-> 0]
Step == /\ i <= Len(Trace) /\ Ev.t = "coho" /\ (InitEv \/ CallEv) /\ i' = i + 1
Finished == i > Len(Trace) /\ UNCHANGED vars
TNext == Step \/ Finished
TraceSpec == Init /\ [][TNext]_vars

\* the count is at most the cap and is the number of counted sessions; a counted session is unauthenticated; a free slot
\* holds nothing; an unauthenticated session's deadline is at most its end
Inv == /\ e.count <= p.max
       /\ e.count = CountOf(e.slots)
       /\ \A j \in DOMAIN e.slots :
            /\ e.slots[j].counted => e.slots[j].unauth /\ e.slots[j].use
            /\ ~e.slots[j].use => e.slots[j] = Free
            /\ e.slots[j].use /\ e.slots[j].unauth => e.slots[j].dl # NoDl /\ e.slots[j].dl <= End(e.slots[j])
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
