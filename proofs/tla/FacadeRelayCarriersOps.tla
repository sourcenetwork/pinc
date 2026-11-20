----------------------- MODULE FacadeRelayCarriersOps -----------------------
(***************************************************************************)
(* The carriers of a node that carries the relay role, step for step:      *)
(* crates/pinc/src/relay/part.rs Part::poll (an accept, completions, the   *)
(* reads and writes to start, the streams to close), Part::end, and the    *)
(* parts of relay/state.rs it calls (want_accept, complete, add_conn,      *)
(* place, tag, slot_of, on_read, on_write, on_open, dying, pop_reap,      *)
(* finish,                                                                 *)
(* begin_shutdown, abort_all, on_timeout, send_frame) and relay/conn.rs    *)
(* (push, take_read, take_write, wrote). FacadeRelayCarriers.tla checks    *)
(* them over every interleaving at small sizes; TraceFacadeRelayCarriers   *)
(* replays the polls a test made on the real code.                         *)
(*                                                                         *)
(* A conn (a slot of Core.conns): on (Some), id, h (the host's stream),    *)
(* node (0 while in its handshake), sid (its machine session), rd and wr   *)
(* (a read or write out), off (the write buffer was partly written: the    *)
(* next write goes on from the offset), q (units queued), wb (units in the *)
(* write buffer), un (Conn.unsent in units, rounded up: what the write in  *)
(* flight has not written yet; Conn.backlog is q + un, fix R5), dy (the    *)
(* Closed reason, "" while alive), kind, dl (handshake deadline), rx (last *)
(* read). A read's bytes are abstracted by what they make the core do:     *)
(* "hello" (a handshake message), "open" (the handshake ends for a node),  *)
(* "frame" (a frame of an open session), "junk" (a protocol failure),      *)
(* "zero" (end of stream or an error), and whether they queue a reply. A   *)
(* unit is one sealed frame; a member's pings and their answers (Conn.ctl, *)
(* one pong at most) are not modelled.                                     *)
(*                                                                         *)
(* The host's operations out are a set of [k, id, slot, h]: an accept is   *)
(* [k "acc", id 0, slot 0, h 0] (Tag::new(0)); a read or write carries the *)
(* tag of its conn (id << 16 | slot). The core's reap list rp (state.rs   *)
(* reap) holds [k, id] for each conn marked dying, in the order marked;    *)
(* a poll finishes them last marked first (pop_reap), which sets the order *)
(* of the free slots and so the slot of the next conn.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS HS,    \* Limits.handshaking
          CAP,   \* Limits.carriers
          BL,    \* Limits.write_backlog in units
          HSD,   \* Limits.handshake_ns in time units
          IDL,   \* Limits.idle_ns in time units
          PAUSE, \* ACCEPT_PAUSE_NS in time units
          CHK,   \* CHECK_NS in time units
          NODES  \* the member nodes

NoConn == [on |-> FALSE, id |-> 0, h |-> 0, node |-> 0, sid |-> 0, rd |-> FALSE, wr |-> FALSE, off |-> FALSE,
           q |-> 0, wb |-> 0, un |-> 0, dy |-> "", kind |-> "tcp", dl |-> 0, rx |-> 0]
Cnt0 == [opened |-> 0, closed |-> 0, full |-> 0, hsfull |-> 0, proto |-> 0, slow |-> 0, tout |-> 0, accerr |-> 0]

\* the whole: the core c, the host's operations o, how often each stream was closed (ends), the streams dropped
\* without a close (drop), and ghosts (late completions ignored, refusals counted as a full handshake table that was not)
Sys0(now) == [c |-> [cs |-> <<>>, free |-> <<>>, next |-> 0, hs |-> 0, cur |-> [n \in NODES |-> 0], nsid |-> 0,
                     by |-> [n \in NODES |-> 0], acc |-> FALSE, pause |-> 0, stop |-> FALSE, chk |-> now + CHK,
                     pinged |-> FALSE, cnt |-> Cnt0, rp |-> <<>>],
              o |-> {}, ends |-> <<>>, drop |-> {}, late |-> FALSE, mis |-> FALSE]

Front(q) == SubSeq(q, 1, Len(q) - 1)
Last(q) == q[Len(q)]
Slots(m) == 1..Len(m.c.cs)
Live(m) == {k \in Slots(m) : m.c.cs[k].on}
Sessions(m) == Cardinality({n \in NODES : m.c.cur[n] # 0})
TagOf(m, k) == [id |-> m.c.cs[k].id, slot |-> k]
AccOp == [k |-> "acc", id |-> 0, slot |-> 0, h |-> 0]

SetConn(m, k, x) == [m EXCEPT !.c.cs[k] = x]
Count(m, f) == [m EXCEPT !.c.cnt[f] = @ + 1]

\* Carriers::close: the stream is closed once more; with late, the host may still hand back what was out on it
Close(m, h, late) ==
    [m EXCEPT !.ends[h] = @ + 1, !.o = IF late THEN @ ELSE {x \in @ : x.h # h}]

\* state.rs dying: once per conn, counted by reason, and pushed on the reap list
Dying(m, k, why) ==
    IF k \notin Slots(m) \/ ~m.c.cs[k].on \/ m.c.cs[k].dy # "" THEN m
    ELSE LET m1 == [m EXCEPT !.c.cs[k].dy = why, !.c.rp = Append(@, [k |-> k, id |-> m.c.cs[k].id])]
         IN CASE why = "proto" -> Count(m1, "proto")
              [] why = "slow" -> Count(m1, "slow")
              [] why \in {"idle", "hstime"} -> Count(m1, "tout")
              [] OTHER -> m1

\* state.rs send_frame, conn.rs push: a unit queued, or the conn closed as slow when the queue and the write in flight
\* (backlog) would pass the limit; slow is the answer push gives (computed from units here, read from the counters in
\* the trace)
SlowAt(m, k) == m.c.cs[k].q + m.c.cs[k].un + 1 > BL
Push(m, k, slow) ==
    IF ~m.c.cs[k].on \/ m.c.cs[k].dy # "" THEN m
    ELSE IF slow THEN Dying(m, k, "slow")
    ELSE [m EXCEPT !.c.cs[k].q = @ + 1]

\* state.rs place: a free slot from the stack, or a new one at the end
Place(m, x) ==
    IF m.c.free # <<>>
    THEN LET k == Last(m.c.free) IN [m EXCEPT !.c.free = Front(@), !.c.cs[k] = x, !.c.next = @ + 1]
    ELSE [m EXCEPT !.c.cs = Append(@, x), !.c.next = @ + 1]

\* state.rs add_conn: the accepted stream h is placed, or given back and closed (Tag 0): while the relay is stopping
\* counted as an accept error, when the handshake table is full as refused_handshakes_full (fix R11; mis records a
\* full-table count with room left). A session config the relay cannot build is an accept error too; it cannot
\* happen with the constant carrier names and is not modelled.
AddConn(m, h, kind, now, late) ==
    IF m.c.stop THEN Close(Count(m, "accerr"), h, late)
    ELSE IF m.c.hs >= HS
    THEN [Close(Count(m, "hsfull"), h, late) EXCEPT !.mis = @ \/ m.c.hs < HS]
    ELSE LET x == [NoConn EXCEPT !.on = TRUE, !.id = m.c.next + 1, !.h = h, !.kind = kind, !.dl = now + HSD,
                                 !.rx = now]
         IN [Place(m, x) EXCEPT !.c.hs = @ + 1]

\* state.rs on_open for a member conn (access admits every node): refused when a new node finds the session table
\* full; else the machine opens a session and the node's entry names the new conn; the conn the entry held before, if
\* it is another one with a session, is closed as replaced by its slot (fix R13: no scan). The machine's close of the
\* replaced session then reaches close_session, which finds the node's entry naming the new session and does nothing.
OnOpen(m, k, n) ==
    IF m.c.by[n] = 0 /\ Sessions(m) >= CAP THEN Dying(Count(m, "full"), k, "full")
    ELSE LET old == m.c.by[n]
             sid == m.c.nsid + 1
             m1 == [m EXCEPT !.c.nsid = sid, !.c.cur[n] = sid, !.c.cs[k].node = n, !.c.cs[k].sid = sid,
                             !.c.hs = @ - 1, !.c.by[n] = k, !.c.cnt.opened = @ + 1]
         IN IF old # 0 /\ old # k /\ m.c.cs[old].on /\ m.c.cs[old].sid # 0 THEN Dying(m1, old, "replaced") ELSE m1

\* state.rs on_read with outcome x (a read of n > 0 bytes also sets last_rx); the buffer goes back. reply: the
\* bytes made the core queue a frame on this conn (a handshake answer, a reply to a frame)
OnRead(m, k, x, n, reply, slow, now) ==
    LET m0 == [m EXCEPT !.c.cs[k].rd = FALSE]
        m1 == IF x = "zero" THEN m0 ELSE [m0 EXCEPT !.c.cs[k].rx = now]
        hs == m1.c.cs[k].node = 0
        m2 == CASE x = "zero" -> Dying(m1, k, "peer")
                [] x = "junk" -> Dying(m1, k, "proto")
                [] x = "open" /\ hs -> OnOpen(m1, k, n)
                [] x = "hello" /\ hs -> m1
                [] x = "frame" /\ ~hs -> m1
                [] OTHER -> Dying(m1, k, "proto")
    IN IF reply /\ x \in {"hello", "open", "frame"} THEN Push(m2, k, slow) ELSE m2

\* state.rs on_write with outcome x: all of the buffer written, part of it (u: the units it has not written, rounded
\* up, at most what was unsent), or none (the peer is gone)
OnWrite(m, k, x, u) ==
    LET m0 == [m EXCEPT !.c.cs[k].wr = FALSE]
    IN CASE x = "all" -> [m0 EXCEPT !.c.cs[k].wb = 0, !.c.cs[k].un = 0, !.c.cs[k].off = FALSE]
         [] x = "part" -> [m0 EXCEPT !.c.cs[k].off = TRUE, !.c.cs[k].un = IF u < @ THEN u ELSE @]
         [] OTHER -> Dying(m0, k, "peer")

\* state.rs complete: an accept; a read or write applied only while its tag names the same conn (slot_of)
Matches(m, op) == op.slot \in Slots(m) /\ m.c.cs[op.slot].on /\ m.c.cs[op.slot].id = op.id
\* to: the bytes also carried a frame for node to (0: none), queued on its conn, slow there by tslow; for a write, n is
\* the u of OnWrite
Fwd(m, to, tslow) == IF to # 0 /\ m.c.by[to] # 0 THEN Push(m, m.c.by[to], tslow) ELSE m
Complete(m, op, x, n, kind, reply, slow, to, tslow, now, late) ==
    LET m0 == [m EXCEPT !.o = @ \ {op}] IN
    IF op.k = "acc"
    THEN IF x = "ok" THEN AddConn([m0 EXCEPT !.c.acc = FALSE, !.ends = Append(@, 0)], Len(m.ends) + 1, kind, now, late)
         ELSE [Count(m0, "accerr") EXCEPT !.c.acc = FALSE, !.c.pause = now + PAUSE]
    ELSE IF ~Matches(m0, op) THEN [m0 EXCEPT !.late = TRUE]
    ELSE IF op.k = "rd" THEN Fwd(OnRead(m0, op.slot, x, n, reply, slow, now), to, tslow)
    ELSE OnWrite(m0, op.slot, x, n)

\* conn.rs take_read and take_write for one live conn that is not dying: a read when none is out; a write when
\* none is out and the buffer was partly written (from its offset, unsent as it was) or units are queued (TCP takes
\* them all, WebSocket one frame; all of them unsent)
Submit1(m, k) ==
    LET x == m.c.cs[k]
        rd == ~x.rd
        wr == ~x.wr /\ (x.off \/ x.q > 0)
        t == TagOf(m, k)
        take == IF x.off THEN 0 ELSE IF x.kind = "tcp" THEN x.q ELSE 1
    IN [m EXCEPT !.c.cs[k].rd = TRUE,
                 !.c.cs[k].wr = @ \/ wr,
                 !.c.cs[k].q = @ - (IF wr THEN take ELSE 0),
                 !.c.cs[k].wb = IF wr /\ ~x.off THEN take ELSE @,
                 !.c.cs[k].un = IF wr /\ ~x.off THEN take ELSE @,
                 !.o = @ \cup (IF rd THEN {[k |-> "rd", id |-> t.id, slot |-> k, h |-> x.h]} ELSE {})
                         \cup (IF wr THEN {[k |-> "wr", id |-> t.id, slot |-> k, h |-> x.h]} ELSE {})]

RECURSIVE SubmitFrom(_, _)
SubmitFrom(m, k) ==
    IF k > Len(m.c.cs) THEN m
    ELSE SubmitFrom(IF m.c.cs[k].on /\ m.c.cs[k].dy = "" THEN Submit1(m, k) ELSE m, k + 1)

\* state.rs finish, then Carriers::close of its stream
Finish(m, k, late) ==
    LET x == m.c.cs[k]
        n == x.node
        m1 == [m EXCEPT !.c.cs[k] = NoConn, !.c.free = Append(@, k), !.c.cnt.closed = @ + 1,
                        !.c.hs = IF n = 0 THEN @ - 1 ELSE @,
                        !.c.by = IF n # 0 /\ @[n] = k THEN [@ EXCEPT ![n] = 0] ELSE @,
                        !.c.cur = IF n # 0 /\ @[n] = x.sid THEN [@ EXCEPT ![n] = 0] ELSE @]
    IN m1

\* part.rs poll, the reaps: pop_reap takes the reap list from its end and skips an entry whose slot no longer holds
\* that conn; each conn it gives is finished and its stream closed
RECURSIVE Reap(_, _)
Reap(m, late) ==
    IF m.c.rp = <<>> THEN m
    ELSE LET e == Last(m.c.rp)
             m0 == [m EXCEPT !.c.rp = Front(@)]
         IN Reap(IF e.k \in Slots(m0) /\ m0.c.cs[e.k].on /\ m0.c.cs[e.k].id = e.id
                 THEN Close(Finish(m0, e.k, late), m0.c.cs[e.k].h, late) ELSE m0, late)

\* part.rs poll: the accept, at most one completion (done: [op, x, n, kind, reply, slow, to, tslow]; done.op.k =
\* "none" when the host had none), the submits, the reaps
NoOp == [k |-> "none", id |-> 0, slot |-> 0, h |-> 0]
NoDone == [op |-> NoOp, x |-> "", n |-> 0, kind |-> "tcp", reply |-> FALSE, slow |-> FALSE, to |-> 0, tslow |-> FALSE]
WantAccept(m, now) == ~m.c.acc /\ ~m.c.stop /\ now >= m.c.pause
Poll(m, now, done, late) ==
    LET m1 == IF WantAccept(m, now) THEN [m EXCEPT !.c.acc = TRUE, !.o = @ \cup {AccOp}] ELSE m
        m2 == IF done.op.k = "none" THEN m1
              ELSE Complete(m1, done.op, done.x, done.n, done.kind, done.reply, done.slow, done.to,
                           done.tslow, now, late)
    IN Reap(SubmitFrom(m2, 1), late)

\* state.rs on_timeout: the machine's first timer pings every member (slow per conn by the map), then once per
\* CHECK_NS the scan for handshakes past their deadline and silent conns
RECURSIVE PingFrom(_, _, _)
PingFrom(m, k, slow) ==
    IF k > Len(m.c.cs) THEN m
    ELSE PingFrom(IF m.c.cs[k].on /\ m.c.cs[k].node # 0 /\ m.c.by[m.c.cs[k].node] = k THEN Push(m, k, slow[k]) ELSE m,
                  k + 1, slow)
RECURSIVE ScanFrom(_, _, _)
ScanFrom(m, k, now) ==
    IF k > Len(m.c.cs) THEN m
    ELSE LET x == m.c.cs[k]
             m1 == IF ~x.on \/ x.dy # "" THEN m
                   ELSE IF x.node = 0 /\ now >= x.dl THEN Dying(m, k, "hstime")
                   ELSE IF now - x.rx >= IDL THEN Dying(m, k, "idle")
                   ELSE m
         IN ScanFrom(m1, k + 1, now)
Timeout(m, now, slow) ==
    LET m1 == IF m.c.pinged THEN m ELSE [PingFrom(m, 1, slow) EXCEPT !.c.pinged = TRUE]
    IN IF now < m1.c.chk THEN m1 ELSE ScanFrom([m1 EXCEPT !.c.chk = now + CHK], 1, now)

\* Part::stop: begin_shutdown
RECURSIVE DieFrom(_, _, _)
DieFrom(m, k, why) == IF k > Len(m.c.cs) THEN m ELSE DieFrom(Dying(m, k, why), k + 1, why)
Stop(m) == DieFrom([m EXCEPT !.c.stop = TRUE], 1, "shutdown")

\* Part::end: abort_all finishes every conn in slot order and drops its stream (no close); stopping and accept_out are
\* cleared (fix R2: the next run asks for its accept again); Carriers::ended abandons every operation out. The reap
\* list keeps the entries begin_shutdown pushed, each naming a conn just finished: conn ids only grow (place), so
\* pop_reap skips every one of them, and the model drops them here
RECURSIVE DropFrom(_, _)
DropFrom(m, k) ==
    IF k > Len(m.c.cs) THEN m
    ELSE DropFrom(IF m.c.cs[k].on THEN [Finish(m, k, FALSE) EXCEPT !.drop = @ \cup {m.c.cs[k].h}] ELSE m, k + 1)
End(m) == [DropFrom(Stop(m), 1) EXCEPT !.c.stop = FALSE, !.c.acc = FALSE, !.o = {}, !.c.rp = <<>>]
=============================================================================
