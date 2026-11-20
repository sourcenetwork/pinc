----------------------------- MODULE FacadeWaits -----------------------------
(***************************************************************************)
(* The waiters of one session of the facade and the events that wake them: *)
(* crates/pinc/src/engine.rs (Core::add_wait, forget, wake_s, on_event,    *)
(* stream_opened, send_failed, session_down, stop, end_session, and the    *)
(* notify_all of Core::service when the endpoint dropped an event), the    *)
(* attempts of crates/pinc/src/engine/ops.rs (accept_stream, read, write,  *)
(* read_datagram, closed, answered) and the order of a poll in             *)
(* crates/pinc/src/drive.rs (Shared::run_as: an attempt runs only after a  *)
(* service that handled nothing; a Wait registers, a Done forgets).        *)
(*                                                                         *)
(* Each future runs one operation of Op on the session (read and write on  *)
(* one stream, 0). The transport's side (Env) changes what a future waits  *)
(* for and queues an event in the endpoint's bounded event queue (EQ       *)
(* places) in the order of pinc-core's EventRing: a full queue drops a new *)
(* read or write notification, evicts the oldest such one for any other    *)
(* event, and refuses the change (the stall) when it holds nothing it may  *)
(* drop. A drop is the counter `lost` that the next service turns into a   *)
(* notify_all. Read and room notifications are edge triggered (raised only *)
(* when the stream had nothing or no room), the weaker of the two choices. *)
(*                                                                         *)
(* The core's drain of BUDGET events per service is one event per step:    *)
(* an attempt runs only once the queue is empty (drive.rs returns Io and   *)
(* polls again while a service handled anything), so how the drain is cut  *)
(* is invisible to a waiter. Opens (SKey::Open) are FacadeOpen.tla's; the  *)
(* driving role and its baton are FacadeTurn.tla's; the standby slab is    *)
(* FacadeStandby.tla's. A waiting future here is one whose ticket is       *)
(* armed.                                                                  *)
(*                                                                         *)
(* Properties, from the docs of engine.rs and conn.rs: a wake is never     *)
(* lost (NoLostWake, WakeLive), a future waits only while registered on    *)
(* a live session (Registered, WaitsOwned), only the events of its key     *)
(* wake it (WakeExact), a closed session ends every waiter with its one    *)
(* reason                                                                  *)
(* (ClosedReason, EndedOnce, EndedWhenGone), streams the peer opened are   *)
(* accepted in order, once, and refused past the accept limit (AcceptFifo, *)
(* AcceptBound, AcceptKept), the stopped streams remembered stay within    *)
(* TRACKED (FailBound) and are only streams the peer stopped, not ones     *)
(* refused (FailOnlyStopped, fix F6), and a refused call changes nothing   *)
(* (ErrKeeps).                                                             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Op,       \* the operation of each future: a sequence over Ops
    Env,      \* the changes the transport may make: a subset of EnvAll
    ACAP,     \* Limits::accept_streams, the accept queue's places
    EQ,       \* the places of the endpoint's event queue
    MAXEV,    \* the most transport changes in a behaviour
    MAXOPEN,  \* the most streams the peer opens
    NSTOP,    \* stop-sending arrives on streams 0 .. NSTOP - 1
    TRK,      \* TRACKED, the stopped streams a session remembers
    DQ        \* the datagrams the endpoint holds for the session

Ops == {"acceptBi", "read", "write", "dgram", "closed", "answered"}
EnvAll == {"open", "data", "fin", "room", "stop", "dgram", "answer", "close", "shutdown"}
\* the configurations' choices
OpsAccept == <<"acceptBi", "read", "answered">>
EnvAccept == {"open", "data", "fin", "answer", "close"}
OpsWrite == <<"write", "dgram", "closed">>
EnvWrite == {"room", "stop", "dgram", "close", "shutdown"}

ASSUME (\A j \in 1..Len(Op) : Op[j] \in Ops) /\ Env \subseteq EnvAll
ASSUME ACAP >= 1 /\ EQ >= 1 /\ TRK >= 1 /\ DQ >= 1 /\ NSTOP >= 0 /\ MAXOPEN >= 0 /\ MAXEV >= 0

Futs == 1..Len(Op)
Reasons == {"closed", "shutdown"}
Lossy == {"readable", "writable"}
Range(q) == {q[j] : j \in DOMAIN q}
RemoveAt(q, j) == SubSeq(q, 1, j - 1) \o SubSeq(q, j + 1, Len(q))

\* the events whose wake_s reaches each operation's key; a session's end reaches every key
WakeKind(op) ==
    CASE op = "acceptBi" -> {"opened"}
      [] op = "read" -> {"readable"}
      [] op = "write" -> {"writable", "stopped"}
      [] op = "dgram" -> {"dgram"}
      [] op = "answered" -> {"answered"}
      [] op = "closed" -> {}

VARIABLES
    st,       \* each future: idle, wait (armed and registered), woken, done
    res,      \* each future's result: none, ok, end, stopped, cmd, or the session's reason
    waits,    \* Sess::waits: pairs <<operation, future>>
    live,     \* the session is in Core::sessions
    ended,    \* SessInfo::ended: none until set once
    acc,      \* Sess::accept_bi
    got,      \* the stream ids accept_bi returned, in order
    refused,  \* streams refused past the accept limit
    dropped,  \* streams queued or announced when the session ended
    fail,     \* Sess::send_fail: stream ids, oldest first
    ans,      \* SessInfo::answered
    up,       \* the transport still holds the session
    nid,      \* streams the peer opened
    rd,       \* chunks readable on stream 0
    rfin,     \* the peer finished stream 0
    room,     \* stream 0 has room to write
    tstop,    \* streams the peer stopped (the transport refuses their writes)
    dq,       \* datagrams held
    ansT,     \* the transport heard the peer
    evq,      \* the endpoint's event queue
    lost,     \* events_dropped moved since the core last looked
    nev       \* transport changes so far

fut == <<st, res, waits>>
sess == <<live, ended, acc, got, refused, dropped, fail, ans>>
tr == <<up, nid, rd, rfin, room, tstop, dq, ansT>>
vars == <<fut, sess, tr, evq, lost, nev>>

Init ==
    /\ st = [f \in Futs |-> "idle"]
    /\ res = [f \in Futs |-> "none"]
    /\ waits = {}
    /\ live = TRUE /\ ended = "none" /\ acc = <<>> /\ got = <<>> /\ refused = {} /\ dropped = {}
    /\ fail = <<>> /\ ans = FALSE
    /\ up = TRUE /\ nid = 0 /\ rd = 0 /\ rfin = FALSE /\ room = FALSE /\ tstop = {} /\ dq = 0 /\ ansT = FALSE
    /\ evq = <<>> /\ lost = FALSE /\ nev = 0

-----------------------------------------------------------------------------
(* The endpoint's event queue (pinc-core queue.rs, EventRing::push).       *)

FirstLossy == CHOOSE j \in 1..Len(evq) : evq[j].k \in Lossy /\ \A m \in 1..(j - 1) : evq[m].k \notin Lossy

Push(e) ==
    \/ /\ Len(evq) < EQ
       /\ evq' = Append(evq, e) /\ lost' = lost
    \/ /\ Len(evq) >= EQ /\ e.k \in Lossy
       /\ evq' = evq /\ lost' = TRUE
    \/ /\ Len(evq) >= EQ /\ e.k \notin Lossy
       /\ \E j \in 1..Len(evq) : evq[j].k \in Lossy
       /\ evq' = Append(RemoveAt(evq, FirstLossy), e) /\ lost' = TRUE

\* one change of the transport: it queues its event (or drops one, or stalls)
Change(kind, e) == /\ kind \in Env /\ up /\ nev < MAXEV /\ Push(e) /\ nev' = nev + 1
\* an edge-triggered notification: queued only if the stream had nothing (or no room) before
Edge(kind, was, e) ==
    /\ kind \in Env /\ up /\ nev < MAXEV /\ nev' = nev + 1
    /\ IF was THEN UNCHANGED <<evq, lost>> ELSE Push(e)

PeerOpen ==
    /\ nid < MAXOPEN /\ Change("open", [k |-> "opened", s |-> nid + 1])
    /\ nid' = nid + 1
    /\ UNCHANGED <<fut, sess, up, rd, rfin, room, tstop, dq, ansT>>
PeerData ==
    /\ ~rfin /\ Edge("data", rd > 0, [k |-> "readable", s |-> 0])
    /\ rd' = rd + 1
    /\ UNCHANGED <<fut, sess, up, nid, rfin, room, tstop, dq, ansT>>
PeerFin ==
    /\ ~rfin /\ Edge("fin", rd > 0, [k |-> "readable", s |-> 0])
    /\ rfin' = TRUE
    /\ UNCHANGED <<fut, sess, up, nid, rd, room, tstop, dq, ansT>>
Room ==
    /\ ~room /\ Change("room", [k |-> "writable", s |-> 0])
    /\ room' = TRUE
    /\ UNCHANGED <<fut, sess, up, nid, rd, rfin, tstop, dq, ansT>>
PeerStop(id) ==
    /\ id \notin tstop /\ Change("stop", [k |-> "stopped", s |-> id])
    /\ tstop' = tstop \cup {id}
    /\ UNCHANGED <<fut, sess, up, nid, rd, rfin, room, dq, ansT>>
\* a full receive queue drops its oldest datagram (DgramQueue.tla); the count stays at DQ
PeerDgram ==
    /\ Change("dgram", [k |-> "dgram", s |-> 0])
    /\ dq' = IF dq < DQ THEN dq + 1 ELSE DQ
    /\ UNCHANGED <<fut, sess, up, nid, rd, rfin, room, tstop, ansT>>
PeerAnswer ==
    /\ ~ansT /\ Change("answer", [k |-> "answered", s |-> 0])
    /\ ansT' = TRUE
    /\ UNCHANGED <<fut, sess, up, nid, rd, rfin, room, tstop, dq>>
PeerClose ==
    /\ Change("close", [k |-> "closed", s |-> 0])
    /\ up' = FALSE
    /\ UNCHANGED <<fut, sess, nid, rd, rfin, room, tstop, dq, ansT>>

-----------------------------------------------------------------------------
(* The core's side: on_event, wake_s, send_failed, end_session.             *)

\* the futures registered on operation `op`, which wake_s notifies and takes off the list
Keyed(op) == {f \in Futs : <<op, f>> \in waits}
Unkey(op) == waits \ {<<op, f>> : f \in Futs}

\* send_failed: the stream's entry replaces an older one; at TRK entries the oldest goes
SendFailed(q, id) ==
    LET g == SelectSeq(q, LAMBDA x : x # id)
    IN Append(IF Len(g) >= TRK THEN Tail(g) ELSE g, id)

\* the futures that move from wait to woken when `w` are notified, and with notify_all if `all`
Wake(w, all) == st' = [f \in Futs |-> IF st[f] = "wait" /\ (f \in w \/ all) THEN "woken" ELSE st[f]]

\* end_session: the reason is set first (once), then every registered future is notified; the record goes
EndSession(r, all) ==
    /\ live' = FALSE
    /\ ended' = IF ended = "none" THEN r ELSE ended
    /\ Wake({w[2] : w \in waits}, all)
    /\ waits' = {}
    /\ dropped' = dropped \cup Range(acc)
    /\ acc' = <<>> /\ fail' = <<>>
    /\ UNCHANGED <<res, got, refused, ans>>

\* one event, handled while the session is live; `all` is the notify_all of a moved drop counter
OnEvent(e, all) ==
    CASE e.k = "opened" ->
            IF Len(acc) < ACAP
            THEN /\ acc' = Append(acc, e.s) /\ Wake(Keyed("acceptBi"), all) /\ waits' = Unkey("acceptBi")
                 /\ UNCHANGED <<res, live, ended, got, refused, dropped, fail, ans>>
            \* refused: reset BUSY, stop-sending BUSY, discard; no failure entry, since no writer of it is ever
            \* made (fix F6: the entry could evict a live writer's past TRACKED)
            ELSE /\ refused' = refused \cup {e.s} /\ Wake({}, all)
                 /\ UNCHANGED <<res, waits, live, ended, acc, got, dropped, fail, ans>>
      [] e.k = "readable" ->
            /\ Wake(Keyed("read"), all) /\ waits' = Unkey("read")
            /\ UNCHANGED <<res, live, ended, acc, got, refused, dropped, fail, ans>>
      [] e.k = "writable" ->
            /\ Wake(Keyed("write"), all) /\ waits' = Unkey("write")
            /\ UNCHANGED <<res, live, ended, acc, got, refused, dropped, fail, ans>>
      [] e.k = "stopped" ->
            /\ fail' = SendFailed(fail, e.s)
            /\ IF e.s = 0 THEN Wake(Keyed("write"), all) /\ waits' = Unkey("write")
                          ELSE Wake({}, all) /\ UNCHANGED waits
            /\ UNCHANGED <<res, live, ended, acc, got, refused, dropped, ans>>
      [] e.k = "dgram" ->
            /\ Wake(Keyed("dgram"), all) /\ waits' = Unkey("dgram")
            /\ UNCHANGED <<res, live, ended, acc, got, refused, dropped, fail, ans>>
      [] e.k = "answered" ->
            /\ ans' = TRUE /\ Wake(Keyed("answered"), all) /\ waits' = Unkey("answered")
            /\ UNCHANGED <<res, live, ended, acc, got, refused, dropped, fail>>
      [] e.k = "closed" -> EndSession("closed", all)

\* Core::service: the head event, then the notify_all if the drop counter moved. The events of a session no
\* longer in the table are ignored (a stream it announced is gone with it).
Service ==
    /\ evq # <<>>
    /\ evq' = Tail(evq) /\ lost' = FALSE
    /\ IF live
       THEN OnEvent(Head(evq), lost)
       ELSE /\ Wake({}, lost)
            /\ dropped' = IF Head(evq).k = "opened" THEN dropped \cup {Head(evq).s} ELSE dropped
            /\ UNCHANGED <<res, waits, live, ended, acc, got, refused, fail, ans>>
    /\ UNCHANGED <<tr, nev>>

\* Core::stop: the endpoint ends every session with the shutdown error
Shutdown ==
    /\ "shutdown" \in Env /\ live
    /\ EndSession("shutdown", FALSE)
    /\ UNCHANGED <<tr, evq, lost, nev>>

-----------------------------------------------------------------------------
(* The attempts (ops.rs) and the end of a poll (drive.rs).                  *)

Unreg(f) == waits \ {<<k, f>> : k \in Ops}
\* Done: the future ends with `r`; its Turn forgets its registration
Done(f, r) ==
    /\ st' = [st EXCEPT ![f] = "done"] /\ res' = [res EXCEPT ![f] = r] /\ waits' = Unreg(f)
\* Wait: forget the old registration, add_wait (which does nothing on a session not in the table), arm
WaitOn(f) ==
    /\ st' = [st EXCEPT ![f] = "wait"] /\ UNCHANGED res
    /\ waits' = IF live THEN Unreg(f) \cup {<<Op[f], f>>} ELSE Unreg(f)

Attempt(f) ==
    /\ st[f] \in {"idle", "woken"} /\ evq = <<>>
    /\ CASE Op[f] = "acceptBi" ->
              IF ~live THEN Done(f, ended) /\ UNCHANGED <<sess, tr>>
              ELSE IF acc # <<>>
              THEN Done(f, "ok") /\ got' = Append(got, Head(acc)) /\ acc' = Tail(acc)
                   /\ UNCHANGED <<live, ended, refused, dropped, fail, ans, tr>>
              ELSE WaitOn(f) /\ UNCHANGED <<sess, tr>>
         [] Op[f] = "read" ->
              IF ~live THEN Done(f, ended) /\ UNCHANGED <<sess, tr>>
              ELSE IF rd > 0 THEN Done(f, "ok") /\ rd' = rd - 1
                                  /\ UNCHANGED <<sess, up, nid, rfin, room, tstop, dq, ansT>>
              ELSE IF rfin THEN Done(f, "end") /\ UNCHANGED <<sess, tr>>
              ELSE WaitOn(f) /\ UNCHANGED <<sess, tr>>
         [] Op[f] = "write" ->
              IF ~live THEN Done(f, ended) /\ UNCHANGED <<sess, tr>>
              ELSE IF 0 \in Range(fail) THEN Done(f, "stopped") /\ UNCHANGED <<sess, tr>>
              \* a stopped stream whose entry was evicted: the transport refuses the write
              ELSE IF 0 \in tstop THEN Done(f, "cmd") /\ UNCHANGED <<sess, tr>>
              ELSE IF room THEN Done(f, "ok") /\ room' \in BOOLEAN
                                /\ UNCHANGED <<sess, up, nid, rd, rfin, tstop, dq, ansT>>
              ELSE WaitOn(f) /\ UNCHANGED <<sess, tr>>
         [] Op[f] = "dgram" ->
              IF ~live THEN Done(f, ended) /\ UNCHANGED <<sess, tr>>
              ELSE IF dq > 0 THEN Done(f, "ok") /\ dq' = dq - 1
                                  /\ UNCHANGED <<sess, up, nid, rd, rfin, room, tstop, ansT>>
              ELSE WaitOn(f) /\ UNCHANGED <<sess, tr>>
         [] Op[f] = "closed" ->
              IF live THEN WaitOn(f) /\ UNCHANGED <<sess, tr>>
              ELSE Done(f, ended) /\ UNCHANGED <<sess, tr>>
         [] Op[f] = "answered" ->
              IF ans THEN Done(f, "ok") /\ UNCHANGED <<sess, tr>>
              ELSE IF live THEN WaitOn(f) /\ UNCHANGED <<sess, tr>>
              ELSE Done(f, ended) /\ UNCHANGED <<sess, tr>>
    /\ UNCHANGED <<evq, lost, nev>>

\* a waiting future dropped (cancelled): its Turn forgets the registration
Drop(f) ==
    /\ st[f] = "wait"
    /\ st' = [st EXCEPT ![f] = "done"] /\ waits' = Unreg(f)
    /\ UNCHANGED <<res, sess, tr, evq, lost, nev>>

Next ==
    \/ PeerOpen \/ PeerData \/ PeerFin \/ Room \/ PeerDgram \/ PeerAnswer \/ PeerClose
    \/ \E id \in 0..(NSTOP - 1) : PeerStop(id)
    \/ Service \/ Shutdown
    \/ \E f \in Futs : Attempt(f) \/ Drop(f)

Spec == Init /\ [][Next]_vars /\ WF_vars(Service)

-----------------------------------------------------------------------------
(* Properties.                                                              *)

TypeOK ==
    /\ st \in [Futs -> {"idle", "wait", "woken", "done"}]
    /\ res \in [Futs -> {"none", "ok", "end", "stopped", "cmd"} \cup Reasons]
    /\ waits \subseteq Ops \X Futs
    /\ ended \in {"none"} \cup Reasons
    /\ Len(evq) <= EQ

\* what would let the attempt of a waiting future end, from the transport's state
Ready(f) ==
    \/ ~up
    \/ CASE Op[f] = "acceptBi" -> acc # <<>>
         [] Op[f] = "read" -> rd > 0 \/ rfin
         [] Op[f] = "write" -> room \/ 0 \in tstop
         [] Op[f] = "dgram" -> dq > 0
         [] Op[f] = "closed" -> FALSE
         [] Op[f] = "answered" -> ansT
\* what will wake it: an event of its key or the session's end still queued, or a drop not yet looked at
Pending(f) == lost \/ \E j \in 1..Len(evq) : evq[j].k \in WakeKind(Op[f]) \cup {"closed"}

\* a wake is never lost: a waiting future that could end has its wake on the way
NoLostWake == \A f \in Futs : st[f] = "wait" /\ Ready(f) => Pending(f)
\* and it is woken (WF of the service only)
WakeLive == \A f \in Futs : (st[f] = "wait" /\ Ready(f)) ~> (st[f] # "wait")

\* a future waits only on a live session, registered for its own key
Registered == \A f \in Futs : st[f] = "wait" => live /\ <<Op[f], f>> \in waits
\* nothing grows with history: only a future still running is registered
WaitsOwned == \A w \in waits : st[w[2]] \in {"wait", "woken"}

\* only an event of the future's key, the session's end or a dropped event wakes a waiting future
WakeExact ==
    [][\A f \in Futs :
          (st[f] = "wait" /\ st'[f] = "woken")
            => \/ lost
               \/ live /\ ~live'
               \/ evq # <<>> /\ Head(evq).k \in WakeKind(Op[f])]_vars

\* a future ended by the session's end gets the session's one reason
ClosedReason == \A f \in Futs : res[f] \in Reasons => res[f] = ended
EndedWhenGone == ~live => ended \in Reasons
EndedOnce == [][ended # "none" => ended' = ended]_vars

\* streams the peer opened: accepted in the order opened, each in exactly one place
AcceptFifo == LET s == got \o acc IN \A j \in 1..(Len(s) - 1) : s[j] < s[j + 1]
AcceptBound == Len(acc) <= ACAP
InQueue(id) == \E j \in 1..Len(evq) : evq[j] = [k |-> "opened", s |-> id]
AcceptKept ==
    \A id \in 1..nid :
        (IF id \in Range(acc) THEN 1 ELSE 0) + (IF id \in Range(got) THEN 1 ELSE 0)
          + (IF id \in refused THEN 1 ELSE 0) + (IF id \in dropped THEN 1 ELSE 0)
          + (IF InQueue(id) THEN 1 ELSE 0) = 1

FailBound == Len(fail) <= TRK /\ Cardinality(Range(fail)) = Len(fail)
\* a failure entry is kept only for a stream the peer stopped, whose writer can read it (fix F6)
FailOnlyStopped == Range(fail) \subseteq tstop

\* a refused call (an error result) changes nothing of the session or the transport
ErrKeeps ==
    [][(\E f \in Futs : res[f] = "none" /\ res'[f] \in {"stopped", "cmd"} \cup Reasons)
         => UNCHANGED <<sess, tr, evq, lost>>]_vars

-----------------------------------------------------------------------------
(* Witnesses: each says a state is never reached; TLC must find it.         *)

\* the accept queue was full and a stream was refused
NoRefuse == refused = {}
\* a future could end while its notification was dropped: only the drop counter wakes it
NoLossWindow == ~(lost /\ \E f \in Futs : st[f] = "wait" /\ Ready(f) /\ up
                         /\ ~\E j \in 1..Len(evq) : evq[j].k \in WakeKind(Op[f]) \cup {"closed"})
\* a stopped stream's entry was evicted past TRACKED and its writer saw the transport's refusal
NoEvict == \A f \in Futs : res[f] # "cmd"
=============================================================================
