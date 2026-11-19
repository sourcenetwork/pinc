--------------------------- MODULE FacadeStreamOps ---------------------------
(***************************************************************************)
(* The operations on one stream and on the datagrams of one connection of  *)
(* the facade, as functions of a state record: crates/pinc/src/stream.rs    *)
(* (SendStream::write, finish, reset, Drop; RecvStream::read, stop, Drop),  *)
(* crates/pinc/src/conn.rs (Connection::recv_datagram, send_datagram,       *)
(* close) over crates/pinc/src/engine/ops.rs (Core::write, finish, reset,   *)
(* drop_send, read, read_with, stop_recv, drop_recv, read_datagram,         *)
(* send_datagram, close_session) and the events of engine.rs that change    *)
(* them (StreamStopped -> send_failed, StreamReadable -> discard_if_dropped,*)
(* Closed -> session_down). Each operation returns [s |-> next state,      *)
(* o |-> result]; FacadeStream.tla and TraceFacadeStream.tla share them.    *)
(*                                                                         *)
(* A result is [r, k, c, v]: r 0 ok (v the chunk or datagram number), 1    *)
(* the end of the stream, 2 an error of kind k with code c, 3 the call     *)
(* waits (it changes nothing; FacadeWaits.tla says who wakes it). Error    *)
(* kinds: 1 Stopped, 2 Reset, 3 Closed by the peer, 4 Closed by this side, *)
(* 5 TooLarge. Codes are constants: RC the handle's reset, SC its stop, PR  *)
(* the peer's reset, PC the peer's stop-sending, PCC the peer's close, LC   *)
(* the local close.                                                        *)
(*                                                                         *)
(* DOC = TRUE is the documented behaviour; DOC = FALSE the code as written  *)
(* where the two differ (the findings, each named at its branch):          *)
(*  - write and finish after reset(code): documented "the error that ended *)
(*    the stream", the code returns Stopped(0) and Ok;                      *)
(*  - dropping or stopping a RecvStream when the session already tracks    *)
(*    TRACKED (128) discarded streams (DFULL): documented "discards what    *)
(*    the peer still sends", the code keeps the bytes unread;              *)
(*  - a stop-sending that arrives after the SendStream was dropped:         *)
(*    documented "a table holds an entry only while its stream lives", the *)
(*    code records an entry no handle removes;                              *)
(*  - recv_datagram after the connection ended: documented "the reason ...  *)
(*    once the datagrams that arrived before are read", the code returns    *)
(*    the reason at once.                                                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS DOC, DFULL, DQ, RC, SC, PR, PC, PCC, LC

STOPPED == 1
RESET == 2
PEERCLOSED == 3
LOCALCLOSED == 4
TOOLARGE == 5

R(r, k, c, v) == [r |-> r, k |-> k, c |-> c, v |-> v]
Ok(v) == R(0, 0, 0, v)
EndR == R(1, 0, 0, 0)
Err(k, c) == R(2, k, c, 0)
WaitR == R(3, 0, 0, 0)
Range(q) == {q[j] : j \in DOMAIN q}

\* SessInfo::gone: the reason the connection ended
Gone(s) == IF s.why = "peer" THEN Err(PEERCLOSED, PCC) ELSE Err(LOCALCLOSED, LC)

\* a live session whose stream already holds `pw` chunks from the peer
S0(pw) ==
    [live |-> TRUE, why |-> "none",
     \* send side: the handle's `finished`, whether it reset, chunks the transport took, the transport's FIN and
     \* reset, the core's send_fail entry, the peer's stop-sending, room, the drop and whether the session lived then
     hfin |-> FALSE, hreset |-> FALSE, tw |-> 0, tfin |-> FALSE, treset |-> FALSE,
     failed |-> FALSE, fcode |-> 0, pstop |-> FALSE, room |-> TRUE, dropS |-> FALSE, dropLive |-> FALSE,
     \* receive side: chunks the peer sent, its FIN and reset, chunks consumed, chunks the application read,
     \* the handle's cached end and stop, the stop-sending sent, the drop, the discard entry
     pw |-> pw, pfin |-> FALSE, preset |-> FALSE, rpos |-> 0, got |-> <<>>, hend |-> "none",
     hstop |-> FALSE, stopSent |-> FALSE, dropR |-> FALSE, disc |-> FALSE,
     \* datagrams: received so far, held (oldest first), read, dropped to make room, sent
     dn |-> 0, dq |-> <<>>, dgot |-> <<>>, ddrop |-> {}, dsent |-> 0]

Res(t, o) == [s |-> t, o |-> o]

-----------------------------------------------------------------------------
(* Send side.                                                               *)

\* SendStream::write then Core::write: the handle's own refusal, the stopped stream, the session, the room
Write(s) ==
    IF s.hfin
    THEN Res(s, IF DOC /\ s.hreset THEN Err(STOPPED, RC) ELSE Err(STOPPED, 0))   \* finding: Stopped(0) after reset
    ELSE IF s.live /\ s.failed THEN Res(s, Err(STOPPED, s.fcode))
    ELSE IF ~s.live THEN Res(s, Gone(s))
    ELSE IF s.room THEN Res([s EXCEPT !.tw = @ + 1], Ok(s.tw + 1))
    ELSE Res(s, WaitR)

\* SendStream::finish: idempotent once finished; Core::finish checks the failure, then the session
Finish(s) ==
    IF s.hfin
    THEN Res(s, IF DOC /\ s.hreset THEN Err(STOPPED, RC) ELSE Ok(0))              \* finding: Ok after reset
    ELSE IF s.live /\ s.failed THEN Res(s, Err(STOPPED, s.fcode))
    ELSE IF ~s.live THEN Res(s, Gone(s))
    ELSE Res([s EXCEPT !.hfin = TRUE, !.tfin = TRUE], Ok(0))

\* SendStream::reset: `finished` first; Core::reset sends the reset and records Stopped(code) (send_failed does
\* nothing on a session no longer in the table)
Reset(s) ==
    Res([s EXCEPT !.hfin = TRUE, !.hreset = TRUE,
                  !.treset = s.live \/ s.treset,
                  !.failed = s.live \/ s.failed,
                  !.fcode = IF s.live THEN RC ELSE s.fcode], Ok(0))

\* Drop for SendStream, Core::drop_send: finish unless finished or failed, then forget the failure
DropSend(s) ==
    Res([s EXCEPT !.dropS = TRUE, !.dropLive = s.live,
                  !.tfin = s.tfin \/ (~s.hfin /\ ~s.failed /\ s.live),
                  !.failed = FALSE], Ok(0))

\* StreamStopped -> send_failed(Stopped(code)); documented: not for a stream whose handle is gone
PeerStop(s) ==
    [s EXCEPT !.pstop = TRUE,
              !.failed = IF DOC /\ s.dropS THEN s.failed ELSE TRUE,                \* finding: entry after the drop
              !.fcode = IF DOC /\ s.dropS THEN s.fcode ELSE PC]

-----------------------------------------------------------------------------
(* Receive side.                                                            *)

\* RecvStream::read: the stop, the cached end, then Core::read (session, reset, a chunk, the FIN, wait); the end
\* that comes with the last chunk is cached
Read(s) ==
    IF s.hstop THEN Res(s, Err(STOPPED, SC))
    ELSE IF s.hend = "fin" THEN Res(s, EndR)
    ELSE IF s.hend = "reset" THEN Res(s, Err(RESET, PR))
    ELSE IF ~s.live THEN Res(s, Gone(s))
    ELSE IF s.preset THEN Res([s EXCEPT !.hend = "reset"], Err(RESET, PR))
    ELSE IF s.rpos < s.pw
    THEN Res([s EXCEPT !.rpos = @ + 1, !.got = Append(@, s.rpos + 1),
                       !.hend = IF s.rpos + 1 = s.pw /\ s.pfin THEN "fin" ELSE "none"], Ok(s.rpos + 1))
    ELSE IF s.pfin THEN Res([s EXCEPT !.hend = "fin"], EndR)
    ELSE Res(s, WaitR)

\* Core::drop_recv: listed in Sess::discard (only below TRACKED in the code), then discard_if_dropped consumes
\* what is held until the stream ends
DropRecvCore(s) ==
    IF DOC \/ ~DFULL
    THEN [s EXCEPT !.rpos = s.pw, !.disc = ~(s.pfin \/ s.preset)]
    ELSE s                                                                        \* finding: nothing discarded

\* RecvStream::stop: `stopped` first; Core::stop_recv sends stop-sending, then drop_recv
Stop(s) ==
    LET t == [s EXCEPT !.hstop = TRUE]
    IN Res(IF s.live THEN DropRecvCore([t EXCEPT !.stopSent = TRUE]) ELSE t, Ok(0))

\* Drop for RecvStream: drop_recv unless the stream ended or was stopped
DropRecv(s) ==
    LET t == [s EXCEPT !.dropR = TRUE]
    IN Res(IF s.live /\ s.hend = "none" /\ ~s.hstop THEN DropRecvCore(t) ELSE t, Ok(0))

\* the peer's chunk, FIN and reset; StreamReadable runs discard_if_dropped on a discarded stream
PeerSend(s) == [s EXCEPT !.pw = @ + 1, !.rpos = IF s.disc THEN s.pw + 1 ELSE @]
PeerFin(s) == [s EXCEPT !.pfin = TRUE, !.rpos = IF s.disc THEN s.pw ELSE @, !.disc = FALSE]
PeerReset(s) == [s EXCEPT !.preset = TRUE, !.disc = FALSE]

\* what the peer's reader has seen of this stream after reading all it can: its own stop, the reset, the end
\* after every chunk, or every chunk so far and a wait
PeerRead(s) ==
    IF s.pstop THEN Err(STOPPED, PC)
    ELSE IF s.treset THEN Err(RESET, RC)
    ELSE IF s.tfin THEN R(1, 0, 0, s.tw)
    ELSE R(3, 0, 0, s.tw)

-----------------------------------------------------------------------------
(* Datagrams.                                                               *)

\* on_datagram_frame: a full queue of DQ drops its oldest
PeerDgram(s) ==
    [s EXCEPT !.dn = @ + 1,
              !.dq = IF Len(s.dq) >= DQ THEN Append(Tail(s.dq), s.dn + 1) ELSE Append(s.dq, s.dn + 1),
              !.ddrop = IF Len(s.dq) >= DQ THEN @ \cup {Head(s.dq)} ELSE @]

\* Connection::recv_datagram, Core::read_datagram: oldest first; TooLarge leaves it queued
RecvDgram(s, fit) ==
    IF ~DOC /\ ~s.live THEN Res(s, Gone(s))                                       \* finding: reason first
    ELSE IF s.dq # <<>>
    THEN IF fit THEN Res([s EXCEPT !.dq = Tail(@), !.dgot = Append(@, Head(s.dq))], Ok(Head(s.dq)))
         ELSE Res(s, Err(TOOLARGE, 0))
    ELSE IF ~s.live THEN Res(s, Gone(s))
    ELSE Res(s, WaitR)

\* Connection::send_datagram, Core::send_datagram: the session, then the transport's size check
SendDgram(s, big) ==
    IF ~s.live THEN Res(s, Gone(s))
    ELSE IF big THEN Res(s, Err(TOOLARGE, 0))
    ELSE Res([s EXCEPT !.dsent = @ + 1], Ok(s.dsent + 1))

\* the Closed event: session_down; `who` is "peer" or "local" (Connection::close, then the endpoint's Closed)
Close(s, who) == [s EXCEPT !.live = FALSE, !.why = who]
=============================================================================
