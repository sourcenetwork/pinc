---------------------------- MODULE FramePackOps ----------------------------
(***************************************************************************)
(* The VINCER packet builder of vinc-transport (conn/send.rs) as operators *)
(* over the frame codecs of FrameOps.tla, call for call.                   *)
(*                                                                         *)
(* ImplicitStreamLen is implicit_stream_len: the varint at at + head is    *)
(* read (varint::decode), and only when it gives exactly the bytes from    *)
(* its end to the end of the frames is the LEN bit of the type byte at at  *)
(* cleared and the varint taken out. PutStreamHeader is put_stream_header: *)
(* the type, the id, the offset when it is not 0 and the length, each a    *)
(* put_varint that stops the rest when it fails, then the check that the   *)
(* buffer is full.                                                         *)
(*                                                                         *)
(* Fill is fill_frames over what each source holds (a case of             *)
(* FramePack.tla: the ACK, the control frames, the path frames, the        *)
(* chunks the stream layer gives, the datagrams, the credit given back     *)
(* after an answer, the switches and the room), slot by slot in the        *)
(* order of the code, with each slot's own test (the room, the count of    *)
(* recorded frames, MIN_ROOM, REKEY_MAX, whether a failure skips the frame *)
(* or ends the loop) and the place of the last STREAM frame it keeps       *)
(* (last_stream). Built is the test build_packet makes before it seals,    *)
(* and Finish the tail of build_packet: the padding to the least payload,  *)
(* or the length of the kept STREAM frame dropped (implicit_stream_len     *)
(* under the ?, so a refusal gives the packet up), or nothing.             *)
(*                                                                         *)
(* The code's constants are MINROOM = 24, SBUDGET = 11, REKEYMAX = 51 and  *)
(* REFS = 8 (MAX_FRAME_REFS). CLEAR and CHECK are TRUE in the code: FALSE  *)
(* is the wrong rule of a witness (the place kept is not forgotten when a  *)
(* datagram or a credit frame follows the STREAM frame; the length is      *)
(* dropped without checking that the frame ends the payload).              *)
(*                                                                         *)
(* Lean counterpart: Vinc/TransportFramePack.lean, with the theorems of    *)
(* TransportFramePackThm.lean.                                             *)
(***************************************************************************)
EXTENDS FrameOps

CONSTANTS MINROOM, SBUDGET, REKEYMAX, REFS, CLEAR, CHECK

(* ---- the byte functions ---- *)
ClearLen(b) == IF (b \div 2) % 2 = 1 THEN b - 2 ELSE b

\* implicit_stream_len over the frames fr: [ok |-> FALSE], or the bytes dropped and the frames that remain
ImplicitStreamLen(fr, at, head) ==
    LET after == at + head IN
    IF after > Len(fr) THEN [ok |-> FALSE, n |-> 0, out |-> fr]
    ELSE LET d == VLoop(Drop(fr, after), 1, 0, 1) IN
         IF ~d.ok THEN [ok |-> FALSE, n |-> 0, out |-> fr]
         ELSE IF CHECK /\ d.v # Len(fr) - (after + d.r) THEN [ok |-> FALSE, n |-> 0, out |-> fr]
         ELSE LET pre == Take(fr, after) IN
              [ok |-> TRUE, n |-> d.r,
               out |-> (IF at < after THEN [pre EXCEPT ![at + 1] = ClearLen(@)] ELSE pre) \o Drop(fr, after + d.r)]

\* the calls in order against a buffer of cap bytes up to the first that fails: whether all went, the bytes written
RECURSIVE RunPutsPart(_, _, _)
RunPutsPart(cap, w, ps) ==
    IF Len(ps) = 0 THEN [all |-> TRUE, w |-> w]
    ELSE LET r == Put(cap, w, Head(ps)) IN IF ~r.ok THEN [all |-> FALSE, w |-> w] ELSE RunPutsPart(cap, r.v, Tail(ps))

HeaderPuts(id, off, len, fin) ==
    <<PV(StreamType(off, fin, FALSE)), PV(id)>> \o (IF off = 0 THEN <<>> ELSE <<PV(off)>>) \o <<PV(len)>>

\* put_stream_header into a buffer of cap bytes: whether it filled it exactly, and the bytes written
PutStreamHeader(cap, id, off, len, fin) ==
    LET r == RunPutsPart(cap, <<>>, HeaderPuts(id, off, len, fin)) IN [ok |-> r.all /\ Len(r.w) = cap, w |-> r.w]

(* ---- fill_frames ---- *)
PING == [k |-> "Ping"]
WAKE == [k |-> "Wake"]
SLEEP == [k |-> "Sleep"]
READY == [k |-> "Ready"]

\* what the fill holds: the bytes, the frames in order, whether one elicits an ACK, the place kept, the frames recorded
St0 == [w |-> <<>>, fs |-> <<>>, el |-> FALSE, hint |-> <<>>, refs |-> 0, ack |-> FALSE]

Room(c, st) == c.cap - Len(st.w)
\* put: Frame::write into what is left of the payload
Fits(c, st, f) == Write(Room(c, st), f).ok
Add(c, st, f) == [st EXCEPT !.w = @ \o Write(Room(c, st), f).v, !.fs = Append(@, f)]
Eli(st) == [st EXCEPT !.el = TRUE]
Ref(st) == [st EXCEPT !.refs = @ + 1]
\* a slot of at most one frame: pending, under the count of recorded frames when it is recorded, and it fits
One(c, st, pend, f, el, ref) ==
    IF pend /\ (ref => st.refs < REFS) /\ Fits(c, st, f)
    THEN LET s1 == Add(c, st, f) IN
         LET s2 == IF el THEN Eli(s1) ELSE s1 IN IF ref THEN Ref(s2) ELSE s2
    ELSE st

\* the ACK: pending (on the active path only), if ack_len fits what is left
DoAck(c, st) ==
    IF Len(c.ack) = 1 /\ EncodedLen(c.ack[1]) <= Room(c, st) /\ Fits(c, st, c.ack[1])
    THEN [Add(c, st, c.ack[1]) EXCEPT !.ack = TRUE] ELSE st

\* the extension frames: one that is not under the count or does not fit is skipped
RECURSIVE ExtLoop(_, _, _)
ExtLoop(c, st, es) ==
    IF Len(es) = 0 THEN st
    ELSE ExtLoop(c, IF st.refs < REFS /\ EncodedLen(es[1]) <= Room(c, st) /\ Fits(c, st, es[1])
                    THEN Ref(Eli(Add(c, st, es[1]))) ELSE st, Tail(es))

\* the stream layer's control frames: the loop ends under MIN_ROOM, at the count, or at a frame that does not fit
RECURSIVE ScLoop(_, _, _)
ScLoop(c, st, fs) ==
    IF st.refs >= REFS \/ Room(c, st) < MINROOM \/ Len(fs) = 0 \/ ~Fits(c, st, fs[1]) THEN st
    ELSE ScLoop(c, Ref(Eli(Add(c, st, fs[1]))), Tail(fs))

Control(c, st) ==
    LET s1 == One(c, st, c.sleep, SLEEP, TRUE, FALSE)
        s2 == One(c, s1, c.wake, WAKE, TRUE, FALSE)
        s3 == One(c, s2, c.echo, [k |-> "MtuProbeEcho", mtu |-> 1300], FALSE, FALSE)
        s4 == One(c, s3, c.ready, READY, TRUE, TRUE)
        s5 == One(c, s4, c.tickets, [k |-> "NewTickets", es |-> <<>>], TRUE, TRUE)
        s6 == One(c, s5, c.rekey /\ Room(c, s5) >= REKEYMAX, c.rk, TRUE, TRUE) IN
    ScLoop(c, ExtLoop(c, s6, c.ext), c.sc)

Path(c, st) ==
    LET s1 == One(c, st, c.resp, [k |-> "PathResponse", d |-> [i \in 1..8 |-> i]], TRUE, FALSE)
        s2 == One(c, s1, c.pping, PING, TRUE, FALSE) IN
    One(c, s2, c.chal, [k |-> "PathChallenge", d |-> [i \in 1..8 |-> 9 - i]], TRUE, FALSE)

\* the next chunk of the stream layer for a budget of data bytes: the head chunk, cut to the budget
Piece(ch, budget) ==
    IF Len(ch.data) <= budget THEN ch ELSE [ch EXCEPT !.data = Take(@, budget), !.fin = FALSE]
Left(cs, budget) ==
    IF Len(cs[1].data) <= budget THEN Tail(cs)
    ELSE <<[cs[1] EXCEPT !.off = @ + budget, !.data = Drop(@, budget)]>> \o Tail(cs)
SFrame(ch) == [k |-> "Stream", id |-> ch.id, off |-> ch.off, fin |-> ch.fin, data |-> ch.data, imp |-> FALSE]

\* fill_streams: at most 16 frames, each header from put_stream_header and the data after it; a frame that does not
\* fit ends the loop; each frame written is the place kept
RECURSIVE StreamLoop(_, _, _, _)
StreamLoop(c, st, cs, left) ==
    IF left = 0 \/ st.refs >= REFS \/ Room(c, st) < MINROOM \/ Len(cs) = 0 THEN st
    ELSE LET budget == Room(c, st) - SBUDGET
             ch == Piece(cs[1], budget)
             hdr == StreamOverhead(ch.id, ch.off, Len(ch.data), FALSE)
             h == PutStreamHeader(hdr, ch.id, ch.off, Len(ch.data), ch.fin) IN
         IF Len(st.w) + hdr + Len(ch.data) > c.cap \/ ~h.ok THEN st
         ELSE StreamLoop(c, [st EXCEPT !.w = @ \o h.w \o ch.data, !.fs = Append(@, SFrame(ch)), !.el = TRUE,
                                       !.refs = @ + 1, !.hint = <<Len(st.w), hdr - VLen(Len(ch.data))>>],
                         Left(cs, budget), left - 1)

\* fill_datagrams: each with its length; one that does not fit ends the loop; a datagram written forgets the place
RECURSIVE DgLoop(_, _, _)
DgLoop(c, st, ds) ==
    IF Len(ds) = 0 THEN st
    ELSE LET f == [k |-> "Datagram", data |-> ds[1], imp |-> FALSE] IN
         IF EncodedLen(f) > Room(c, st) \/ ~Fits(c, st, f) THEN st
         ELSE DgLoop(c, [Eli(Add(c, st, f)) EXCEPT !.hint = IF CLEAR THEN <<>> ELSE @], Tail(ds))

\* fill_repair: the stream frames of the packet repaired that are not acknowledged, each as the stream layer gives it
\* (cut to start after its stream's acknowledged prefix, resend_from; a part acknowledged for good was released), while
\* they fit the repair's room and the payload
RECURSIVE RepLoop(_, _, _, _)
RepLoop(c, st, cs, room) ==
    IF Len(cs) = 0 \/ Len(cs[1].data) + 24 > room \/ st.refs >= REFS THEN st
    ELSE LET ch == cs[1]
             hdr == StreamOverhead(ch.id, ch.off, Len(ch.data), FALSE)
             h == PutStreamHeader(hdr, ch.id, ch.off, Len(ch.data), ch.fin) IN
         IF Len(st.w) + hdr + Len(ch.data) > c.cap \/ ~h.ok THEN st
         ELSE RepLoop(c, [st EXCEPT !.w = @ \o h.w \o ch.data, !.fs = Append(@, SFrame(ch)), !.el = TRUE,
                                    !.refs = @ + 1], Tail(cs), room - hdr - Len(ch.data))

Fill(c) ==
    LET s1 == DoAck(c, St0) IN
    CASE c.mode = "pingonly" ->
           One(c, One(c, s1, c.wakeUntil, WAKE, TRUE, FALSE), TRUE, PING, TRUE, FALSE)
      [] c.mode = "probe" -> Eli(One(c, s1, TRUE, PING, TRUE, FALSE))
      [] c.mode = "repair" -> RepLoop(c, s1, c.streams, c.rroom)
      [] OTHER ->
           LET s2 == IF c.ring THEN Control(c, s1) ELSE s1
               s3 == Path(c, s2)
               s4 == IF c.cc THEN DgLoop(c, StreamLoop(c, s3, c.streams, 16), c.dgrams) ELSE s3
               s5 == IF c.ring /\ c.released
                     THEN LET t == ScLoop(c, s4, c.sc2) IN
                          IF CLEAR /\ Len(t.w) # Len(s4.w) THEN [t EXCEPT !.hint = <<>>] ELSE t
                     ELSE s4
               s6 == One(c, s5, c.force /\ c.ring /\ ~s5.el, PING, TRUE, FALSE) IN
           [s6 EXCEPT !.hint = IF Len(@) = 2 /\ @[1] + @[2] > Len(s6.w) THEN <<>> ELSE @]

\* build_packet seals the fill unless it is empty, or only an ACK that is not due (and nothing forces a packet)
Built(c, st) == Len(st.w) > 0 /\ ~(~st.el /\ st.ack /\ ~c.ackDue /\ ~c.force /\ c.mode # "probe")

(* ---- the tail of build_packet ---- *)
\* the payload sealed and what was done (the padding, the bytes dropped), or ok = FALSE when the ? gives the packet up
Finish(fr, hint, minp) ==
    IF Len(fr) < minp THEN [ok |-> TRUE, pay |-> fr \o Zeros(minp - Len(fr)), pad |-> minp - Len(fr), n |-> 0]
    ELSE IF Len(hint) = 2 /\ hint[1] + hint[2] <= Len(fr)
         THEN LET i == ImplicitStreamLen(fr, hint[1], hint[2]) IN
              IF i.ok THEN [ok |-> TRUE, pay |-> i.out, pad |-> 0, n |-> i.n] ELSE [ok |-> FALSE]
         ELSE [ok |-> TRUE, pay |-> fr, pad |-> 0, n |-> 0]

(* ---- what a receiver reads ---- *)
\* the frames written, the last one without its length when it was dropped, and the padding as one PADDING frame
Expected(fs, f) ==
    LET base == IF f.n > 0 THEN [fs EXCEPT ![Len(fs)].imp = TRUE] ELSE fs IN
    IF f.pad > 0 THEN Append(base, [k |-> "Padding", len |-> f.pad]) ELSE base

\* the slots of fill_frames for a mode, in order: the kinds a slot writes and whether it writes any number of frames
SC == {"MaxStreamData", "MaxStreams", "StopSending", "ResetStream"}
Slots(m) ==
    CASE m = "normal" ->
           << <<{"Ack"}, FALSE>>, <<{"Sleep"}, FALSE>>, <<{"Wake"}, FALSE>>, <<{"MtuProbeEcho"}, FALSE>>,
              <<{"Ready"}, FALSE>>, <<{"NewTickets"}, FALSE>>, <<{"Rekey"}, FALSE>>, <<{"Extension"}, TRUE>>,
              <<SC, TRUE>>, <<{"PathResponse"}, FALSE>>, <<{"Ping"}, FALSE>>, <<{"PathChallenge"}, FALSE>>,
              <<{"Stream"}, TRUE>>, <<{"Datagram"}, TRUE>>, <<SC, TRUE>>, <<{"Ping"}, FALSE>> >>
      [] m = "pingonly" -> << <<{"Ack"}, FALSE>>, <<{"Wake"}, FALSE>>, <<{"Ping"}, FALSE>> >>
      [] m = "probe" -> << <<{"Ack"}, FALSE>>, <<{"Ping"}, FALSE>> >>
      [] m = "repair" -> << <<{"Ack"}, FALSE>>, <<{"Stream"}, TRUE>> >>
      [] m = "close" -> << <<{"Close"}, FALSE>> >>

\* the kinds come in the order of the slots: each frame takes the first slot from the current one that writes its
\* kind, and a slot of at most one frame is then passed (taking the first such slot is never worse than a later one)
RECURSIVE MatchFrom(_, _, _)
MatchFrom(sl, ks, i) ==
    IF Len(ks) = 0 THEN TRUE
    ELSE LET js == {j \in i..Len(sl) : ks[1] \in sl[j][1]} IN
         IF js = {} THEN FALSE
         ELSE LET j == CHOOSE j \in js : \A x \in js : j <= x IN MatchFrom(sl, Tail(ks), IF sl[j][2] THEN j ELSE j + 1)

Kinds(fs) == [i \in 1..Len(fs) |-> fs[i].k]
Ordered(m, fs) == MatchFrom(Slots(m), Kinds(fs), 1)

\* the bytes of frames written one after the other
RECURSIVE Bytes(_)
Bytes(fs) == IF Len(fs) = 0 THEN <<>> ELSE Write(1000000, fs[1]).v \o Bytes(Tail(fs))
=============================================================================
