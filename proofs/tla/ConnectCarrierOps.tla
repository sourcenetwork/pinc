-------------------------- MODULE ConnectCarrierOps --------------------------
(***************************************************************************)
(* The operations of pinc-connect carrier/session.rs (ProtectedCarrier),   *)
(* step for step: the unit framing of the byte stream (a 2-byte big-endian *)
(* length, then that many bytes), the bounded input buffer and its lazy    *)
(* release, the handshake units (the handshake machine is a step that      *)
(* yields keys: its outputs are an input here, it is proved in             *)
(* Handshake*.tla), the record units with their packet numbers, and the    *)
(* sealing of a frame. ConnectCarrier.tla checks them over every           *)
(* interleaving of reads, polls and seals at small sizes against a stream  *)
(* an adversary builds; TraceConnectCarrier.tla replays the recorded calls *)
(* of the real code.                                                       *)
(*                                                                         *)
(* The state c of one carrier:                                             *)
(*   st    "hs" (Dialing or Accepting), "open" or "ended" (Stage);          *)
(*   rd    the stream offset of the first byte in the input buffer;        *)
(*   wr    the stream offset after the last byte in it (in_len = wr - rd); *)
(*   cons  the bytes of the last unit, released at the next receive/poll; *)
(*   out   the handshake bytes waiting for transmit (out_len);             *)
(*   spn   send_pn, rpn recv_pn;                                           *)
(*   sk    the send PacketKey, rk the receive PacketKey (NoKey before      *)
(*         the handshake completes and after the end), as Record.tla has  *)
(*         them: the carrier calls Record's SealOp and OpenOp, so the     *)
(*         nonce rules are Record's, not re-proved here;                   *)
(*   kr    whether the handshake machine waits for a key operation         *)
(*         (key_request().is_some()).                                      *)
(* The host feeds the stream in order: a receive offers bytes from offset  *)
(* wr, so the buffer always holds the stream segment [rd, wr). The stream  *)
(* is given by operators: Hdr(o) is the big-endian value of the bytes at  *)
(* o and o + 1; Opens(o, pn) says whether the unit at o authenticates     *)
(* under the receive key at packet number pn (with its two length bytes   *)
(* as associated data); Fok(o) whether the plaintext of that record       *)
(* decodes as a frame (the frame codec is proved in ConnectCodec.tla).     *)
(* A handshake step hs is [herr |-> the machine refused the input,         *)
(* outs |-> its outputs in order ([o |-> "send", m |-> length],             *)
(* [o |-> "est", kok |-> the traffic keys derived], [o |-> "fail"]),       *)
(* kreq |-> a key operation is pending after it, sb, rb |-> the names of   *)
(* the send and receive secrets the handshake yields].                     *)
(*                                                                         *)
(* K is the record of the sizes: inl (IN_LEN), maxm (MAX_MESSAGE_LEN),     *)
(* maxu (MAX_UNIT_LEN), tag (Aead::TAG_LEN), outn (OUT_LEN), maxf          *)
(* (MAX_FRAME_LEN), aead and the two key limits. MaxPn and Sat are         *)
(* Record.tla's (MAX_PACKET_NUMBER and u64::MAX).                          *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS MaxPn, Sat

Rec == INSTANCE Record WITH MaxPn <- MaxPn, AesLimit <- 0, ChachaLimit <- 0, MaxGen <- 0, Sat <- Sat,
                            Aead <- "aes", DhIds <- {}, key <- 0, log <- 0

Mn(a, b) == IF a < b THEN a ELSE b

NoKey == [none |-> TRUE]
C0(st) == [st |-> st, rd |-> 0, wr |-> 0, cons |-> 0, out |-> 0, spn |-> 0, rpn |-> 0,
           sk |-> NoKey, rk |-> NoKey, kr |-> FALSE]

InLen(c) == c.wr - c.rd
\* free(): what receive would take now, the room left once the unit the last poll took is released
Free(K, c) == K.inl - (InLen(c) - c.cons)

(* release(): drop the bytes of the last unit *)
Release(c) == IF c.cons > 0 THEN [c EXCEPT !.rd = @ + c.cons, !.cons = 0] ELSE c

(* end(): the carrier ends for good and forgets its keys *)
End(c) == [c EXCEPT !.st = "ended", !.sk = NoKey, !.rk = NoKey]

(* receive(bytes): release, then take as many of the n offered bytes as fit *)
Receive(K, c, n) ==
    LET c1 == Release(c)
        t == Mn(n, K.inl - InLen(c1))
    IN [c |-> [c1 EXCEPT !.wr = @ + t], took |-> t]

(* transmit(out): hand out the first bytes of the handshake output *)
Transmit(c, cap) == LET t == Mn(cap, c.out) IN [c |-> [c EXCEPT !.out = @ - t], n |-> t]

(* unit_len(max): "idle" (more bytes needed), "bad" (the length is 0 or over max) or the length of a whole unit *)
UnitLen(c, Hdr(_), max) ==
    IF InLen(c) < 2 THEN [k |-> "idle", len |-> 0]
    ELSE LET len == Hdr(c.rd)
         IN IF len = 0 \/ len > max THEN [k |-> "bad", len |-> len]
            ELSE IF InLen(c) >= 2 + len THEN [k |-> "unit", len |-> len] ELSE [k |-> "idle", len |-> 0]

(* the drive! macro: append each message with its 2-byte length while it fits, collect the outcome *)
RECURSIVE DriveR(_, _, _, _)
DriveR(K, out, outs, res) ==
    IF outs = <<>> THEN [out |-> out, res |-> res]
    ELSE LET o == Head(outs) IN
         IF o.o = "send" THEN
            IF o.m > 65535 THEN DriveR(K, out, Tail(outs), "UnitSize")
            ELSE IF out + 2 + o.m > K.outn THEN DriveR(K, out, Tail(outs), "OutputFull")
            ELSE DriveR(K, out + 2 + o.m, Tail(outs), res)
         ELSE IF o.o = "est" THEN
            DriveR(K, out, Tail(outs), IF res \in {"ok", "est", "estbad"} THEN (IF o.kok THEN "est" ELSE "estbad") ELSE res)
         ELSE DriveR(K, out, Tail(outs), "Handshake")
Drive(K, out, outs) == DriveR(K, out, outs, "ok")

NewKey(K, b) == Rec!NewKey(K.aead, b, K.aesLim, K.chachaLim)

(* finish(): the outcome of a handshake step *)
Finish(K, c, res, hs) ==
    IF res \notin {"ok", "est", "estbad"} THEN [c |-> End(c), r |-> res]
    ELSE IF res = "ok" THEN [c |-> [c EXCEPT !.kr = hs.kreq], r |-> IF hs.kreq THEN "kreq" ELSE "hs"]
    ELSE IF res = "estbad" THEN [c |-> End(c), r |-> "Handshake"]
    ELSE [c |-> [c EXCEPT !.st = "open", !.sk = NewKey(K, hs.sb), !.rk = NewKey(K, hs.rb), !.kr = FALSE], r |-> "open"]

(* the machine's handle() and the drain of its outputs *)
HsRun(K, out, hs) == IF hs.herr THEN [out |-> out, res |-> "Handshake"] ELSE Drive(K, out, hs.outs)

PollHs(K, c, Hdr(_), hs) ==
    LET u == UnitLen(c, Hdr, K.maxm) IN
    IF u.k = "idle" THEN [c |-> c, r |-> "idle"]
    ELSE IF u.k = "bad" THEN [c |-> End(c), r |-> "UnitSize"]
    ELSE LET d == HsRun(K, c.out, hs)
         IN Finish(K, [c EXCEPT !.cons = 2 + u.len, !.out = d.out], d.res, hs)

(* poll_record(): a whole record is opened at recv_pn with its length bytes as associated data *)
PollRecord(K, c, Hdr(_), Opens(_, _), Fok(_)) ==
    LET u == UnitLen(c, Hdr, K.maxu) IN
    IF u.k = "idle" THEN [c |-> c, r |-> "idle"]
    ELSE IF u.k = "bad" THEN [c |-> End(c), r |-> "UnitSize"]
    ELSE IF u.len <= K.tag THEN [c |-> End(c), r |-> "UnitSize"]
    ELSE IF c.rk = NoKey THEN [c |-> End(c), r |-> "NotOpen"]
    ELSE LET o == Rec!OpenOp(c.rk, c.rpn, Opens(c.rd, c.rpn)) IN
         IF o.err = "authentication" THEN [c |-> End(c), r |-> "Authentication"]
         ELSE IF o.err = "roll_required" THEN [c |-> End(c), r |-> "KeyLimit"]
         ELSE IF o.err # "ok" THEN [c |-> End(c), r |-> "Record"]
         ELSE LET c1 == [c EXCEPT !.rk = o.k, !.rpn = @ + 1, !.cons = 2 + u.len]
              IN [c |-> c1, r |-> IF Fok(c.rd) THEN "frame" ELSE "Frame"]

(* poll(): release, then the next unit of the stage *)
Poll(K, c, Hdr(_), Opens(_, _), Fok(_), hs) ==
    LET c1 == Release(c) IN
    IF c1.st = "ended" THEN [c |-> c1, r |-> "Closed"]
    ELSE IF c1.st = "open" THEN PollRecord(K, c1, Hdr, Opens, Fok)
    ELSE PollHs(K, c1, Hdr, hs)

(* key_response(): Closed on an ended carrier, checked first; NoKeyRequest when no key request is outstanding
   (key_request() is none: an open carrier, or a handshake that waits for no key operation), and nothing changes;
   otherwise the machine's on_key_response and the drain (a wrong kind of answer fails the machine: Handshake, and the
   carrier ends) *)
KeyResponse(K, c, hs) ==
    IF c.st = "ended" THEN [c |-> c, r |-> "Closed"]
    ELSE IF ~(c.st = "hs" /\ c.kr) THEN [c |-> c, r |-> "NoKeyRequest"]
    ELSE LET d == HsRun(K, c.out, hs) IN Finish(K, [c EXCEPT !.out = d.out], d.res, hs)

(* answer_soft(): the software answer to the outstanding request, or a Failed answer when there is none, through
   key_response: so it answers as key_response does *)
AnswerSoft(K, c, hs) == KeyResponse(K, c, hs)

(* sealable(): a seal answers Closed on an ended carrier and NotOpen before the handshake completes, before anything
   else is looked at *)
StageErr(c) == IF c.st = "ended" THEN "Closed" ELSE "NotOpen"

(* seal_in_place(n): seal the n plaintext bytes at out[2..] as one unit of n + tag bytes, at packet number send_pn *)
SealIn(K, c, n, cap) ==
    IF n + K.tag > 65535 THEN [c |-> c, r |-> "UnitSize", n |-> 0, pn |-> -1]
    ELSE IF c.sk = NoKey THEN [c |-> c, r |-> "NotOpen", n |-> 0, pn |-> -1]
    ELSE IF cap < 2 + n + K.tag THEN [c |-> c, r |-> "NoRoom", n |-> 0, pn |-> -1]
    ELSE LET s == Rec!SealOp(c.sk, c.spn) IN
         IF s.err = "ok" THEN [c |-> [c EXCEPT !.sk = s.k, !.spn = @ + 1], r |-> "ok", n |-> 2 + n + K.tag, pn |-> c.spn]
         ELSE IF s.err = "roll_required" THEN [c |-> End(c), r |-> "KeyLimit", n |-> 0, pn |-> -1]
         ELSE [c |-> End(c), r |-> "Record", n |-> 0, pn |-> -1]

(* seal(frame): encode into out[2..] (fe is the encoder's outcome there: "ok", "wire" for a short buffer, "frame"
   for a frame that cannot be encoded), then seal the plen bytes written *)
SealFrame(K, c, plen, cap, fe) ==
    IF c.st # "open" THEN [c |-> c, r |-> StageErr(c), n |-> 0, pn |-> -1]
    ELSE IF cap < 2 \/ fe = "wire" THEN [c |-> c, r |-> "NoRoom", n |-> 0, pn |-> -1]
    ELSE IF fe = "frame" THEN [c |-> c, r |-> "Frame", n |-> 0, pn |-> -1]
    ELSE SealIn(K, c, plen, cap)

(* seal_bytes(plain): bytes that are empty or longer than a frame are refused as a frame (Frame), the carrier lives on *)
SealBytes(K, c, plen, cap) ==
    IF c.st # "open" THEN [c |-> c, r |-> StageErr(c), n |-> 0, pn |-> -1]
    ELSE IF plen = 0 \/ plen > K.maxf THEN [c |-> c, r |-> "Frame", n |-> 0, pn |-> -1]
    ELSE IF cap < 2 + plen THEN [c |-> c, r |-> "NoRoom", n |-> 0, pn |-> -1]
    ELSE SealIn(K, c, plen, cap)

(* dial(): the first handshake output is buffered at once; an outcome of the drain other than an error is dropped
   (`drive!(..)?`), a refused machine or drain gives no carrier *)
Dial(K, hs) ==
    LET d == HsRun(K, 0, hs)
    IN IF d.res \in {"ok", "est", "estbad"} THEN [c |-> [C0("hs") EXCEPT !.out = d.out, !.kr = hs.kreq], r |-> "ok"]
       ELSE [c |-> C0("ended"), r |-> d.res]
=============================================================================
