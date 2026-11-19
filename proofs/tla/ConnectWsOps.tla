---------------------------- MODULE ConnectWsOps -----------------------------
(***************************************************************************)
(* The operations of pinc-connect carrier/ws.rs (WebSocket framing, RFC    *)
(* 6455 section 5), step for step: `encode` (one unfragmented frame, the  *)
(* length in the shortest form, a client's payload masked) and             *)
(* `Decoder::decode` (the checks in the order the code makes them).        *)
(* ConnectWs.tla checks them over every split of a byte stream into reads; *)
(* TraceConnectWs.tla replays the recorded calls of the real code.         *)
(*                                                                         *)
(* Bytes are integers 0..255 and a buffer is a sequence of them. The      *)
(* constant MP is MAX_PAYLOAD (MAX_UNIT_LEN + 2) and must be at most      *)
(* 65535, as it is in the code: then the 64-bit length form is never      *)
(* accepted. TLC integers are 32 bits wide, so a 64-bit length of 2^30 or *)
(* more stands for Huge (2^30, over every MP and over 65535): the code    *)
(* gives a length over MAX_PAYLOAD for the value, so the decoder says     *)
(* TooLong for it, as it does for Huge.                                    *)
(*                                                                         *)
(* A decoder's state is `inm`, the code's in_message: a fragmented data   *)
(* message is in progress. `peer` is "client" or "server": the role of    *)
(* the sender whose frames are decoded (a server decodes "client").       *)
(*                                                                         *)
(* Wrong names a rule of the decoder to drop, for the witness configs     *)
(* that show each property is not vacuous: "none" (the code), "rsv",      *)
(* "opcode", "mask", "lenform", "bound", "ctl", "seq".                     *)
(*                                                                         *)
(* Where the code departs from RFC 6455, by design: text frames and the   *)
(* opcodes 3 to 7 and 11 to 15 are refused (a binary carrier); a close    *)
(* with a one-byte payload is accepted and reports no status (the RFC     *)
(* calls it a protocol error); the UTF-8 check of a close reason is not   *)
(* made; the decoder does not stop after a close (the host does).         *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS MP, Wrong

Huge == 1073741824

Bit(x, i) == (x \div 2^i) % 2
XorAt(a, b, i) == ((Bit(a, i) + Bit(b, i)) % 2) * 2^i
Xor(a, b) == XorAt(a, b, 0) + XorAt(a, b, 1) + XorAt(a, b, 2) + XorAt(a, b, 3)
             + XorAt(a, b, 4) + XorAt(a, b, 5) + XorAt(a, b, 6) + XorAt(a, b, 7)

(* apply_mask(key, data): XOR with the key, repeated *)
Mask(key, d) == [j \in 1..Len(d) |-> Xor(d[j], key[((j - 1) % 4) + 1])]

Be16(n) == <<n \div 256, n % 256>>
Be64(n) == <<0, 0, 0, 0, (n \div 16777216) % 256, (n \div 65536) % 256, (n \div 256) % 256, n % 256>>
U16(a, b) == a * 256 + b

IsOp(o) == o \in {0, 2, 8, 9, 10}
IsCtl(o) == o >= 8

(* Which opcode a decoded frame has: the kind the decoder reports *)
KindOf(o) == CASE o = 0 \/ o = 2 -> "data" [] o = 8 -> "close" [] o = 9 -> "ping" [] OTHER -> "pong"

-----------------------------------------------------------------------------
(* encode(opcode, payload, mask, out): mask is <<>> for None or the 4-byte key; cap is out.len() *)
EncErr(e) == [ok |-> FALSE, e |-> e, b |-> <<>>, n |-> 0]

Encode(op, pl, mask, cap) ==
    LET n == Len(pl)
        mb == IF mask = <<>> THEN 0 ELSE 128
        lenb == IF n <= 125 THEN <<mb + n>> ELSE <<mb + 126>> \o Be16(n)
        hdr == <<128 + op>> \o lenb \o mask
        total == Len(hdr) + n
    IN IF n > MP THEN EncErr("toolong")
       ELSE IF IsCtl(op) /\ n > 125 THEN EncErr("control")
       ELSE IF total > cap THEN EncErr("noroom")
       ELSE [ok |-> TRUE, e |-> "", n |-> total,
             b |-> hdr \o (IF mask = <<>> THEN pl ELSE Mask(mask, pl))]

-----------------------------------------------------------------------------
(* Decoder::decode: the result is [k |-> "idle"] (more bytes needed), [k |-> "err", e |-> tag] (the connection is *)
(* closed) or [k |-> "frame", f |-> kind, pl |-> payload, st |-> close status or -1, used, inm |-> state after]. *)
Idle == [k |-> "idle"]
DErr(e) == [k |-> "err", e |-> e]

V64(b) == IF (\E j \in 1..4 : b[j] /= 0) \/ U16(b[5], b[6]) >= 16384 THEN Huge ELSE U16(b[5], b[6]) * 65536 + U16(b[7], b[8])

Decode(peer, inm, buf) ==
    LET n == Len(buf)
        b0 == buf[1]
        b1 == buf[2]
        fin == b0 >= 128
        o == b0 % 16
        masked == b1 >= 128
        l7 == b1 % 128
        ctl == IsCtl(o)
        \* the length: <<ok, length, header bytes>> or a refusal or "more"
        v16 == IF n >= 4 THEN U16(buf[3], buf[4]) ELSE 0
        v64 == IF n >= 10 THEN V64(SubSeq(buf, 3, 10)) ELSE 0
        lenres == IF l7 = 126 THEN (IF n < 4 THEN "more" ELSE IF v16 < 126 /\ Wrong # "lenform" THEN "lenform" ELSE "ok")
                  ELSE IF l7 = 127 THEN (IF n < 10 THEN "more" ELSE IF v64 < 65536 /\ Wrong # "lenform" THEN "lenform" ELSE "ok")
                  ELSE "ok"
        len == IF l7 = 126 THEN v16 ELSE IF l7 = 127 THEN v64 ELSE l7
        head == IF l7 = 126 THEN 4 ELSE IF l7 = 127 THEN 10 ELSE 2
        start == head + (IF masked THEN 4 ELSE 0)
        key == IF masked /\ n >= head + 4 THEN SubSeq(buf, head + 1, head + 4) ELSE <<>>
        raw == IF n >= start + len THEN SubSeq(buf, start + 1, start + len) ELSE <<>>
        pl == IF masked THEN Mask(key, raw) ELSE raw
    IN IF n < 2 THEN Idle
       ELSE IF (b0 \div 16) % 8 /= 0 /\ Wrong # "rsv" THEN DErr("reserved")
       ELSE IF ~IsOp(o) /\ Wrong # "opcode" THEN DErr("opcode")
       ELSE IF masked /= (peer = "client") /\ Wrong # "mask" THEN DErr("mask")
       ELSE IF lenres = "more" THEN Idle
       ELSE IF lenres = "lenform" THEN DErr("lenform")
       ELSE IF len > MP /\ Wrong # "bound" THEN DErr("toolong")
       ELSE IF ctl /\ (~fin \/ len > 125) /\ Wrong # "ctl" THEN DErr("control")
       ELSE IF ~ctl /\ ((o = 0) /= inm) /\ Wrong # "seq" THEN DErr("sequence")
       ELSE IF masked /\ n < head + 4 THEN Idle
       ELSE IF n < start + len THEN Idle
       ELSE [k |-> "frame", f |-> KindOf(o), used |-> start + len,
             pl |-> IF o = 8 THEN <<>> ELSE pl,
             st |-> IF o = 8 /\ len >= 2 THEN U16(pl[1], pl[2]) ELSE -1,
             inm |-> IF ctl THEN inm ELSE ~fin]

=============================================================================
