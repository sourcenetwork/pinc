------------------------------ MODULE ConnectWs ------------------------------
(***************************************************************************)
(* The WebSocket framing of the carrier, pinc-connect carrier/ws.rs, over  *)
(* every split of the byte stream into reads (ConnectWsOps.tla has the     *)
(* operators, which follow the code step for step).                        *)
(*                                                                         *)
(* A peer of one role (client or server) sends a plan: a short sequence of *)
(* frames, each described by its fields: reserved bit, FIN, opcode, mask   *)
(* bit, the length form (7, 16 or 64 bits) and the length. The plan is     *)
(* written as bytes (a frame whose length is over MAX_PAYLOAD carries only *)
(* two bytes of payload, since nobody sends them, and the decoder must     *)
(* refuse from the header alone). The decoder's host offers the stream in  *)
(* reads of the sizes ReadSizes (one byte, a few, or all of it, so every   *)
(* split is reached) and decodes after each read as long as it gets        *)
(* frames, as a host does, with the buffer it keeps. A refused frame ends  *)
(* the connection (dead).                                                  *)
(*                                                                         *)
(* Valid is the rule written from the code's documentation and RFC 6455,   *)
(* from the description of the frame alone (no reserved bit, an opcode of  *)
(* binary, continuation, close, ping or pong, the mask bit the role asks   *)
(* for, the shortest length form, a length of at most MAX_PAYLOAD, a       *)
(* control frame final and of at most 125 bytes, a continuation exactly    *)
(* inside a fragmented message). Checked, in every reachable state:        *)
(*  - Faithful: the frames delivered are the first frames of the plan,    *)
(*    each valid where it stands, with the payload unmasked, whatever the  *)
(*    split; the decoder's state is whether a fragmented message is open;  *)
(*    when the connection is ended by a refusal the next frame of the plan *)
(*    is not valid; when every byte is read and the connection lives, all  *)
(*    frames of the plan were delivered. So: a wrong mask, a longer length *)
(*    form, an unknown opcode, a reserved bit, an oversized, fragmented or *)
(*    long control frame and a frame out of sequence are each refused,     *)
(*    and a data frame between fragments of one message is refused;        *)
(*  - BufBound: a living decoder never holds MAX_PAYLOAD + 14 bytes or    *)
(*    more: an announced length over the bound is refused before any of    *)
(*    its payload is waited for or kept.                                   *)
(* EncOK checks encode and its round trip frame by frame (shortest length  *)
(* form, the refusals in the code's order, the mask only for a client, and *)
(* a decoder of the right role gets the same payload back and idles at     *)
(* every proper prefix, and one of the other role refuses the mask).       *)
(* Config Wrong drops one rule of the decoder; the witness configs show    *)
(* Faithful or BufBound then fails.                                        *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC
CONSTANTS MP, Wrong, Ops, RSVs, FLs, ReadSizes, NF, EncCaps, EncLens
VARIABLES peer, plan, S, rd, buf, inm, dead, got
vars == <<peer, plan, S, rd, buf, inm, dead, got>>

INSTANCE ConnectWsOps

Min(a, b) == IF a < b THEN a ELSE b
Key == <<7, 130, 255, 1>>
Pl(n) == [j \in 1..n |-> (j * 37 + n) % 256]

Descs == {[rsv |-> r, fin |-> f, op |-> o, m |-> m, form |-> fl \div 2000000, len |-> fl % 2000000] :
          r \in RSVs, f \in BOOLEAN, o \in Ops, m \in BOOLEAN, fl \in FLs}

(* the bytes of a frame written by a peer that does not check what it writes *)
RawBytes(d) ==
    LET b0 == (IF d.fin THEN 128 ELSE 0) + (IF d.rsv THEN 64 ELSE 0) + d.op
        b1 == (IF d.m THEN 128 ELSE 0) + (IF d.form = 7 THEN d.len ELSE IF d.form = 16 THEN 126 ELSE 127)
        ext == IF d.form = 7 THEN <<>> ELSE IF d.form = 16 THEN Be16(d.len) ELSE Be64(d.len)
        w == IF d.len <= MP THEN Pl(d.len) ELSE <<1, 2>>
    IN <<b0, b1>> \o ext \o (IF d.m THEN Key ELSE <<>>) \o (IF d.m THEN Mask(Key, w) ELSE w)

RECURSIVE Flat(_)
Flat(p) == IF p = <<>> THEN <<>> ELSE RawBytes(Head(p)) \o Flat(Tail(p))

Canon(d) == CASE d.form = 7 -> d.len <= 125
              [] d.form = 16 -> d.len >= 126 /\ d.len <= 65535
              [] OTHER -> d.len >= 65536
Valid(pe, d, im) ==
    /\ ~d.rsv /\ IsOp(d.op) /\ d.m = (pe = "client") /\ Canon(d) /\ d.len <= MP
    /\ (IsCtl(d.op) => d.fin /\ d.len <= 125)
    /\ (~IsCtl(d.op) => ((d.op = 0) = im))

RECURSIVE InmAfter(_, _)
InmAfter(p, j) == IF j = 0 THEN FALSE
                  ELSE IF IsCtl(p[j].op) THEN InmAfter(p, j - 1) ELSE ~p[j].fin

Expected(o, n) == [f |-> KindOf(o), pl |-> IF o = 8 THEN <<>> ELSE Pl(n),
                   st |-> IF o = 8 /\ n >= 2 THEN U16(Pl(n)[1], Pl(n)[2]) ELSE -1]
Seen(r) == [f |-> r.f, pl |-> r.pl, st |-> r.st]

RECURSIVE Drain(_, _, _, _)
Drain(pe, im, b, g) ==
    LET r == Decode(pe, im, b) IN
    IF r.k = "idle" THEN [im |-> im, b |-> b, g |-> g, d |-> FALSE]
    ELSE IF r.k = "err" THEN [im |-> im, b |-> b, g |-> g, d |-> TRUE]
    ELSE Drain(pe, r.inm, SubSeq(b, r.used + 1, Len(b)), Append(g, r))

Init == /\ peer \in {"client", "server"}
        /\ plan \in UNION {[1..k -> Descs] : k \in 0..NF}
        /\ S = Flat(plan) /\ rd = 0 /\ buf = <<>> /\ inm = FALSE /\ dead = FALSE /\ got = <<>>

Read(n) ==
    /\ ~dead /\ rd < Len(S)
    /\ LET t == Min(n, Len(S) - rd)
           x == Drain(peer, inm, buf \o SubSeq(S, rd + 1, rd + t), got)
       IN /\ rd' = rd + t /\ buf' = x.b /\ inm' = x.im /\ got' = x.g /\ dead' = x.d
    /\ UNCHANGED <<peer, plan, S>>

Next == \E n \in ReadSizes : Read(n)
Spec == Init /\ [][Next]_vars

(* one state: the encoder checks do not depend on a run *)
Init0 == /\ peer = "client" /\ plan = <<>> /\ S = <<>> /\ rd = 0 /\ buf = <<>> /\ inm = FALSE /\ dead = FALSE
         /\ got = <<>>
EncSpec == Init0 /\ [][UNCHANGED vars]_vars

Faithful ==
    /\ Len(got) <= Len(plan)
    /\ \A j \in 1..Len(got) : /\ Valid(peer, plan[j], InmAfter(plan, j - 1))
                              /\ Seen(got[j]) = Expected(plan[j].op, plan[j].len)
    /\ inm = InmAfter(plan, Len(got))
    /\ dead => /\ Len(got) < Len(plan)
               /\ ~Valid(peer, plan[Len(got) + 1], InmAfter(plan, Len(got)))
    /\ (rd = Len(S) /\ ~dead) => Len(got) = Len(plan)

BufBound == ~dead => Len(buf) < MP + 14

(* a witness: some run delivers a fragmented message (a non-final binary frame, then more, ending in a final continuation) *)
NoFragmented == ~(Len(got) >= 2 /\ plan[1].op = 2 /\ ~plan[1].fin /\ plan[Len(got)].op = 0 /\ plan[Len(got)].fin)

(* a witness: some run delivers a frame of exactly MAX_PAYLOAD bytes in the 16-bit form *)
NoMaxFrame == ~(\E j \in 1..Len(got) : plan[j].len = MP /\ plan[j].op = 2 /\ plan[j].form = 16)

(* encode, frame by frame *)
EncCases == {[op |-> o, n |-> n, k |-> k, cap |-> c] :
             o \in {0, 2, 8, 9, 10}, n \in EncLens, k \in {<<>>, Key}, c \in EncCaps}
HdrLen(e) == 2 + (IF e.n > 125 THEN 2 ELSE 0) + (IF e.k = <<>> THEN 0 ELSE 4)
EncOK ==
    \A e \in EncCases :
      LET r == Encode(e.op, Pl(e.n), e.k, e.cap)
          canon == [rsv |-> FALSE, fin |-> TRUE, op |-> e.op, m |-> e.k # <<>>,
                    form |-> IF e.n <= 125 THEN 7 ELSE 16, len |-> e.n]
          pe == IF e.k # <<>> THEN "client" ELSE "server"
          other == IF e.k # <<>> THEN "server" ELSE "client"
          d == Decode(pe, FALSE, r.b)
      IN /\ r.ok = ~(e.n > MP \/ (IsCtl(e.op) /\ e.n > 125) \/ HdrLen(e) + e.n > e.cap)
         /\ ~r.ok => r.e = IF e.n > MP THEN "toolong"
                           ELSE IF IsCtl(e.op) /\ e.n > 125 THEN "control" ELSE "noroom"
         /\ r.ok => /\ r.b = RawBytes(canon) /\ Len(r.b) = r.n /\ r.n = HdrLen(e) + e.n
                    /\ (e.op # 0 => /\ Decode(pe, FALSE, r.b \o <<9, 9>>) = d
                                    /\ d.k = "frame" /\ d.used = r.n /\ d.inm = FALSE
                                    /\ Seen(d) = Expected(e.op, e.n)
                                    /\ \A j \in 0..(r.n - 1) : Decode(pe, FALSE, SubSeq(r.b, 1, j)).k = "idle"
                                    /\ Decode(other, FALSE, r.b) = DErr("mask"))
=============================================================================
