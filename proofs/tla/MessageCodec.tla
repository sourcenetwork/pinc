---------------------------- MODULE MessageCodec ----------------------------
(***************************************************************************)
(* The byte codec of the handshake messages, pinc-security message.rs,     *)
(* byte for byte: MessageType::of (TypeOf), the parse and write of         *)
(* Initial (types 1 and 2), Reject (3 and 8), Reply (4), Finish (5),       *)
(* ResumeHello (6), ResumeReply (7, with TicketBatch::read and write of    *)
(* tickets.rs) and the sealed plaintext IdSig, with the Reader and Writer  *)
(* of pinc-wire as they are: a read past the end is Truncated with the     *)
(* bytes missing of the field being read, a write that does not fit is     *)
(* BufferTooSmall with the bytes missing of the piece being written, a     *)
(* length that does not fit its prefix is VarintOverflow, and the checks   *)
(* run in the order of the code (a connection id is read before its length *)
(* is checked; the ALPN, sealed, ticket count, key and signature lengths   *)
(* are checked before their bytes are read).                               *)
(* The sizes come from Padding.tla (KEM ciphertext 1088, AEAD tag 16,      *)
(* credit record 6, connection id 20, MAX_SEALED_LEN 5384, MAX_ID_SIG_LEN  *)
(* 5368, MAX_MESSAGE_LEN 6529, the key and signature lengths of the four   *)
(* identity algorithms), which proves them; nothing is scaled. A message   *)
(* is a record of its fields as bytes (a credit record as its 6 bytes, a   *)
(* ticket as its id and its lifetime as 4 big-endian bytes, an AEAD by its *)
(* tag, the offer by its bits).                                            *)
(*                                                                         *)
(* Checked (MessageCodec.cfg) for each message of a systematic domain of   *)
(* every kind (the two Initial forms, connection ids of 0, 1, 4 and 20     *)
(* bytes, ALPNs of 1 and 32 bytes, every offer and AEAD, sealed fields of  *)
(* 16, 17, 123 and 5384 bytes, 0 to 4 tickets, versions 0, 1 and 255, the *)
(* plaintexts of the four algorithms with and without the credit record):  *)
(*   RoundTrip  parse(write(m)) = m; write into a buffer of exactly the    *)
(*              message's size gives its bytes, one byte less fails one    *)
(*              byte short;                                                *)
(*   Fits       every message fits MAX_MESSAGE_LEN (the buffer of the      *)
(*              outbox) and every plaintext MAX_ID_SIG_LEN;                *)
(*   Strict     every proper prefix is Truncated, every trailing byte is   *)
(*              refused as trailing;                                       *)
(*   Unique     every single-byte change at the header, the field          *)
(*              boundaries and the end that parses re-encodes to itself,   *)
(*              so a message has one accepted encoding (canonical);        *)
(*   Cross      each message type is refused by the parser of every other; *)
(*   Classes    each malformed class is refused with its own reason;       *)
(*   OutOfRange the code's answer to fields outside the documented ranges: *)
(*              an ALPN of 0, 33, 255 or 256 bytes is refused by the       *)
(*              writer with the parser's own error ("alpn length", fix     *)
(*              S4), a sealed field of 15 or 5385 bytes and a key of the   *)
(*              wrong length are written and refused by the parser, a      *)
(*              sealed field of 65536 bytes is VarintOverflow.             *)
(* MessageCodec_alpn.cfg checks WriteRefusesBadAlpn, the doc of            *)
(* Initial::write ("a length error for a field out of range"), which the   *)
(* code keeps with fix S4; before it the code wrote an ALPN of 0 or 33 to  *)
(* 255 bytes and TLC found it violated. The machines cannot produce one    *)
(* (their ALPN is an Alpn, 1 to 32 bytes).                                 *)
(* Not modelled: Initial::prekey_hash (a hash, an ideal primitive) and     *)
(* CreditRecord::decode and encode (a bijection on 6 bytes, Credit.tla).   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

P == INSTANCE Padding WITH x <- 0

MaxCid == P!MaxCid
MaxAlpn == 32
EkLen == 1184
CtLen == P!KemCt
TagLen == P!TagLen
CrLen == P!CreditLen
MaxSealed == P!MaxSealed
MaxBatch == 4
TidLen == 16
Big == 1000000

Be16(n) == <<n \div 256, n % 256>>
Least(S) == CHOOSE i \in S : \A j \in S : i <= j

(* ---- writing: the pieces each write appends, in the order of the code ---- *)
Pc(b) == [ok |-> TRUE, b |-> b, why |-> ""]
Ovf == [ok |-> FALSE, b |-> <<>>, why |-> "overflow"]
U8(v) == Pc(<<v>>)
\* u8::try_from(len) then put_u8, and u16::try_from(len) then put_u16
Len8(s) == IF Len(s) <= 255 THEN U8(Len(s)) ELSE Ovf
Len16(s) == IF Len(s) <= 65535 THEN Pc(Be16(Len(s))) ELSE Ovf
\* write_alpn with fix S4: the length the parser accepts (alpn_len_ok, 1 to MaxAlpn), else the parser's own error
AlpnLen(s) == IF Len(s) >= 1 /\ Len(s) <= MaxAlpn THEN U8(Len(s)) ELSE [ok |-> FALSE, b |-> <<>>, why |-> "alpn length"]
AlpnRefused == [res |-> "unexpected", what |-> "alpn length"]

RECURSIVE TicketPieces(_)
TicketPieces(ts) == IF ts = <<>> THEN <<>> ELSE <<Pc(Head(ts).tid), Pc(Head(ts).life)>> \o TicketPieces(Tail(ts))

Pieces(m) ==
    CASE m.k = "initial" ->
            <<U8(IF m.full THEN 1 ELSE 2), U8(m.ver), Len8(m.dcid), Pc(m.dcid), Len8(m.scid), Pc(m.scid),
              AlpnLen(m.alpn), Pc(m.alpn), U8(m.offer), Pc(m.e), Pc(m.pre), Pc(m.cr)>>
      [] m.k = "reject" -> <<U8(m.ty), Pc(m.echo)>>
      [] m.k = "reply" -> <<U8(4), Len8(m.scid), Pc(m.scid), U8(m.aead), Pc(m.e), Pc(m.ct), Len16(m.sealed), Pc(m.sealed)>>
      [] m.k = "finish" -> <<U8(5), Len16(m.sealed), Pc(m.sealed)>>
      [] m.k = "hello" ->
            <<U8(6), U8(m.ver), Len8(m.dcid), Pc(m.dcid), Len8(m.scid), Pc(m.scid), AlpnLen(m.alpn), Pc(m.alpn),
              U8(m.aead), Pc(m.tid), Pc(m.e), Pc(m.binder), Pc(m.cr)>>
      [] m.k = "rreply" ->
            <<U8(7), Len8(m.scid), Pc(m.scid), Pc(m.e), U8(Len(m.tickets))>> \o TicketPieces(m.tickets)
            \o <<Pc(m.cr), Pc(m.confirm)>>
      [] m.k = "idsig" ->
            <<U8(m.alg), Len16(m.pk), Pc(m.pk), Len16(m.sig), Pc(m.sig)>> \o (IF m.cr = <<>> THEN <<>> ELSE <<Pc(m.cr)>>)

\* the write into a buffer of cap bytes: the first piece that overflows its prefix or does not fit stops it
RECURSIVE Fold(_, _, _)
Fold(ps, cap, acc) ==
    IF ps = <<>> THEN [res |-> "ok", bytes |-> acc]
    ELSE LET pc == Head(ps)
         IN IF ~pc.ok THEN (IF pc.why = "overflow" THEN [res |-> "overflow"] ELSE [res |-> "unexpected", what |-> pc.why])
            ELSE IF Len(pc.b) > cap - Len(acc) THEN [res |-> "small", needed |-> Len(pc.b) - (cap - Len(acc))]
            ELSE Fold(Tail(ps), cap, acc \o pc.b)
EncodeCap(m, cap) == Fold(Pieces(m), cap, <<>>)
Enc(m) == EncodeCap(m, Big).bytes

\* the byte offsets at which the pieces end, and where piece i starts (1-based)
RECURSIVE EndsFrom(_, _)
EndsFrom(ps, n) == IF ps = <<>> THEN {} ELSE {n + Len(Head(ps).b)} \cup EndsFrom(Tail(ps), n + Len(Head(ps).b))
Ends(m) == EndsFrom(Pieces(m), 0)
RECURSIVE SumTo(_, _)
SumTo(ps, i) == IF i = 0 THEN 0 ELSE Len(ps[i].b) + SumTo(ps, i - 1)
PieceStart(m, i) == 1 + SumTo(Pieces(m), i - 1)

(* ---- parsing: a reader at offset p of the bytes b ---- *)
Tr(n) == [res |-> "truncated", needed |-> n]
Un(w) == [res |-> "unexpected", what |-> w]
Got(v, p) == [res |-> "ok", v |-> v, p |-> p]

F(t) == [t |-> t]
Fix(n) == [t |-> "fix", n |-> n]
Exact16(n, w) == [t |-> "exact16", n |-> n, w |-> w]

TicketsAt(b, p, c) ==
    [i \in 1..c |-> [tid |-> SubSeq(b, p + 2 + 20 * (i - 1), p + 1 + 20 * (i - 1) + TidLen),
                     life |-> SubSeq(b, p + 2 + 20 * (i - 1) + TidLen, p + 1 + 20 * i)]]

ReadField(fd, b, p) ==
    LET rem == Len(b) - p
    IN CASE fd.t = "u8" -> IF rem < 1 THEN Tr(1) ELSE Got(b[p + 1], p + 1)
         [] fd.t = "fix" -> IF rem < fd.n THEN Tr(fd.n - rem) ELSE Got(SubSeq(b, p + 1, p + fd.n), p + fd.n)
         \* read_cid: the length, the bytes, then ConnId::new
         [] fd.t = "cid" ->
              IF rem < 1 THEN Tr(1)
              ELSE LET n == b[p + 1]
                   IN IF rem - 1 < n THEN Tr(n - (rem - 1))
                      ELSE IF n > MaxCid THEN Un("connection id too long")
                      ELSE Got(SubSeq(b, p + 2, p + 1 + n), p + 1 + n)
         \* read_alpn: the length, its range, then the bytes
         [] fd.t = "alpn" ->
              IF rem < 1 THEN Tr(1)
              ELSE LET n == b[p + 1]
                   IN IF n < 1 \/ n > MaxAlpn THEN Un("alpn length")
                      ELSE IF rem - 1 < n THEN Tr(n - (rem - 1))
                      ELSE Got(SubSeq(b, p + 2, p + 1 + n), p + 1 + n)
         [] fd.t = "offer" ->
              IF rem < 1 THEN Tr(1) ELSE IF b[p + 1] \in 1..3 THEN Got(b[p + 1], p + 1) ELSE Un("aead offer")
         [] fd.t = "aead" ->
              IF rem < 1 THEN Tr(1) ELSE IF b[p + 1] \in 1..2 THEN Got(b[p + 1], p + 1) ELSE Un("unknown aead")
         \* read_sealed: a u16 length in TAG_LEN..=MAX_SEALED_LEN, then the bytes
         [] fd.t = "sealed" ->
              IF rem < 2 THEN Tr(2 - rem)
              ELSE LET n == b[p + 1] * 256 + b[p + 2]
                   IN IF n < TagLen \/ n > MaxSealed THEN Un("sealed length")
                      ELSE IF rem - 2 < n THEN Tr(n - (rem - 2))
                      ELSE Got(SubSeq(b, p + 3, p + 2 + n), p + 2 + n)
         \* the key and signature of IdSig: a u16 length that must be exactly n, then the bytes
         [] fd.t = "exact16" ->
              IF rem < 2 THEN Tr(2 - rem)
              ELSE LET n == b[p + 1] * 256 + b[p + 2]
                   IN IF n # fd.n THEN Un(fd.w)
                      ELSE IF rem - 2 < n THEN Tr(n - (rem - 2))
                      ELSE Got(SubSeq(b, p + 3, p + 2 + n), p + 2 + n)
         \* TicketBatch::read: the count (at most MAX_BATCH), then per entry tid(16) and lifetime(4)
         [] fd.t = "tickets" ->
              IF rem < 1 THEN Tr(1)
              ELSE LET c == b[p + 1]
                   IN IF c > MaxBatch THEN Un("ticket count")
                      ELSE LET short == {i \in 1..c : Len(b) - (p + 1 + 20 * (i - 1)) < 20}
                           IN IF short # {}
                              THEN LET r == Len(b) - (p + 1 + 20 * (Least(short) - 1))
                                   IN IF r < TidLen THEN Tr(TidLen - r) ELSE Tr(4 - (r - TidLen))
                              ELSE Got(TicketsAt(b, p, c), p + 1 + 20 * c)

\* the fields of a schema in order, then finish: a byte left over is "trailing bytes"
RECURSIVE Run(_, _, _)
Run(sch, b, p) ==
    IF sch = <<>> THEN IF p = Len(b) THEN [res |-> "ok", vs |-> <<>>] ELSE Un("trailing bytes")
    ELSE LET r == ReadField(Head(sch), b, p)
         IN IF r.res # "ok" THEN r
            ELSE LET t == Run(Tail(sch), b, r.p)
                 IN IF t.res # "ok" THEN t ELSE [res |-> "ok", vs |-> <<r.v>> \o t.vs]

InitialSch(full) == <<F("u8"), F("cid"), F("cid"), F("alpn"), F("offer"), Fix(32), Fix(IF full THEN EkLen ELSE 32), Fix(CrLen)>>
RejectSch == <<Fix(16)>>
ReplySch == <<F("cid"), F("aead"), Fix(32), Fix(CtLen), F("sealed")>>
FinishSch == <<F("sealed")>>
HelloSch == <<F("u8"), F("cid"), F("cid"), F("alpn"), F("aead"), Fix(TidLen), Fix(32), Fix(32), Fix(CrLen)>>
RReplySch == <<F("cid"), Fix(32), F("tickets"), Fix(CrLen), Fix(32)>>
IdSigSch(a, wc) == <<Exact16(P!Pk[a], "public key length"), Exact16(P!Sig[a], "signature length")>>
                   \o (IF wc THEN <<Fix(CrLen)>> ELSE <<>>)

\* MessageType::of
TypeOf(b) == IF Len(b) = 0 THEN Tr(1) ELSE IF b[1] \in 1..8 THEN [res |-> "ok", ty |-> b[1]] ELSE Un("unknown message type")
\* read_type, then the fields
Typed(b, ty, sch) == IF Len(b) = 0 THEN Tr(1) ELSE IF b[1] # ty THEN Un("wrong message type") ELSE Run(sch, b, 1)
Ok(m) == [res |-> "ok", m |-> m]

ParseInitial(b) ==
    LET t == TypeOf(b)
    IN IF t.res # "ok" THEN t
       ELSE IF t.ty \notin {1, 2} THEN Un("wrong message type")
       ELSE LET r == Run(InitialSch(t.ty = 1), b, 1)
            IN IF r.res # "ok" THEN r
               ELSE Ok([k |-> "initial", full |-> t.ty = 1, ver |-> r.vs[1], dcid |-> r.vs[2], scid |-> r.vs[3],
                        alpn |-> r.vs[4], offer |-> r.vs[5], e |-> r.vs[6], pre |-> r.vs[7], cr |-> r.vs[8]])
ParseReject(b, ty) ==
    LET r == Typed(b, ty, RejectSch) IN IF r.res # "ok" THEN r ELSE Ok([k |-> "reject", ty |-> ty, echo |-> r.vs[1]])
ParseReply(b) ==
    LET r == Typed(b, 4, ReplySch)
    IN IF r.res # "ok" THEN r
       ELSE Ok([k |-> "reply", scid |-> r.vs[1], aead |-> r.vs[2], e |-> r.vs[3], ct |-> r.vs[4], sealed |-> r.vs[5]])
ParseFinish(b) ==
    LET r == Typed(b, 5, FinishSch) IN IF r.res # "ok" THEN r ELSE Ok([k |-> "finish", sealed |-> r.vs[1]])
ParseHello(b) ==
    LET r == Typed(b, 6, HelloSch)
    IN IF r.res # "ok" THEN r
       ELSE Ok([k |-> "hello", ver |-> r.vs[1], dcid |-> r.vs[2], scid |-> r.vs[3], alpn |-> r.vs[4], aead |-> r.vs[5],
                tid |-> r.vs[6], e |-> r.vs[7], binder |-> r.vs[8], cr |-> r.vs[9]])
ParseRReply(b) ==
    LET r == Typed(b, 7, RReplySch)
    IN IF r.res # "ok" THEN r
       ELSE Ok([k |-> "rreply", scid |-> r.vs[1], e |-> r.vs[2], tickets |-> r.vs[3], cr |-> r.vs[4], confirm |-> r.vs[5]])
ParseIdSig(b, wc) ==
    IF Len(b) = 0 THEN Tr(1)
    ELSE IF b[1] \notin 1..4 THEN Un("unknown identity algorithm")
    ELSE LET r == Run(IdSigSch(b[1], wc), b, 1)
         IN IF r.res # "ok" THEN r
            ELSE Ok([k |-> "idsig", alg |-> b[1], pk |-> r.vs[1], sig |-> r.vs[2], cr |-> IF wc THEN r.vs[3] ELSE <<>>])

\* the parser of a kind; ty is the type a reject is parsed as, wc whether a plaintext carries the credit record
Parse(kind, b, ty, wc) ==
    CASE kind = "initial" -> ParseInitial(b)
      [] kind = "reject" -> ParseReject(b, ty)
      [] kind = "reply" -> ParseReply(b)
      [] kind = "finish" -> ParseFinish(b)
      [] kind = "hello" -> ParseHello(b)
      [] kind = "rreply" -> ParseRReply(b)
      [] kind = "idsig" -> ParseIdSig(b, wc)
ParseOwn(m, b) == Parse(m.k, b, IF m.k = "reject" THEN m.ty ELSE 0, m.k = "idsig" /\ m.cr # <<>>)

(***************************************************************************)
(* The checked domain                                                      *)
(***************************************************************************)
Pat(n, s) == [i \in 1..n |-> (i * s + 7) % 256]
Z(n) == [i \in 1..n |-> 0]
C0 == <<>>
C1 == <<9>>
C4 == Pat(4, 3)
C20 == Pat(20, 5)
Cids == {C0, C1, C4, C20}
A1 == <<104>>
A32 == Pat(32, 11)
E32 == Pat(32, 17)
H32 == Pat(32, 23)
Ek1 == Pat(EkLen, 19)
Ct1 == Pat(CtLen, 41)
P16 == Pat(16, 29)
CrA == <<0, 4, 0, 100, 5, 220>>
CrZ == Z(6)
CrF == [i \in 1..6 |-> 255]
Sealeds == {Pat(16, 31), Pat(17, 31), Pat(123, 31), Pat(MaxSealed, 37)}
Ent1 == [tid |-> P16, life |-> <<0, 0, 0, 0>>]
Ent2 == [tid |-> Z(16), life |-> <<255, 255, 255, 255>>]

Shorts == {[k |-> "initial", full |-> FALSE, ver |-> v, dcid |-> d, scid |-> s, alpn |-> a, offer |-> o,
            e |-> E32, pre |-> H32, cr |-> CrA] : v \in {0, 255}, d \in Cids, s \in {C0, C20}, a \in {A1, A32}, o \in {1, 3}}
Fulls == {[k |-> "initial", full |-> TRUE, ver |-> 1, dcid |-> pr[1], scid |-> pr[2], alpn |-> a, offer |-> o,
           e |-> E32, pre |-> Ek1, cr |-> c] : pr \in {<<C0, C20>>, <<C20, C0>>, <<C4, C4>>}, a \in {A1, A32}, o \in 1..3, c \in {CrZ, CrF}}
Rejects == {[k |-> "reject", ty |-> t, echo |-> x] : t \in {3, 8}, x \in {Z(16), P16}}
Replies == {[k |-> "reply", scid |-> s, aead |-> a, e |-> E32, ct |-> Ct1, sealed |-> x] : s \in Cids, a \in 1..2, x \in Sealeds}
Finishes == {[k |-> "finish", sealed |-> x] : x \in Sealeds}
Hellos == {[k |-> "hello", ver |-> 1, dcid |-> d, scid |-> s, alpn |-> a, aead |-> g, tid |-> P16, e |-> E32, binder |-> H32,
            cr |-> CrA] : d \in Cids, s \in {C0, C20}, a \in {A1, A32}, g \in 1..2}
TicketSeqs == {<<>>, <<Ent1>>, <<Ent1, Ent2>>, <<Ent2, Ent1, Ent2>>, <<Ent1, Ent2, Ent1, Ent2>>}
RReplies == {[k |-> "rreply", scid |-> s, e |-> E32, tickets |-> t, cr |-> CrA, confirm |-> H32] : s \in {C0, C20}, t \in TicketSeqs}
IdSigs == {[k |-> "idsig", alg |-> a, pk |-> Pat(P!Pk[a], 43), sig |-> Pat(P!Sig[a], 47), cr |-> c] : a \in 1..4, c \in {<<>>, CrA}}
Msgs == Shorts \cup Fulls \cup Rejects \cup Replies \cup Finishes \cup Hellos \cup RReplies \cup IdSigs

\* fields outside the documented ranges
BadInitial(a) == [k |-> "initial", full |-> FALSE, ver |-> 1, dcid |-> C4, scid |-> C4, alpn |-> a, offer |-> 1,
                  e |-> E32, pre |-> H32, cr |-> CrA]
BadHello(a) == [k |-> "hello", ver |-> 1, dcid |-> C4, scid |-> C4, alpn |-> a, aead |-> 1, tid |-> P16, e |-> E32,
                binder |-> H32, cr |-> CrA]
WrittenAlpns == {<<>>, Pat(33, 11), Pat(255, 13)}
A256 == Pat(256, 13)

VARIABLE msg
Spec == msg \in Msgs /\ [][UNCHANGED msg]_msg

(* The bytes changed and the cuts: the first 4, the last 3, and the last and first byte of every piece   *)
(* (each type, version, length prefix, tag, offer and count byte is a piece of its own). A byte inside a  *)
(* fixed field is copied through by the parser and cannot change its outcome, so it is left out: a state *)
(* costs a few hundred parses, not one per byte of a 6529-byte message.                                  *)
MutVals == {0, 1, 4, 21, 33, 255}
Near(m) == UNION {{e - 1, e, e + 1} : e \in Ends(m)}
MutPos(m, b) == (1..4 \cup (Len(b) - 2)..Len(b) \cup Near(m)) \cap 1..Len(b)
CutPos(m, b) == (0..4 \cup (Len(b) - 3)..Len(b) \cup Near(m)) \cap 0..(Len(b) - 1)
Set(b, i, v) == [b EXCEPT ![i] = v]
Set2(b, i, n) == [b EXCEPT ![i] = n \div 256, ![i + 1] = n % 256]

RoundTrip ==
    LET b == Enc(msg)
        n == Len(b)
    IN /\ ParseOwn(msg, b) = Ok(msg)
       /\ EncodeCap(msg, n) = [res |-> "ok", bytes |-> b]
       /\ EncodeCap(msg, n - 1) = [res |-> "small", needed |-> 1]

Fits == IF msg.k = "idsig" THEN Len(Enc(msg)) <= P!MaxIdSig ELSE Len(Enc(msg)) <= P!MaxMessage

Strict ==
    LET b == Enc(msg)
    IN /\ \A j \in CutPos(msg, b) : LET d == ParseOwn(msg, SubSeq(b, 1, j)) IN d.res = "truncated" /\ d.needed >= 1
       /\ \A v \in {0, 1, 255} : ParseOwn(msg, b \o <<v>>) = Un("trailing bytes")

Reenc(m, y) == LET d == ParseOwn(m, y) IN d.res = "ok" => Enc(d.m) = y
Unique ==
    LET b == Enc(msg)
    IN \A j \in MutPos(msg, b) : \A v \in MutVals \ {b[j]} : Reenc(msg, Set(b, j, v))

Cross ==
    msg.k # "idsig" =>
        LET b == Enc(msg)
        IN /\ \A kind \in {"initial", "reply", "finish", "hello", "rreply"} \ {msg.k} : Parse(kind, b, 0, FALSE) = Un("wrong message type")
           /\ \A t \in {3, 8} : (msg.k # "reject" \/ msg.ty # t) => ParseReject(b, t) = Un("wrong message type")

Classes ==
    LET b == Enc(msg)
        S(i) == PieceStart(msg, i)
    IN /\ msg.k = "initial" =>
             /\ \A v \in {0, 9, 255} : ParseInitial(Set(b, 1, v)) = Un("unknown message type")
             /\ \A v \in 3..8 : ParseInitial(Set(b, 1, v)) = Un("wrong message type")
             /\ ParseInitial(Set(b, S(3), 21)) = Un("connection id too long")
             /\ \A v \in {0, 33, 255} : ParseInitial(Set(b, S(7), v)) = Un("alpn length")
             /\ \A v \in {0, 4, 255} : ParseInitial(Set(b, S(9), v)) = Un("aead offer")
       /\ msg.k = "reply" =>
             /\ ParseReply(Set(b, S(2), 21)) = Un("connection id too long")
             /\ \A v \in {0, 3, 255} : ParseReply(Set(b, S(4), v)) = Un("unknown aead")
             /\ \A n \in {0, TagLen - 1, MaxSealed + 1, 65535} : ParseReply(Set2(b, S(7), n)) = Un("sealed length")
       /\ msg.k = "finish" =>
             \A n \in {0, TagLen - 1, MaxSealed + 1, 65535} : ParseFinish(Set2(b, S(2), n)) = Un("sealed length")
       /\ msg.k = "hello" =>
             /\ \A v \in {0, 33, 255} : ParseHello(Set(b, S(7), v)) = Un("alpn length")
             /\ \A v \in {0, 3, 255} : ParseHello(Set(b, S(9), v)) = Un("unknown aead")
       /\ msg.k = "rreply" =>
             \A v \in {MaxBatch + 1, MaxBatch + 2, 255} : ParseRReply(Set(b, S(5), v)) = Un("ticket count")
       /\ msg.k = "idsig" =>
             /\ \A v \in {0, 5, 255} : ParseOwn(msg, Set(b, 1, v)) = Un("unknown identity algorithm")
             /\ \A n \in {P!Pk[msg.alg] - 1, P!Pk[msg.alg] + 1} : ParseOwn(msg, Set2(b, S(2), n)) = Un("public key length")
             /\ \A n \in {P!Sig[msg.alg] - 1, P!Sig[msg.alg] + 1} : ParseOwn(msg, Set2(b, S(4), n)) = Un("signature length")

\* what the code does with fields outside the documented ranges (constant: checked once per state, cheap)
OutOfRange ==
    /\ \A a \in WrittenAlpns \cup {A256} :
          EncodeCap(BadInitial(a), Big) = AlpnRefused /\ EncodeCap(BadHello(a), Big) = AlpnRefused
    /\ \A n \in {TagLen - 1, MaxSealed + 1} :
          LET f == [k |-> "finish", sealed |-> Pat(n, 3)]
          IN EncodeCap(f, Big).res = "ok" /\ ParseFinish(Enc(f)) = Un("sealed length")
    /\ EncodeCap([k |-> "finish", sealed |-> Pat(65536, 3)], Big) = [res |-> "overflow"]
    /\ LET s == [k |-> "idsig", alg |-> 1, pk |-> Pat(31, 43), sig |-> Pat(64, 47), cr |-> <<>>]
       IN EncodeCap(s, Big).res = "ok" /\ ParseIdSig(Enc(s), FALSE) = Un("public key length")

\* the doc of Initial::write: "BufferTooSmall if it does not fit, or a length error for a field out of range"
WriteRefusesBadAlpn == \A a \in WrittenAlpns \cup {A256} : EncodeCap(BadInitial(a), Big).res # "ok"
=============================================================================
