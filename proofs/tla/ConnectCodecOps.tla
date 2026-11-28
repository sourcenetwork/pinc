---------------------------- MODULE ConnectCodecOps ----------------------------
(***************************************************************************)
(* The wire formats of pinc-connect as pure operators over byte sequences: *)
(* the carrier frame (carrier/frame.rs), the relay datagram                *)
(* (relay/datagram.rs), the signed record (record.rs), the beacon          *)
(* (local.rs), the sleep notice (relay/sleep.rs), the ticket (ticket.rs)   *)
(* and the candidate list of a REACH_OUT (client/punch.rs).                *)
(*                                                                         *)
(* A format is a type byte followed by fields, read in order with the      *)
(* reader of pinc-wire: RdU8, RdBytes (Truncated with the shortfall),      *)
(* RdNode (the tag byte, 32 bytes, then the check of the tag) and RdAddr.  *)
(* Every refusal is the string the Rust test prints for the error it got:  *)
(* "trunc:N", "type:T", "trailing", "alias:A", "packet", "body",           *)
(* "status:S", "batch:why", "magic", "reach:T", "addrtag:T", "toomany",    *)
(* "padding",                                                              *)
(* "hints", "version:V", "flags:F", "toolong", "unexpected:why", with the  *)
(* prefix "frame/" for the wire errors of a datagram and "addr/", "taddr/" *)
(* and "baddr/" for those of an address of a datagram, a ticket and a      *)
(* beacon. A decoded frame is its type and its fields as byte sequences    *)
(* (a node is its 33 bytes, a flag is one byte, a batch is its member      *)
(* frames); an encoder runs a list of steps against a buffer of cap bytes: *)
(* a put that does not fit fails with the shortfall, a check fails with    *)
(* its error, so the error is the first one the code meets.                *)
(*                                                                         *)
(* The 64-bit lengths of a batch are the words of U64.tla (TLC integers    *)
(* are 32 bits wide).                                                      *)
(* Lean counterpart: Pinc/ConnectCodecCore.lean, ConnectFrame*.lean,       *)
(* ConnectDatagram.lean, ConnectRecord.lean, ConnectSigned.lean,           *)
(* ConnectTicket.lean.                                                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64

Er(e) == [ok |-> FALSE, e |-> e]
RdOk(v, r) == [ok |-> TRUE, v |-> v, r |-> r]
Pre(p, x) == IF x.ok THEN x ELSE Er(p \o x.e)

(* ---- the reader of pinc-wire ---- *)
RdU8(b) == IF b = <<>> THEN Er("trunc:1") ELSE RdOk(b[1], Tail(b))
RdBytes(n, b) == IF n <= Len(b) THEN RdOk(SubSeq(b, 1, n), SubSeq(b, n + 1, Len(b)))
                 ELSE Er("trunc:" \o ToString(n - Len(b)))

RdNode(b) ==
    LET r1 == RdU8(b) IN
    IF ~r1.ok THEN r1
    ELSE LET r2 == RdBytes(32, r1.r) IN
         IF ~r2.ok THEN r2
         ELSE IF r1.v \in 1..4 THEN RdOk(<<r1.v>> \o r2.v, r2.r)
              ELSE Er("unexpected:identity algorithm tag")

(* read_addr: the family tag, then the octets, then the port, in two reads *)
RdAddr(b) ==
    LET r1 == RdU8(b) IN
    IF ~r1.ok THEN r1
    ELSE IF r1.v \in {4, 6}
         THEN LET k == IF r1.v = 4 THEN 4 ELSE 16
                  r2 == RdBytes(k, r1.r) IN
              IF ~r2.ok THEN r2
              ELSE LET r3 == RdBytes(2, r2.r) IN
                   IF ~r3.ok THEN r3 ELSE RdOk(<<r1.v>> \o r2.v \o r3.v, r3.r)
         ELSE Er("addrtag:" \o ToString(r1.v))

(* n addresses; the prefix p wraps the error of the one that fails *)
RECURSIVE RdAddrs(_, _, _)
RdAddrs(p, n, b) ==
    IF n = 0 THEN RdOk(<<>>, b)
    ELSE LET a == Pre(p, RdAddr(b)) IN
         IF ~a.ok THEN a
         ELSE LET rest == RdAddrs(p, n - 1, a.r) IN
              IF ~rest.ok THEN rest ELSE RdOk(<<a.v>> \o rest.v, rest.r)

RECURSIVE Cat(_)
Cat(ss) == IF ss = <<>> THEN <<>> ELSE Head(ss) \o Cat(Tail(ss))

(* ---- the field engine ---- *)
(* a field kind: [k |-> "node"], "alias", "u8", [k |-> "fixed", n |-> N], [k |-> "addr", p |-> prefix] *)
RdField(lp, k, b) ==
    CASE k.k = "node" -> Pre(lp, RdNode(b))
      [] k.k = "alias" ->
           LET r == Pre(lp, RdU8(b)) IN
           IF ~r.ok THEN r ELSE IF r.v < 32 THEN RdOk(<<r.v>>, r.r) ELSE Er("alias:" \o ToString(r.v))
      [] k.k = "u8" -> LET r == Pre(lp, RdU8(b)) IN IF r.ok THEN RdOk(<<r.v>>, r.r) ELSE r
      [] k.k = "fixed" -> Pre(lp, RdBytes(k.n, b))
      [] k.k = "addr" -> Pre(k.p, RdAddr(b))

RECURSIVE RdPre(_, _, _)
RdPre(lp, ks, b) ==
    IF ks = <<>> THEN RdOk(<<>>, b)
    ELSE LET f == RdField(lp, Head(ks), b) IN
         IF ~f.ok THEN f
         ELSE LET rest == RdPre(lp, Tail(ks), f.r) IN
              IF ~rest.ok THEN rest ELSE RdOk(<<f.v>> \o rest.v, rest.r)

(* the tail: all that is left, 1 to max bytes, else the error e *)
RdTail(t, b) ==
    IF t = <<>> THEN RdOk(<<>>, b)
    ELSE IF Len(b) = 0 \/ t[1].max < Len(b) THEN Er(t[1].e) ELSE RdOk(<<b>>, <<>>)

RdLayout(lp, l, b) ==
    LET p == RdPre(lp, l.pre, b) IN
    IF ~p.ok THEN p
    ELSE LET t == RdTail(l.tail, p.r) IN
         IF ~t.ok THEN t ELSE RdOk(p.v \o t.v, t.r)

Finish(r) == IF r = <<>> THEN [ok |-> TRUE] ELSE Er("trailing")

(* ---- numbers: a byte sequence as a word of U64, and back ---- *)
RECURSIVE BeVal(_)
BeVal(bs) == IF bs = <<>> THEN U!Zero
             ELSE U!Add(U!Shl(BeVal(SubSeq(bs, 1, Len(bs) - 1)), 8), U!W(bs[Len(bs)]))

(* ---- the varint of pinc-wire as the loop of the code ---- *)
RECURSIVE VarLoop(_, _, _)
VarLoop(i, v, b) ==
    IF b = <<>> \/ i >= 9 THEN [done |-> FALSE]
    ELSE LET x == b[1]
             v2 == U!Add(v, U!Shl(U!W(x % 128), 7 * i)) IN
         IF x < 128
         THEN (IF x = 0 /\ i > 0 THEN [done |-> TRUE, err |-> "vnonmin"] ELSE [done |-> TRUE, val |-> v2, n |-> i + 1])
         ELSE VarLoop(i + 1, v2, Tail(b))

RdVar(b) ==
    LET r == VarLoop(0, U!Zero, b) IN
    IF r.done THEN (IF "err" \in DOMAIN r THEN Er(r.err) ELSE RdOk(r.val, SubSeq(b, r.n + 1, Len(b))))
    ELSE IF Len(b) >= 9 THEN Er("vlong") ELSE Er("trunc:1")

(* ---- the carrier frame ---- *)
MaxPacket == 1452
MaxNotice == 8192
BatchFrames == 64
BatchBytes == 16384

\* PUB, SYNC and DNSR carry a record of up to MaxRec bytes: 8 + 66 + 8 + 2 + 8 * 19 + 1 + 64 + 1984 + 3373
MaxRec == 8 + 2 * 33 + 8 + 2 + 8 * 19 + 1 + 64 + 1984 + 3373

PktTail == <<[max |-> MaxPacket, e |-> "packet"]>>
RecTail == <<[max |-> MaxRec, e |-> "body"]>>
NtcTail == <<[max |-> MaxNotice, e |-> "body"]>>
Nd == [k |-> "node"]
Al == [k |-> "alias"]
U8 == [k |-> "u8"]

FrameLayout(ty) ==
    CASE ty \in {2, 3} -> [pre |-> <<Nd, U8>>, tail |-> PktTail]
      [] ty \in {4, 17} -> [pre |-> <<>>, tail |-> RecTail]
      [] ty \in {5, 6} -> [pre |-> <<>>, tail |-> <<>>]
      [] ty \in {7, 8} -> [pre |-> <<>>, tail |-> PktTail]
      [] ty \in {9, 11} -> [pre |-> <<Nd, Al, U8>>, tail |-> PktTail]
      [] ty \in {10, 12} -> [pre |-> <<Al, U8>>, tail |-> PktTail]
      [] ty = 14 -> [pre |-> <<Nd>>, tail |-> <<>>]
      [] ty = 16 -> [pre |-> <<Nd, Nd, U8>>, tail |-> PktTail]
      [] ty = 18 -> [pre |-> <<>>, tail |-> NtcTail]
      [] OTHER -> [none |-> TRUE]

(* the DNSR step after the type byte: lp lifts wire errors, sp is the prefix of the other errors of the answer *)
DnsrStep(lp, sp, ty, b) ==
    LET p == RdPre(lp, <<Nd, U8>>, b) IN
    IF ~p.ok THEN p
    ELSE LET st == p.v[2][1] IN
         IF st = 1
         THEN LET t == RdTail(<<[max |-> MaxRec, e |-> sp \o "body"]>>, p.r) IN
              IF ~t.ok THEN t
              ELSE LET f == Finish(t.r) IN IF ~f.ok THEN f ELSE RdOk([ty |-> ty, fs |-> p.v \o t.v], <<>>)
         ELSE IF st \in {0, 2}
              THEN LET f == Finish(p.r) IN IF ~f.ok THEN f ELSE RdOk([ty |-> ty, fs |-> p.v], <<>>)
              ELSE Er(sp \o "status:" \o ToString(st))

(* the lengths of a batch: k nonzero varints whose running total stays below 2^64 *)
RECURSIVE BatLens(_, _, _)
BatLens(k, total, b) ==
    IF k = 0 THEN RdOk(<<>>, b)
    ELSE LET v == RdVar(b) IN
         IF ~v.ok THEN v
         ELSE IF v.v = U!Zero THEN Er("batch:empty frame")
         ELSE IF U!Le(U!Pw(64), U!Add(total, v.v)) THEN Er("batch:length")
         ELSE LET rest == BatLens(k - 1, U!Add(total, v.v), v.r) IN
              IF ~rest.ok THEN rest ELSE RdOk(<<v.v>> \o rest.v, rest.r)

RECURSIVE Sum(_)
Sum(ws) == IF ws = <<>> THEN U!Zero ELSE U!Add(Head(ws), Sum(Tail(ws)))

(* one frame from exactly b; Bat decodes the rest of a batch frame after its type byte *)
FrameWith(Bat(_), b) ==
    LET r == RdU8(b) IN
    IF ~r.ok THEN r
    ELSE LET ty == r.v IN
         IF ty = 13 THEN Bat(r.r)
         ELSE IF ty = 15 THEN DnsrStep("", "", 15, r.r)
         ELSE IF FrameLayout(ty) = [none |-> TRUE] THEN Er("type:" \o ToString(ty))
         ELSE LET l == RdLayout("", FrameLayout(ty), r.r) IN
              IF ~l.ok THEN l
              ELSE LET f == Finish(l.r) IN IF ~f.ok THEN f ELSE RdOk([ty |-> ty, fs |-> l.v], <<>>)

NoBat(r) == Er("type:13")
FrameNB(b) == FrameWith(NoBat, b)

RECURSIVE Members(_, _)
Members(ls, body) ==
    IF ls = <<>> THEN RdOk(<<>>, body)
    ELSE LET l == U!Val(Head(ls))
             head == SubSeq(body, 1, l) IN
         IF head[1] = 13 THEN Er("batch:nested batch")
         ELSE LET d == FrameNB(head) IN
              IF ~d.ok THEN d
              ELSE LET rest == Members(Tail(ls), SubSeq(body, l + 1, Len(body))) IN
                   IF ~rest.ok THEN rest ELSE RdOk(<<head>> \o rest.v, rest.r)

BatchStep(r) ==
    LET c == RdU8(r) IN
    IF ~c.ok THEN c
    ELSE IF c.v < 2 \/ c.v > BatchFrames THEN Er("batch:frame count")
    ELSE LET ls == BatLens(c.v, U!Zero, c.r)
             total == IF ls.ok THEN Sum(ls.v) ELSE U!Zero IN
         IF ~ls.ok THEN ls
         ELSE IF total # U!W(Len(ls.r)) \/ U!Lt(U!W(BatchBytes), total) THEN Er("batch:size")
         ELSE LET m == Members(ls.v, ls.r) IN
              IF ~m.ok THEN m ELSE RdOk([ty |-> 13, fs |-> m.v], <<>>)

\* Frame::decode
Frame(b) == FrameWith(BatchStep, b)

(* ---- the relay datagram ---- *)
MaxTunnel == MaxPacket - 28
DgLayout(ty) ==
    CASE ty = 1 -> [pre |-> <<[k |-> "fixed", n |-> 8]>>, tail |-> <<>>]
      [] ty = 2 -> [pre |-> <<[k |-> "fixed", n |-> 8], [k |-> "addr", p |-> "addr/"]>>, tail |-> <<>>]
      [] ty = 3 -> [pre |-> <<Nd>>, tail |-> <<>>]
      [] ty = 6 -> [pre |-> <<>>, tail |-> <<[max |-> MaxNotice, e |-> "frame/body"]>>]
      [] ty \in {8, 9} -> [pre |-> <<Nd, U8>>, tail |-> <<[max |-> MaxTunnel - 35, e |-> "packet"]>>]
      [] OTHER -> [none |-> TRUE]

\* The zero bytes an address query (type 1) and a lookup (type 3) carry after their fields: the longest answer (a QADR
\* of 1 + 8 + 19 bytes, a DNSR of MAX_DNS_DATAGRAM, which is MaxTunnel) plus its 28 header bytes is at most three times
\* the query's length, so the ledger of the node that answers lets the answer go to a source that proved nothing
\* (pinc-connect relay/datagram.rs QAD_LEN 19 and DNSQ_LEN 484: query_len of the answer, (answer + 28) / 3 rounded up).
MaxQadr == 1 + 8 + 19
QueryLen(a) == (a + 28 + 2) \div 3
DgPad(ty) == CASE ty = 1 -> QueryLen(MaxQadr) - 9
               [] ty = 3 -> QueryLen(MaxTunnel) - 34
               [] OTHER -> 0
Zeros(n) == [i \in 1..n |-> 0]
\* the padding: n bytes (Truncated with the shortfall), each zero, else Padding
RdPad(n, b) ==
    LET r == Pre("frame/", RdBytes(n, b)) IN
    IF ~r.ok THEN r ELSE IF r.v = Zeros(n) THEN RdOk(<<>>, r.r) ELSE Er("padding")

\* Datagram::decode
Dgram(b) ==
    LET r == Pre("frame/", RdU8(b)) IN
    IF ~r.ok THEN r
    ELSE LET ty == r.v IN
         IF ty = 4 THEN DnsrStep("frame/", "frame/", 4, r.r)
         ELSE IF DgLayout(ty) = [none |-> TRUE] THEN Er("type:" \o ToString(ty))
         ELSE LET l == RdLayout("frame/", DgLayout(ty), r.r) IN
              IF ~l.ok THEN l
              ELSE LET z == RdPad(DgPad(ty), l.r) IN
                   IF ~z.ok THEN z
                   ELSE LET f == Finish(z.r) IN IF ~f.ok THEN f ELSE RdOk([ty |-> ty, fs |-> l.v], <<>>)

(* ---- the writer: steps run against a buffer of cap bytes ---- *)
Put(bs) == [t |-> "put", b |-> bs]
Chk(c, e) == [t |-> "chk", c |-> c, e |-> e]

\* wp prefixes the wire error of a put that does not fit ("frame/" for a datagram)
RECURSIVE Run(_, _, _, _)
Run(wp, cap, ops, acc) ==
    IF ops = <<>> THEN [ok |-> TRUE, v |-> acc]
    ELSE LET o == Head(ops) IN
         IF o.t = "put"
         THEN IF Len(o.b) <= cap - Len(acc) THEN Run(wp, cap, Tail(ops), acc \o o.b)
              ELSE [ok |-> FALSE, e |-> wp \o "small:" \o ToString(Len(o.b) - (cap - Len(acc))),
                    small |-> Len(o.b) - (cap - Len(acc))]
         ELSE IF o.c THEN Run(wp, cap, Tail(ops), acc) ELSE Er(o.e)

\* the varint of a value below 2^30, as encode writes it
RECURSIVE VarEnc(_)
VarEnc(n) == IF n < 128 THEN <<n>> ELSE <<(n % 128) + 128>> \o VarEnc(n \div 128)

RECURSIVE LensBytes(_)
LensBytes(ps) == IF ps = <<>> THEN <<>> ELSE VarEnc(Len(Head(ps))) \o LensBytes(Tail(ps))

FieldOps(k, f) == IF k.k = "alias" THEN <<Chk(f[1] < 32, "alias:" \o ToString(f[1])), Put(f)>> ELSE <<Put(f)>>

RECURSIVE PreOps(_, _)
PreOps(ks, fs) == IF ks = <<>> THEN <<>> ELSE FieldOps(Head(ks), Head(fs)) \o PreOps(Tail(ks), Tail(fs))

TailOps(t, b) == <<Chk(1 <= Len(b) /\ Len(b) <= t.max, t.e), Put(b)>>

LayoutOps(l, fs) ==
    PreOps(l.pre, SubSeq(fs, 1, Len(l.pre))) \o
    (IF l.tail = <<>> THEN <<>> ELSE TailOps(l.tail[1], fs[Len(l.pre) + 1]))

DnsrOps(ty, e, fs) ==
    <<Put(<<ty>>), Put(fs[1]), Put(fs[2])>> \o (IF Len(fs) = 3 THEN TailOps([max |-> MaxRec, e |-> e], fs[3]) ELSE <<>>)

\* the steps of Frame::encode for the frame [ty, fs]
FrameOps(f) ==
    IF f.ty = 13 THEN <<Put(<<13>>), Put(<<Len(f.fs)>>), Put(LensBytes(f.fs)), Put(Cat(f.fs))>>
    ELSE IF f.ty = 15 THEN DnsrOps(15, "body", f.fs)
    ELSE <<Put(<<f.ty>>)>> \o LayoutOps(FrameLayout(f.ty), f.fs)

EncodeFrame(cap, f) == Run("", cap, FrameOps(f), <<>>)

FrameBytes(f) == IF f.ty = 13 THEN <<13, Len(f.fs)>> \o LensBytes(f.fs) \o Cat(f.fs) ELSE <<f.ty>> \o Cat(f.fs)

DgOps(f) ==
    IF f.ty = 4 THEN DnsrOps(4, "frame/body", f.fs)
    ELSE <<Put(<<f.ty>>)>> \o LayoutOps(DgLayout(f.ty), f.fs) \o (IF DgPad(f.ty) = 0 THEN <<>> ELSE <<Put(Zeros(DgPad(f.ty)))>>)

\* Datagram::encode: a datagram is refused with the error its decoder would give, once the bytes before the field fit
EncodeDg(cap, f) == Run("frame/", cap, DgOps(f), <<>>)

DgBytes(f) == <<f.ty>> \o Cat(f.fs) \o Zeros(DgPad(f.ty))

(* ---- signed structures ---- *)
RecMagic == <<86, 78, 67, 82, 69, 67, 0, 1>>
BcnMagic == <<86, 78, 67, 66, 67, 78, 0, 1>>
PkLen(t) == CASE t = 1 -> 32 [] t = 2 -> 33 [] t = 3 -> 1952 [] t = 4 -> 1984
SigLen(t) == CASE t = 1 -> 64 [] t = 2 -> 64 [] t = 3 -> 3309 [] t = 4 -> 3373

\* the reads shared by the three: bytes of the node's key and signature
RdKey(node, b) ==
    LET pk == RdBytes(PkLen(node[1]), b) IN
    IF ~pk.ok THEN pk
    ELSE LET sg == RdBytes(SigLen(node[1]), pk.r) IN
         IF ~sg.ok THEN sg ELSE RdOk([pk |-> pk.v, sg |-> sg.v], sg.r)

RecTailParse(node, home, seq, b) ==
    LET tag == RdU8(b) IN
    IF ~tag.ok THEN tag
    ELSE IF tag.v < 1 \/ tag.v > 5 THEN Er("reach:" \o ToString(tag.v))
    ELSE LET n == RdU8(tag.r) IN
         IF ~n.ok THEN n
         ELSE IF n.v > 8 THEN Er("toomany")
         ELSE LET as == RdAddrs("", n.v, n.r) IN
              IF ~as.ok THEN as
              ELSE LET hl == RdU8(as.r) IN
                   IF ~hl.ok THEN hl
                   ELSE IF hl.v > 64 THEN Er("hints")
                   ELSE LET h == RdBytes(hl.v, hl.r) IN
                        IF ~h.ok THEN h
                        ELSE LET k == RdKey(node, h.r) IN
                             IF ~k.ok THEN k
                             ELSE IF k.r # <<>> THEN Er("trailing")
                             ELSE RdOk([node |-> node, home |-> home, seq |-> seq, reach |-> tag.v, addrs |-> as.v,
                                        hints |-> h.v, pk |-> k.v.pk, sg |-> k.v.sg], <<>>)

\* Record::parse
RecParse(b) ==
    LET m == RdBytes(8, b) IN
    IF ~m.ok THEN m
    ELSE IF m.v # RecMagic THEN Er("magic")
    ELSE LET n1 == RdNode(m.r) IN
         IF ~n1.ok THEN n1
         ELSE LET n2 == RdNode(n1.r) IN
              IF ~n2.ok THEN n2
              ELSE LET sq == RdBytes(8, n2.r) IN
                   IF ~sq.ok THEN sq ELSE RecTailParse(n1.v, n2.v, sq.v, sq.r)

RecHead(r) == RecMagic \o r.node \o r.home \o r.seq \o <<r.reach, Len(r.addrs)>> \o Cat(r.addrs) \o <<Len(r.hints)>> \o r.hints \o r.pk
RecBytes(r) == RecHead(r) \o r.sg

\* prepare: the bounds are checked before anything is written
RecPrepare(cap, r) ==
    Run("", cap,
        <<Chk(Len(r.addrs) <= 8, "toomany"), Chk(Len(r.hints) <= 64, "hints"), Put(RecMagic), Put(r.node), Put(r.home),
          Put(r.seq), Put(<<r.reach>>), Put(<<Len(r.addrs)>>)>> \o [i \in 1..Len(r.addrs) |-> Put(r.addrs[i])] \o
        <<Put(<<Len(r.hints)>>), Put(r.hints), Put(r.pk)>>, <<>>)

BcnTailParse(node, seq, b) ==
    LET n == RdU8(b) IN
    IF ~n.ok THEN n
    ELSE IF n.v > 4 THEN Er("toolong")
    ELSE LET as == RdAddrs("baddr/", n.v, n.r) IN
         IF ~as.ok THEN as
         ELSE LET hl == RdU8(as.r) IN
              IF ~hl.ok THEN hl
              ELSE IF hl.v > 8 THEN Er("toolong")
              ELSE LET h == RdBytes(hl.v, hl.r) IN
                   IF ~h.ok THEN h
                   ELSE LET k == RdKey(node, h.r) IN
                        IF ~k.ok THEN k
                        ELSE IF k.r # <<>> THEN Er("trailing")
                        ELSE RdOk([node |-> node, seq |-> seq, addrs |-> as.v, hint |-> h.v, pk |-> k.v.pk, sg |-> k.v.sg], <<>>)

\* Beacon::parse
BcnParse(b) ==
    LET m == RdBytes(8, b) IN
    IF ~m.ok THEN m
    ELSE IF m.v # BcnMagic THEN Er("magic")
    ELSE LET n1 == RdNode(m.r) IN
         IF ~n1.ok THEN n1
         ELSE LET sq == RdBytes(8, n1.r) IN
              IF ~sq.ok THEN sq ELSE BcnTailParse(n1.v, sq.v, sq.r)

BcnHead(r) == BcnMagic \o r.node \o r.seq \o <<Len(r.addrs)>> \o Cat(r.addrs) \o <<Len(r.hint)>> \o r.hint \o r.pk
BcnBytes(r) == BcnHead(r) \o r.sg

BcnPrepare(cap, r) ==
    Run("", cap,
        <<Chk(Len(r.addrs) <= 4 /\ Len(r.hint) <= 8, "toolong"), Put(BcnMagic), Put(r.node), Put(r.seq),
          Put(<<Len(r.addrs)>>)>> \o [i \in 1..Len(r.addrs) |-> Put(r.addrs[i])] \o
        <<Put(<<Len(r.hint)>>), Put(r.hint), Put(r.pk)>>, <<>>)

\* Notice::parse; bytes after the signature are Unexpected("trailing bytes")
NtcParse(b) ==
    LET n == RdNode(b) IN
    IF ~n.ok THEN n
    ELSE LET ts == RdBytes(8, n.r) IN
         IF ~ts.ok THEN ts
         ELSE LET k == RdKey(n.v, ts.r) IN
              IF ~k.ok THEN k
              ELSE IF k.r # <<>> THEN Er("unexpected:trailing bytes")
              ELSE RdOk([node |-> n.v, ts |-> ts.v, pk |-> k.v.pk, sg |-> k.v.sg], <<>>)

NtcHead(r) == r.node \o r.ts \o r.pk
NtcBytes(r) == NtcHead(r) \o r.sg
NtcPrepare(cap, r) == Run("", cap, <<Put(r.node), Put(r.ts), Put(r.pk)>>, <<>>)
SleepLabel == <<112, 105, 110, 99, 45, 115, 108, 101, 101, 112>>  \* "pinc-sleep"
SleepMessage(relay, node, ts) == SleepLabel \o relay \o node \o ts

(* ---- the ticket ---- *)
TkFlags(t) == (IF t.home = <<>> THEN 0 ELSE 1) + 2 * Len(t.addrs)

\* Ticket::parse; the home relay is the empty sequence when absent
TkParse(b) ==
    LET v == RdU8(b) IN
    IF ~v.ok THEN v
    ELSE IF v.v # 1 THEN Er("version:" \o ToString(v.v))
    ELSE LET fl == RdU8(v.r) IN
         IF ~fl.ok THEN fl
         ELSE IF fl.v \div 16 # 0 \/ (fl.v \div 2) % 8 > 4 THEN Er("flags:" \o ToString(fl.v))
         ELSE LET nd == RdNode(fl.r) IN
              IF ~nd.ok THEN nd
              ELSE LET hm == IF fl.v % 2 = 1 THEN RdNode(nd.r) ELSE RdOk(<<>>, nd.r) IN
                   IF ~hm.ok THEN hm
                   ELSE LET as == RdAddrs("taddr/", (fl.v \div 2) % 8, hm.r) IN
                        IF ~as.ok THEN as
                        ELSE IF as.r # <<>> THEN Er("unexpected:trailing bytes")
                        ELSE RdOk([node |-> nd.v, home |-> hm.v, addrs |-> as.v], <<>>)

TkBytes(t) == <<1, TkFlags(t)>> \o t.node \o t.home \o Cat(t.addrs)
TkEncode(cap, t) ==
    Run("", cap, <<Put(<<1>>), Put(<<TkFlags(t)>>), Put(t.node)>> \o (IF t.home = <<>> THEN <<>> ELSE <<Put(t.home)>>) \o
        [i \in 1..Len(t.addrs) |-> Put(t.addrs[i])], <<>>)

(* ---- the candidate list of a REACH_OUT ---- *)
\* punch::decode: the addresses, or FALSE for a malformed body
CandsDec(b) ==
    LET n == RdU8(b) IN
    IF ~n.ok \/ n.v > 8 THEN [ok |-> FALSE]
    ELSE LET as == RdAddrs("", n.v, n.r) IN
         IF ~as.ok \/ as.r # <<>> THEN [ok |-> FALSE] ELSE [ok |-> TRUE, v |-> as.v]

\* punch::encode keeps the first 8 candidates
CandsEnc(cs) == LET k == IF Len(cs) > 8 THEN 8 ELSE Len(cs) IN <<k>> \o Cat(SubSeq(cs, 1, k))

(* ---- the base32 text of a ticket ---- *)
(* The accumulator of the code is a u32 whose high bits are never read: a symbol or a byte is taken from the lowest 13
   bits (at most 12 pending bits), so it is kept modulo 2^16 here, which TLC's 32-bit integers hold. *)
\* the symbols (0..31) of the bytes, the way to_text emits them; pending bits kept as (value, count)
RECURSIVE B32Drain(_, _, _)
B32Drain(acc, bits, out) ==
    IF bits >= 5 THEN B32Drain(acc, bits - 5, Append(out, ((acc \div (2 ^ (bits - 5))) % 32))) ELSE [acc |-> acc, bits |-> bits, out |-> out]

RECURSIVE B32Enc(_, _, _, _)
B32Enc(bs, acc, bits, out) ==
    IF bs = <<>> THEN (IF bits > 0 THEN Append(out, ((acc * (2 ^ (5 - bits))) % 32)) ELSE out)
    ELSE LET a == ((acc * 256) % 65536) + Head(bs)
             d == B32Drain(a, bits + 8, out) IN
         B32Enc(Tail(bs), d.acc, d.bits, d.out)

B32Of(bs) == B32Enc(bs, 0, 0, <<>>)

\* from_text: the symbols (already mapped from the characters), or the error "text"
RECURSIVE B32Dec(_, _, _, _)
B32Dec(ss, acc, bits, out) ==
    IF ss = <<>>
    THEN IF bits >= 5 \/ (acc % (2 ^ bits)) # 0 THEN Er("text") ELSE RdOk(out, <<>>)
    ELSE LET a == ((acc * 32) % 65536) + Head(ss)
             nb == bits + 5 IN
         IF nb >= 8
         THEN (IF Len(out) >= 144 THEN Er("text")
               ELSE B32Dec(Tail(ss), a, nb - 8, Append(out, ((a \div (2 ^ (nb - 8))) % 256))))
         ELSE B32Dec(Tail(ss), a, nb, out)

Alphabet(sym) == IF sym < 26 THEN 97 + sym ELSE 50 + (sym - 26)

\* the symbol of a character, either case, or FALSE
CharSym(c) ==
    LET l == IF c >= 65 /\ c <= 90 THEN c + 32 ELSE c IN
    IF l >= 97 /\ l <= 122 THEN [ok |-> TRUE, v |-> l - 97]
    ELSE IF l >= 50 /\ l <= 55 THEN [ok |-> TRUE, v |-> l - 50 + 26]
    ELSE [ok |-> FALSE]

TextSyms(text) ==
    IF \E i \in 1..Len(text) : ~CharSym(text[i]).ok THEN [ok |-> FALSE]
    ELSE [ok |-> TRUE, v |-> [i \in 1..Len(text) |-> CharSym(text[i]).v]]

\* Ticket::to_text into a buffer of cap bytes
TkText(cap, t) ==
    LET sy == B32Of(TkBytes(t))
        cs == [i \in 1..Len(sy) |-> Alphabet(sy[i])] IN
    IF Len(cs) <= cap THEN [ok |-> TRUE, v |-> cs] ELSE Er("small:" \o ToString(cap + 1))

\* Ticket::from_text
TkFromText(text) ==
    LET ss == TextSyms(text) IN
    IF ~ss.ok THEN Er("text")
    ELSE LET d == B32Dec(ss.v, 0, 0, <<>>) IN IF ~d.ok THEN d ELSE TkParse(d.v)

=============================================================================
