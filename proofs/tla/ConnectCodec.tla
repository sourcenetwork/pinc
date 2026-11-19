------------------------------ MODULE ConnectCodec ------------------------------
(***************************************************************************)
(* Model check of the wire formats of pinc-connect (ConnectCodecOps.tla):  *)
(* a systematic finite domain of valid frames, datagrams, records,         *)
(* beacons, notices, tickets and candidate lists, with the field           *)
(* boundaries of every width, and the properties below over it.            *)
(*                                                                         *)
(*  RoundTrip   decoding the bytes of a valid value returns the value and *)
(*              uses all the bytes; the encoder into a buffer of exactly  *)
(*              that size writes those bytes, into a smaller one reports  *)
(*              the shortfall of the first write that does not fit        *)
(*  Canon       every single-byte mutation, every proper cut and every    *)
(*              byte appended to a valid encoding that is still accepted  *)
(*              re-encodes to itself, so a value has exactly one accepted *)
(*              encoding                                                  *)
(*  Strict      the exact refusal for each class of malformed input: an   *)
(*              empty input, an unknown type, a truncated node id, a node *)
(*              tag out of range, bytes after a fixed-size frame, a       *)
(*              packet that is empty or over the bound, an alias of 32    *)
(*              or more, an answer status above 2, a batch with a count,  *)
(*              a length, a size or a member that is not allowed, a       *)
(*              record, beacon or ticket with a field out of range, and   *)
(*              bytes after the signature                                 *)
(*  Prepare     a record or beacon with too many addresses or hint bytes  *)
(*              is refused before anything is written                     *)
(*  Text        the base32 text of a ticket decodes to the ticket, in     *)
(*              either case, and a text with a stray bit, a stray         *)
(*              character or an impossible length is refused              *)
(* Lean: Pinc/ConnectFrame*.lean, ConnectBatch.lean, ConnectDatagram.lean, *)
(* ConnectRecord.lean, ConnectSigned.lean, ConnectTicket*.lean.            *)
(***************************************************************************)
EXTENDS ConnectCodecOps

VARIABLE x

Rep(n, v) == [i \in 1..n |-> v]
Node(t, base) == <<t>> \o [i \in 1..32 |-> base + i]
N1 == Node(1, 0)
N2 == Node(2, 100)
N3 == Node(3, 50)
N4 == Node(4, 200)
Nodes == {N1, N2, N3, N4}
Packets == {<<3>>, <<1, 2>>, Rep(MaxPacket, 5)}
Flags == {<<0>>, <<255>>}
Aliases == {<<0>>, <<31>>}
Addr4 == <<4, 10, 0, 0, 1, 1, 187>>
Addr6 == <<6>> \o [i \in 1..16 |-> i] \o <<255, 255>>
Addrs == {Addr4, Addr6}

(* ---- signed structures: Ed25519 (32 / 64), P-256 (33 / 64) and the hybrid (1984 / 3373) ---- *)
Rec(node, home, addrs, hints, reach) ==
    [node |-> node, home |-> home, seq |-> <<0, 0, 0, 0, 0, 1, 2, 255>>, reach |-> reach, addrs |-> addrs, hints |-> hints,
     pk |-> Rep(PkLen(node[1]), 9), sg |-> Rep(SigLen(node[1]), 8)]
Recs == {Rec(N1, N2, <<>>, <<>>, 1), Rec(N2, N1, <<Addr4>>, <<7>>, 5), Rec(N3, N2, <<Addr6, Addr4>>, Rep(64, 3), 3),
         Rec(N1, N4, [i \in 1..8 |-> Addr6], <<>>, 2), Rec(N4, N1, <<>>, <<1, 2>>, 4)}
Bcn(node, addrs, hint) ==
    [node |-> node, seq |-> <<1, 2, 3, 4, 5, 6, 7, 8>>, addrs |-> addrs, hint |-> hint,
     pk |-> Rep(PkLen(node[1]), 9), sg |-> Rep(SigLen(node[1]), 8)]
Bcns == {Bcn(N1, <<>>, <<>>), Bcn(N2, <<Addr4, Addr6>>, Rep(8, 4)), Bcn(N3, [i \in 1..4 |-> Addr4], <<1>>),
         Bcn(N4, <<>>, <<>>)}
Ntc(node) == [node |-> node, ts |-> <<0, 0, 0, 0, 0, 0, 1, 44>>, pk |-> Rep(PkLen(node[1]), 9), sg |-> Rep(SigLen(node[1]), 8)]
Ntcs == {Ntc(N1), Ntc(N2), Ntc(N3), Ntc(N4)}
Tk(node, home, addrs) == [node |-> node, home |-> home, addrs |-> addrs]
Tks == {Tk(N1, <<>>, <<>>), Tk(N2, N1, <<>>), Tk(N3, <<>>, <<Addr4>>), Tk(N4, N3, <<Addr6, Addr4, Addr4, Addr6>>),
        Tk(N1, N2, <<Addr4, Addr4>>)}

RecBodies == {RecBytes(r) : r \in {Rec(N1, N2, <<>>, <<>>, 1), Rec(N2, N1, <<Addr4>>, <<7>>, 5)}}

(* ---- frames ---- *)
Fr(ty, fs) == [ty |-> ty, fs |-> fs]
Simple ==
    {Fr(ty, <<n, f, p>>) : ty \in {2, 3}, n \in Nodes, f \in Flags, p \in Packets}
    \cup {Fr(ty, <<n, a, f, p>>) : ty \in {9, 11}, n \in {N1, N4}, a \in Aliases, f \in Flags, p \in {<<3>>, Rep(MaxPacket, 5)}}
    \cup {Fr(ty, <<a, f, p>>) : ty \in {10, 12}, a \in Aliases, f \in Flags, p \in Packets}
    \cup {Fr(ty, <<p>>) : ty \in {7, 8}, p \in Packets}
    \cup {Fr(ty, <<>>) : ty \in {5, 6}}
    \cup {Fr(14, <<n>>) : n \in Nodes}
    \cup {Fr(16, <<n, m, f, p>>) : n \in {N1, N2}, m \in {N3, N4}, f \in Flags, p \in {<<3>>, Rep(MaxPacket, 5)}}
    \cup {Fr(ty, <<b>>) : ty \in {4, 17}, b \in RecBodies \cup {<<1>>, Rep(MaxRec, 6)}}
    \cup {Fr(18, <<b>>) : b \in {<<1>>, Rep(MaxNotice, 6)}}
    \cup {Fr(15, <<n, <<0>>>>) : n \in Nodes} \cup {Fr(15, <<n, <<2>>>>) : n \in Nodes}
    \cup {Fr(15, <<n, <<1>>, b>>) : n \in {N1, N3}, b \in RecBodies \cup {<<1>>, Rep(MaxRec, 6)}}

Mem == {<<5>>, <<6>>, <<7, 3>>, <<2>> \o N1 \o <<0, 3>>, <<14>> \o N2, <<10, 1, 2, 9>>}
Batches ==
    {Fr(13, <<a, b>>) : a \in Mem, b \in Mem}
    \cup {Fr(13, <<a, b, c>>) : a \in {<<5>>, <<7, 3>>}, b \in {<<6>>, <<14>> \o N1}, c \in {<<5>>}}
    \cup {Fr(13, Rep(64, <<5>>)),
          Fr(13, Rep(11, <<7>> \o Rep(MaxPacket, 5)) \o <<<<7>> \o Rep(400, 1)>>)}
Frames == Simple \cup Batches

(* mutations of one byte, proper cuts and one appended byte *)
Vals == {0, 2, 13, 32, 255}
Mut(b) == UNION {{[b EXCEPT ![i] = v] : v \in Vals \ {b[i]}} : i \in 1..Len(b)}
Cuts(b) == {SubSeq(b, 1, k) : k \in 0..(Len(b) - 1)}
Ext(b) == {b \o <<v>> : v \in {0, 7, 255}}
Around(b) == Mut(b) \cup Cuts(b) \cup Ext(b)

Lower(m) == [i \in 1..Len(m) |-> IF m[i] >= 65 /\ m[i] <= 90 THEN m[i] + 32 ELSE m[i]]

Small(S, n) == {f \in S : Len(FrameBytes(f)) <= n}

(* ---- the properties ---- *)
Shortfall(r) == r.ok = FALSE /\ "small" \in DOMAIN r /\ r.small > 0

FrameRT ==
    \A f \in Frames :
        LET b == FrameBytes(f) IN
        /\ Frame(b) = RdOk(f, <<>>)
        /\ EncodeFrame(Len(b), f) = [ok |-> TRUE, v |-> b]
        /\ \A c \in {0, 1, 2, 5, 34, Len(b) - 1} : c < Len(b) => Shortfall(EncodeFrame(c, f))

FrameCanon ==
    \A f \in Small(Frames, 80) :
        \A m \in Around(FrameBytes(f)) : Frame(m).ok => FrameBytes(Frame(m).v) = m

DgramOf(ty, fs) == Fr(ty, fs)
Dgrams ==
    {DgramOf(1, <<Rep(8, 7)>>), DgramOf(1, <<Rep(8, 0)>>)}
    \cup {DgramOf(2, <<Rep(8, 7), a>>) : a \in Addrs}
    \cup {DgramOf(3, <<n>>) : n \in Nodes}
    \cup {DgramOf(4, <<n, <<0>>>>) : n \in Nodes} \cup {DgramOf(4, <<n, <<2>>>>) : n \in {N1, N4}}
    \cup {DgramOf(4, <<n, <<1>>, b>>) : n \in {N1, N2}, b \in RecBodies \cup {<<1>>, Rep(MaxRec, 6)}}
    \cup {DgramOf(6, <<b>>) : b \in {<<1>>, Rep(MaxNotice, 6)}}
    \cup {DgramOf(ty, <<n, f, p>>) : ty \in {8, 9}, n \in Nodes, f \in Flags,
                                     p \in {<<3>>, <<1, 2>>, Rep(MaxTunnel - 35, 5)}}

DgramRT ==
    \A d \in Dgrams :
        LET b == DgBytes(d) IN
        /\ Dgram(b) = RdOk(d, <<>>)
        /\ EncodeDg(Len(b), d) = [ok |-> TRUE, v |-> b]
        /\ \A c \in {0, 1, 8, 34, Len(b) - 1} : c < Len(b) => Shortfall(EncodeDg(c, d))

DgramCanon ==
    \A d \in {e \in Dgrams : Len(DgBytes(e)) <= 80} :
        \A m \in Around(DgBytes(d)) : Dgram(m).ok => DgBytes(Dgram(m).v) = m

RecRT ==
    \A r \in Recs :
        LET b == RecBytes(r) IN
        /\ RecParse(b) = RdOk(r, <<>>)
        /\ RecPrepare(Len(RecHead(r)), r) = [ok |-> TRUE, v |-> RecHead(r)]
        /\ \A c \in {0, 8, 41, Len(RecHead(r)) - 1} : c < Len(RecHead(r)) => RecPrepare(c, r).ok = FALSE

RecCanon ==
    \A r \in {Rec(N2, N1, <<Addr4>>, <<7>>, 5), Rec(N1, N2, <<>>, <<>>, 1)} :
        \A m \in Around(RecBytes(r)) : RecParse(m).ok => RecBytes(RecParse(m).v) = m

BcnRT ==
    \A r \in Bcns :
        LET b == BcnBytes(r) IN
        /\ BcnParse(b) = RdOk(r, <<>>)
        /\ BcnPrepare(Len(BcnHead(r)), r) = [ok |-> TRUE, v |-> BcnHead(r)]
        /\ \A c \in {0, 8, 41} : c < Len(BcnHead(r)) => BcnPrepare(c, r).ok = FALSE

BcnCanon ==
    \A r \in {Bcn(N2, <<Addr4, Addr6>>, Rep(8, 4)), Bcn(N1, <<>>, <<>>)} :
        \A m \in Around(BcnBytes(r)) : BcnParse(m).ok => BcnBytes(BcnParse(m).v) = m

NtcRT ==
    \A r \in Ntcs :
        LET b == NtcBytes(r) IN
        /\ NtcParse(b) = RdOk(r, <<>>)
        /\ NtcPrepare(Len(NtcHead(r)), r) = [ok |-> TRUE, v |-> NtcHead(r)]
        /\ \A c \in {0, 8, 41} : c < Len(NtcHead(r)) => NtcPrepare(c, r).ok = FALSE
        /\ SleepMessage(N1, r.node, r.ts) # SleepMessage(N2, r.node, r.ts)
        /\ Len(SleepMessage(N1, r.node, r.ts)) = 84

NtcCanon ==
    \A r \in {Ntc(N1), Ntc(N2)} :
        \A m \in Around(NtcBytes(r)) : NtcParse(m).ok => NtcBytes(NtcParse(m).v) = m

Upper(m) == [i \in 1..Len(m) |-> IF m[i] >= 97 /\ m[i] <= 122 THEN m[i] - 32 ELSE m[i]]

TkRT ==
    \A t \in Tks :
        LET b == TkBytes(t)
            tx == TkText(500, t).v IN
        /\ TkParse(b) = RdOk(t, <<>>)
        /\ TkEncode(Len(b), t) = [ok |-> TRUE, v |-> b]
        /\ \A c \in {0, 1, 2, 34} : c < Len(b) => Shortfall(TkEncode(c, t))
        /\ TkFromText(tx) = RdOk(t, <<>>)
        /\ TkFromText(Upper(tx)) = RdOk(t, <<>>)
        /\ TkText(Len(tx), t).ok /\ ~TkText(Len(tx) - 1, t).ok

TkCanon ==
    \A t \in Tks :
        \A m \in Around(TkBytes(t)) : TkParse(m).ok => TkBytes(TkParse(m).v) = m

TextCanon ==
    \A t \in Tks :
        LET s == TkText(500, t).v IN
        \A m \in Cuts(s) \cup Ext(s) \cup {[s EXCEPT ![i] = v] : i \in 1..Len(s), v \in {48, 97, 122, 55}} :
            TkFromText(m).ok => Lower(m) = TkText(500, TkFromText(m).v).v

CandSets == {<<>>, <<Addr4>>, <<Addr6, Addr4>>, [i \in 1..8 |-> Addr6]}
CandRT ==
    \A cs \in CandSets :
        /\ CandsDec(CandsEnc(cs)) = [ok |-> TRUE, v |-> cs]
        /\ \A m \in Around(CandsEnc(cs)) : CandsDec(m).ok => CandsEnc(CandsDec(m).v) = m
    /\ CandsEnc([i \in 1..9 |-> Addr4]) = CandsEnc([i \in 1..8 |-> Addr4])

(* ---- the refusals ---- *)
BadNode == <<0>> \o [i \in 1..32 |-> 1]
BadNode5 == <<5>> \o [i \in 1..32 |-> 1]
FrameStrict ==
    /\ Frame(<<>>) = Er("trunc:1")
    /\ \A t \in {0, 1, 19, 20, 255} : Frame(<<t, 1, 2>>) = Er("type:" \o ToString(t))
    /\ Frame(<<13>>) = Er("trunc:1")
    /\ Frame(<<5, 0>>) = Er("trailing") /\ Frame(<<6, 1, 2, 3>>) = Er("trailing")
    /\ Frame(<<14>> \o N1 \o <<0>>) = Er("trailing")
    /\ Frame(<<14>>) = Er("trunc:1")
    /\ \A k \in 1..32 : Frame(<<14>> \o SubSeq(N1, 1, k)) = Er("trunc:" \o ToString(33 - k))
    /\ Frame(<<14>> \o BadNode) = Er("unexpected:identity algorithm tag")
    /\ Frame(<<14>> \o BadNode5) = Er("unexpected:identity algorithm tag")
    /\ \A ty \in {2, 3} : Frame(<<ty>> \o N1 \o <<9>>) = Er("packet")
    /\ \A ty \in {2, 3} : Frame(<<ty>> \o N1 \o <<9>> \o Rep(MaxPacket + 1, 1)) = Er("packet")
    /\ \A ty \in {2, 3} : Frame(<<ty>> \o N1) = Er("trunc:1")
    /\ \A ty \in {7, 8} : Frame(<<ty>>) = Er("packet") /\ Frame(<<ty>> \o Rep(MaxPacket + 1, 1)) = Er("packet")
    /\ \A ty \in {9, 11} : Frame(<<ty>> \o N1 \o <<32, 0, 7>>) = Er("alias:32")
    /\ \A ty \in {10, 12} : Frame(<<ty, 200, 0, 7>>) = Er("alias:200") /\ Frame(<<ty, 5>>) = Er("trunc:1")
    /\ \A ty \in {10, 12} : Frame(<<ty, 5, 0>>) = Er("packet")
    /\ \A ty \in {4, 17} : Frame(<<ty>>) = Er("body") /\ Frame(<<ty>> \o Rep(MaxRec + 1, 1)) = Er("body")
    /\ Frame(<<18>>) = Er("body") /\ Frame(<<18>> \o Rep(MaxNotice + 1, 1)) = Er("body")
    /\ Frame(<<15>> \o N1) = Er("trunc:1")
    /\ \A s \in {3, 4, 255} : Frame(<<15>> \o N1 \o <<s>>) = Er("status:" \o ToString(s))
    /\ Frame(<<15>> \o N1 \o <<1>>) = Er("body")
    /\ Frame(<<15>> \o N1 \o <<0, 0>>) = Er("trailing") /\ Frame(<<15>> \o N1 \o <<2, 0>>) = Er("trailing")
    /\ Frame(<<15>> \o N1 \o <<1>> \o Rep(MaxRec + 1, 1)) = Er("body")
    /\ \A c \in {0, 1, 65, 255} : Frame(<<13, c, 1, 1, 5, 6>>) = Er("batch:frame count")
    /\ Frame(<<13, 2, 0, 1, 5>>) = Er("batch:empty frame")
    /\ Frame(<<13, 2, 1, 1, 5>>) = Er("batch:size") /\ Frame(<<13, 2, 1, 1, 5, 6, 7>>) = Er("batch:size")
    /\ Frame(<<13, 2, 1, 128>>) = Er("trunc:1") /\ Frame(<<13, 2, 1>>) = Er("trunc:1")
    /\ Frame(<<13, 2, 1, 128, 0, 5>>) = Er("vnonmin")
    /\ Frame(<<13, 2>> \o Rep(9, 128)) = Er("vlong")
    /\ Frame(<<13, 2, 1, 1, 13, 5>>) = Er("batch:nested batch")
    /\ Frame(<<13, 2, 1, 1, 5, 99>>) = Er("type:99")
    /\ Frame(<<13, 2, 1, 2, 5, 14, 1>>) = Er("trunc:32")
    /\ Frame(<<13, 2, 255, 255, 255, 255, 255, 255, 255, 127, 1>>) = Er("batch:size")
    /\ Frame(<<13, 3, 255, 255, 255, 255, 255, 255, 255, 255, 127, 255, 255, 255, 255, 255, 255, 255, 255, 127, 2>>)
         = Er("batch:length")

DgramStrict ==
    /\ Dgram(<<>>) = Er("frame/trunc:1")
    /\ \A t \in {0, 5, 7, 10, 255} : Dgram(<<t, 1>>) = Er("type:" \o ToString(t))
    /\ Dgram(<<1, 1, 2, 3>>) = Er("frame/trunc:5")
    /\ Dgram(<<1>> \o Rep(8, 1) \o <<0>>) = Er("trailing")
    /\ Dgram(<<2>> \o Rep(8, 1) \o <<7>>) = Er("addr/addrtag:7")
    /\ Dgram(<<2>> \o Rep(8, 1) \o <<4, 1, 2>>) = Er("addr/trunc:2")
    /\ Dgram(<<2>> \o Rep(8, 1) \o Addr4 \o <<0>>) = Er("trailing")
    /\ Dgram(<<2>> \o Rep(8, 1)) = Er("addr/trunc:1")
    /\ Dgram(<<3>> \o N1 \o <<0>>) = Er("trailing")
    /\ Dgram(<<3>>) = Er("frame/trunc:1")
    /\ \A s \in {3, 9} : Dgram(<<4>> \o N1 \o <<s>>) = Er("frame/status:" \o ToString(s))
    /\ Dgram(<<4>> \o N1 \o <<1>>) = Er("frame/body")
    /\ Dgram(<<6>>) = Er("frame/body") /\ Dgram(<<6>> \o Rep(MaxNotice + 1, 1)) = Er("frame/body")
    /\ \A ty \in {8, 9} : Dgram(<<ty>> \o N1 \o <<0>>) = Er("packet")
    /\ \A ty \in {8, 9} : Dgram(<<ty>> \o N1 \o <<0>> \o Rep(MaxTunnel - 35 + 1, 1)) = Er("packet")
    /\ \A ty \in {8, 9} : Dgram(<<ty>> \o N1 \o <<0>> \o Rep(MaxTunnel - 35, 1)).ok

RecStrict ==
    LET r == Rec(N1, N2, <<Addr4>>, <<7>>, 3)
        b == RecBytes(r) IN
    /\ RecParse(<<>>) = Er("trunc:8")
    /\ RecParse(SubSeq(b, 1, 5)) = Er("trunc:3")
    /\ RecParse([b EXCEPT ![8] = 2]) = Er("magic")
    /\ RecParse([b EXCEPT ![9] = 0]) = Er("unexpected:identity algorithm tag")
    /\ RecParse(SubSeq(b, 1, 20)) = Er("trunc:21")
    /\ RecParse([b EXCEPT ![8 + 66 + 8 + 1] = 0]) = Er("reach:0")
    /\ RecParse([b EXCEPT ![8 + 66 + 8 + 1] = 6]) = Er("reach:6")
    /\ RecParse([b EXCEPT ![8 + 66 + 8 + 2] = 9]) = Er("toomany")
    /\ RecParse([b EXCEPT ![8 + 66 + 8 + 3] = 5]) = Er("addrtag:5")
    /\ RecParse(b \o <<0>>) = Er("trailing")
    /\ RecParse(SubSeq(b, 1, Len(b) - 1)) = Er("trunc:1")
    /\ RecParse(SubSeq(b, 1, 8 + 66 + 8 + 2)) = Er("trunc:1")
    /\ RecPrepare(2000, [Rec(N1, N2, <<Addr4>>, <<7>>, 3) EXCEPT !.addrs = [i \in 1..9 |-> Addr4]]) = Er("toomany")
    /\ RecPrepare(0, [Rec(N1, N2, <<Addr4>>, <<7>>, 3) EXCEPT !.addrs = [i \in 1..9 |-> Addr4]]) = Er("toomany")
    /\ RecPrepare(2000, [Rec(N1, N2, <<Addr4>>, <<7>>, 3) EXCEPT !.hints = Rep(65, 1)]) = Er("hints")
    /\ RecPrepare(0, [Rec(N1, N2, <<Addr4>>, <<7>>, 3) EXCEPT !.hints = Rep(65, 1)]) = Er("hints")

BcnStrict ==
    LET r == Bcn(N2, <<Addr4>>, <<7>>)
        b == BcnBytes(r) IN
    /\ BcnParse(<<>>) = Er("trunc:8")
    /\ BcnParse([b EXCEPT ![8] = 2]) = Er("magic")
    /\ BcnParse([b EXCEPT ![8 + 33 + 8 + 1] = 5]) = Er("toolong")
    /\ BcnParse([b EXCEPT ![8 + 33 + 8 + 2] = 3]) = Er("baddr/addrtag:3")
    /\ BcnParse(b \o <<1>>) = Er("trailing")
    /\ BcnPrepare(2000, [r EXCEPT !.addrs = [i \in 1..5 |-> Addr4]]) = Er("toolong")
    /\ BcnPrepare(0, [r EXCEPT !.hint = Rep(9, 1)]) = Er("toolong")

NtcStrict ==
    LET r == Ntc(N2)
        b == NtcBytes(r) IN
    /\ NtcParse(<<>>) = Er("trunc:1")
    /\ NtcParse(SubSeq(b, 1, 34)) = Er("trunc:7")
    /\ NtcParse(b \o <<0>>) = Er("unexpected:trailing bytes")
    /\ NtcParse(SubSeq(b, 1, Len(b) - 1)) = Er("trunc:1")
    /\ NtcParse([b EXCEPT ![1] = 9]) = Er("unexpected:identity algorithm tag")

TkStrict ==
    LET t == Tk(N4, N3, <<Addr4>>)
        b == TkBytes(t) IN
    /\ TkParse(<<>>) = Er("trunc:1")
    /\ \A v \in {0, 2, 255} : TkParse([b EXCEPT ![1] = v]) = Er("version:" \o ToString(v))
    /\ TkParse(<<1>>) = Er("trunc:1")
    /\ \A f \in {16, 128, 10, 12, 14} : TkParse(<<1, f>> \o N1) = Er("flags:" \o ToString(f))
    /\ TkParse(<<1, 1>> \o N1) = Er("trunc:1")
    /\ TkParse(<<1, 2>> \o N1) = Er("taddr/trunc:1")
    /\ TkParse(<<1, 2>> \o N1 \o <<9>>) = Er("taddr/addrtag:9")
    /\ TkParse(b \o <<0>>) = Er("unexpected:trailing bytes")
    /\ TkParse(<<1, 0>> \o N1 \o <<0>>) = Er("unexpected:trailing bytes")
    /\ TkFromText(<<>>) = Er("trunc:1")
    /\ TkFromText(<<97, 33>>) = Er("text")
    /\ TkFromText(<<49>>) = Er("text")
    /\ TkFromText(<<56>>) = Er("text")
    /\ TkFromText(<<97>>) = Er("text")
    /\ TkFromText(Rep(400, 97)) = Er("text")

Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
=============================================================================
