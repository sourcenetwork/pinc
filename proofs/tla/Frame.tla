------------------------------- MODULE Frame -------------------------------
(***************************************************************************)
(* The PINCER frame codecs (FrameOps.tla, the operators that follow        *)
(* pinc-transport frame/) checked on three domains, each case a state:     *)
(*                                                                         *)
(*   MODE = "frames"  every frame kind with its fields at the varint       *)
(*                    boundaries, at LIMIT and around the stream end;      *)
(*   MODE = "acks"    every list of up to MAXRANGES + 1 ranges over a      *)
(*                    small packet-number space, valid or not;             *)
(*   MODE = "bytes"   every byte string of up to 4 bytes over an alphabet  *)
(*                    with every type class and the varint edges, and      *)
(*                    every 6-byte string that starts as an ACK.           *)
(*                                                                         *)
(* Properties:                                                             *)
(*   RoundTrip  a frame Validate refuses is refused by Write with that     *)
(*              error; otherwise Write gives EncodedLen bytes, a buffer    *)
(*              one or more bytes short gives BufferTooSmall with the      *)
(*              shortfall, and Decode of the bytes followed by rest gives  *)
(*              the frame and rest. Three kinds take what follows them     *)
(*              (Expect): PADDING is the whole zero run, a STREAM or       *)
(*              DATAGRAM frame without a length runs to the end. A REKEY   *)
(*              request comes back with a zero echo and switch number.     *)
(*   Canon      whatever Decode accepts (the encodings, every cut, single  *)
(*              bytes changed, bytes appended, every short string) leaves  *)
(*              less than it was given and is the encoding Write gives for *)
(*              the frame, followed by what is left; or, for a STREAM      *)
(*              frame at offset 0, that encoding with the OFF bit and a    *)
(*              zero offset (the one leniency of the parser). The ranges   *)
(*              of an accepted ACK are extra + 1 ranges that WriteAck      *)
(*              writes back as the bytes read. Whatever Decode refuses is  *)
(*              refused with a documented error (DecErr).                  *)
(*   Strict     every proper cut of the encoding of a frame with a known   *)
(*              end is Truncated.                                          *)
(*   AckRT      WriteAck and AckLen accept exactly the lists whose first   *)
(*              MAXRANGES ranges are non-empty, inside the packet-number   *)
(*              space, descending and not touching (ValidRanges, stated    *)
(*              here from the definition); a refusal is Ack from both;     *)
(*              AckLen is the bytes written; Decode reads the frame back   *)
(*              and its ranges are the first MAXRANGES given.              *)
(*   IterOK     FrameIter that ends without an error has read frames whose *)
(*              encodings, in order, are the payload (up to the OFF bit).  *)
(*                                                                         *)
(* Witnesses (each must be violated): CanonStrict, Canon without the OFF   *)
(* exemption (Frame_off.cfg); Canon when a varint with a redundant zero    *)
(* byte is accepted, MINIMAL = FALSE (Frame_nonminimal.cfg); RoundTripAny, *)
(* the round trip claimed for any bytes after the frame (Frame_sep.cfg).   *)
(*                                                                         *)
(* Lean counterpart: TransportFrameThm.write_eq, bytes_length;             *)
(* TransportFrameCodec.decode_bytes, decode_inv, decode_offBytes,          *)
(* decode_unknown, decode_progress, frames_bytes; TransportFrameAck.       *)
(* writeAck_ok, writeAck_decode, writeAck_room, ackLen_error,              *)
(* ranges_write, decode_ranges.                                            *)
(***************************************************************************)
EXTENDS FrameOps, FiniteSets

CONSTANT MODE
VARIABLE c

BIG == 400

(* ---- the domains ---- *)
Vals == {0, 1, 127, 128, LIMIT - 1, LIMIT}
Datas == {<<>>, <<0>>, <<7, 0>>}
Long == [i \in 1..130 |-> i % 251]
B8 == {Zeros(8), [i \in 1..8 |-> 247 + i]}
B32 == {Zeros(32), [i \in 1..32 |-> i]}
T1 == [tid |-> Zeros(16), lt |-> <<0, 0>>]
T2 == [tid |-> [i \in 1..16 |-> 239 + i], lt |-> <<65535, 65534>>]
Batches == {<<>>, <<T1>>, <<T2>>, <<T2, T1>>, <<T1, T2, T2>>, <<T2, T1, T2, T1>>}

Frames ==
    {[k |-> "Padding", len |-> n] : n \in {1, 2, 3, 64, 65, 129}}
    \cup {[k |-> x] : x \in {"Ping", "Sleep", "Wake", "Ready"}}
    \cup {[k |-> "ResetStream", id |-> a, error |-> b, fs |-> d] : a, b, d \in {0, 128, LIMIT - 1, LIMIT}}
    \cup {[k |-> "StopSending", id |-> a, error |-> b] : a, b \in Vals}
    \cup {[k |-> "Stream", id |-> a, off |-> o, fin |-> fi, data |-> d, imp |-> im] :
            a \in {0, 128, LIMIT}, o \in {0, 1, MAXEND - 1, MAXEND, MAXEND + 1, LIMIT}, fi \in BOOLEAN,
            d \in Datas \cup {Long}, im \in BOOLEAN}
    \cup {[k |-> "MaxStreamData", id |-> a, max |-> b] : a, b \in Vals}
    \cup {[k |-> "MaxStreams", limit |-> a] : a \in Vals}
    \cup {[k |-> x, d |-> d] : x \in {"PathChallenge", "PathResponse"}, d \in B8}
    \cup {[k |-> "Close", error |-> a] : a \in Vals}
    \cup {[k |-> "Datagram", data |-> d, imp |-> im] : d \in Datas \cup {Long}, im \in BOOLEAN}
    \cup {[k |-> "MtuProbeEcho", mtu |-> m] : m \in {0, 255, 256, 1200, 65535}}
    \cup {[k |-> "Rekey", ans |-> a, sh |-> s, echo |-> e, spn |-> p] : a \in BOOLEAN, s \in B32, e \in B8, p \in Vals}
    \cup {[k |-> "NewTickets", es |-> es] : es \in Batches}
    \cup {[k |-> "Extension", ty |-> t, body |-> d] : t \in {0, 63, 64, 127, 128, LIMIT - 1, LIMIT}, d \in Datas \cup {Long}}

\* the frames of the quick profile (proofs/tla/quick): every kind, each field at its varint edges with the others held,
\* and the 130-byte payload in seven frames only
FramesQuick ==
    {[k |-> "Padding", len |-> n] : n \in {1, 64, 65}}
    \cup {[k |-> x] : x \in {"Ping", "Sleep", "Wake", "Ready"}}
    \cup {[k |-> "ResetStream", id |-> a, error |-> b, fs |-> d] : a \in {0, 128, LIMIT - 1, LIMIT}, b, d \in {0, LIMIT}}
    \cup {[k |-> "StopSending", id |-> a, error |-> b] : a \in {127, 128, LIMIT - 1, LIMIT}, b \in {0, LIMIT}}
    \cup {[k |-> "Stream", id |-> a, off |-> o, fin |-> fi, data |-> d, imp |-> im] :
            a \in {0, LIMIT}, o \in {0, 1, MAXEND - 1, MAXEND, LIMIT}, fi \in BOOLEAN, d \in {<<>>, <<7, 0>>}, im \in BOOLEAN}
    \cup {[k |-> "Stream", id |-> 128, off |-> o, fin |-> FALSE, data |-> Long, imp |-> im] : o \in {0, 1}, im \in BOOLEAN}
    \cup {[k |-> "MaxStreamData", id |-> a, max |-> b] : a \in {127, 128, LIMIT - 1, LIMIT}, b \in {0, LIMIT}}
    \cup {[k |-> "MaxStreams", limit |-> a] : a \in Vals}
    \cup {[k |-> x, d |-> d] : x \in {"PathChallenge", "PathResponse"}, d \in B8}
    \cup {[k |-> "Close", error |-> a] : a \in Vals}
    \cup {[k |-> "Datagram", data |-> d, imp |-> im] : d \in Datas \cup {Long}, im \in BOOLEAN}
    \cup {[k |-> "MtuProbeEcho", mtu |-> m] : m \in {0, 255, 256, 1200, 65535}}
    \cup {[k |-> "Rekey", ans |-> a, sh |-> [i \in 1..32 |-> i], echo |-> e, spn |-> p] :
            a \in BOOLEAN, e \in B8, p \in {127, 128, LIMIT}}
    \cup {[k |-> "NewTickets", es |-> es] : es \in {<<>>, <<T1>>, <<T2, T1>>, <<T1, T2, T2>>}}
    \cup {[k |-> "Extension", ty |-> t, body |-> d] : t \in {63, 64, 128, LIMIT}, d \in {<<>>, <<7, 0>>}}
    \cup {[k |-> "Extension", ty |-> 64, body |-> Long]}

PNs == 0..(MAXPN + 1)
Ranges == PNs \X PNs
RangeLists == UNION {[1..n -> Ranges] : n \in 0..(MAXRANGES + 1)}
\* the range lists of the quick profile: every list of up to MAXRANGES ranges, and one past it after two valid ranges
RangeListsQuick == UNION {[1..n -> Ranges] : n \in 0..MAXRANGES} \cup {<<<<2, 2>>, <<0, 0>>, r>> : r \in Ranges}

Alphabet == {0, 1, 2, 3, 4, 5, 8, 10, 12, 14, 17, 28, 48, 49, 58, 63, 64, 128, 129, 255}
Strings == UNION {[1..n -> Alphabet] : n \in 0..4} \cup {<<2>> \o s : s \in [1..5 -> {0, 1, 2, 3, 5, 128}]}
\* the quick profile (proofs/tla/quick): strings of up to 3 bytes, and ack bytes of 4 after the type
StringsQuick == UNION {[1..n -> Alphabet] : n \in 0..3} \cup {<<2>> \o s : s \in [1..4 -> {0, 1, 2, 3, 5, 128}]}

Cases ==
    CASE MODE = "frames" -> {[t |-> "frame", f |-> f] : f \in Frames}
      [] MODE = "acks" -> {[t |-> "ack", rs |-> rs] : rs \in RangeLists}
      [] MODE = "bytes" -> {[t |-> "bytes", b |-> b] : b \in Strings}

Init == c \in Cases
Spec == Init /\ [][UNCHANGED c]_c

(* ---- what is accepted ---- *)
Rests == {<<>>, <<1>>, <<0>>, <<0, 0, 9>>, <<128>>}
Cuts(b) == {Take(b, n) : n \in 1..(Len(b) - 1)}
Muts(b) ==
    Cuts(b) \cup {b} \cup {b \o <<x>> : x \in {0, 1, 128}}
    \cup {[b EXCEPT ![i] = x] : i \in 1..Min(Len(b), 12), x \in {0, 1, 2, 5, 12, 64, 128, 255}}

Unassigned == {3, 6, 7, 16} \cup (19..25) \cup (29..47) \cup (50..57)
DecErr(d) ==
    /\ d.e \in {"Truncated", "VarintTooLong", "VarintNonMinimal", "ticket count", "UnknownType", "Ack",
                "TooManyRanges", "StreamEnd", "RekeyKind"}
    /\ d.e = "UnknownType" => d.n \in Unassigned
    /\ d.e = "Truncated" => d.n >= 1
    /\ d.e \notin {"UnknownType", "Truncated"} => d.n = 0

\* the second accepted encoding of a STREAM frame at offset 0: the OFF bit and the offset written as 0
OffBytes(f) ==
    VEnc(StreamType(1, f.fin, f.imp)) \o VEnc(f.id) \o <<0>>
      \o (IF f.imp THEN f.data ELSE VEnc(Len(f.data)) \o f.data)

AcceptedAt(b, lenient) ==
    LET d == Decode(b) IN
    IF d.ok
    THEN /\ Len(d.r) < Len(b)
         /\ LET w == Write(BIG, d.v) IN
            /\ w.ok
            /\ \/ w.v \o d.r = b
               \/ lenient /\ d.v.k = "Stream" /\ d.v.off = 0 /\ OffBytes(d.v) \o d.r = b
         /\ d.v.k = "Ack" =>
              LET rr == AckRanges(d.v) IN
              /\ Len(rr) = d.v.extra + 1
              /\ WriteAck(BIG, rr) = Ok(Take(b, Len(b) - Len(d.r)), <<>>)
    ELSE DecErr(d)

Inputs ==
    CASE c.t = "frame" -> LET w == Write(BIG, c.f) IN IF w.ok THEN Muts(w.v) ELSE {}
      [] c.t = "ack" -> LET w == WriteAck(BIG, c.rs) IN IF w.ok THEN Muts(w.v) ELSE {}
      [] c.t = "bytes" -> {c.b}

Canon == \A b \in Inputs : AcceptedAt(b, TRUE)
CanonStrict == \A b \in Inputs : AcceptedAt(b, FALSE)

(* ---- round trip, lengths, errors of the encoder ---- *)
Expect(f, rest) ==
    CASE f.k = "Padding" -> Ok([f EXCEPT !.len = f.len + ZeroRun(rest)], Drop(rest, ZeroRun(rest)))
      [] f.k = "Stream" /\ f.imp ->
           IF f.off + Len(f.data) + Len(rest) > MAXEND THEN Er("StreamEnd", 0)
           ELSE Ok([f EXCEPT !.data = f.data \o rest], <<>>)
      [] f.k = "Datagram" /\ f.imp -> Ok([f EXCEPT !.data = f.data \o rest], <<>>)
      [] f.k = "Rekey" /\ ~f.ans -> Ok([f EXCEPT !.echo = Zeros(8), !.spn = 0], rest)
      [] OTHER -> Ok(f, rest)

\* what Validate must answer, from the documentation of Frame::write
Refused(f) ==
    IF \/ f.k = "ResetStream" /\ (f.id >= LIMIT \/ f.error >= LIMIT \/ f.fs >= LIMIT)
       \/ f.k \in {"StopSending", "Close"} /\ f.error >= LIMIT
       \/ f.k \in {"StopSending", "MaxStreamData", "Stream"} /\ f.id >= LIMIT
       \/ f.k = "MaxStreamData" /\ f.max >= LIMIT
       \/ f.k = "MaxStreams" /\ f.limit >= LIMIT
       \/ f.k = "Stream" /\ f.off >= LIMIT
       \/ f.k = "Extension" /\ f.ty >= LIMIT
       \/ f.k = "Rekey" /\ f.spn >= LIMIT
    THEN Er("VarintOverflow", 0)
    ELSE IF f.k = "Stream" /\ f.off + Len(f.data) > MAXEND THEN Er("StreamEnd", 0)
    ELSE IF f.k = "Extension" /\ f.ty < 64 THEN Er("UnknownType", f.ty)
    ELSE Ok(<<>>, <<>>)

RoundTripWith(rests) ==
    c.t = "frame" =>
        LET f == c.f
            w == Write(BIG, f) IN
        /\ Validate(f) = Refused(f)
        /\ IF ~Refused(f).ok THEN w = Refused(f) /\ \A cap \in 0..3 : Write(cap, f) = Refused(f)
           ELSE /\ w.ok
                /\ Len(w.v) = EncodedLen(f)
                /\ \A cap \in 0..(Len(w.v) - 1) : Write(cap, f) = Er("BufferTooSmall", Len(w.v) - cap)
                /\ Write(Len(w.v), f) = w
                /\ \A rest \in rests : Decode(w.v \o rest) = Expect(f, rest)

RoundTrip == RoundTripWith(Rests) /\ Write(BIG, [k |-> "Padding", len |-> 0]) = Ok(<<>>, <<>>)
\* the wrong claim of a witness: the frame comes back whatever follows it
RoundTripAny ==
    c.t = "frame" =>
        LET w == Write(BIG, c.f) IN
        w.ok => \A rest \in Rests : Decode(w.v \o rest).ok /\ Decode(w.v \o rest).r = rest

Greedy(f) == f.k = "Padding" \/ (f.k \in {"Stream", "Datagram"} /\ f.imp)
Strict ==
    /\ Decode(<<>>) = Er("Truncated", 1)
    /\ c.t = "frame" =>
         LET w == Write(BIG, c.f) IN
         w.ok /\ ~Greedy(c.f) => \A p \in Cuts(w.v) : ~Decode(p).ok /\ Decode(p).e = "Truncated"
    /\ c.t = "ack" =>
         LET w == WriteAck(BIG, c.rs) IN
         w.ok => \A p \in Cuts(w.v) : ~Decode(p).ok /\ Decode(p).e = "Truncated"

(* ---- the ACK encoder ---- *)
ValidRanges(rs) ==
    LET n == Min(MAXRANGES, Len(rs)) IN
    /\ n >= 1
    /\ \A i \in 1..n : /\ rs[i][1] <= rs[i][2]
                       /\ rs[i][2] <= MAXPN
                       /\ i > 1 => rs[i][2] + 2 <= rs[i - 1][1]

AckRT ==
    c.t = "ack" =>
        LET rs == c.rs
            w == WriteAck(BIG, rs)
            l == AckLen(rs) IN
        IF ValidRanges(rs)
        THEN /\ w.ok
             /\ l = Ok(Len(w.v), <<>>)
             /\ \A cap \in 0..(Len(w.v) - 1) : WriteAck(cap, rs) = Er("BufferTooSmall", Len(w.v) - cap)
             /\ WriteAck(Len(w.v), rs) = w
             /\ \A rest \in Rests :
                    LET d == Decode(w.v \o rest) IN
                    /\ d.ok
                    /\ d.r = rest
                    /\ d.v.k = "Ack"
                    /\ AckRanges(d.v) = Take(rs, Min(MAXRANGES, Len(rs)))
                    /\ Write(BIG, d.v) = w
                    /\ EncodedLen(d.v) = Len(w.v)
        ELSE w = Er("Ack", 0) /\ l = Er("Ack", 0) /\ WriteAck(0, rs) = Er("Ack", 0)

(* ---- the iterator ---- *)
RECURSIVE Payload(_)
Payload(fs) == IF Len(fs) = 0 THEN <<>> ELSE Write(BIG, fs[1]).v \o Payload(Tail(fs))

IterOK ==
    c.t = "bytes" =>
        LET it == Iter(c.b) IN
        /\ Len(it.fs) <= Len(c.b)
        /\ it.e = "none" /\ (\A i \in 1..Len(it.fs) : ~(it.fs[i].k = "Stream" /\ it.fs[i].off = 0)) =>
             Payload(it.fs) = c.b
        /\ it.e # "none" => DecErr(it)
=============================================================================
