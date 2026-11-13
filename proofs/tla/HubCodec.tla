---------------------------- MODULE HubCodec ----------------------------
(***************************************************************************)
(* The hub stream codec of vinc-membership codec.rs, byte for byte:       *)
(* Frame::parse (Decode), Frame::read (Read), Frame::encode (EncodeCap)   *)
(* and Frame::body_len (BodyLen). A frame is len32 | type | topic_len |   *)
(* topic | rest. Membership owns HELLO 1, ACK 2, DELTA 3, SNAP 4, PROBE 12 *)
(* and DOWN 13; every other type passes through as "other". Parsing is    *)
(* strict: a short body, a stray byte, a reserved flag, an alive byte or a *)
(* path byte out of range, a probe count outside 1..4, a snapshot that is  *)
(* not whole alive entries, and a membership frame with a topic are all    *)
(* refused, each with the reason the code names (the strings below are the *)
(* constructors of Err in Vinc/MembershipCodec.lean). The 64-bit and      *)
(* 32-bit fields (incarnation, silence, probe age) are the words of U64.   *)
(*                                                                         *)
(* Checked (the HubCodec_*.cfg configs), for a systematic finite domain   *)
(* of frames of                                                           *)
(* every kind (field boundaries of every width, all flag combinations,    *)
(* 0..3 snapshot entries, 1..4 probes, topics of 0, 1 and 255 bytes):     *)
(*   RoundTrip   Decode (body f) = f, the body is BodyLen f long, and      *)
(*               Read (Enc f ++ rest) returns f with 4 + BodyLen f bytes;  *)
(*   Unique      every single-byte mutation, every cut and every trailing  *)
(*               byte of a body that is accepted re-encodes to itself, so  *)
(*               each frame has exactly one accepted body;                 *)
(*   Strict      each malformed class named above is refused with its own  *)
(*               reason, every proper cut of a fixed-size frame is "short", *)
(*               every trailing byte of a fixed frame or a snapshot is     *)
(*               refused with that frame's reason;                         *)
(*   Stream      Read of any proper prefix of a frame asks for more bytes,  *)
(*               and a prefix that names a body above 262144 is refused    *)
(*               with "tooLarge" even though the body is not there yet;    *)
(*   Buffers     EncodeCap succeeds exactly when the buffer holds the      *)
(*               frame; the 160-byte buffer of Membership::tx holds every  *)
(*               small frame, 4 + 3 + 64 * 51 a 64-entry chunk, FLOOR_MAX + *)
(*               8 a FLOOR frame.                                          *)
(* Lean counterpart: Vinc/MembershipCodec*.lean (parse_encBody,            *)
(* parse_canonical, read_enc, read_canonical, read_prefix, the strictness  *)
(* theorems, encode_ok, small_fits, snapFrames_shape).                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

U == INSTANCE U64

MaxBody == 262144
EntryLen == 51
SnapMax == 4096
SnapChunk == 64
MaxProbes == 4
FloorMax == 4096

IsMem(t) == t \in {1, 2, 3, 4, 12, 13}

(* ---- numbers: big-endian bytes of the words of U64 ---- *)
Be8(w) == <<w[4] \div 256, w[4] % 256, w[3] \div 256, w[3] % 256, w[2] \div 256, w[2] % 256, w[1] \div 256, w[1] % 256>>
BeBytes(w, k) == SubSeq(Be8(w), 9 - k, 8)
FromBytes(bs) ==
    LET n == Len(bs)
        p == [i \in 1..8 |-> IF i <= 8 - n THEN 0 ELSE bs[i - (8 - n)]]
    IN <<p[7] * 256 + p[8], p[5] * 256 + p[6], p[3] * 256 + p[4], p[1] * 256 + p[2], 0>>

Bit(b) == IF b THEN 1 ELSE 0

RECURSIVE Cat(_)
Cat(ss) == IF ss = <<>> THEN <<>> ELSE Head(ss) \o Cat(Tail(ss))

(* ---- encoding ---- *)
EncEntry(e) == e.m \o BeBytes(e.inc, 8) \o BeBytes(U!W(e.ver), 2) \o e.th \o <<e.a>>
EncProbe(p) == BeBytes(p.age, 4) \o <<p.path>>

EncBody(f) ==
    CASE f.k = "hello" ->
            <<1, 0>> \o BeBytes(f.inc, 8) \o BeBytes(U!W(f.ver), 2) \o f.th \o <<Bit(f.snap) + 2 * Bit(f.homed)>>
      [] f.k = "ack" -> <<2, 0>>
      [] f.k = "probe" -> <<12, 0>>
      [] f.k = "delta" -> <<3, 0>> \o EncEntry(f.e)
      [] f.k = "snap" -> <<4, 0, Bit(f.part) + 2 * Bit(f.more)>> \o Cat([i \in 1..Len(f.es) |-> EncEntry(f.es[i])])
      [] f.k = "down" ->
            <<13, 0>> \o f.m \o BeBytes(f.inc, 8) \o BeBytes(f.sil, 4) \o <<Len(f.pr)>> \o Cat([i \in 1..Len(f.pr) |-> EncProbe(f.pr[i])])
      [] f.k = "other" -> <<f.ty, Len(f.topic)>> \o f.topic \o f.rest

BodyLen(f) ==
    CASE f.k = "hello" -> 2 + 19
      [] f.k = "ack" \/ f.k = "probe" -> 2
      [] f.k = "delta" -> 2 + EntryLen
      [] f.k = "snap" -> 2 + (1 + Len(f.es) * EntryLen)
      [] f.k = "down" -> 2 + (32 + 8 + 4 + 1 + 5 * Len(f.pr))
      [] f.k = "other" -> 2 + (Len(f.topic) + Len(f.rest))

Topic(f) == IF f.k = "other" THEN f.topic ELSE <<>>

Enc(f) == BeBytes(U!W(Len(EncBody(f))), 4) \o EncBody(f)

(* Frame::encode into a buffer of cap bytes, in the order of the writes of the code *)
EncodeCap(f, cap) ==
    IF BodyLen(f) > MaxBody THEN [err |-> "tooLarge"]
    ELSE IF cap < 5 THEN [err |-> "bufferSmall"]
    ELSE IF Len(Topic(f)) > 255 THEN [err |-> "topicLong"]
    ELSE IF cap < 4 + BodyLen(f) THEN [err |-> "bufferSmall"]
    ELSE [err |-> "ok", bytes |-> Enc(f)]

(* ---- decoding ---- *)
Err(c) == [err |-> c]
Ok(f) == [err |-> "ok", f |-> f]

EntryOf(c) == [m |-> SubSeq(c, 1, 32), inc |-> FromBytes(SubSeq(c, 33, 40)), ver |-> FromBytes(SubSeq(c, 41, 42))[1],
               th |-> SubSeq(c, 43, 50), a |-> c[51]]

PHello(r) ==
    IF Len(r) < 19 THEN Err("short")
    ELSE IF r[19] \div 4 # 0 THEN Err("helloFlag")
    ELSE IF Len(r) # 19 THEN Err("helloLen")
    ELSE Ok([k |-> "hello", inc |-> FromBytes(SubSeq(r, 1, 8)), ver |-> FromBytes(SubSeq(r, 9, 10))[1], th |-> SubSeq(r, 11, 18),
             snap |-> r[19] % 2 = 1, homed |-> (r[19] \div 2) % 2 = 1])

PDelta(r) ==
    IF Len(r) < EntryLen THEN Err("short")
    ELSE IF r[EntryLen] > 2 THEN Err("aliveByte")
    ELSE IF Len(r) # EntryLen THEN Err("deltaLen")
    ELSE Ok([k |-> "delta", e |-> EntryOf(SubSeq(r, 1, EntryLen))])

PSnap(r) ==
    IF Len(r) < 1 THEN Err("short")
    ELSE IF r[1] \div 4 # 0 THEN Err("snapFlag")
    ELSE LET eb == SubSeq(r, 2, Len(r))
             n == Len(eb) \div EntryLen
             bad == {i \in 1..n : eb[EntryLen * i] # 1}
         IN IF Len(eb) % EntryLen # 0 \/ n > SnapMax THEN Err("snapSize")
            ELSE IF bad # {}
                 THEN LET i == CHOOSE i \in bad : \A j \in bad : i <= j
                      IN IF eb[EntryLen * i] > 2 THEN Err("aliveByte") ELSE Err("snapNotAlive")
                 ELSE Ok([k |-> "snap", part |-> r[1] % 2 = 1, more |-> (r[1] \div 2) % 2 = 1,
                          es |-> [i \in 1..n |-> EntryOf(SubSeq(eb, EntryLen * (i - 1) + 1, EntryLen * i))]])

PDown(r) ==
    IF Len(r) < 45 THEN Err("short")
    ELSE LET n == r[45] IN
         IF n = 0 \/ n > MaxProbes THEN Err("probeCount")
         ELSE LET bad == {i \in 1..n : Len(r) < 45 + 5 * i \/ (IF Len(r) < 45 + 5 * i THEN FALSE ELSE r[45 + 5 * i] > 2)}
              IN IF bad # {}
                 THEN LET i == CHOOSE i \in bad : \A j \in bad : i <= j
                      IN IF Len(r) < 45 + 5 * i THEN Err("short") ELSE Err("probePath")
                 ELSE IF Len(r) # 45 + 5 * n THEN Err("downLen")
                 ELSE Ok([k |-> "down", m |-> SubSeq(r, 1, 32), inc |-> FromBytes(SubSeq(r, 33, 40)),
                          sil |-> FromBytes(SubSeq(r, 41, 44)),
                          pr |-> [i \in 1..n |-> [age |-> FromBytes(SubSeq(r, 46 + 5 * (i - 1), 49 + 5 * (i - 1))),
                                                  path |-> r[45 + 5 * i]]]])

Dispatch(ty, topic, r) ==
    CASE ty = 1 -> PHello(r)
      [] ty = 2 -> IF r # <<>> THEN Err("ackLen") ELSE Ok([k |-> "ack"])
      [] ty = 12 -> IF r # <<>> THEN Err("probeLen") ELSE Ok([k |-> "probe"])
      [] ty = 3 -> PDelta(r)
      [] ty = 4 -> PSnap(r)
      [] ty = 13 -> PDown(r)
      [] OTHER -> Ok([k |-> "other", ty |-> ty, topic |-> topic, rest |-> r])

Decode(b) ==
    IF Len(b) < 2 THEN Err("short")
    ELSE LET ty == b[1]
             tl == b[2]
         IN IF Len(b) - 2 < tl THEN Err("short")
            ELSE LET topic == SubSeq(b, 3, 2 + tl)
                     r == SubSeq(b, 3 + tl, Len(b))
                 IN IF topic # <<>> /\ IsMem(ty) THEN Err("topic") ELSE Dispatch(ty, topic, r)

(* Frame::read: Err, "more" (need more bytes) or the frame and the bytes used *)
Read(buf) ==
    IF Len(buf) < 4 THEN [err |-> "more"]
    ELSE LET w == FromBytes(SubSeq(buf, 1, 4))
         IN IF w[2] > 4 \/ (w[2] = 4 /\ w[1] > 0) THEN Err("tooLarge")
            ELSE LET len == w[1] + 65536 * w[2]
                 IN IF Len(buf) - 4 < len THEN [err |-> "more"]
                    ELSE LET d == Decode(SubSeq(buf, 5, 4 + len))
                         IN IF d.err # "ok" THEN d ELSE [err |-> "ok", f |-> d.f, n |-> 4 + len]

(***************************************************************************)
(* The checked domain                                                      *)
(***************************************************************************)
P2(k) == U!Pw(k)
Edge(k) == U!Sub(U!Pw(k), U!One)
(* the field values of a 64-bit incarnation: the boundaries of every limb and byte *)
Incs == {U!Zero, U!One, U!W(255), U!W(256), Edge(16), P2(16), Edge(32), P2(32), Edge(48), P2(48), Edge(63), P2(63), U!Max64}
Incs3 == {U!Zero, Edge(32), U!Max64}
Words32 == {U!Zero, U!One, U!W(65536), Edge(32)}
Vers == {0, 256, 65535}
Z(n) == [i \in 1..n |-> 0]
Seq1(n) == [i \in 1..n |-> i]
Mems == {Z(32), Seq1(32)}
Ths == {Z(8), Seq1(8)}

Hellos == {[k |-> "hello", inc |-> i, ver |-> v, th |-> t, snap |-> s, homed |-> h] :
              i \in Incs, v \in Vers, t \in Ths, s \in BOOLEAN, h \in BOOLEAN}
Entries == {[m |-> m, inc |-> i, ver |-> v, th |-> t, a |-> a] : m \in Mems, i \in Incs3, v \in {0, 65535}, t \in Ths, a \in 0..2}
Deltas == {[k |-> "delta", e |-> e] : e \in Entries}
AliveEntries == {e \in Entries : e.a = 1}
SnapEntries == {[m |-> Seq1(32), inc |-> Edge(32), ver |-> 1, th |-> th, a |-> 1] : th \in Ths} \cup
               {[m |-> Z(32), inc |-> U!Max64, ver |-> 65535, th |-> Z(8), a |-> 1]}
RECURSIVE EntrySeqs(_)
EntrySeqs(n) == IF n = 0 THEN {<<>>} ELSE {<<e>> \o s : e \in SnapEntries, s \in EntrySeqs(n - 1)}
Snaps == {[k |-> "snap", part |-> p, more |-> m, es |-> es] : p \in BOOLEAN, m \in BOOLEAN, es \in UNION {EntrySeqs(n) : n \in 0..3}}
DProbes == {[age |-> U!Zero, path |-> 0], [age |-> Edge(32), path |-> 1], [age |-> U!W(1000), path |-> 2]}
RECURSIVE ProbeSeqs(_)
ProbeSeqs(n) == IF n = 0 THEN {<<>>} ELSE {<<p>> \o s : p \in DProbes, s \in ProbeSeqs(n - 1)}
Downs == {[k |-> "down", m |-> m, inc |-> i, sil |-> w, pr |-> pr] :
              m \in {Seq1(32)}, i \in {U!Max64}, w \in {U!Zero, Edge(32)}, pr \in UNION {ProbeSeqs(n) : n \in 1..MaxProbes}}
Others == {[k |-> "other", ty |-> ty, topic |-> tp, rest |-> r] :
              ty \in {0, 5, 11, 14, 255}, tp \in {<<>>, <<7>>, Z(255)}, r \in {<<>>, <<9>>, Seq1(5)}}
(* the chunk size of send_snapshot and one more: 64 and 65 entries *)
Rep(e, n) == [i \in 1..n |-> e]
SnapNs == {[k |-> "snap", part |-> p, more |-> m, es |-> Rep(e, n)] :
              p \in {FALSE}, m \in {TRUE}, e \in {[m |-> Seq1(32), inc |-> Edge(32), ver |-> 1, th |-> Z(8), a |-> 1]}, n \in {SnapChunk, SnapChunk + 1}}
Fixeds == {[k |-> "ack"], [k |-> "probe"]} \cup Deltas

(* the domain is split into parts so that each configuration checks in well under a minute *)
CONSTANT Part
Frames == CASE Part = "hello" -> Hellos
            [] Part = "fixed" -> Fixeds
            [] Part = "snap" -> Snaps
            [] Part = "snapn" -> SnapNs
            [] Part = "down" -> Downs
            [] Part = "other" -> Others

VARIABLE f
Spec == f \in Frames /\ [][UNCHANGED f]_f

Fixed(x) == x.k \in {"hello", "ack", "probe", "delta", "down"}
FixedErr(x) == CASE x.k = "hello" -> "helloLen" [] x.k = "ack" -> "ackLen" [] x.k = "probe" -> "probeLen"
                 [] x.k = "delta" -> "deltaLen" [] x.k = "down" -> "downLen" [] x.k = "snap" -> "snapSize"

(* every byte of a short body; of a long one the header, the ends and the entry and probe boundaries *)
MutPos(body) == {j \in 1..Len(body) : Len(body) <= 60 \/ j <= 8 \/ j >= Len(body) - 6 \/ j % EntryLen \in {0, 1, 2, 50} \/ j \in 44..52}
CutPos(body) == {j \in 0..(Len(body) - 1) : Len(body) <= 60 \/ j <= 8 \/ j >= Len(body) - 6 \/ (j - 3) % EntryLen \in {0, 1, 50} \/ j \in 44..52}
Cuts(body) == {SubSeq(body, 1, j) : j \in CutPos(body)}
Extras(body) == {body \o <<x>> : x \in {0, 1, 128, 255}}

RoundTrip ==
    LET body == EncBody(f)
        enc == Enc(f)
        bl == BodyLen(f)
    IN /\ Decode(body) = Ok(f)
       /\ Len(body) = bl
       /\ Read(enc \o <<7, 7>>) = [err |-> "ok", f |-> f, n |-> 4 + bl]
       /\ EncodeCap(f, 4 + bl).err = "ok" /\ EncodeCap(f, 4 + bl).bytes = enc
       /\ EncodeCap(f, 3 + bl) = [err |-> "bufferSmall"]

(* an accepted cut or trailing byte re-encodes to itself: each frame has exactly one accepted body *)
Reenc(b) == LET d == Decode(b) IN d.err = "ok" => EncBody(d.f) = b
Unique ==
    LET body == EncBody(f)
    IN /\ \A b \in Cuts(body) \cup Extras(body) : Reenc(b)
       /\ \A j \in MutPos(body) : \A v \in {0, 1, 2, 3, 4, 13, 255} \ {body[j]} :
            Reenc([body EXCEPT ![j] = v])

(* the cuts of a fixed frame are all "short"; a trailing byte is the frame's own refusal; the cuts of a snapshot are
   short or the size refusal unless they end at an entry boundary; the cuts of a passthrough frame are short until
   the topic is complete, and an accepted cut is an other frame with a shorter rest *)
Strict ==
    LET body == EncBody(f)
    IN /\ Fixed(f) => \A b \in Cuts(body) : Decode(b) = Err("short")
       /\ (Fixed(f) \/ f.k = "snap") => \A b \in Extras(body) : Decode(b) = Err(FixedErr(f))
       /\ f.k = "snap" => \A b \in Cuts(body) : ((Len(b) < 3 \/ (Len(b) - 3) % EntryLen # 0) => Decode(b).err \in {"short", "snapSize"})
       /\ f.k = "other" => \A j \in CutPos(body) :
            LET d == Decode(SubSeq(body, 1, j)) IN
            IF j < 2 + Len(f.topic) THEN d = Err("short")
            ELSE d = Ok([k |-> "other", ty |-> f.ty, topic |-> f.topic, rest |-> SubSeq(f.rest, 1, j - 2 - Len(f.topic))])

(* the malformed classes by name *)
Classes ==
    LET body == EncBody(f)
        n == Len(body)
    IN /\ f.k = "hello" => \A fl \in {4, 5, 128, 255} : Decode([body EXCEPT ![n] = fl]) = Err("helloFlag")
       /\ f.k = "snap" => \A fl \in {4, 7, 128, 255} : Decode([body EXCEPT ![3] = fl]) = Err("snapFlag")
       /\ f.k = "delta" => \A v \in {3, 4, 255} : Decode([body EXCEPT ![n] = v]) = Err("aliveByte")
       /\ (f.k = "snap" /\ Len(f.es) > 0) =>
            /\ \A v \in {0, 2} : Decode([body EXCEPT ![n] = v]) = Err("snapNotAlive")
            /\ \A v \in {3, 255} : Decode([body EXCEPT ![n] = v]) = Err("aliveByte")
            /\ Decode(body \o Seq1(EntryLen - 1)) = Err("snapSize")
       /\ f.k = "down" =>
            /\ \A c \in {0, 5, 255} : Decode([body EXCEPT ![2 + 32 + 8 + 4 + 1] = c]) = Err("probeCount")
            /\ \A j \in 1..Len(f.pr) : Decode([body EXCEPT ![2 + 45 + 5 * j] = 3]) = Err("probePath")
       /\ \A ty \in {1, 2, 3, 4, 12, 13} : Decode(<<ty, 1, 7>> \o body) = Err("topic")
       /\ f.k = "other" => (\A ty \in {1, 2, 3, 4, 12, 13} : Decode(<<ty, Len(f.topic)>> \o f.topic \o f.rest) # Ok(f))

Stream ==
    LET enc == Enc(f)
        n == Len(enc)
    IN /\ \A j \in {j \in 0..(n - 1) : n <= 64 \/ j <= 8 \/ j >= n - 6 \/ (j - 7) % EntryLen \in {0, 1, 50}} :
            Read(SubSeq(enc, 1, j)) = [err |-> "more"]
       /\ \A len \in {MaxBody + 1, MaxBody + 2, 65536 * 5, 65536 * 30000} :
            Read(BeBytes(U!Add(U!W(len \div 2), U!W(len - len \div 2)), 4)) = Err("tooLarge")
       /\ Read(BeBytes(U!W(MaxBody), 4)) = [err |-> "more"]

Buffers ==
    /\ f.k \in {"hello", "ack", "probe", "delta", "down"} => 4 + BodyLen(f) <= 160
    /\ (f.k = "snap" /\ Len(f.es) <= SnapChunk) => 4 + BodyLen(f) <= 4 + 3 + SnapChunk * EntryLen
    /\ EncodeCap(f, 4) = [err |-> "bufferSmall"]
    /\ (f.k = "other" /\ Len(f.topic) = 0 /\ Len(f.rest) <= FloorMax) => 4 + BodyLen(f) <= FloorMax + 8
(* Not a law: a snapshot cut at an entry boundary is a shorter snapshot. TLC finds the violation (HubCodec_snapcut.cfg),
   which is why Strict only restricts the other cuts of a snapshot. *)
SnapCutRefused == f.k = "snap" => \A b \in Cuts(EncBody(f)) : Decode(b).err # "ok"
=============================================================================
