------------------------------ MODULE BroadcastWire ------------------------------
(***************************************************************************)
(* The head of a vinc-broadcast message, wire.rs `Head::parse` and         *)
(* `Head::write`, and the frame of `build`, over small byte alphabets and  *)
(* field widths, exhaustively: every byte string up to MaxLen symbols is   *)
(* parsed. The widths are parameters (the code uses 8, 32, 1, 0/key/sig    *)
(* lengths by algorithm, 1, 4, 12); the structure is the code's: mid,      *)
(* origin, an algorithm tag, the public key (absent for tag 0), the        *)
(* signature, the body flag (0 or 1), blen, the timestamp, then exactly    *)
(* blen body bytes (a body of another length is refused). Integers are     *)
(* big-endian digit lists of fixed width.                                  *)
(*                                                                         *)
(* Checked: RoundTripHead and FrameRoundTrip hold as ASSUMEs for every head and frame; for every string: CanonicalHead (if it parses, writing the     *)
(* head back gives the same bytes: no two byte strings are one head and    *)
(* body), RoundTripHead (every head with a matching body parses back to    *)
(* itself), Rejects (a string too short, with an unknown tag, with a flag  *)
(* other than 0 or 1 or with a body of the wrong length is refused);       *)
(* FrameRoundTrip and FrameCanonical for `build`: len | type | topic_len | *)
(* topic | rest, with the topic within its limit.                          *)
(*                                                                         *)
(* The signed envelope, envelope.rs `EnvelopeRef::{encode_into, decode}`:  *)
(* version | kind | topic_len | topic | head | body, the head and body     *)
(* being the codec above. EnvRoundTrip (an ASSUME) and EnvCanonical: what  *)
(* decodes is exactly what `encode_into` writes, so no byte string has two *)
(* readings and none carries a trailing byte; EnvRejects: a version other  *)
(* than 1, a kind other than 1 (a dispatch whose only accepted case is     *)
(* kind 1), a topic over the bound, a string cut by one byte and one       *)
(* lengthened by one byte are refused. EnvStrict is the check that the     *)
(* body is exactly blen bytes: the witness config sets it FALSE and TLC    *)
(* finds a byte string with a trailing byte that decodes.                  *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/BroadcastWire.lean.                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Sym, MaxLen, MaxTopic, EnvMaxTopic, EnvStrict

\* widths: mid, origin, tag, flag, blen, ts wall, ts counter
MidW == 1
OrgW == 1
PkW(tag) == IF tag = 0 THEN 0 ELSE 1
SigW(tag) == IF tag = 0 THEN 1 ELSE 2
Base == 2          \* the digits of blen and ts are 0 or 1 here (a big-endian number of fixed width)

Take(b, from, n) == IF from + n - 1 <= Len(b) THEN [i \in 1..n |-> b[from + i - 1]] ELSE <<>>
Fits(b, from, n) == from + n - 1 <= Len(b)

\* wire.rs Head::parse_prefix and the body check: with `strict` the body must be exactly blen bytes (Head::parse);
\* without it a longer tail is read as a body of blen bytes (the check dropped, for the witness)
ParseX(b, strict) ==
    LET p1 == 1 + MidW + OrgW
    IN IF ~Fits(b, 1, MidW + OrgW + 1) THEN [ok |-> FALSE]
       ELSE LET tag == b[p1]
            IN IF tag \notin {0, 1} THEN [ok |-> FALSE]
               ELSE LET p2 == p1 + 1
                        p3 == p2 + PkW(tag)
                        p4 == p3 + SigW(tag)
                    IN IF ~Fits(b, p2, PkW(tag) + SigW(tag) + 1 + 1 + 2) THEN [ok |-> FALSE]
                       ELSE LET flag == b[p4]
                                blen == b[p4 + 1]
                                ts == Take(b, p4 + 2, 2)
                                body == SubSeq(b, p4 + 4, Len(b))
                            IN IF flag \notin {0, 1} THEN [ok |-> FALSE]
                               ELSE IF (IF strict THEN Len(body) # blen ELSE Len(body) < blen) THEN [ok |-> FALSE]
                               ELSE [ok |-> TRUE, mid |-> Take(b, 1, MidW), org |-> Take(b, 1 + MidW, OrgW), tag |-> tag,
                                     pk |-> Take(b, p2, PkW(tag)), sig |-> Take(b, p3, SigW(tag)), flag |-> flag,
                                     ts |-> ts, body |-> SubSeq(body, 1, blen)]

Parse(b) == ParseX(b, TRUE)

\* wire.rs Head::write followed by the body
Write(h) == h.mid \o h.org \o <<h.tag>> \o h.pk \o h.sig \o <<h.flag, Len(h.body)>> \o h.ts \o h.body

AllBytes == UNION {[1..n -> Sym] : n \in 0..MaxLen}
HeadsOf(t) == {[mid |-> m, org |-> o, tag |-> t, pk |-> k, sig |-> sg, flag |-> f, ts |-> ts, body |-> bd] :
                 m \in [1..MidW -> Sym], o \in [1..OrgW -> Sym], k \in [1..PkW(t) -> Sym],
                 sg \in [1..SigW(t) -> Sym], f \in {0, 1}, ts \in [1..2 -> Sym], bd \in {<<>>, <<0>>, <<1>>}}
Heads == HeadsOf(0) \union HeadsOf(1)

\* build(): len | type | topic_len | topic | rest (len counts what follows it), and its parse
Frame(ty, topic, rest) == <<Len(topic) + 2 + Len(rest), ty, Len(topic)>> \o topic \o rest
ParseFrame(f) == IF Len(f) < 3 \/ f[1] # Len(f) - 1 \/ f[3] > Len(f) - 3 THEN [ok |-> FALSE]
                 ELSE [ok |-> TRUE, ty |-> f[2], topic |-> SubSeq(f, 4, 3 + f[3]), rest |-> SubSeq(f, 4 + f[3], Len(f))]

\* envelope.rs: version 1 | kind | topic_len | topic | head | body. The kind is a dispatch: kind 1 is the only case.
EnvEnc(topic, h) == <<1, 1, Len(topic)>> \o topic \o Write(h)
EnvDec(e) ==
    IF Len(e) < 3 \/ e[1] # 1 \/ e[2] # 1 \/ e[3] > EnvMaxTopic \/ Len(e) < 3 + e[3] THEN [ok |-> FALSE]
    ELSE LET p == ParseX(SubSeq(e, 4 + e[3], Len(e)), EnvStrict)
         IN IF ~p.ok THEN [ok |-> FALSE] ELSE [ok |-> TRUE, topic |-> SubSeq(e, 4, 3 + e[3]), head |-> p]

VARIABLE b
Init == b \in AllBytes
Next == UNCHANGED b
Spec == Init /\ [][Next]_b

CanonicalHead == LET p == Parse(b) IN p.ok => Write(p) = b

RoundTripHead == \A h \in Heads :
    LET p == Parse(Write(h))
    IN /\ p.ok /\ p.mid = h.mid /\ p.org = h.org /\ p.tag = h.tag /\ p.pk = h.pk /\ p.sig = h.sig
       /\ p.flag = h.flag /\ p.ts = h.ts /\ p.body = h.body

HeadLen(tag) == MidW + OrgW + 1 + PkW(tag) + SigW(tag) + 1 + 1 + 2
Rejects == /\ Len(b) < MidW + OrgW + 1 => ~Parse(b).ok
           /\ (Len(b) > MidW + OrgW /\ b[MidW + OrgW + 1] \notin {0, 1}) => ~Parse(b).ok
           /\ (Len(b) > MidW + OrgW /\ b[MidW + OrgW + 1] \in {0, 1} /\ Len(b) < HeadLen(b[MidW + OrgW + 1])) => ~Parse(b).ok
           /\ (Parse(b).ok => Len(b) >= HeadLen(b[MidW + OrgW + 1]))
           \* the body is exactly blen bytes: one more or one fewer is refused
           /\ (Parse(b).ok /\ Len(b) < MaxLen) => ~Parse(b \o <<0>>).ok
           /\ (Parse(b).ok /\ Len(b) > 0 /\ Parse(b).body # <<>>) => ~Parse(SubSeq(b, 1, Len(b) - 1)).ok

FrameRoundTrip == \A ty \in Sym, tp \in UNION {[1..n -> Sym] : n \in 0..MaxTopic}, r \in UNION {[1..n -> Sym] : n \in 0..2} :
    LET p == ParseFrame(Frame(ty, tp, r)) IN p.ok /\ p.ty = ty /\ p.topic = tp /\ p.rest = r
FrameCanonical == LET p == ParseFrame(b) IN p.ok => Frame(p.ty, p.topic, p.rest) = b

EnvCanonical == LET d == EnvDec(b) IN d.ok => EnvEnc(d.topic, d.head) = b
EnvRejects == /\ (Len(b) > 0 /\ b[1] # 1) => ~EnvDec(b).ok
              /\ (Len(b) > 1 /\ b[2] # 1) => ~EnvDec(b).ok
              /\ (Len(b) > 2 /\ b[3] > EnvMaxTopic) => ~EnvDec(b).ok
              \* a string cut by one byte, or lengthened by one, is refused
              /\ (EnvDec(b).ok /\ Len(b) > 0) => ~EnvDec(SubSeq(b, 1, Len(b) - 1)).ok
              /\ (EnvDec(b).ok /\ Len(b) < MaxLen) => ~EnvDec(b \o <<0>>).ok
EnvRoundTrip == \A tp \in UNION {[1..n -> Sym] : n \in 0..EnvMaxTopic}, h \in Heads :
    LET d == EnvDec(EnvEnc(tp, h))
    IN /\ d.ok /\ d.topic = tp /\ d.head.mid = h.mid /\ d.head.org = h.org /\ d.head.tag = h.tag /\ d.head.pk = h.pk
       /\ d.head.sig = h.sig /\ d.head.flag = h.flag /\ d.head.ts = h.ts /\ d.head.body = h.body
ASSUME RoundTripHead
ASSUME EnvRoundTrip
ASSUME FrameRoundTrip
=============================================================================
