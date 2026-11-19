------------------------------ MODULE BroadcastWire ------------------------------
(***************************************************************************)
(* The head of a pinc-broadcast message, wire.rs `Head::parse` and         *)
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
(* Lean counterpart: proofs/lean/Pinc/BroadcastWire.lean.                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Sym, MaxLen, MaxTopic

\* widths: mid, origin, tag, flag, blen, ts wall, ts counter
MidW == 1
OrgW == 1
PkW(tag) == IF tag = 0 THEN 0 ELSE 1
SigW(tag) == IF tag = 0 THEN 1 ELSE 2
Base == 2          \* the digits of blen and ts are 0 or 1 here (a big-endian number of fixed width)

Take(b, from, n) == IF from + n - 1 <= Len(b) THEN [i \in 1..n |-> b[from + i - 1]] ELSE <<>>
Fits(b, from, n) == from + n - 1 <= Len(b)

\* wire.rs Head::parse: the head and the body, or the marker of a refusal
Parse(b) ==
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
                               ELSE IF Len(body) # blen THEN [ok |-> FALSE]
                               ELSE [ok |-> TRUE, mid |-> Take(b, 1, MidW), org |-> Take(b, 1 + MidW, OrgW), tag |-> tag,
                                     pk |-> Take(b, p2, PkW(tag)), sig |-> Take(b, p3, SigW(tag)), flag |-> flag,
                                     ts |-> ts, body |-> body]

\* wire.rs Head::write followed by the body
Write(h) == h.mid \o h.org \o <<h.tag>> \o h.pk \o h.sig \o <<h.flag, Len(h.body)>> \o h.ts \o h.body

AllBytes == UNION {[1..n -> Sym] : n \in 0..MaxLen}
\* the quick profile (proofs/tla/quick): every string with the message id byte, which is only copied, held at 0 past
\* the first byte
AllBytesQuick == UNION {[1..n -> Sym] : n \in 0..1} \cup {<<0>> \o s : s \in UNION {[1..n -> Sym] : n \in 1..(MaxLen - 1)}}
HeadsOf(t) == {[mid |-> m, org |-> o, tag |-> t, pk |-> k, sig |-> sg, flag |-> f, ts |-> ts, body |-> bd] :
                 m \in [1..MidW -> Sym], o \in [1..OrgW -> Sym], k \in [1..PkW(t) -> Sym],
                 sg \in [1..SigW(t) -> Sym], f \in {0, 1}, ts \in [1..2 -> Sym], bd \in {<<>>, <<0>>, <<1>>}}
Heads == HeadsOf(0) \union HeadsOf(1)

\* build(): len | type | topic_len | topic | rest (len counts what follows it), and its parse
Frame(ty, topic, rest) == <<Len(topic) + 2 + Len(rest), ty, Len(topic)>> \o topic \o rest
ParseFrame(f) == IF Len(f) < 3 \/ f[1] # Len(f) - 1 \/ f[3] > Len(f) - 3 THEN [ok |-> FALSE]
                 ELSE [ok |-> TRUE, ty |-> f[2], topic |-> SubSeq(f, 4, 3 + f[3]), rest |-> SubSeq(f, 4 + f[3], Len(f))]

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
ASSUME RoundTripHead
ASSUME FrameRoundTrip
=============================================================================
