------------------------------- MODULE Padding -------------------------------
(***************************************************************************)
(* The size functions of pinc-security message.rs: sealed_len, reply_len,  *)
(* min_initial_len and the constants FULL_INITIAL_MIN (1200),              *)
(* SHORT_INITIAL_MIN (464), MIN_DATAGRAM (1200), FRAGMENT_HEADER (50),     *)
(* WHOLE_REPLY_MAX (1388), reply_datagrams, MAX_ID_SIG_LEN,                *)
(* MAX_SEALED_LEN and MAX_MESSAGE_LEN, with the key and signature lengths  *)
(* of the four identity algorithms of pinc-crypto (tags 1 to 4: Ed25519,   *)
(* ECDSA P-256, ML-DSA-65, hybrid), the KEM ciphertext (1088), the AEAD    *)
(* tag (16), the credit record (6) and the longest connection id (20).     *)
(* The numbers are the real ones: nothing is scaled.                       *)
(*                                                                         *)
(* Checked, for every algorithm and both Initial forms: three times        *)
(* min_initial_len covers the Reply plus the framing (FRAGMENT_HEADER) and *)
(* the 48-byte overhead of every datagram reply_datagrams counts (one for  *)
(* a Reply of at most WHOLE_REPLY_MAX bytes, which a first flight sent     *)
(* whole carries, else the datagrams of MIN_DATAGRAM bytes less the        *)
(* framing); the padded Initial is at least the floor of its form and is,  *)
(* for each pair, the value of the table of the hand computation (1200,    *)
(* 1200, 2341, 2373 for the full form; 464, 464, 2341, 2373 for the short  *)
(* form); the short form of a 32-byte identity is 464 and 3 * 464 covers   *)
(* its Reply; MAX_MESSAGE_LEN = reply_len(hybrid) = 6529 bounds every      *)
(* Reply; sealed_len <= MAX_SEALED_LEN; a path that received               *)
(* min_initial_len bytes may send the Reply in datagrams of any size, one  *)
(* after another, under the can_send rule of amp.rs (simulated for chunk   *)
(* sizes 16, 100, 1200 and the whole Reply); the transport, which charges  *)
(* every datagram its size plus 48 bytes, sends the Reply as it cuts it    *)
(* (whole, or in MIN_DATAGRAM-byte datagrams) within the budget; and with  *)
(* connection ids of at most SPLIT_CID_MAX (5) bytes, the transport's      *)
(* default cut of a Reply into MIN_DATAGRAM-byte datagrams, short Replies  *)
(* included, fits as well, while 6-byte ids do not fit the short Initial   *)
(* of a 32-byte identity (the bound is tight).                             *)
(*                                                                         *)
(* TraceSecurity.tla checks the recorded values of the real public         *)
(* functions against these operators. Lean counterpart:                    *)
(* proofs/lean/Pinc/Padding.lean (budget_covers_reply,                     *)
(* budget_covers_split, reply_sendable, reply_sendable_charged,            *)
(* split_sendable_charged).                                                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

VARIABLE x

Overhead == 48
Factor == 3
FullMin == 1200
ShortMin == 464
MinDatagram == 1200
FragHeader == 1 + 1 + 2 * (1 + 20) + 2 + 2 + 2
WholeReplyMax == 1452 - 64
SplitCidMax == 5
KemCt == 1088
TagLen == 16
CreditLen == 6
MaxCid == 20

(* IdentityAlg tag -> public key length and signature length *)
Pk == [t \in 1..4 |-> CASE t = 1 -> 32 [] t = 2 -> 33 [] t = 3 -> 1952 [] t = 4 -> 32 + 1952]
Sig == [t \in 1..4 |-> CASE t = 1 -> 64 [] t = 2 -> 64 [] t = 3 -> 3309 [] t = 4 -> 64 + 3309]
MaxPk == 32 + 1952
MaxSig == 64 + 3309
MaxIdSig == 1 + 2 + MaxPk + 2 + MaxSig + CreditLen
MaxSealed == MaxIdSig + TagLen

SealedLen(a) == 1 + 2 + Pk[a] + 2 + Sig[a] + CreditLen + TagLen
ReplyLen(a) == 1 + (1 + MaxCid) + 1 + 32 + KemCt + 2 + SealedLen(a)
MaxMessage == ReplyLen(4)
CeilDiv(a, b) == IF a % b = 0 THEN a \div b ELSE a \div b + 1
Floor(f) == IF f = "full" THEN FullMin ELSE ShortMin
Datagrams(r) == IF r <= WholeReplyMax THEN 1 ELSE CeilDiv(r, MinDatagram - FragHeader)
Needed(a) == CeilDiv(ReplyLen(a) + Datagrams(ReplyLen(a)) * (Overhead + FragHeader), Factor)
MinInitial(f, a) == IF Needed(a) > Floor(f) THEN Needed(a) ELSE Floor(f)

(* The Reply with connection ids of c bytes instead of the 20 reply_len allows for, the framing of a datagram with
   such ids, and the datagrams of MIN_DATAGRAM bytes the transport cuts a Reply of r bytes into. *)
ReplyWith(a, c) == ReplyLen(a) - (MaxCid - c)
FramingWith(c) == 1 + 1 + 2 * (1 + c) + 2 + 2 + 2
SplitDatagrams(r, c) == CeilDiv(r, MinDatagram - FramingWith(c))
SplitFits(f, a, c) ==
    Factor * MinInitial(f, a) >= ReplyWith(a, c) + SplitDatagrams(ReplyWith(a, c), c) * (Overhead + FramingWith(c))

Forms == {"full", "short"}
Algs == 1..4

(* the values of the hand computation *)
Expected == [f \in Forms |-> [a \in Algs |->
    IF f = "full" THEN (CASE a = 1 -> 1200 [] a = 2 -> 1200 [] a = 3 -> 2341 [] a = 4 -> 2373)
    ELSE (CASE a = 1 -> 464 [] a = 2 -> 464 [] a = 3 -> 2341 [] a = 4 -> 2373)]]

(* send the Reply in chunks of c bytes (the last one shorter) under can_send, starting from a budget that received
   rx bytes: whether every send is allowed *)
RECURSIVE Sendable(_, _, _, _)
Sendable(rx, tx, left, c) ==
    IF left = 0 THEN TRUE
    ELSE LET n == IF left < c THEN left ELSE c
         IN /\ tx + n + Overhead <= Factor * rx
            /\ Sendable(rx, tx + n, left - n, c)

(* send `left` bytes of a message cut into fragments of at most q bytes, each in a datagram with k bytes of framing,
   as the transport does: each send allowed by can_send and charged its size plus the overhead (finish_datagram) *)
RECURSIVE SendCut(_, _, _, _, _)
SendCut(rx, tx, left, q, k) ==
    IF left = 0 THEN TRUE
    ELSE LET n == IF left < q THEN left ELSE q
         IN /\ tx + n + k + Overhead <= Factor * rx
            /\ SendCut(rx, tx + n + k + Overhead, left - n, q, k)

Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

BudgetCoversReply ==
    \A f \in Forms, a \in Algs : Factor * MinInitial(f, a) >= ReplyLen(a) + Datagrams(ReplyLen(a)) * (Overhead + FragHeader)
AtLeastFloor == \A f \in Forms, a \in Algs : MinInitial(f, a) >= Floor(f)
TableMatches == \A f \in Forms, a \in Algs : MinInitial(f, a) = Expected[f][a]
Short32 == MinInitial("short", 1) = 464 /\ ReplyLen(1) <= 3 * 464 /\ ReplyLen(1) + Datagrams(ReplyLen(1)) * (Overhead + FragHeader) <= 3 * 464
Constants == MaxIdSig = 5368 /\ MaxSealed = 5384 /\ MaxMessage = 6529 /\ ReplyLen(1) = 1268
ReplyBounded == \A a \in Algs : ReplyLen(a) <= MaxMessage /\ SealedLen(a) <= MaxSealed /\ Pk[a] <= MaxPk /\ Sig[a] <= MaxSig
MaxIsHybrid == MaxSealed = SealedLen(4)
ReplySendable ==
    \A f \in Forms, a \in Algs : \A c \in {16, 100, 1200, ReplyLen(a)} :
        Sendable(MinInitial(f, a), 0, ReplyLen(a), c)
BudgetCoversSplit == \A f \in Forms, a \in Algs, c \in 0..SplitCidMax : SplitFits(f, a, c)
SplitCidTight == ~SplitFits("short", 1, SplitCidMax + 1)
ReplySendableCharged ==
    \A f \in Forms, a \in Algs :
        /\ ReplyLen(a) <= WholeReplyMax =>
               SendCut(MinInitial(f, a), 0, ReplyLen(a), ReplyLen(a), FragHeader)
        /\ SendCut(MinInitial(f, a), 0, ReplyLen(a), MinDatagram - FragHeader, FragHeader) \/ ReplyLen(a) <= WholeReplyMax
        /\ \A c \in 0..SplitCidMax :
               SendCut(MinInitial(f, a), 0, ReplyWith(a, c), MinDatagram - FramingWith(c), FramingWith(c))
=============================================================================
