------------------------------- MODULE Padding -------------------------------
(***************************************************************************)
(* The size functions of vinc-security message.rs: sealed_len, reply_len,  *)
(* min_initial_len and the constants FULL_INITIAL_MIN (1200),              *)
(* SHORT_INITIAL_MIN (464), MIN_DATAGRAM (1200), MAX_ID_SIG_LEN,           *)
(* MAX_SEALED_LEN and MAX_MESSAGE_LEN, with the key and signature lengths  *)
(* of the four identity algorithms of vinc-crypto (tags 1 to 4: Ed25519,   *)
(* ECDSA P-256, ML-DSA-65, hybrid), the KEM ciphertext (1088), the AEAD    *)
(* tag (16), the credit record (6) and the longest connection id (20).     *)
(* The numbers are the real ones: nothing is scaled.                       *)
(*                                                                         *)
(* Checked, for every algorithm and both Initial forms: 3 * min_initial_len*)
(* covers the Reply plus the overhead of each datagram it needs; the       *)
(* padded Initial is at least the floor of its form and is, for each pair, *)
(* the value of the table of the hand computation (1200, 1200, 2241, 2273  *)
(* for the full form; 464, 464, 2241, 2273 for the short form); the short  *)
(* form of a 32-byte identity is 464 and 3 * 464 covers its Reply;         *)
(* MAX_MESSAGE_LEN = reply_len(hybrid) = 6529 bounds every Reply;          *)
(* sealed_len <= MAX_SEALED_LEN; and a path that received min_initial_len  *)
(* bytes may send the Reply in datagrams of any size, one after another,   *)
(* under the can_send rule of amp.rs (simulated for chunk sizes 16, 100, *)
(* 1200 and the whole Reply).                                              *)
(*                                                                         *)
(* TraceSecurity.tla checks the recorded values of the real public         *)
(* functions against these operators. Lean counterpart:                    *)
(* proofs/lean/Vinc/Padding.lean (budget_covers_reply, reply_sendable).    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

VARIABLE x

Overhead == 48
Factor == 3
FullMin == 1200
ShortMin == 464
MinDatagram == 1200
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
Needed(a) == CeilDiv(ReplyLen(a) + CeilDiv(ReplyLen(a), MinDatagram) * Overhead, Factor)
MinInitial(f, a) == IF Needed(a) > Floor(f) THEN Needed(a) ELSE Floor(f)

Forms == {"full", "short"}
Algs == 1..4

(* the values of the hand computation *)
Expected == [f \in Forms |-> [a \in Algs |->
    IF f = "full" THEN (CASE a = 1 -> 1200 [] a = 2 -> 1200 [] a = 3 -> 2241 [] a = 4 -> 2273)
    ELSE (CASE a = 1 -> 464 [] a = 2 -> 464 [] a = 3 -> 2241 [] a = 4 -> 2273)]]

(* send the Reply in chunks of c bytes (the last one shorter) under can_send, starting from a budget that received
   rx bytes: whether every send is allowed *)
RECURSIVE Sendable(_, _, _, _)
Sendable(rx, tx, left, c) ==
    IF left = 0 THEN TRUE
    ELSE LET n == IF left < c THEN left ELSE c
         IN /\ tx + n + Overhead <= Factor * rx
            /\ Sendable(rx, tx + n, left - n, c)

Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

BudgetCoversReply ==
    \A f \in Forms, a \in Algs : Factor * MinInitial(f, a) >= ReplyLen(a) + CeilDiv(ReplyLen(a), MinDatagram) * Overhead
AtLeastFloor == \A f \in Forms, a \in Algs : MinInitial(f, a) >= Floor(f)
TableMatches == \A f \in Forms, a \in Algs : MinInitial(f, a) = Expected[f][a]
Short32 == MinInitial("short", 1) = 464 /\ ReplyLen(1) <= 3 * 464 /\ ReplyLen(1) + CeilDiv(ReplyLen(1), MinDatagram) * Overhead <= 3 * 464
Constants == MaxIdSig = 5368 /\ MaxSealed = 5384 /\ MaxMessage = 6529 /\ ReplyLen(1) = 1268
ReplyBounded == \A a \in Algs : ReplyLen(a) <= MaxMessage /\ SealedLen(a) <= MaxSealed /\ Pk[a] <= MaxPk /\ Sig[a] <= MaxSig
MaxIsHybrid == MaxSealed = SealedLen(4)
ReplySendable ==
    \A f \in Forms, a \in Algs : \A c \in {16, 100, 1200, ReplyLen(a)} :
        Sendable(MinInitial(f, a), 0, ReplyLen(a), c)
=============================================================================
