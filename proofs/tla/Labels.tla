------------------------------- MODULE Labels -------------------------------
(***************************************************************************)
(* The domain-separation labels of pinc-security labels.rs, as the literal *)
(* strings of the code (TLC compares strings, and reads them as sequences  *)
(* of characters), and the purposes of schedule.rs that use them.          *)
(*                                                                         *)
(* Checked, exhaustively: there are exactly 23 labels (the length of       *)
(* labels::ALL); they are pairwise distinct; every one starts with the     *)
(* prefix "PINC 2026 v1 " and is longer than it; none is a label of        *)
(* pinc-crypto (NODE_ID, HYBRID_SIGNATURE); every character is ASCII, so  *)
(* the UTF-8 bytes of a label are its character codes; the two signature   *)
(* labels have the same length (the const assertion of schedule.rs); the   *)
(* removed labels (key update, token) are not in the list and the two that *)
(* replaced them (key roll, connection id secret) are; and the label of    *)
(* every derivation purpose is a distinct member of the list, so two       *)
(* derivations of different purposes never share a (label, context) pair.  *)
(*                                                                         *)
(* TraceLabels.tla checks that the strings below are the constants the     *)
(* compiled code holds. Lean counterpart: proofs/lean/Pinc/Labels.lean and *)
(* Schedule.lean (labels_nodup, label_injective, distinct_purposes).       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

VARIABLE x

Prefix == "PINC 2026 v1 "

(* labels::ALL, in the order of the source *)
AllLabels == <<
    "PINC 2026 v1 handshake",
    "PINC 2026 v1 resume handshake",
    "PINC 2026 v1 chain",
    "PINC 2026 v1 prekey hash",
    "PINC 2026 v1 responder",
    "PINC 2026 v1 initiator",
    "PINC 2026 v1 handshake secret initiator",
    "PINC 2026 v1 handshake secret responder",
    "PINC 2026 v1 application secret initiator",
    "PINC 2026 v1 application secret responder",
    "PINC 2026 v1 resumption secret",
    "PINC 2026 v1 ticket",
    "PINC 2026 v1 binder",
    "PINC 2026 v1 early data",
    "PINC 2026 v1 resume confirm",
    "PINC 2026 v1 sub session",
    "PINC 2026 v1 sub session context",
    "PINC 2026 v1 packet key",
    "PINC 2026 v1 packet iv",
    "PINC 2026 v1 header key",
    "PINC 2026 v1 key roll",
    "PINC 2026 v1 key roll id",
    "PINC 2026 v1 connection id secret">>

(* pinc-crypto kdf.rs labels *)
CryptoLabels == {"PINC 2026 v1 node id", "PINC 2026 v1 hybrid signature"}

(* the labels removed from the code *)
Removed == {"PINC 2026 v1 key update", "PINC 2026 v1 token"}

SigResponder == AllLabels[5]
SigInitiator == AllLabels[6]

(* the derivation purposes of schedule.rs (Purpose in Schedule.lean) and the label each passes to expand *)
PurposeLabel == [
    hsInitiator |-> "PINC 2026 v1 handshake secret initiator",
    hsResponder |-> "PINC 2026 v1 handshake secret responder",
    appInitiator |-> "PINC 2026 v1 application secret initiator",
    appResponder |-> "PINC 2026 v1 application secret responder",
    resumption |-> "PINC 2026 v1 resumption secret",
    confirm |-> "PINC 2026 v1 resume confirm",
    ticket |-> "PINC 2026 v1 ticket",
    binder |-> "PINC 2026 v1 binder",
    early |-> "PINC 2026 v1 early data",
    subSession |-> "PINC 2026 v1 sub session",
    packetKey |-> "PINC 2026 v1 packet key",
    packetIv |-> "PINC 2026 v1 packet iv",
    headerKey |-> "PINC 2026 v1 header key",
    keyRoll |-> "PINC 2026 v1 key roll",
    keyRollId |-> "PINC 2026 v1 key roll id",
    cidSecret |-> "PINC 2026 v1 connection id secret"]

Chars == {"A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V",
          "W", "X", "Y", "Z", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r",
          "s", "t", "u", "v", "w", "x", "y", "z", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", " "}

Idx == 1..Len(AllLabels)
Starts(s, p) == Len(s) > Len(p) /\ SubSeq(s, 1, Len(p)) = p

Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

CountOK == Len(AllLabels) = 23
Distinct == \A i, j \in Idx : AllLabels[i] = AllLabels[j] => i = j
HasPrefix == \A i \in Idx : Starts(AllLabels[i], Prefix)
DisjointCrypto == \A i \in Idx : AllLabels[i] \notin CryptoLabels
AsciiOnly == \A i \in Idx : \A k \in 1..Len(AllLabels[i]) : SubSeq(AllLabels[i], k, k) \in Chars
SigLengthsEqual == Len(SigResponder) = Len(SigInitiator)
RemovedGone == \A r \in Removed : \A i \in Idx : AllLabels[i] # r
KeyRollAndCidIn == "PINC 2026 v1 key roll" \in {AllLabels[i] : i \in Idx} /\ "PINC 2026 v1 connection id secret" \in {AllLabels[i] : i \in Idx}
PurposesDistinct == \A p, q \in DOMAIN PurposeLabel : PurposeLabel[p] = PurposeLabel[q] => p = q
PurposesKnown == \A p \in DOMAIN PurposeLabel : \E i \in Idx : AllLabels[i] = PurposeLabel[p]
=============================================================================
