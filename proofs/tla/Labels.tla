------------------------------- MODULE Labels -------------------------------
(***************************************************************************)
(* The domain-separation labels of vinc-security labels.rs, as the literal *)
(* strings of the code (TLC compares strings, and reads them as sequences  *)
(* of characters), and the purposes of schedule.rs that use them.          *)
(*                                                                         *)
(* Checked, exhaustively: there are exactly 22 labels (the length of       *)
(* labels::ALL); they are pairwise distinct; every one starts with the     *)
(* prefix "VINC 2026 v1 " and is longer than it; none is a label of        *)
(* vinc-crypto (NODE_ID, HYBRID_SIGNATURE); every character is ASCII, so  *)
(* the UTF-8 bytes of a label are its character codes; the two signature   *)
(* labels have the same length (the const assertion of schedule.rs); the   *)
(* removed labels (key update, token) are not in the list and the two that *)
(* replaced them (key roll, connection id secret) are; and the label of    *)
(* every derivation purpose is a distinct member of the list, so two       *)
(* derivations of different purposes never share a (label, context) pair.  *)
(*                                                                         *)
(* TraceLabels.tla checks that the strings below are the constants the     *)
(* compiled code holds. Lean counterpart: proofs/lean/Vinc/Labels.lean and *)
(* Schedule.lean (labels_nodup, label_injective, distinct_purposes).       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

VARIABLE x

Prefix == "VINC 2026 v1 "

(* labels::ALL, in the order of the source *)
AllLabels == <<
    "VINC 2026 v1 handshake",
    "VINC 2026 v1 resume handshake",
    "VINC 2026 v1 chain",
    "VINC 2026 v1 prekey hash",
    "VINC 2026 v1 responder",
    "VINC 2026 v1 initiator",
    "VINC 2026 v1 handshake secret initiator",
    "VINC 2026 v1 handshake secret responder",
    "VINC 2026 v1 application secret initiator",
    "VINC 2026 v1 application secret responder",
    "VINC 2026 v1 resumption secret",
    "VINC 2026 v1 ticket",
    "VINC 2026 v1 binder",
    "VINC 2026 v1 early data",
    "VINC 2026 v1 resume confirm",
    "VINC 2026 v1 sub session",
    "VINC 2026 v1 sub session context",
    "VINC 2026 v1 packet key",
    "VINC 2026 v1 packet iv",
    "VINC 2026 v1 header key",
    "VINC 2026 v1 key roll",
    "VINC 2026 v1 connection id secret">>

(* vinc-crypto kdf.rs labels *)
CryptoLabels == {"VINC 2026 v1 node id", "VINC 2026 v1 hybrid signature"}

(* the labels removed from the code *)
Removed == {"VINC 2026 v1 key update", "VINC 2026 v1 token"}

SigResponder == AllLabels[5]
SigInitiator == AllLabels[6]

(* the derivation purposes of schedule.rs (Purpose in Schedule.lean) and the label each passes to expand *)
PurposeLabel == [
    hsInitiator |-> "VINC 2026 v1 handshake secret initiator",
    hsResponder |-> "VINC 2026 v1 handshake secret responder",
    appInitiator |-> "VINC 2026 v1 application secret initiator",
    appResponder |-> "VINC 2026 v1 application secret responder",
    resumption |-> "VINC 2026 v1 resumption secret",
    confirm |-> "VINC 2026 v1 resume confirm",
    ticket |-> "VINC 2026 v1 ticket",
    binder |-> "VINC 2026 v1 binder",
    early |-> "VINC 2026 v1 early data",
    subSession |-> "VINC 2026 v1 sub session",
    packetKey |-> "VINC 2026 v1 packet key",
    packetIv |-> "VINC 2026 v1 packet iv",
    headerKey |-> "VINC 2026 v1 header key",
    keyRoll |-> "VINC 2026 v1 key roll",
    cidSecret |-> "VINC 2026 v1 connection id secret"]

Chars == {"A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V",
          "W", "X", "Y", "Z", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r",
          "s", "t", "u", "v", "w", "x", "y", "z", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", " "}

Idx == 1..Len(AllLabels)
Starts(s, p) == Len(s) > Len(p) /\ SubSeq(s, 1, Len(p)) = p

Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

CountOK == Len(AllLabels) = 22
Distinct == \A i, j \in Idx : AllLabels[i] = AllLabels[j] => i = j
HasPrefix == \A i \in Idx : Starts(AllLabels[i], Prefix)
DisjointCrypto == \A i \in Idx : AllLabels[i] \notin CryptoLabels
AsciiOnly == \A i \in Idx : \A k \in 1..Len(AllLabels[i]) : SubSeq(AllLabels[i], k, k) \in Chars
SigLengthsEqual == Len(SigResponder) = Len(SigInitiator)
RemovedGone == \A r \in Removed : \A i \in Idx : AllLabels[i] # r
KeyRollAndCidIn == "VINC 2026 v1 key roll" \in {AllLabels[i] : i \in Idx} /\ "VINC 2026 v1 connection id secret" \in {AllLabels[i] : i \in Idx}
PurposesDistinct == \A p, q \in DOMAIN PurposeLabel : PurposeLabel[p] = PurposeLabel[q] => p = q
PurposesKnown == \A p \in DOMAIN PurposeLabel : \E i \in Idx : AllLabels[i] = PurposeLabel[p]
=============================================================================
