---------------------------- MODULE CryptoIdentity ----------------------------
(***************************************************************************)
(* The identities of vinc-crypto (identity.rs): algorithm tags and         *)
(* lengths, node ids, the decision tables of verify, verify_node and       *)
(* verify_ml_dsa_65, and the errors of the key pair operations.            *)
(*                                                                         *)
(* A byte string whose content does not matter is a record [len, head,    *)
(* id]: its length, its first byte (the one the P-256 form check reads)    *)
(* and an atom for the rest. The signature primitives are abstract: the    *)
(* flags record what they answer (key parses, signature parses, s is low,  *)
(* the equation holds), and the code's decision is a function of the flags *)
(* and the lengths. The node id of a non-Ed25519 key is the term of its    *)
(* derive_key call (a perfect primitive).                                  *)
(*                                                                         *)
(* Checked, over every combination of algorithm, length (right, one off,   *)
(* zero), first byte (2, 3, 4, 5, 0) and flags:                            *)
(*   TagsOK            from_tag accepts exactly 1 to 4 and inverts tag;    *)
(*                     lengths fit the maxima and the hybrid is the sum   *)
(*   IdLengthError     from_public refuses a wrong length with            *)
(*                     InvalidLength and nothing else                      *)
(*   IdInjective       two (algorithm, key) pairs never share an id        *)
(*   IdEncodingInjective  nor an id encoding (the tag is part of it)       *)
(*   MatchesIff        matches is from_public equal to the id              *)
(*   LengthFirst, EdOkIff, P256OkIff, MlOkIff, HybridOkIff  accepted iff   *)
(*   P256OtherForm, P256HighS, EdErrorFirst, CtxTooLong  the exact errors  *)
(*   NodeIdMismatchFirst, VerifyNodeOk  verify_node                        *)
(*   SeedBoundary, LexIsNumeric  the P-256 seed range                      *)
(*   WriteRule, NodeIdNoFallback  the output buffer rules                  *)
(* TraceCrypto.tla checks the recorded calls against these operators.      *)
(* Lean counterpart: proofs/lean/Vinc/CryptoIdentity.lean.                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

VARIABLE x

PkLen == <<32, 33, 1952, 1984>>
SigLen == <<64, 64, 3309, 3373>>
SeedLen == <<32, 32, 32, 64>>
MaxPk == 1984
MaxSig == 3373
Algs == 1..4

FromTag(t) == IF t \in 1..4 THEN [ok |-> TRUE, alg |-> t] ELSE [ok |-> FALSE]

Key(len, head, id) == [len |-> len, head |-> head, id |-> id]

(* NodeId::from_public: the id is the key for Ed25519 and the term of the derive_key call otherwise *)
FromPublic(alg, pk) ==
    IF pk.len # PkLen[alg] THEN [ok |-> FALSE, err |-> "InvalidLength"]
    ELSE [ok |-> TRUE, id |-> [alg |-> alg, bytes |-> IF alg = 1 THEN pk ELSE <<"derive", "node id", alg, pk>>]]

EncodeId(id) == <<id.alg, id.bytes>>

Matches(id, alg, pk) == LET r == FromPublic(alg, pk) IN r.ok /\ r.id.alg = id.alg /\ r.id.bytes = id.bytes

F(l) == [pkOk |-> l[1], sigOk |-> l[2], lowS |-> l[3], ok |-> l[4]]

EdV(pk, sig, f) ==
    IF pk.len # 32 \/ sig.len # 64 THEN "InvalidLength"
    ELSE IF ~f.pkOk THEN "InvalidPublicKey"
    ELSE IF ~f.ok THEN "InvalidSignature"
    ELSE "ok"

PV(pk, sig, f) ==
    IF pk.len # 33 THEN "InvalidLength"
    ELSE IF pk.head \notin {2, 3} THEN "InvalidPublicKey"
    ELSE IF ~f.pkOk THEN "InvalidPublicKey"
    ELSE IF ~f.sigOk THEN "InvalidSignature"
    ELSE IF ~f.lowS THEN "HighS"
    ELSE IF ~f.ok THEN "InvalidSignature"
    ELSE "ok"

MV(pk, ctxLen, sig, f) ==
    IF ctxLen > 255 \/ sig.len # 3309 THEN "InvalidLength"
    ELSE IF pk.len # 1952 THEN "InvalidLength"
    ELSE IF ~f.sigOk THEN "InvalidSignature"
    ELSE IF ~f.ok THEN "InvalidSignature"
    ELSE "ok"

AndR(a, b) == IF a # "ok" THEN a ELSE b

(* the halves of a hybrid key and signature (lengths are right when this is evaluated) *)
EdHalf(k) == Key(32, k.head, <<"ed", k.id>>)
MlHalf(k) == Key(1952, 0, <<"ml", k.id>>)
EdSigHalf(s) == [len |-> 64]
MlSigHalf(s) == [len |-> 3309]

Verify(alg, pk, sig, fe, fm) ==
    IF pk.len # PkLen[alg] \/ sig.len # SigLen[alg] THEN "InvalidLength"
    ELSE CASE alg = 1 -> EdV(pk, sig, fe)
           [] alg = 2 -> PV(pk, sig, fe)
           [] alg = 3 -> MV(pk, 0, sig, fm)
           [] alg = 4 -> AndR(EdV(EdHalf(pk), EdSigHalf(sig), fe), MV(MlHalf(pk), 0, MlSigHalf(sig), fm))

VerifyNode(id, pk, sig, fe, fm) ==
    IF ~Matches(id, id.alg, pk) THEN "NodeIdMismatch" ELSE Verify(id.alg, pk, sig, fe, fm)

(* the P-256 scalar range: 16 big-endian limbs of 16 bits *)
NLimbs == <<65535, 65535, 0, 0, 65535, 65535, 65535, 65535, 48358, 64173, 42775, 40580, 62393, 51906, 64611, 9553>>
RECURSIVE LexLess(_, _)
LexLess(a, b) == IF Len(a) = 0 THEN FALSE ELSE IF a[1] # b[1] THEN a[1] < b[1] ELSE LexLess(Tail(a), Tail(b))
IsZero(a) == \A i \in 1..Len(a) : a[i] = 0
SeedOk(s) == ~IsZero(s) /\ LexLess(s, NLimbs)
FromSeed(alg, seedLen, seed) ==
    IF seedLen # SeedLen[alg] THEN "InvalidLength"
    ELSE IF alg = 2 /\ ~SeedOk(seed) THEN "InvalidSecretKey"
    ELSE "ok"

WriteOut(need, out) == IF out < need THEN "InvalidLength" ELSE "ok"

Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

(* ---- the domains ---- *)
Heads == {0, 2, 3, 4, 5}
KeysOf(a) == {Key(l, h, i) : l \in {0, PkLen[a] - 1, PkLen[a], PkLen[a] + 1}, h \in Heads, i \in 1..2}
SigsOf(a) == {[len |-> l] : l \in {0, SigLen[a] - 1, SigLen[a], SigLen[a] + 1}}
Flags == {F(<<a, b, c, d>>) : a, b, c, d \in BOOLEAN}

TagsOK ==
    /\ \A t \in 0..255 : FromTag(t).ok = (t \in 1..4)
    /\ \A a \in Algs : FromTag(a).ok /\ FromTag(a).alg = a
    /\ \A a \in Algs : PkLen[a] <= MaxPk /\ SigLen[a] <= MaxSig
    /\ PkLen[4] = PkLen[1] + PkLen[3] /\ SigLen[4] = SigLen[1] + SigLen[3] /\ SeedLen[4] = SeedLen[1] + SeedLen[3]

IdLengthError ==
    \A a \in Algs : \A k \in KeysOf(a) :
        (FromPublic(a, k).ok = (k.len = PkLen[a])) /\ (~FromPublic(a, k).ok => FromPublic(a, k).err = "InvalidLength")

IdInjective ==
    \A a, b \in Algs : \A k \in KeysOf(a) : \A m \in KeysOf(b) :
        (FromPublic(a, k).ok /\ FromPublic(b, m).ok /\ FromPublic(a, k).id = FromPublic(b, m).id) => (a = b /\ k = m)

IdEncodingInjective ==
    \A a, b \in Algs : \A k \in KeysOf(a) : \A m \in KeysOf(b) :
        (FromPublic(a, k).ok /\ FromPublic(b, m).ok /\ EncodeId(FromPublic(a, k).id) = EncodeId(FromPublic(b, m).id)) => (a = b /\ k = m)

MatchesIff ==
    \A a, b \in Algs : \A k \in KeysOf(a) : \A m \in KeysOf(b) :
        FromPublic(a, k).ok => (Matches(FromPublic(a, k).id, b, m) <=> (a = b /\ k = m))

LengthFirst ==
    \A a \in Algs : \A k \in KeysOf(a) : \A s \in SigsOf(a) : \A fe, fm \in Flags :
        (k.len # PkLen[a] \/ s.len # SigLen[a]) => Verify(a, k, s, fe, fm) = "InvalidLength"

RightLen(a, k, s) == k.len = PkLen[a] /\ s.len = SigLen[a]

EdOkIff ==
    \A k \in KeysOf(1) : \A s \in SigsOf(1) : \A fe, fm \in Flags :
        (Verify(1, k, s, fe, fm) = "ok") <=> (RightLen(1, k, s) /\ fe.pkOk /\ fe.ok)

P256OkIff ==
    \A k \in KeysOf(2) : \A s \in SigsOf(2) : \A fe, fm \in Flags :
        (Verify(2, k, s, fe, fm) = "ok") <=>
            (RightLen(2, k, s) /\ k.head \in {2, 3} /\ fe.pkOk /\ fe.sigOk /\ fe.lowS /\ fe.ok)

MlOkIff ==
    \A k \in KeysOf(3) : \A s \in SigsOf(3) : \A fe, fm \in Flags :
        (Verify(3, k, s, fe, fm) = "ok") <=> (RightLen(3, k, s) /\ fm.sigOk /\ fm.ok)

HybridOkIff ==
    \A k \in KeysOf(4) : \A s \in SigsOf(4) : \A fe, fm \in Flags :
        (Verify(4, k, s, fe, fm) = "ok") <=> (RightLen(4, k, s) /\ fe.pkOk /\ fe.ok /\ fm.sigOk /\ fm.ok)

P256OtherForm ==
    \A k \in KeysOf(2) : \A s \in SigsOf(2) : \A fe, fm \in Flags :
        (RightLen(2, k, s) /\ k.head \notin {2, 3}) => Verify(2, k, s, fe, fm) = "InvalidPublicKey"

P256HighS ==
    \A k \in KeysOf(2) : \A s \in SigsOf(2) : \A fe, fm \in Flags :
        (RightLen(2, k, s) /\ k.head \in {2, 3} /\ fe.pkOk /\ fe.sigOk /\ ~fe.lowS) => Verify(2, k, s, fe, fm) = "HighS"

EdErrorFirst ==
    \A k \in KeysOf(4) : \A s \in SigsOf(4) : \A fe, fm \in Flags :
        (RightLen(4, k, s) /\ EdV(EdHalf(k), EdSigHalf(s), fe) # "ok") =>
            Verify(4, k, s, fe, fm) = EdV(EdHalf(k), EdSigHalf(s), fe)

CtxTooLong ==
    \A k \in KeysOf(3) : \A s \in SigsOf(3) : \A fm \in Flags :
        \A c \in {0, 255, 256, 300} : (c > 255) => MV(k, c, s, fm) = "InvalidLength"

IdsOf(a) == {FromPublic(a, k).id : k \in {k \in KeysOf(a) : k.len = PkLen[a]}}
NodeIdMismatchFirst ==
    \A a \in Algs : \A id \in IdsOf(a) : \A k \in KeysOf(a) : \A s \in SigsOf(a) : \A fe, fm \in Flags :
        ~Matches(id, a, k) => VerifyNode(id, k, s, fe, fm) = "NodeIdMismatch"

VerifyNodeOk ==
    \A a \in Algs : \A id \in IdsOf(a) : \A k \in KeysOf(a) : \A s \in SigsOf(a) : \A fe, fm \in Flags :
        VerifyNode(id, k, s, fe, fm) = "ok" => (Matches(id, a, k) /\ Verify(a, k, s, fe, fm) = "ok")

NMinus1 == [i \in 1..16 |-> IF i = 16 THEN NLimbs[16] - 1 ELSE NLimbs[i]]
NPlus1 == [i \in 1..16 |-> IF i = 16 THEN NLimbs[16] + 1 ELSE NLimbs[i]]
Zero16 == [i \in 1..16 |-> 0]
One16 == [i \in 1..16 |-> IF i = 16 THEN 1 ELSE 0]
Max16 == [i \in 1..16 |-> 65535]
SeedBoundary ==
    /\ ~SeedOk(Zero16) /\ SeedOk(One16) /\ SeedOk(NMinus1)
    /\ ~SeedOk(NLimbs) /\ ~SeedOk(NPlus1) /\ ~SeedOk(Max16)
    /\ FromSeed(2, 31, <<>>) = "InvalidLength" /\ FromSeed(2, 32, Zero16) = "InvalidSecretKey"
    /\ FromSeed(2, 32, One16) = "ok" /\ FromSeed(1, 32, Zero16) = "ok" /\ FromSeed(4, 64, Zero16) = "ok"
    /\ FromSeed(4, 32, Zero16) = "InvalidLength"

(* lexicographic order of equal-length big-endian limbs is numeric order *)
Num(a) == a[1] * 9 + a[2] * 3 + a[3]
LexIsNumeric == \A a, b \in [1..3 -> 0..2] : LexLess(a, b) <=> Num(a) < Num(b)

WriteRule ==
    \A a \in Algs : \A o \in {0, 1, 31, 32, 33, 1983, 1984, 1985, 3372, 3373, 3374} :
        /\ (WriteOut(PkLen[a], o) = "ok") <=> PkLen[a] <= o
        /\ (WriteOut(SigLen[a], o) = "ok") <=> SigLen[a] <= o

NodeIdNoFallback ==
    \A a \in Algs : PkLen[a] <= MaxPk /\ \A k \in KeysOf(a) : k.len = PkLen[a] => FromPublic(a, k).ok
=============================================================================
