---------------------------- MODULE CryptoProvider ----------------------------
(***************************************************************************)
(* The provider of vinc-crypto (provider.rs, software.rs): the length      *)
(* checks and errors of every method, the AEAD wrappers, the sampling of   *)
(* the header protection mask (RFC 9001 5.4.3 and 5.4.4), the X25519       *)
(* non-contributory check and the ML-KEM parsers. The primitives are       *)
(* abstract; the nonce of an AEAD call is a [u8; 12] passed through        *)
(* (the protocol nonce is vinc-security's record.rs, checked in Record.tla *)
(* NoNonceReuse).                                                          *)
(*                                                                         *)
(* A ChaCha20 mask: the first 4 bytes of the 16-byte sample are the block  *)
(* counter (little endian), the other 12 the nonce; the block is made at   *)
(* counter and its first 5 bytes are the mask. The counter and the offset  *)
(* counter * 64 are exact words of U64.tla.                                *)
(*                                                                         *)
(* Checked (the counter over every combination of the byte values          *)
(* {0, 1, 128, 255} in its four bytes):                          *)
(*   KeyRule           aead_key and hp_key accept exactly the key length   *)
(*                     of the algorithm and refuse any other with          *)
(*                     InvalidLength                                       *)
(*   CounterRange      the counter is below 2^32, equals the RFC formula   *)
(*                     and determines its four bytes                       *)
(*   MaskInStream      counter * 64 + 5 is within the 2^32 blocks of the   *)
(*                     stream, for every counter                           *)
(*   SampleSplit       a 16-byte sample is a 4-byte counter and a 12-byte  *)
(*                     nonce                                               *)
(*   AeadErrors, DhRule, KemRules  the exact errors                        *)
(* TraceCrypto.tla checks the recorded calls against these operators.      *)
(* Lean counterpart: proofs/lean/Vinc/CryptoProvider.lean.                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

VARIABLE x

U == INSTANCE U64

KeyLen == [chacha |-> 32, aes |-> 16]
NonceLen == 12
TagLen == 16
MaskLen == 5
SampleLen == 16
KemEkLen == 1184
KemCtLen == 1088

KeySetup(alg, len) == IF len = KeyLen[alg] THEN "ok" ELSE "InvalidLength"

(* u32::from_le_bytes of four bytes, as a word *)
LE32(b) == U!Add(U!W(b[1] + 256 * b[2] + 65536 * b[3]), U!Shl(U!W(b[4]), 24))

SealW(fits) == IF fits THEN "ok" ELSE "InputTooLong"
OpenW(valid) == IF valid THEN "ok" ELSE "Authentication"
DhW(zero) == IF zero THEN "NonContributory" ELSE "ok"
KemKey(len, modOk) == IF len # KemEkLen THEN "InvalidEncapsulationKey" ELSE IF ~modOk THEN "InvalidEncapsulationKey" ELSE "ok"
KemCt(len) == IF len # KemCtLen THEN "InvalidLength" ELSE "ok"

Init == x = 0
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

ByteVals == {0, 1, 128, 255}
Counters == [1..4 -> ByteVals]
StreamEnd == U!Shl(U!Pw(32), 6)       \* 2^32 blocks of 64 bytes

KeyRule ==
    \A a \in {"chacha", "aes"} : \A n \in 0..70 :
        /\ (KeySetup(a, n) = "ok") <=> (n = KeyLen[a])
        /\ (KeySetup(a, n) # "ok" => KeySetup(a, n) = "InvalidLength")

CounterRange ==
    /\ \A c \in Counters : U!Lt(LE32(c), U!Pw(32))
    /\ \A c \in Counters : U!Val(U!Shr(LE32(c), 16)) = c[3] + 256 * c[4]
    /\ \A c, d \in Counters : LE32(c) = LE32(d) => c = d
    /\ LE32(<<255, 255, 255, 255>>) = U!Sub(U!Pw(32), U!One) /\ LE32(<<0, 0, 0, 0>>) = U!Zero

MaskInStream ==
    \A c \in Counters :
        LET off == U!Shl(LE32(c), 6)
        IN U!Le(off, StreamEnd) /\ U!Le(U!Add(off, U!W(MaskLen)), StreamEnd)

SampleSplit == SampleLen = 4 + NonceLen /\ MaskLen <= SampleLen

AeadErrors ==
    /\ SealW(TRUE) = "ok" /\ SealW(FALSE) = "InputTooLong"
    /\ OpenW(TRUE) = "ok" /\ OpenW(FALSE) = "Authentication"
    /\ TagLen = 16 /\ NonceLen = 12

DhRule == DhW(TRUE) = "NonContributory" /\ DhW(FALSE) = "ok"

KemRules ==
    /\ \A n \in {0, 1, 1183, 1184, 1185, 1088} : \A m \in BOOLEAN : (KemKey(n, m) = "ok") <=> (n = 1184 /\ m)
    /\ \A n \in {0, 1, 1087, 1088, 1089, 1184} : (KemCt(n) = "ok") <=> (n = 1088)
    /\ \A n \in {0, 1183, 1185} : KemKey(n, TRUE) = "InvalidEncapsulationKey"
    /\ \A n \in {0, 1087, 1089} : KemCt(n) = "InvalidLength"
=============================================================================
