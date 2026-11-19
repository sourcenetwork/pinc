--------------------------- MODULE KeystoreTemplate ---------------------------
(***************************************************************************)
(* The public templates the TPM store asks the TPM to create its objects   *)
(* from: pinc-keystore tpm/template.rs (`storage_primary`,                 *)
(* `p256_signing_key`, `sealed_data`), as the bytes of the TPM2B_PUBLIC    *)
(* that goes into TPM2_CreatePrimary (client.rs `create_primary`) and      *)
(* TPM2_Create (store.rs `generate` and `seal`).                           *)
(*                                                                         *)
(* The story. The store makes three kinds of object: the storage primary   *)
(* (a restricted decryption key, ECC P-256 with AES-128-CFB, the parent of *)
(* every key), a P-256 ECDSA-SHA256 signing key, and a sealed data object  *)
(* (keyed hash, the data encryption key of a sealed blob). Each template   *)
(* is built by the store and marshalled by the protocol library; the model *)
(* writes each one from the field layout of TPM 2.0 Part 2 (TPMT_PUBLIC,   *)
(* TPMS_ECC_PARMS, TPMS_KEYEDHASH_PARMS, TPMA_OBJECT) and reads it back    *)
(* with a parser that knows only that layout.                              *)
(*                                                                         *)
(* What must hold (the module documentation of template.rs): every object  *)
(* is fixedTPM and fixedParent (Fixed); none carries a policy, the         *)
(* password is the only gate (NoPolicy); each kind has the role its        *)
(* comment states (Role); the bytes are one well formed TPM2B_PUBLIC with  *)
(* nothing left over (WellFormed), of the type, name algorithm and curve   *)
(* of its kind (TypeOK); the size is fixed per kind (Sizes) and the kinds  *)
(* never share a template (Distinct).                                      *)
(*                                                                         *)
(* SEALATTRS is the attribute word of the sealed data object: 82 in the    *)
(* code (fixedTPM, fixedParent, userWithAuth). KeystoreTemplate_nofixed    *)
(* drops fixedParent (66): the sealed object could be duplicated under     *)
(* another parent, and TLC must find Fixed violated.                       *)
(*                                                                         *)
(* Assumed, not modelled: the TPM device and its transport, and the        *)
(* object the TPM creates from a template (that is the TPM's).             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANT SEALATTRS

\* The kind of object whose template is checked; every kind is an initial state and nothing changes after it.
VARIABLE x

Kinds == {"storage", "sign", "seal"}

\* TPM_ALG_ID and TPM_ECC_CURVE values (TPM 2.0 Part 2, tables 9 and 10).
AlgAes == 6
AlgKeyedHash == 8
AlgSha256 == 11
AlgNull == 16
AlgEcdsa == 24
AlgEcc == 35
AlgCfb == 67
CurveP256 == 3

\* TPMA_OBJECT bits (TPM 2.0 Part 2, table 31).
FixedTpm == 2
StClear == 4
FixedParent == 16
SensitiveDataOrigin == 32
UserWithAuth == 64
AdminWithPolicy == 128
NoDa == 1024
EncryptedDuplication == 2048
Restricted == 65536
Decrypt == 131072
SignEncrypt == 262144

\* The attribute words of the code: storage_primary and p256_signing_key (sealed_data's is SEALATTRS).
StorageAttrs == FixedTpm + FixedParent + SensitiveDataOrigin + UserWithAuth + NoDa + Restricted + Decrypt
SignAttrs == FixedTpm + FixedParent + SensitiveDataOrigin + UserWithAuth + SignEncrypt

(* ---- writing: the TPM marshalling, big-endian ---- *)

U16(n) == <<n \div 256, n % 256>>
U32(n) == U16(n \div 65536) \o U16(n % 65536)
\* A TPM2B: its size, then its bytes.
B2(bs) == U16(Len(bs)) \o bs
\* TPMT_SYM_DEF_OBJECT: TPM_ALG_NULL alone, or the algorithm, the key bits and the mode.
SymDef(alg, bits, mode) == IF alg = AlgNull THEN U16(AlgNull) ELSE U16(alg) \o U16(bits) \o U16(mode)
\* A scheme (TPMT_ECC_SCHEME, TPMT_KDF_SCHEME, TPMT_KEYEDHASH_SCHEME): TPM_ALG_NULL alone, or the scheme and its hash.
Scheme(alg, hash) == IF alg = AlgNull THEN U16(AlgNull) ELSE U16(alg) \o U16(hash)
\* TPMS_ECC_PARMS: symmetric, scheme, curve, kdf.
EccParms(sym, scheme, curve, kdf) == sym \o scheme \o U16(curve) \o kdf
\* An empty TPMS_ECC_POINT: the TPM fills in the point.
EccPoint == B2(<<>>) \o B2(<<>>)
\* TPMT_PUBLIC: type, name algorithm (SHA-256 for every object of the store), attributes, an empty authPolicy, the
\* parameters and the unique field.
Public(type, attrs, params, unique) == U16(type) \o U16(AlgSha256) \o U32(attrs) \o B2(<<>>) \o params \o unique

\* The TPM2B_PUBLIC of each kind, as the store sends it.
Template(k) ==
    B2(CASE k = "storage" -> Public(AlgEcc, StorageAttrs,
                                    EccParms(SymDef(AlgAes, 128, AlgCfb), Scheme(AlgNull, 0), CurveP256, Scheme(AlgNull, 0)),
                                    EccPoint)
         [] k = "sign"    -> Public(AlgEcc, SignAttrs,
                                    EccParms(SymDef(AlgNull, 0, 0), Scheme(AlgEcdsa, AlgSha256), CurveP256, Scheme(AlgNull, 0)),
                                    EccPoint)
         [] k = "seal"    -> Public(AlgKeyedHash, SEALATTRS, Scheme(AlgNull, 0), B2(<<>>)))

(* ---- reading: a parser of the TPM layout alone, offsets from 0 ---- *)

\* The byte at offset o, 0 past the end (a short input then fails WellFormed, never an error of TLC).
At(b, o) == IF o >= 0 /\ o < Len(b) THEN b[o + 1] ELSE 0
Rd16(b, o) == At(b, o) * 256 + At(b, o + 1)
Rd32(b, o) == Rd16(b, o) * 65536 + Rd16(b, o + 2)
Bit(w, m) == (w \div m) % 2 = 1

Size(b) == Rd16(b, 0)
Type(b) == Rd16(b, 2)
NameAlg(b) == Rd16(b, 4)
Attrs(b) == Rd32(b, 6)
PolicySize(b) == Rd16(b, 10)
\* Where the parameters start: after the authPolicy's bytes.
P0(b) == 12 + PolicySize(b)
\* ECC: the symmetric definition, then the scheme (S1), the curve (S2), the kdf, the unique point (S3).
SymAlg(b) == Rd16(b, P0(b))
S1(b) == IF SymAlg(b) = AlgNull THEN P0(b) + 2 ELSE P0(b) + 6
SchemeAlg(b) == Rd16(b, S1(b))
SchemeHash(b) == Rd16(b, S1(b) + 2)
S2(b) == IF SchemeAlg(b) = AlgNull THEN S1(b) + 2 ELSE S1(b) + 4
Curve(b) == Rd16(b, S2(b))
KdfAlg(b) == Rd16(b, S2(b) + 2)
S3(b) == IF KdfAlg(b) = AlgNull THEN S2(b) + 4 ELSE S2(b) + 6
EccEnd(b) == LET xs == Rd16(b, S3(b)) IN S3(b) + 4 + xs + Rd16(b, S3(b) + 2 + xs)
\* KEYEDHASH: the scheme, then the unique digest.
KhSchemeAlg(b) == Rd16(b, P0(b))
K1(b) == IF KhSchemeAlg(b) = AlgNull THEN P0(b) + 2 ELSE P0(b) + 4
KhEnd(b) == K1(b) + 2 + Rd16(b, K1(b))
\* Where the parse of the whole structure ends.
ParseEnd(b) == CASE Type(b) = AlgEcc -> EccEnd(b) [] Type(b) = AlgKeyedHash -> KhEnd(b) [] OTHER -> -1

(* ---- the properties, of any bytes b of kind k (the trace check reuses them on recorded bytes) ---- *)

\* One TPM2B_PUBLIC: its size field counts the rest, and the parse consumes every byte.
WellFormedB(b) == Len(b) >= 12 /\ Size(b) = Len(b) - 2 /\ ParseEnd(b) = Len(b)
\* The type, the name algorithm and the curve of the kind.
TypeOKB(k, b) ==
    /\ Type(b) = (IF k = "seal" THEN AlgKeyedHash ELSE AlgEcc)
    /\ NameAlg(b) = AlgSha256
    /\ (k # "seal" => Curve(b) = CurveP256)
\* The object stays in this TPM, under this parent.
FixedB(b) == Bit(Attrs(b), FixedTpm) /\ Bit(Attrs(b), FixedParent)
\* No policy: an empty authPolicy, the password (userWithAuth) opens it, and the admin role needs no policy either.
NoPolicyB(b) == PolicySize(b) = 0 /\ Bit(Attrs(b), UserWithAuth) /\ ~Bit(Attrs(b), AdminWithPolicy)
\* The role of each kind, as template.rs states it.
RoleB(k, b) ==
    CASE k = "storage" ->
            /\ Bit(Attrs(b), Restricted) /\ Bit(Attrs(b), Decrypt) /\ ~Bit(Attrs(b), SignEncrypt)
            /\ Bit(Attrs(b), SensitiveDataOrigin)
            /\ SymAlg(b) = AlgAes /\ Rd16(b, P0(b) + 2) = 128 /\ Rd16(b, P0(b) + 4) = AlgCfb
            /\ SchemeAlg(b) = AlgNull /\ KdfAlg(b) = AlgNull
      [] k = "sign" ->
            /\ Bit(Attrs(b), SignEncrypt) /\ ~Bit(Attrs(b), Restricted) /\ ~Bit(Attrs(b), Decrypt)
            /\ Bit(Attrs(b), SensitiveDataOrigin)
            /\ SymAlg(b) = AlgNull /\ SchemeAlg(b) = AlgEcdsa /\ SchemeHash(b) = AlgSha256 /\ KdfAlg(b) = AlgNull
      [] k = "seal" ->
            /\ ~Bit(Attrs(b), SignEncrypt) /\ ~Bit(Attrs(b), Restricted) /\ ~Bit(Attrs(b), Decrypt)
            /\ ~Bit(Attrs(b), SensitiveDataOrigin)
            /\ KhSchemeAlg(b) = AlgNull
\* The size of each kind's template.
SizeOf == [storage |-> 28, sign |-> 26, seal |-> 16]

Init == x \in Kinds
Next == UNCHANGED x
Spec == Init /\ [][Next]_x

WellFormed == WellFormedB(Template(x))
TypeOK == x \in Kinds /\ TypeOKB(x, Template(x))
Fixed == FixedB(Template(x))
NoPolicy == NoPolicyB(Template(x))
Role == RoleB(x, Template(x))
Sizes == Len(Template(x)) = SizeOf[x]
\* One template per kind: no two kinds are sent the same bytes.
Distinct == \A k \in Kinds : k # x => Template(k) # Template(x)
=============================================================================
