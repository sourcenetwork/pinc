//! The TPM object templates the key store creates.
//!
//! Invariants: every object is `fixedTPM` and `fixedParent`, so it cannot be duplicated off the device, and none
//! carries a policy, so password authorization is the only gate.

use tpm2_protocol::basic::TpmUint16;
use tpm2_protocol::data::{
    Tpm2bDigest, Tpm2bPublic, TpmAlgId, TpmEccCurve, TpmaObject, TpmsEccParms, TpmsEccPoint, TpmsKeyedhashParms,
    TpmsSchemeHash, TpmtEccScheme, TpmtKdfScheme, TpmtKeyedhashScheme, TpmtPublic, TpmtSymDef, TpmuAsymScheme,
    TpmuKeyedhashScheme, TpmuPublicId, TpmuPublicParms, TpmuSymKeyBits, TpmuSymMode,
};

fn public(area: TpmtPublic) -> Tpm2bPublic {
    Tpm2bPublic::from(area)
}

/// The storage parent of every object: a restricted decrypt ECC P-256 key with an AES-128-CFB inner wrap.
pub(crate) fn storage_primary() -> Tpm2bPublic {
    public(TpmtPublic {
        object_type: TpmAlgId::Ecc,
        name_alg: TpmAlgId::Sha256,
        object_attributes: TpmaObject::FIXED_TPM
            | TpmaObject::FIXED_PARENT
            | TpmaObject::SENSITIVE_DATA_ORIGIN
            | TpmaObject::USER_WITH_AUTH
            | TpmaObject::NO_DA
            | TpmaObject::RESTRICTED
            | TpmaObject::DECRYPT,
        auth_policy: Tpm2bDigest::default(),
        parameters: TpmuPublicParms::Ecc(TpmsEccParms {
            symmetric: TpmtSymDef {
                algorithm: TpmAlgId::Aes,
                key_bits: TpmuSymKeyBits::Aes(TpmUint16::new(128)),
                mode: TpmuSymMode::Aes(TpmAlgId::Cfb),
            },
            scheme: TpmtEccScheme::default(),
            curve_id: TpmEccCurve::NistP256,
            kdf: TpmtKdfScheme::default(),
        }),
        unique: TpmuPublicId::Ecc(TpmsEccPoint::default()),
    })
}

/// An ECDSA-SHA256 P-256 signing key whose private part is generated inside the TPM.
pub(crate) fn p256_signing_key() -> Tpm2bPublic {
    public(TpmtPublic {
        object_type: TpmAlgId::Ecc,
        name_alg: TpmAlgId::Sha256,
        object_attributes: TpmaObject::FIXED_TPM
            | TpmaObject::FIXED_PARENT
            | TpmaObject::SENSITIVE_DATA_ORIGIN
            | TpmaObject::USER_WITH_AUTH
            | TpmaObject::SIGN_ENCRYPT,
        auth_policy: Tpm2bDigest::default(),
        parameters: TpmuPublicParms::Ecc(TpmsEccParms {
            symmetric: TpmtSymDef::default(),
            scheme: TpmtEccScheme {
                scheme: TpmAlgId::Ecdsa,
                details: TpmuAsymScheme::Hash(TpmsSchemeHash {
                    hash_alg: TpmAlgId::Sha256,
                }),
            },
            curve_id: TpmEccCurve::NistP256,
            kdf: TpmtKdfScheme::default(),
        }),
        unique: TpmuPublicId::Ecc(TpmsEccPoint::default()),
    })
}

/// A sealed data object: a keyed-hash object with no scheme, whose secret the caller supplies at creation.
pub(crate) fn sealed_data() -> Tpm2bPublic {
    public(TpmtPublic {
        object_type: TpmAlgId::KeyedHash,
        name_alg: TpmAlgId::Sha256,
        object_attributes: TpmaObject::FIXED_TPM | TpmaObject::FIXED_PARENT | TpmaObject::USER_WITH_AUTH,
        auth_policy: Tpm2bDigest::default(),
        parameters: TpmuPublicParms::KeyedHash(TpmsKeyedhashParms {
            scheme: TpmtKeyedhashScheme {
                scheme: TpmAlgId::Null,
                details: TpmuKeyedhashScheme::Null,
            },
        }),
        unique: TpmuPublicId::KeyedHash(Tpm2bDigest::default()),
    })
}
