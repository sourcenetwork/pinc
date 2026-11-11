//! Answering the key requests of the endpoint and of the connectivity client from software keys.
//!
//! Invariants: an answer owns its bytes, so the request it answers can be dropped first; a request this host cannot
//! answer is a failed answer, never a guess.

use vinc_crypto::{Drbg, Keypair, Secret, Software};
use vinc_security::{Env, KeyHandle, KeyRequest, KeyResponse, SoftKeys, SoftPrekeys};

#[allow(
    clippy::large_enum_variant,
    reason = "built once per key request and dropped at once"
)]
pub(super) enum Answer {
    Sig([u8; vinc_crypto::identity::MAX_SIGNATURE_LEN], usize),
    Secret(Secret<32>),
    Failed,
}

impl Answer {
    pub(super) fn response(&self) -> KeyResponse<'_> {
        match self {
            Self::Sig(b, n) => KeyResponse::Signature(b.get(..*n).unwrap_or_default()),
            Self::Secret(s) => KeyResponse::SharedSecret(Secret::new(*s.expose())),
            Self::Failed => KeyResponse::Failed,
        }
    }
}

pub(super) fn answer(
    prov: Software,
    kp: &Keypair,
    prekeys: &SoftPrekeys<Software>,
    drbg: &mut Drbg,
    now: u64,
    req: &KeyRequest<'_>,
) -> Answer {
    let soft = SoftKeys {
        signer: Some((KeyHandle(1), kp)),
        prekeys: Some(prekeys),
    };
    let mut env = Env {
        provider: &prov,
        now,
        drbg,
    };
    let mut sig = [0u8; vinc_crypto::identity::MAX_SIGNATURE_LEN];
    match soft.answer(&mut env, req, &mut sig) {
        KeyResponse::Signature(s) => {
            let n = s.len();
            let mut out = [0u8; vinc_crypto::identity::MAX_SIGNATURE_LEN];
            if let (Some(d), Some(src)) = (out.get_mut(..n), s.get(..n)) {
                d.copy_from_slice(src);
            }
            Answer::Sig(out, n)
        }
        KeyResponse::SharedSecret(s) => Answer::Secret(s),
        KeyResponse::Failed => Answer::Failed,
    }
}
