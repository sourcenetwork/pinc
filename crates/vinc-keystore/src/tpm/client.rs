//! [`TpmClient`]: the TPM 2.0 commands the key store needs, marshaled by `tpm2-protocol`.
//!
//! Invariants: every command uses a password authorization session (`TPM_RS_PW`) where the TPM asks for
//! authorization, and none otherwise; every response is length-checked against its header and its response code is
//! checked before the body is read, so a failure is a [`KeyStoreError::Tpm`] carrying the code; buffers that held
//! commands or responses with secrets are zeroized.

use std::time::Duration;

use tpm2_protocol::basic::{TpmHandle, TpmUint16};
use tpm2_protocol::constant::TPM_MAX_COMMAND_SIZE;
use tpm2_protocol::data::{
    Tpm2bAuth, Tpm2bData, Tpm2bDigest, Tpm2bEccParameter, Tpm2bNonce, Tpm2bPrivate, Tpm2bPublic, Tpm2bSensitiveCreate,
    Tpm2bSensitiveData, TpmAlgId, TpmRh, TpmSt, TpmSu, TpmaSession, TpmlPcrSelection, TpmsAuthCommand, TpmsSchemeHash,
    TpmsSensitiveCreate, TpmtSigScheme, TpmtTkHashcheck, TpmuPublicId, TpmuSigScheme, TpmuSignature,
};
use tpm2_protocol::frame::{
    TpmCreateCommand, TpmCreatePrimaryCommand, TpmCreatePrimaryResponse, TpmCreateResponse, TpmEvictControlCommand,
    TpmEvictControlResponse, TpmFlushContextCommand, TpmFlushContextResponse, TpmFrame, TpmGetRandomCommand,
    TpmGetRandomResponse, TpmLoadCommand, TpmLoadResponse, TpmReadPublicCommand, TpmReadPublicResponse, TpmResponse,
    TpmSignCommand, TpmSignResponse, TpmStartupCommand, TpmStartupResponse, TpmUnmarshalBody, TpmUnsealCommand,
    TpmUnsealResponse, tpm_marshal_command,
};
use tpm2_protocol::{TpmMarshal, TpmUnmarshal, TpmWriter};
use zeroize::Zeroizing;

use super::template;
use super::transport::Transport;
use crate::{KeyStoreError, Result};

/// The longest auth value a TPM accepts (the size of its largest digest).
pub const MAX_AUTH_LEN: usize = 64;

/// `TPM_RC_INITIALIZE`: the TPM was already started.
pub const RC_INITIALIZE: u32 = 0x100;

/// `TPM_RC_YIELDED`: the TPM gave up the command to let others run; send it again.
pub const RC_YIELDED: u32 = 0x908;
/// `TPM_RC_TESTING`: a self test is still running; send the command again.
pub const RC_TESTING: u32 = 0x90A;
/// `TPM_RC_RETRY`: the TPM was busy; send the command again.
pub const RC_RETRY: u32 = 0x922;

/// Whether `code` is a warning the TPM 2.0 specification defines as "send the same command again".
const fn is_resend(code: u32) -> bool {
    matches!(code, RC_YIELDED | RC_TESTING | RC_RETRY)
}

/// How often and how long a command is resent when the TPM answers "send it again".
///
/// A command is sent at most `attempts` times. Before send `n + 1` the client waits `first_wait * 2^(n-1)`, never
/// more than `max_wait`, so the whole wait is bounded by `(attempts - 1) * max_wait`. The default is 8 sends and
/// waits of 1, 2, 4, 8, 16, 32 and 50 ms: 113 ms in all, enough for a TPM to finish a self test slice or yield,
/// short enough that a wedged TPM is reported promptly as [`KeyStoreError::TpmBusy`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RetryPolicy {
    /// The most times one command is sent; `0` is treated as `1`.
    pub attempts: u32,
    /// The wait before the first resend.
    pub first_wait: Duration,
    /// The longest single wait.
    pub max_wait: Duration,
}

impl RetryPolicy {
    /// Resend at once, as often as `attempts` allows, without waiting.
    pub const fn immediate(attempts: u32) -> Self {
        Self {
            attempts,
            first_wait: Duration::ZERO,
            max_wait: Duration::ZERO,
        }
    }
}

impl Default for RetryPolicy {
    fn default() -> Self {
        Self {
            attempts: 8,
            first_wait: Duration::from_millis(1),
            max_wait: Duration::from_millis(50),
        }
    }
}

const HEADER_LEN: usize = 10;
/// `GetRandom` returns at most one digest of the TPM's largest hash; ask for no more than SHA-256's size.
const RANDOM_CHUNK: u16 = 32;

/// The wire form of a created object: its TPM2B private and TPM2B public parts, each with its size prefix.
#[derive(Debug, Clone)]
pub struct Blob {
    pub(crate) private: Vec<u8>,
    pub(crate) public: Vec<u8>,
}

/// An ECC public point as two 32-byte big-endian coordinates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EccPoint {
    /// The x coordinate.
    pub x: [u8; 32],
    /// The y coordinate.
    pub y: [u8; 32],
}

/// A TPM 2.0 command client over a [`Transport`].
pub struct TpmClient<T: Transport> {
    transport: T,
    retry: RetryPolicy,
}

impl<T: Transport> core::fmt::Debug for TpmClient<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("TpmClient(..)")
    }
}

fn proto<E>(_: E) -> KeyStoreError {
    KeyStoreError::Protocol
}

fn handle(raw: u32) -> TpmHandle {
    TpmHandle::new(raw)
}

fn rh(h: TpmRh) -> TpmHandle {
    handle(h.value())
}

fn auth_value(auth: &[u8]) -> Result<Tpm2bAuth> {
    Tpm2bAuth::try_from(auth).map_err(|_| KeyStoreError::InvalidAuth)
}

/// A password session carrying `auth`.
fn password(auth: &[u8]) -> Result<TpmsAuthCommand> {
    Ok(TpmsAuthCommand {
        session_handle: rh(TpmRh::Pw),
        nonce: Tpm2bNonce::default(),
        session_attributes: TpmaSession::CONTINUE_SESSION,
        hmac: auth_value(auth)?,
    })
}

fn to_vec<T: TpmMarshal>(value: &T) -> Result<Vec<u8>> {
    let mut buf = Zeroizing::new([0u8; TPM_MAX_COMMAND_SIZE]);
    let mut w = TpmWriter::new(buf.as_mut_slice());
    value.marshal(&mut w).map_err(proto)?;
    Ok(w.as_bytes().to_vec())
}

/// The 32-byte big-endian form of an ECC coordinate or signature scalar the TPM may have trimmed.
fn pad32(bytes: &[u8]) -> Result<[u8; 32]> {
    let mut out = [0u8; 32];
    let start = out.len().checked_sub(bytes.len()).ok_or(KeyStoreError::Protocol)?;
    out.get_mut(start..)
        .ok_or(KeyStoreError::Protocol)?
        .copy_from_slice(bytes);
    Ok(out)
}

impl<T: Transport> TpmClient<T> {
    /// A client that sends commands over `transport`.
    pub fn new(transport: T) -> Self {
        Self {
            transport,
            retry: RetryPolicy::default(),
        }
    }

    /// Replace the policy for resending a command the TPM asked to be sent again.
    #[must_use]
    pub fn with_retry(mut self, retry: RetryPolicy) -> Self {
        self.retry = retry;
        self
    }

    /// Marshal `cmd` with `sessions`, send it, check the response and read its body as `R`.
    fn execute<C: TpmFrame, R: TpmUnmarshalBody>(&mut self, cmd: &C, sessions: &[TpmsAuthCommand]) -> Result<R> {
        let mut buf = Zeroizing::new([0u8; TPM_MAX_COMMAND_SIZE]);
        let mut w = TpmWriter::new(buf.as_mut_slice());
        let tag = if sessions.is_empty() {
            TpmSt::NoSessions
        } else {
            TpmSt::Sessions
        };
        tpm_marshal_command(cmd, tag, sessions, &mut w).map_err(proto)?;
        let rsp = self.exchange(w.as_bytes())?;
        TpmResponse::cast(&rsp).map_err(proto)?.unmarshal::<R>().map_err(proto)
    }

    /// Send `command` and return its whole response, resending the same bytes while the TPM answers one of the
    /// warnings that mean "send it again" ([`RC_RETRY`], [`RC_YIELDED`], [`RC_TESTING`]), within the [`RetryPolicy`].
    /// Every command goes through here. Any other nonzero code is returned as [`KeyStoreError::Tpm`].
    fn exchange(&mut self, command: &[u8]) -> Result<Zeroizing<Vec<u8>>> {
        let attempts = self.retry.attempts.max(1);
        let mut wait = self.retry.first_wait;
        for attempt in 1..=attempts {
            let rsp = Zeroizing::new(
                self.transport
                    .transmit(command)
                    .map_err(|e| KeyStoreError::Transport(e.kind()))?,
            );
            let header = rsp.get(..HEADER_LEN).ok_or(KeyStoreError::Protocol)?;
            let size = header
                .get(2..6)
                .and_then(|b| <[u8; 4]>::try_from(b).ok())
                .map(u32::from_be_bytes);
            let code = header
                .get(6..10)
                .and_then(|b| <[u8; 4]>::try_from(b).ok())
                .map(u32::from_be_bytes);
            let (Some(size), Some(code)) = (size, code) else {
                return Err(KeyStoreError::Protocol);
            };
            if usize::try_from(size) != Ok(rsp.len()) {
                return Err(KeyStoreError::Protocol);
            }
            if is_resend(code) {
                if attempt == attempts {
                    return Err(KeyStoreError::TpmBusy { code });
                }
                std::thread::sleep(wait);
                wait = wait.saturating_mul(2).min(self.retry.max_wait);
                continue;
            }
            if code != 0 {
                return Err(KeyStoreError::Tpm { code });
            }
            return Ok(rsp);
        }
        Err(KeyStoreError::Protocol)
    }

    /// `TPM2_Startup(TPM_SU_CLEAR)`. A TPM that is already running answers [`RC_INITIALIZE`].
    ///
    /// # Errors
    /// [`KeyStoreError::Tpm`] with the TPM's code, including [`RC_INITIALIZE`].
    pub fn startup_clear(&mut self) -> Result<()> {
        let cmd = TpmStartupCommand {
            handles: [],
            startup_type: TpmSu::Clear,
        };
        self.execute::<_, TpmStartupResponse>(&cmd, &[]).map(drop)
    }

    /// `TPM2_GetRandom`: up to 32 random bytes from the TPM's generator (fewer if the TPM returns fewer).
    ///
    /// # Errors
    /// A TPM or transport failure.
    pub fn get_random(&mut self, n: u16) -> Result<Vec<u8>> {
        let cmd = TpmGetRandomCommand {
            handles: [],
            bytes_requested: TpmUint16::new(n.min(RANDOM_CHUNK)),
        };
        let rsp: TpmGetRandomResponse = self.execute(&cmd, &[])?;
        Ok(rsp.random_bytes.to_vec())
    }

    /// Fill `out` with TPM randomness, one `GetRandom` per 32 bytes.
    ///
    /// # Errors
    /// A TPM or transport failure, or [`KeyStoreError::Protocol`] if the TPM returns no bytes.
    pub fn fill_random(&mut self, out: &mut [u8]) -> Result<()> {
        let mut filled = 0;
        while let Some(rest) = out.get_mut(filled..).filter(|r| !r.is_empty()) {
            let want = u16::try_from(rest.len()).unwrap_or(u16::MAX);
            let got = Zeroizing::new(self.get_random(want)?);
            let n = got.len().min(rest.len());
            if n == 0 {
                return Err(KeyStoreError::Protocol);
            }
            rest.get_mut(..n)
                .ok_or(KeyStoreError::Protocol)?
                .copy_from_slice(got.get(..n).ok_or(KeyStoreError::Protocol)?);
            filled += n;
        }
        Ok(())
    }

    /// `TPM2_CreatePrimary` under the owner hierarchy: the ECC P-256 storage key. The key is derived from the
    /// owner seed and the template, so the same TPM always yields the same key. Returns its transient handle.
    ///
    /// # Errors
    /// [`KeyStoreError::InvalidAuth`] for an over-long `owner_auth`; a TPM or transport failure.
    pub fn create_primary(&mut self, owner_auth: &[u8]) -> Result<u32> {
        let cmd = TpmCreatePrimaryCommand {
            handles: [rh(TpmRh::Owner)],
            in_sensitive: Tpm2bSensitiveCreate::default(),
            in_public: template::storage_primary(),
            outside_info: Tpm2bData::default(),
            creation_pcr: TpmlPcrSelection::default(),
        };
        let rsp: TpmCreatePrimaryResponse = self.execute(&cmd, &[password(owner_auth)?])?;
        rsp.handles.first().map(|h| h.value()).ok_or(KeyStoreError::Protocol)
    }

    /// `TPM2_Create` of `template` under `parent`, with `object_auth` and optional sensitive `data` (the secret of a
    /// sealed object).
    ///
    /// # Errors
    /// [`KeyStoreError::InvalidAuth`]; a TPM or transport failure.
    pub fn create(
        &mut self,
        parent: u32,
        parent_auth: &[u8],
        template: Tpm2bPublic,
        object_auth: &[u8],
        data: &[u8],
    ) -> Result<Blob> {
        let sensitive = TpmsSensitiveCreate {
            user_auth: auth_value(object_auth)?,
            data: Tpm2bSensitiveData::try_from(data).map_err(proto)?,
        };
        let cmd = TpmCreateCommand {
            handles: [handle(parent)],
            in_sensitive: Tpm2bSensitiveCreate::from(sensitive),
            in_public: template,
            outside_info: Tpm2bData::default(),
            creation_pcr: TpmlPcrSelection::default(),
        };
        let rsp: TpmCreateResponse = self.execute(&cmd, &[password(parent_auth)?])?;
        Ok(Blob {
            private: to_vec(&rsp.out_private)?,
            public: to_vec(&rsp.out_public)?,
        })
    }

    /// `TPM2_Load` of `blob` under `parent`; returns the transient handle.
    ///
    /// # Errors
    /// [`KeyStoreError::Protocol`] for a malformed blob; a TPM or transport failure.
    pub fn load(&mut self, parent: u32, parent_auth: &[u8], blob: &Blob) -> Result<u32> {
        let cmd = TpmLoadCommand {
            handles: [handle(parent)],
            in_private: Tpm2bPrivate::unmarshal(&blob.private).map_err(proto)?.0,
            in_public: Tpm2bPublic::unmarshal(&blob.public).map_err(proto)?.0,
        };
        let rsp: TpmLoadResponse = self.execute(&cmd, &[password(parent_auth)?])?;
        rsp.handles.first().map(|h| h.value()).ok_or(KeyStoreError::Protocol)
    }

    /// `TPM2_EvictControl`: make the transient object `object` persistent at `persistent`, authorized by the owner.
    ///
    /// # Errors
    /// A TPM or transport failure, such as `TPM_RC_NV_DEFINED` when `persistent` is taken.
    pub fn evict_control(&mut self, owner_auth: &[u8], object: u32, persistent: u32) -> Result<()> {
        let cmd = TpmEvictControlCommand {
            handles: [rh(TpmRh::Owner), handle(object)],
            persistent_handle: handle(persistent),
        };
        self.execute::<_, TpmEvictControlResponse>(&cmd, &[password(owner_auth)?])
            .map(drop)
    }

    /// `TPM2_ReadPublic`: the ECC public point of the object at `object`.
    ///
    /// # Errors
    /// [`KeyStoreError::WrongKeyKind`] if the object is not an ECC key; a TPM or transport failure.
    pub fn read_public(&mut self, object: u32) -> Result<EccPoint> {
        let cmd = TpmReadPublicCommand {
            handles: [handle(object)],
        };
        let rsp: TpmReadPublicResponse = self.execute(&cmd, &[])?;
        let TpmuPublicId::Ecc(point) = rsp.out_public.inner.unique else {
            return Err(KeyStoreError::WrongKeyKind);
        };
        Ok(EccPoint {
            x: pad32(&point.x)?,
            y: pad32(&point.y)?,
        })
    }

    /// `TPM2_Sign` with ECDSA-SHA256 over `digest`; returns the raw `(r, s)` the TPM produced, which may have a
    /// high `s`.
    ///
    /// # Errors
    /// A TPM or transport failure, or [`KeyStoreError::Protocol`] if the TPM returns another signature kind.
    pub fn sign_p256(&mut self, key: u32, key_auth: &[u8], digest: &[u8; 32]) -> Result<([u8; 32], [u8; 32])> {
        let cmd = TpmSignCommand {
            handles: [handle(key)],
            digest: Tpm2bDigest::try_from(digest.as_slice()).map_err(proto)?,
            in_scheme: TpmtSigScheme {
                scheme: TpmAlgId::Ecdsa,
                details: TpmuSigScheme::Hash(TpmsSchemeHash {
                    hash_alg: TpmAlgId::Sha256,
                }),
            },
            validation: TpmtTkHashcheck {
                tag: TpmSt::HashCheck,
                hierarchy: TpmRh::Null,
                digest: Tpm2bDigest::default(),
            },
        };
        let rsp: TpmSignResponse = self.execute(&cmd, &[password(key_auth)?])?;
        let TpmuSignature::Ecdsa(sig) = rsp.signature.signature else {
            return Err(KeyStoreError::Protocol);
        };
        let (r, s): (&Tpm2bEccParameter, &Tpm2bEccParameter) = (&sig.signature_r, &sig.signature_s);
        Ok((pad32(r)?, pad32(s)?))
    }

    /// `TPM2_Unseal` of the sealed data object at `item`.
    ///
    /// # Errors
    /// A TPM or transport failure, such as `TPM_RC_AUTH_FAIL` for a wrong auth value.
    pub fn unseal(&mut self, item: u32, item_auth: &[u8]) -> Result<Zeroizing<Vec<u8>>> {
        let cmd = TpmUnsealCommand {
            handles: [handle(item)],
        };
        let rsp: TpmUnsealResponse = self.execute(&cmd, &[password(item_auth)?])?;
        Ok(Zeroizing::new(rsp.out_data.to_vec()))
    }

    /// `TPM2_FlushContext`: free the transient object at `object`.
    ///
    /// # Errors
    /// A TPM or transport failure.
    pub fn flush_context(&mut self, object: u32) -> Result<()> {
        let cmd = TpmFlushContextCommand {
            handles: [],
            flush_handle: handle(object),
        };
        self.execute::<_, TpmFlushContextResponse>(&cmd, &[]).map(drop)
    }
}

const _: () = assert!(MAX_AUTH_LEN == tpm2_protocol::constant::MAX_DIGEST_SIZE);

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing)]
mod tests {
    use std::io;

    use super::*;

    /// Answers each command from a script of response codes (the last repeats), recording what it was sent.
    struct Scripted {
        codes: Vec<u32>,
        sent: Vec<Vec<u8>>,
    }

    impl Transport for Scripted {
        fn transmit(&mut self, command: &[u8]) -> io::Result<Vec<u8>> {
            let i = self.sent.len().min(self.codes.len() - 1);
            self.sent.push(command.to_vec());
            let mut rsp = vec![0x80, 0x01, 0, 0, 0, 10];
            rsp.extend_from_slice(&self.codes[i].to_be_bytes());
            Ok(rsp)
        }
    }

    fn client(codes: &[u32], attempts: u32) -> TpmClient<Scripted> {
        let t = Scripted {
            codes: codes.to_vec(),
            sent: Vec::new(),
        };
        TpmClient::new(t).with_retry(RetryPolicy::immediate(attempts))
    }

    #[test]
    fn retry_twice_then_success_resends_the_same_bytes() {
        let mut c = client(&[RC_RETRY, RC_RETRY, 0], 8);
        c.flush_context(0x8000_0000).unwrap();
        let sent = &c.transport.sent;
        assert_eq!(sent.len(), 3);
        assert!(sent.iter().all(|s| *s == sent[0]));
    }

    #[test]
    fn every_resend_warning_is_retried() {
        for code in [RC_RETRY, RC_YIELDED, RC_TESTING] {
            let mut c = client(&[code, 0], 2);
            c.flush_context(0x8000_0000).unwrap();
            assert_eq!(c.transport.sent.len(), 2, "{code:#x}");
        }
    }

    #[test]
    fn never_succeeding_gives_the_typed_error_after_the_bound() {
        let mut c = client(&[RC_YIELDED], 5);
        assert_eq!(
            c.flush_context(0x8000_0000),
            Err(KeyStoreError::TpmBusy { code: RC_YIELDED })
        );
        assert_eq!(c.transport.sent.len(), 5);
    }

    #[test]
    fn other_codes_are_not_retried() {
        let mut c = client(&[0x9A2], 8);
        assert_eq!(c.flush_context(0x8000_0000), Err(KeyStoreError::Tpm { code: 0x9A2 }));
        assert_eq!(c.transport.sent.len(), 1);
    }

    #[test]
    fn default_policy_wait_is_bounded() {
        let p = RetryPolicy::default();
        assert!(p.max_wait.saturating_mul(p.attempts) <= Duration::from_secs(1));
    }
}
