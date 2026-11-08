//! The handshake messages and their exact byte layout: the wire specification.
//!
//! All integers are big-endian. Every field is fixed-size or length-prefixed, and every message starts with a
//! one-byte type. The parsers are strict: a wrong type, a length out of range, a missing byte or a trailing byte is
//! an error, and nothing panics. A handshake message is a payload; the transport carries it in packets and pads the
//! datagrams to [`min_initial_len`] where a message needs it. Throughout, `cid` is `len(1) || bytes` with
//! `len <= 20`, `alpn` is `len(1) || bytes` with `1 <= len <= 32`, and `lp16` is `len(2) || bytes`.
//!
//! | Type | Message | Layout after the type byte |
//! |---|---|---|
//! | 1 | Initial (full) | `version(4)`, `dcid`, `scid`, `alpn`, `aead_offer(1)`, `e_I(32)`, `pk_I(1184)`, `token`(`len(1) <= 101`, bytes), `params`(`lp16`, at most 256 bytes) |
//! | 2 | Initial (short) | as the full Initial, with `hash(pk_I)(32)` in place of `pk_I` |
//! | 3 | Prekey reject | `echo(16)` |
//! | 4 | Reply | `scid_R`, `aead(1)`, `e_R(32)`, `ct(1088)`, `sealed`(`lp16`) |
//! | 5 | Finish | `sealed`(`lp16`) |
//! | 6 | Resume Hello | `version(4)`, `dcid`, `scid`, `alpn`, `aead(1)`, `tid(16)`, `e_I(32)`, `binder(32)`, `params`(`lp16`, at most 256 bytes) |
//! | 7 | Resume Reply | `scid_R`, `e_R(32)`, `tickets`, `params`(`lp16`, at most 256 bytes), `confirm(32)` |
//! | 8 | Resume reject | `echo(16)` |
//!
//! * `aead_offer` is a bit set (bit 0 ChaCha20-Poly1305, bit 1 AES-128-GCM; 1 to 3), `aead` is the tag of one AEAD
//!   (1 ChaCha20-Poly1305, 2 AES-128-GCM).
//! * `sealed` is an AEAD ciphertext followed by its 16-byte tag. Its plaintext is an identity and a signature:
//!   `alg(1)`, `pk`(`lp16`, exactly the length of `alg`'s key), `sig`(`lp16`, exactly the length of `alg`'s
//!   signature), `params`(`lp16`, at most 256 bytes; the responder's transport parameters in a Reply, empty in a
//!   Finish). The Reply is sealed under the responder's handshake key, the Finish under the initiator's, both with
//!   packet number 0 and the transcript hash as associated data.
//! * `tickets` is `count(1) <= 4` followed by `count` entries of `tid(16) || lifetime_seconds(4)`.
//! * `echo` is the first 16 bytes of the transcript hash of the message being rejected; it lets the sender match a
//!   reject to its message. A reject is not authenticated: forging one only forces the fallback handshake.
//! * `params` are opaque transport parameters of at most 256 bytes ([`crate::params`]). Each side's parameters are
//!   absorbed into the transcript as their own length-prefixed field (the initiator's with the Initial or Hello, the
//!   responder's right after its identity, or with the resume Reply), so they are authenticated by the handshake.
//! * The token is an opaque address-validation token (see [`crate::token`]); it is absorbed into the transcript.
//! * A message that is padded for amplification limits is padded by the transport, never inside the message.

use vinc_crypto::identity::{MAX_PUBLIC_KEY_LEN, MAX_SIGNATURE_LEN};
use vinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use vinc_crypto::{Aead, IdentityAlg};
use vinc_wire::{Reader, WireError, Writer};

use crate::ids::{AeadSet, ConnId, MAX_ALPN_LEN, MAX_CID_LEN, aead_from_tag, aead_tag};
use crate::keys::prekey_hash;
use crate::params::{MAX_PARAMS_LEN, Params};
use crate::tickets::TicketBatch;
use crate::token::MAX_TOKEN_LEN;

/// The transport parameters a Reply is sized for when padding the Initial: larger ones (up to [`MAX_PARAMS_LEN`]) still
/// work, the responder just needs another round under the amplification limit.
pub const TYPICAL_PARAMS_LEN: usize = 64;
/// The full Initial is padded to at least this many bytes.
pub const FULL_INITIAL_MIN: usize = 1200;
/// The short Initial is padded to at least this many bytes: 480 x 3 covers the Reply of a 32-byte identity.
pub const SHORT_INITIAL_MIN: usize = 480;
/// The datagram size the padding rule assumes when it counts the datagrams of a Reply.
pub const MIN_DATAGRAM: usize = 1200;
/// The longest plaintext of a sealed identity and signature.
pub const MAX_ID_SIG_LEN: usize = 1 + 2 + MAX_PUBLIC_KEY_LEN + 2 + MAX_SIGNATURE_LEN + 2 + MAX_PARAMS_LEN;
/// The longest sealed identity and signature, tag included.
pub const MAX_SEALED_LEN: usize = MAX_ID_SIG_LEN + Aead::TAG_LEN;

/// Which Initial form is meant when asking for its padding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InitialForm {
    /// The Initial that carries the prekey.
    Full,
    /// The Initial that carries the hash of a cached prekey.
    Short,
}

/// The size in bytes of the sealed identity and signature of `alg`.
const fn sealed_len(alg: IdentityAlg) -> usize {
    1 + 2 + alg.public_key_len() + 2 + alg.signature_len() + 2 + TYPICAL_PARAMS_LEN + Aead::TAG_LEN
}

/// An upper bound on the length of a Reply from a responder with identity `alg` (a 20-byte connection id) and
/// transport parameters of up to [`TYPICAL_PARAMS_LEN`] bytes.
pub const fn reply_len(alg: IdentityAlg) -> usize {
    1 + (1 + MAX_CID_LEN) + 1 + 32 + KEM_CIPHERTEXT_LEN + 2 + sealed_len(alg)
}

/// The least number of bytes the datagrams of an Initial of `form` must total, so that three times that covers the
/// responder's Reply (with the per-datagram overhead of [`crate::amp`]) when the responder uses identity `alg`.
///
/// The bound is 1200 bytes for the full form and 480 for the short form, raised for a responder whose Reply is
/// larger (ML-DSA-65 and hybrid identities).
pub const fn min_initial_len(form: InitialForm, responder: IdentityAlg) -> usize {
    let reply = reply_len(responder);
    let datagrams = reply.div_ceil(MIN_DATAGRAM);
    let needed = (reply + datagrams * crate::amp::OVERHEAD).div_ceil(3);
    let floor = match form {
        InitialForm::Full => FULL_INITIAL_MIN,
        InitialForm::Short => SHORT_INITIAL_MIN,
    };
    if needed > floor { needed } else { floor }
}

/// The longest message this crate produces: the largest Reply.
pub const MAX_MESSAGE_LEN: usize = reply_len(IdentityAlg::Hybrid) + MAX_PARAMS_LEN - TYPICAL_PARAMS_LEN;

/// The type byte of a message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MessageType {
    /// Initial with the full prekey.
    Initial = 1,
    /// Initial with the prekey hash.
    ShortInitial = 2,
    /// The responder does not know the prekey.
    PrekeyReject = 3,
    /// The responder's Reply.
    Reply = 4,
    /// The initiator's Finish.
    Finish = 5,
    /// The resumption Hello.
    ResumeHello = 6,
    /// The resumption Reply.
    ResumeReply = 7,
    /// The responder does not accept the ticket.
    ResumeReject = 8,
}

impl MessageType {
    /// The type of the first byte of `buf`.
    ///
    /// # Errors
    /// [`WireError::Truncated`] for an empty buffer, [`WireError::Unexpected`] for an unknown type.
    pub fn of(buf: &[u8]) -> Result<Self, WireError> {
        match buf.first() {
            None => Err(WireError::Truncated { needed: 1 }),
            Some(1) => Ok(Self::Initial),
            Some(2) => Ok(Self::ShortInitial),
            Some(3) => Ok(Self::PrekeyReject),
            Some(4) => Ok(Self::Reply),
            Some(5) => Ok(Self::Finish),
            Some(6) => Ok(Self::ResumeHello),
            Some(7) => Ok(Self::ResumeReply),
            Some(8) => Ok(Self::ResumeReject),
            Some(_) => Err(WireError::Unexpected("unknown message type")),
        }
    }
}

const TRAILING: WireError = WireError::Unexpected("trailing bytes");

fn finish(r: &Reader<'_>) -> Result<(), WireError> {
    if r.is_empty() { Ok(()) } else { Err(TRAILING) }
}

fn read_type(r: &mut Reader<'_>, want: MessageType) -> Result<(), WireError> {
    if r.read_u8()? == want as u8 {
        Ok(())
    } else {
        Err(WireError::Unexpected("wrong message type"))
    }
}

fn read_cid(r: &mut Reader<'_>) -> Result<ConnId, WireError> {
    let len = usize::from(r.read_u8()?);
    ConnId::new(r.read_bytes(len)?).ok_or(WireError::Unexpected("connection id too long"))
}

fn write_cid(w: &mut Writer<'_>, cid: &ConnId) -> Result<(), WireError> {
    w.put_u8(u8::try_from(cid.as_bytes().len()).map_err(|_| WireError::VarintOverflow)?)?;
    w.put_slice(cid.as_bytes())
}

fn read_alpn<'a>(r: &mut Reader<'a>) -> Result<&'a [u8], WireError> {
    let len = usize::from(r.read_u8()?);
    if !(1..=MAX_ALPN_LEN).contains(&len) {
        return Err(WireError::Unexpected("alpn length"));
    }
    r.read_bytes(len)
}

fn write_alpn(w: &mut Writer<'_>, alpn: &[u8]) -> Result<(), WireError> {
    w.put_u8(u8::try_from(alpn.len()).map_err(|_| WireError::VarintOverflow)?)?;
    w.put_slice(alpn)
}

fn read_aead(r: &mut Reader<'_>) -> Result<Aead, WireError> {
    aead_from_tag(r.read_u8()?).ok_or(WireError::Unexpected("unknown aead"))
}

fn read_sealed<'a>(r: &mut Reader<'a>) -> Result<&'a [u8], WireError> {
    let len = usize::from(r.read_u16()?);
    if !(Aead::TAG_LEN..=MAX_SEALED_LEN).contains(&len) {
        return Err(WireError::Unexpected("sealed length"));
    }
    r.read_bytes(len)
}

fn write_sealed(w: &mut Writer<'_>, sealed: &[u8]) -> Result<(), WireError> {
    w.put_u16(u16::try_from(sealed.len()).map_err(|_| WireError::VarintOverflow)?)?;
    w.put_slice(sealed)
}

fn read_params<'a>(r: &mut Reader<'a>) -> Result<&'a [u8], WireError> {
    let len = usize::from(r.read_u16()?);
    if len > MAX_PARAMS_LEN {
        return Err(WireError::Unexpected("transport parameters length"));
    }
    r.read_bytes(len)
}

fn write_params(w: &mut Writer<'_>, params: &[u8]) -> Result<(), WireError> {
    if params.len() > MAX_PARAMS_LEN {
        return Err(WireError::Unexpected("transport parameters length"));
    }
    w.put_u16(u16::try_from(params.len()).map_err(|_| WireError::VarintOverflow)?)?;
    w.put_slice(params)
}

fn read_array<'a, const N: usize>(r: &mut Reader<'a>) -> Result<&'a [u8; N], WireError> {
    r.read_bytes(N)?
        .try_into()
        .map_err(|_| WireError::Truncated { needed: N })
}

/// The prekey field of an Initial.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrekeyField<'a> {
    /// The ML-KEM-768 encapsulation key.
    Full(&'a [u8; KEM_ENCAPS_KEY_LEN]),
    /// The hash of the encapsulation key.
    Hash(&'a [u8; 32]),
}

/// The Initial and the short Initial (types 1 and 2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Initial<'a> {
    /// The protocol version.
    pub version: u32,
    /// The destination connection id the initiator picked at random.
    pub dcid: ConnId,
    /// The initiator's own connection id.
    pub scid: ConnId,
    /// The requested ALPN.
    pub alpn: &'a [u8],
    /// The AEADs the initiator offers.
    pub aead_offer: AeadSet,
    /// The initiator's ephemeral X25519 public key.
    pub e: [u8; 32],
    /// The prekey, or its hash.
    pub prekey: PrekeyField<'a>,
    /// The address-validation token, possibly empty.
    pub token: &'a [u8],
    /// The initiator's transport parameters, possibly empty.
    pub params: &'a [u8],
}

impl<'a> Initial<'a> {
    /// Parse an Initial of either form.
    ///
    /// # Errors
    /// A [`WireError`] for a wrong type, a length out of range, a short buffer or a trailing byte.
    pub fn parse(buf: &'a [u8]) -> Result<Self, WireError> {
        let mut r = Reader::new(buf);
        let full = match MessageType::of(buf)? {
            MessageType::Initial => true,
            MessageType::ShortInitial => false,
            _ => return Err(WireError::Unexpected("wrong message type")),
        };
        r.read_u8()?;
        let version = r.read_u32()?;
        let dcid = read_cid(&mut r)?;
        let scid = read_cid(&mut r)?;
        let alpn = read_alpn(&mut r)?;
        let aead_offer = AeadSet::from_bits(r.read_u8()?).ok_or(WireError::Unexpected("aead offer"))?;
        let e = r.read_array::<32>()?;
        let prekey = if full {
            PrekeyField::Full(read_array(&mut r)?)
        } else {
            PrekeyField::Hash(read_array(&mut r)?)
        };
        let token_len = usize::from(r.read_u8()?);
        if token_len > MAX_TOKEN_LEN {
            return Err(WireError::Unexpected("token length"));
        }
        let token = r.read_bytes(token_len)?;
        let params = read_params(&mut r)?;
        finish(&r)?;
        Ok(Self {
            version,
            dcid,
            scid,
            alpn,
            aead_offer,
            e,
            prekey,
            token,
            params,
        })
    }

    /// Append the message.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit, or a length error for a field out of range.
    pub fn write(&self, w: &mut Writer<'_>) -> Result<(), WireError> {
        w.put_u8(match self.prekey {
            PrekeyField::Full(_) => MessageType::Initial as u8,
            PrekeyField::Hash(_) => MessageType::ShortInitial as u8,
        })?;
        w.put_u32(self.version)?;
        write_cid(w, &self.dcid)?;
        write_cid(w, &self.scid)?;
        write_alpn(w, self.alpn)?;
        w.put_u8(self.aead_offer.bits())?;
        w.put_slice(&self.e)?;
        match self.prekey {
            PrekeyField::Full(k) => w.put_slice(k)?,
            PrekeyField::Hash(h) => w.put_slice(h)?,
        }
        w.put_u8(u8::try_from(self.token.len()).map_err(|_| WireError::VarintOverflow)?)?;
        w.put_slice(self.token)?;
        write_params(w, self.params)
    }

    /// The hash of the prekey, computed for the full form and read for the short form.
    pub fn prekey_hash(&self) -> [u8; 32] {
        match self.prekey {
            PrekeyField::Full(k) => prekey_hash(k),
            PrekeyField::Hash(h) => *h,
        }
    }
}

/// A reject (types 3 and 8): the first 16 bytes of the transcript hash of the message rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reject {
    /// The echo.
    pub echo: [u8; 16],
}

impl Reject {
    /// Parse a reject of type `ty`.
    ///
    /// # Errors
    /// A [`WireError`] for a wrong type, a short buffer or a trailing byte.
    pub fn parse(buf: &[u8], ty: MessageType) -> Result<Self, WireError> {
        let mut r = Reader::new(buf);
        read_type(&mut r, ty)?;
        let echo = r.read_array::<16>()?;
        finish(&r)?;
        Ok(Self { echo })
    }

    /// Append the message of type `ty`.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn write(&self, w: &mut Writer<'_>, ty: MessageType) -> Result<(), WireError> {
        w.put_u8(ty as u8)?;
        w.put_slice(&self.echo)
    }
}

/// The Reply (type 4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reply<'a> {
    /// The responder's connection id.
    pub scid: ConnId,
    /// The AEAD the responder chose.
    pub aead: Aead,
    /// The responder's ephemeral X25519 public key.
    pub e: [u8; 32],
    /// The ML-KEM-768 ciphertext.
    pub ct: &'a [u8; KEM_CIPHERTEXT_LEN],
    /// The sealed identity and signature, tag included.
    pub sealed: &'a [u8],
}

impl<'a> Reply<'a> {
    /// Parse a Reply.
    ///
    /// # Errors
    /// A [`WireError`] for a wrong type, a length out of range, a short buffer or a trailing byte.
    pub fn parse(buf: &'a [u8]) -> Result<Self, WireError> {
        let mut r = Reader::new(buf);
        read_type(&mut r, MessageType::Reply)?;
        let scid = read_cid(&mut r)?;
        let aead = read_aead(&mut r)?;
        let e = r.read_array::<32>()?;
        let ct = read_array(&mut r)?;
        let sealed = read_sealed(&mut r)?;
        finish(&r)?;
        Ok(Self {
            scid,
            aead,
            e,
            ct,
            sealed,
        })
    }

    /// Append the message.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn write(&self, w: &mut Writer<'_>) -> Result<(), WireError> {
        w.put_u8(MessageType::Reply as u8)?;
        write_cid(w, &self.scid)?;
        w.put_u8(aead_tag(self.aead))?;
        w.put_slice(&self.e)?;
        w.put_slice(self.ct)?;
        write_sealed(w, self.sealed)
    }
}

/// The Finish (type 5).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Finish<'a> {
    /// The sealed identity and signature, tag included.
    pub sealed: &'a [u8],
}

impl<'a> Finish<'a> {
    /// Parse a Finish.
    ///
    /// # Errors
    /// A [`WireError`] for a wrong type, a length out of range, a short buffer or a trailing byte.
    pub fn parse(buf: &'a [u8]) -> Result<Self, WireError> {
        let mut r = Reader::new(buf);
        read_type(&mut r, MessageType::Finish)?;
        let sealed = read_sealed(&mut r)?;
        finish(&r)?;
        Ok(Self { sealed })
    }

    /// Append the message.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn write(&self, w: &mut Writer<'_>) -> Result<(), WireError> {
        w.put_u8(MessageType::Finish as u8)?;
        write_sealed(w, self.sealed)
    }
}

/// The resume Hello (type 6).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResumeHello<'a> {
    /// The protocol version.
    pub version: u32,
    /// The destination connection id the initiator picked at random.
    pub dcid: ConnId,
    /// The initiator's own connection id.
    pub scid: ConnId,
    /// The requested ALPN.
    pub alpn: &'a [u8],
    /// The AEAD of the ticket's session.
    pub aead: Aead,
    /// The ticket id.
    pub tid: [u8; 16],
    /// The initiator's ephemeral X25519 public key.
    pub e: [u8; 32],
    /// The binder over the transcript.
    pub binder: [u8; 32],
    /// The initiator's transport parameters, possibly empty.
    pub params: &'a [u8],
}

impl<'a> ResumeHello<'a> {
    /// Parse a resume Hello.
    ///
    /// # Errors
    /// A [`WireError`] for a wrong type, a length out of range, a short buffer or a trailing byte.
    pub fn parse(buf: &'a [u8]) -> Result<Self, WireError> {
        let mut r = Reader::new(buf);
        read_type(&mut r, MessageType::ResumeHello)?;
        let version = r.read_u32()?;
        let dcid = read_cid(&mut r)?;
        let scid = read_cid(&mut r)?;
        let alpn = read_alpn(&mut r)?;
        let aead = read_aead(&mut r)?;
        let tid = r.read_array::<16>()?;
        let e = r.read_array::<32>()?;
        let binder = r.read_array::<32>()?;
        let params = read_params(&mut r)?;
        finish(&r)?;
        Ok(Self {
            version,
            dcid,
            scid,
            alpn,
            aead,
            tid,
            e,
            binder,
            params,
        })
    }

    /// Append the message.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn write(&self, w: &mut Writer<'_>) -> Result<(), WireError> {
        w.put_u8(MessageType::ResumeHello as u8)?;
        w.put_u32(self.version)?;
        write_cid(w, &self.dcid)?;
        write_cid(w, &self.scid)?;
        write_alpn(w, self.alpn)?;
        w.put_u8(aead_tag(self.aead))?;
        w.put_slice(&self.tid)?;
        w.put_slice(&self.e)?;
        w.put_slice(&self.binder)?;
        write_params(w, self.params)
    }
}

/// The resume Reply (type 7).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResumeReply {
    /// The responder's connection id.
    pub scid: ConnId,
    /// The responder's ephemeral X25519 public key.
    pub e: [u8; 32],
    /// The new tickets.
    pub tickets: TicketBatch,
    /// The responder's transport parameters.
    pub params: Params,
    /// The confirmation tag.
    pub confirm: [u8; 32],
}

impl ResumeReply {
    /// Parse a resume Reply.
    ///
    /// # Errors
    /// A [`WireError`] for a wrong type, a length out of range, a short buffer or a trailing byte.
    pub fn parse(buf: &[u8]) -> Result<Self, WireError> {
        let mut r = Reader::new(buf);
        read_type(&mut r, MessageType::ResumeReply)?;
        let scid = read_cid(&mut r)?;
        let e = r.read_array::<32>()?;
        let tickets = TicketBatch::read(&mut r)?;
        let params = Params::new(read_params(&mut r)?).ok_or(WireError::Unexpected("transport parameters length"))?;
        let confirm = r.read_array::<32>()?;
        finish(&r)?;
        Ok(Self {
            scid,
            e,
            tickets,
            params,
            confirm,
        })
    }

    /// Append the message.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn write(&self, w: &mut Writer<'_>) -> Result<(), WireError> {
        w.put_u8(MessageType::ResumeReply as u8)?;
        write_cid(w, &self.scid)?;
        w.put_slice(&self.e)?;
        self.tickets.write(w)?;
        write_params(w, self.params.as_bytes())?;
        w.put_slice(&self.confirm)
    }
}

/// The identity and signature a Reply or a Finish seals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IdSig<'a> {
    /// The identity algorithm.
    pub alg: IdentityAlg,
    /// The public key, exactly [`IdentityAlg::public_key_len`] bytes.
    pub public_key: &'a [u8],
    /// The signature, exactly [`IdentityAlg::signature_len`] bytes.
    pub signature: &'a [u8],
    /// The sender's transport parameters (the responder's; empty in a Finish).
    pub params: &'a [u8],
}

impl<'a> IdSig<'a> {
    /// Parse the plaintext of a sealed identity and signature.
    ///
    /// # Errors
    /// A [`WireError`] for an unknown algorithm, a key or signature of the wrong length, a short buffer or a
    /// trailing byte.
    pub fn parse(plain: &'a [u8]) -> Result<Self, WireError> {
        let mut r = Reader::new(plain);
        let alg = IdentityAlg::from_tag(r.read_u8()?).ok_or(WireError::Unexpected("unknown identity algorithm"))?;
        let pk_len = usize::from(r.read_u16()?);
        if pk_len != alg.public_key_len() {
            return Err(WireError::Unexpected("public key length"));
        }
        let public_key = r.read_bytes(pk_len)?;
        let sig_len = usize::from(r.read_u16()?);
        if sig_len != alg.signature_len() {
            return Err(WireError::Unexpected("signature length"));
        }
        let signature = r.read_bytes(sig_len)?;
        let params = read_params(&mut r)?;
        finish(&r)?;
        Ok(Self {
            alg,
            public_key,
            signature,
            params,
        })
    }

    /// Append the plaintext.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn write(&self, w: &mut Writer<'_>) -> Result<(), WireError> {
        w.put_u8(self.alg.tag())?;
        w.put_u16(u16::try_from(self.public_key.len()).map_err(|_| WireError::VarintOverflow)?)?;
        w.put_slice(self.public_key)?;
        w.put_u16(u16::try_from(self.signature.len()).map_err(|_| WireError::VarintOverflow)?)?;
        w.put_slice(self.signature)?;
        write_params(w, self.params)
    }
}
