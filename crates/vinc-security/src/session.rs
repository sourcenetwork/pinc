//! What the state machines take in and hand out: the environment, the outputs and the established session.
//!
//! Invariants: the machines never read a clock or a random source themselves. They take both through [`Env`]: `now`
//! in nanoseconds (the caller's own monotonic or wall clock, used only to compare against ticket and prekey
//! expiry) and a [`Drbg`] the caller owns. Every secret in an event is a zeroizing [`Secret`]. [`Traffic`] holds the
//! two directional application secrets of a session; the record keys derive from them.

use vinc_crypto::{Aead, CryptoError, Drbg, NodeId, Provider, Secret};

use crate::credit::CreditRecord;
use crate::error::Failure;
use crate::ids::Alpn;
use crate::keys::KeyRequest;
use crate::record::{HeaderKey, PacketKey};
use crate::schedule::sub_session_secret;
use crate::tickets::TicketBatch;

/// What a call into a state machine may use from the host.
#[derive(Debug)]
pub struct Env<'a, P: Provider> {
    /// The cryptographic provider.
    pub provider: &'a P,
    /// The current time in nanoseconds, compared against ticket and prekey expiry.
    pub now: u64,
    /// The random generator, seeded by the caller.
    pub drbg: &'a mut Drbg,
}

impl<P: Provider> Env<'_, P> {
    /// `N` random bytes from the generator.
    ///
    /// # Errors
    /// [`Failure::Randomness`] if the generator refuses.
    pub fn random<const N: usize>(&mut self) -> Result<[u8; N], Failure> {
        let mut out = [0u8; N];
        self.drbg.fill(&mut out).map_err(|_| Failure::Randomness)?;
        Ok(out)
    }
}

/// The two directional application secrets of a session, and its AEAD.
#[derive(Debug, Clone)]
pub struct Traffic {
    /// The AEAD both directions use.
    pub aead: Aead,
    /// The secret of packets this side sends.
    pub send: Secret<32>,
    /// The secret of packets this side receives.
    pub recv: Secret<32>,
}

/// The record keys of one direction: the packet key (updatable) and the header key (fixed).
#[derive(Debug)]
pub struct Protection<P: Provider> {
    /// The packet-protection key, generation 0.
    pub packet: PacketKey<P>,
    /// The header-protection key.
    pub header: HeaderKey<P>,
}

impl Traffic {
    /// The keys for packets this side sends.
    ///
    /// # Errors
    /// [`CryptoError::InvalidLength`] if the provider refuses a derived key.
    pub fn send_keys<P: Provider>(&self, p: &P) -> Result<Protection<P>, CryptoError> {
        Self::keys(p, self.aead, &self.send)
    }

    /// The keys for packets this side receives.
    ///
    /// # Errors
    /// [`CryptoError::InvalidLength`] if the provider refuses a derived key.
    pub fn recv_keys<P: Provider>(&self, p: &P) -> Result<Protection<P>, CryptoError> {
        Self::keys(p, self.aead, &self.recv)
    }

    fn keys<P: Provider>(p: &P, aead: Aead, secret: &Secret<32>) -> Result<Protection<P>, CryptoError> {
        Ok(Protection {
            packet: PacketKey::from_secret(p, aead, secret)?,
            header: HeaderKey::from_secret(p, aead, secret)?,
        })
    }

    /// The traffic of a sub-session: both directional secrets become `expand(parent, "sub session", H(alpn, cc,
    /// cs))`. The peer derives the same from the same arguments, so no round trip is needed; the open frame that
    /// carries `cc` and `cs` travels inside the parent's protected channel.
    #[must_use]
    pub fn sub_session(&self, alpn: &[u8], cc: &[u8], cs: &[u8]) -> Self {
        Self {
            aead: self.aead,
            send: sub_session_secret(&self.send, alpn, cc, cs),
            recv: sub_session_secret(&self.recv, alpn, cc, cs),
        }
    }
}

/// The keys of a 0-RTT flight, derived from the ticket's pre-shared key.
#[derive(Debug, Clone)]
pub struct EarlyKeys {
    /// The AEAD of the ticket's session.
    pub aead: Aead,
    /// The 0-RTT traffic secret: the initiator sends with it, the responder receives with it.
    pub secret: Secret<32>,
}

/// A completed handshake.
#[derive(Debug, Clone)]
pub struct Established {
    /// The authenticated peer.
    pub peer: NodeId,
    /// The negotiated ALPN.
    pub alpn: Alpn,
    /// The application secrets of this session.
    pub traffic: Traffic,
    /// The resumption secret, from which the tickets of this session derive.
    pub resume: Secret<32>,
    /// The tickets issued during the handshake: the new tickets of a resumption, and on the responder the tickets
    /// of a full handshake. Empty otherwise.
    pub tickets: TicketBatch,
    /// Whether this session resumed an earlier one.
    pub resumed: bool,
    /// The credit record the peer sent in the handshake, authenticated by it.
    pub peer_credit: CreditRecord,
    /// The credit record this side sent.
    pub local_credit: CreditRecord,
    /// On a resumption: the issuer's credit record that the ticket remembered (what 0-RTT data may rely on);
    /// [`CreditRecord::NONE`] otherwise.
    pub remembered_credit: CreditRecord,
    /// The secret both sides derive their connection ids from; the same on both sides and fresh for every session.
    pub cid_secret: Secret<32>,
}

/// Something that happened.
#[derive(Debug, Clone)]
#[allow(
    clippy::large_enum_variant,
    reason = "events are returned by value; boxing would allocate"
)]
pub enum Event {
    /// The 0-RTT keys are ready.
    EarlyKeys(EarlyKeys),
    /// The handshake completed.
    Established(Established),
    /// The responder did not accept the ticket: 0-RTT data was not accepted either, and a full handshake follows.
    ResumeRejected,
    /// The handshake failed.
    Failed(Failure),
}

/// The next thing a state machine wants done.
#[derive(Debug)]
#[allow(
    clippy::large_enum_variant,
    reason = "outputs are returned by value; boxing would allocate"
)]
pub enum Output<'a> {
    /// Send this handshake message. The transport pads the datagrams that carry it to at least `min_len` bytes
    /// (0 means no padding is needed).
    Send {
        /// The message.
        data: &'a [u8],
        /// The least total size of the datagrams carrying it.
        min_len: usize,
    },
    /// Perform this key operation and answer with `on_key_response`.
    Key(KeyRequest<'a>),
    /// Something happened.
    Event(Event),
}
