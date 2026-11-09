//! The key roll: how a running session replaces its traffic keys without a new handshake.
//!
//! A roll mixes a fresh Diffie-Hellman value into both directions' secrets, so a party that stole the old secrets
//! but is not on the path now cannot derive the new keys: `next = roll_secret(secret, dh)`, where
//! `roll_secret(secret, dh) = expand(extract(secret, dh), "key roll")`. There is no hash-only successor of a key.
//!
//! # The exchange
//!
//! Two REKEY messages, carried by the transport in a frame:
//!
//! 1. the side whose key is due sends a *request*: a fresh X25519 public value;
//! 2. the peer answers with its own fresh public value, the identifier of the request it answers (the *echo*) and the
//!    packet number at which it switches to the new keys (the first number it seals under them);
//! 3. both sides compute `dh = X25519(own secret, other public)`, bind the echo into it (`extract(dh, echo)`) and
//!    roll both directions with the result. The side that
//!    answered switches at its announced number; the side that requested switches at its next packet after the
//!    answer. The packet header's phase bit marks the first packet under the new keys; the old keys stay for one
//!    probe timeout for packets that arrive late.
//!
//! # Wire form of a REKEY body
//!
//! `kind(1)`: 0 request, 1 answer; `share(32)`: the sender's X25519 public value; for an answer only,
//! `echo(8)`, the first eight bytes of the hash of the request's share ([`request_id`]), and `switch_pn(varint)`. A
//! request is 33 bytes, an answer 42 to 50. The frame type that carries it belongs to the transport's frame codec.
//!
//! # State machine
//!
//! [`Roll`] holds one roll at a time. If both sides ask at once, the dialing side's request wins and the other side
//! drops its own and answers. A duplicate request (the answer was lost) gets the same answer again and no new
//! key. A request is sent again until it is answered ([`Roll::pending`]). Invariants: no I/O, clock or randomness
//! of its own; the Diffie-Hellman secret never leaves [`Roll`]; each request share is used for one roll.

use vinc_crypto::{Provider, Secret, Transcript, ct_eq};
use vinc_wire::{Reader, WireError, Writer};
use zeroize::Zeroize;

use crate::error::Failure;
use crate::labels;
use crate::record::PacketKey;
use crate::schedule::chain;
use crate::session::Env;

/// A key older than this many nanoseconds (10 minutes) is rolled, whatever it sealed.
pub const MAX_KEY_AGE_NS: u64 = 600 * 1_000_000_000;
/// The length of the identifier an answer echoes.
pub const ECHO_LEN: usize = 8;
/// The longest REKEY body.
pub const MAX_REKEY_LEN: usize = 1 + 32 + ECHO_LEN + vinc_wire::varint::MAX_LEN;

/// The identifier of a request: the first [`ECHO_LEN`] bytes of the hash of its share. An answer carries it and
/// binds it into the key derivation.
pub fn request_id(share: &[u8; 32]) -> [u8; ECHO_LEN] {
    let mut t = Transcript::with_label(labels::KEY_ROLL_ID);
    t.absorb(share);
    let mut id = [0u8; ECHO_LEN];
    id.iter_mut().zip(t.snapshot()).for_each(|(o, h)| *o = h);
    id
}

/// The Diffie-Hellman value with the request identifier bound in: `extract(dh, id)`.
fn bind(dh: &Secret<32>, id: [u8; ECHO_LEN]) -> Secret<32> {
    chain(dh, &id)
}

/// One REKEY message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rekey {
    /// Whether this answers a request.
    pub answer: bool,
    /// The sender's fresh X25519 public value.
    pub share: [u8; 32],
    /// For an answer: the identifier of the request it answers ([`request_id`]). Zero in a request.
    pub echo: [u8; ECHO_LEN],
    /// For an answer: the first packet number the sender seals under the new keys. Zero in a request.
    pub switch_pn: u64,
}

impl Rekey {
    /// Append the body.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit; [`WireError::VarintOverflow`] for a switch number of 2^63
    /// or more.
    pub fn write(&self, w: &mut Writer<'_>) -> Result<(), WireError> {
        w.put_u8(u8::from(self.answer))?;
        w.put_slice(&self.share)?;
        if self.answer {
            w.put_slice(&self.echo)?;
            w.put_varint(self.switch_pn)?;
        }
        Ok(())
    }

    /// Read a body from the front of `r`, leaving what follows.
    ///
    /// # Errors
    /// A [`WireError`] for an unknown kind or a short body.
    pub fn read(r: &mut Reader<'_>) -> Result<Self, WireError> {
        let answer = match r.read_u8()? {
            0 => false,
            1 => true,
            _ => return Err(WireError::Unexpected("rekey kind")),
        };
        let share = r.read_array::<32>()?;
        let (echo, switch_pn) = if answer {
            (r.read_array::<ECHO_LEN>()?, r.read_varint()?)
        } else {
            ([0; ECHO_LEN], 0)
        };
        Ok(Self {
            answer,
            share,
            echo,
            switch_pn,
        })
    }

    /// The body as bytes in `buf`, and their count.
    ///
    /// # Errors
    /// As [`Rekey::write`].
    pub fn encode(&self, buf: &mut [u8]) -> Result<usize, WireError> {
        let mut w = Writer::new(buf);
        self.write(&mut w)?;
        Ok(w.written().len())
    }

    /// Parse a body that fills `buf` exactly.
    ///
    /// # Errors
    /// A [`WireError`] for an unknown kind, a short buffer or a trailing byte.
    pub fn decode(buf: &[u8]) -> Result<Self, WireError> {
        let mut r = Reader::new(buf);
        let rekey = Self::read(&mut r)?;
        if r.is_empty() {
            Ok(rekey)
        } else {
            Err(WireError::Unexpected("trailing bytes"))
        }
    }
}

/// What answering a request produced.
#[derive(Debug)]
pub struct Answered {
    /// The answer to send.
    pub answer: Rekey,
    /// The Diffie-Hellman value to roll with; `None` for a duplicate request (the keys already rolled).
    pub dh: Option<Secret<32>>,
}

/// What a received answer produced.
#[derive(Debug)]
pub struct Completed {
    /// The Diffie-Hellman value to roll with.
    pub dh: Secret<32>,
    /// The first packet number the peer seals under the new keys.
    pub peer_switch_pn: u64,
}

enum State {
    Idle,
    /// A request is out, waiting for the answer.
    Requested {
        seed: Secret<32>,
        request: Rekey,
    },
}

/// The roll state machine of one connection.
pub struct Roll {
    dialer: bool,
    state: State,
    /// The last request answered and the answer given, to repeat it for a duplicate request.
    last: Option<([u8; 32], Rekey)>,
    rolls: u64,
}

impl core::fmt::Debug for Roll {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Roll")
            .field("dialer", &self.dialer)
            .field("rolls", &self.rolls)
            .finish_non_exhaustive()
    }
}

impl Roll {
    /// A machine for the dialing (`dialer`) or the accepting side.
    pub const fn new(dialer: bool) -> Self {
        Self {
            dialer,
            state: State::Idle,
            last: None,
            rolls: 0,
        }
    }

    /// Whether no roll is under way.
    pub const fn is_idle(&self) -> bool {
        matches!(self.state, State::Idle)
    }

    /// The share of the last request answered and the answer given.
    #[cfg(feature = "trace")]
    pub const fn last_answered(&self) -> Option<([u8; 32], Rekey)> {
        self.last
    }

    /// How many rolls completed.
    pub const fn rolls(&self) -> u64 {
        self.rolls
    }

    /// Whether `request` repeats the last request answered: the answer is sent again and no key changes.
    pub fn is_duplicate(&self, request: &Rekey) -> bool {
        !request.answer
            && self
                .last
                .as_ref()
                .is_some_and(|(share, _)| ct_eq(share, &request.share))
    }

    /// The request to send (again) while one is waiting for its answer.
    pub const fn pending(&self) -> Option<Rekey> {
        match &self.state {
            State::Requested { request, .. } => Some(*request),
            State::Idle => None,
        }
    }

    /// Begin a roll: a fresh X25519 value and the request that carries it.
    ///
    /// # Errors
    /// [`Failure::UnexpectedMessage`] if a roll is already under way; [`Failure::Randomness`] if the generator
    /// refuses.
    pub fn start<P: Provider>(&mut self, env: &mut Env<'_, P>) -> Result<Rekey, Failure> {
        if !self.is_idle() {
            return Err(Failure::UnexpectedMessage);
        }
        let mut seed = env.random::<32>()?;
        let p = env.provider;
        let request = Rekey {
            answer: false,
            share: p.x25519_public(&p.x25519_secret(&seed)),
            echo: [0; ECHO_LEN],
            switch_pn: 0,
        };
        self.state = State::Requested {
            seed: Secret::new(seed),
            request,
        };
        seed.zeroize();
        Ok(request)
    }

    /// Answer a request. `switch_pn` is the first packet number this side will seal under the new keys.
    ///
    /// If this side has its own request out, the dialer's wins: the dialing side ignores the peer's request, the
    /// accepting side drops its own and answers.
    ///
    /// # Errors
    /// [`Failure::UnexpectedMessage`] for an answer, or for a request the dialing side ignores;
    /// [`Failure::InvalidPeerKey`] for a share that gives no shared secret; [`Failure::Randomness`] if the
    /// generator refuses.
    pub fn on_request<P: Provider>(
        &mut self,
        env: &mut Env<'_, P>,
        request: &Rekey,
        switch_pn: u64,
    ) -> Result<Answered, Failure> {
        if request.answer {
            return Err(Failure::UnexpectedMessage);
        }
        if self.is_duplicate(request)
            && let Some((_, answer)) = &self.last
        {
            return Ok(Answered {
                answer: *answer,
                dh: None,
            });
        }
        if !self.is_idle() {
            if self.dialer {
                return Err(Failure::UnexpectedMessage);
            }
            self.state = State::Idle;
        }
        let mut seed = env.random::<32>()?;
        let p = env.provider;
        let secret = p.x25519_secret(&seed);
        seed.zeroize();
        let echo = request_id(&request.share);
        let dh = bind(
            &p.x25519_dh(&secret, &request.share)
                .map_err(|_| Failure::InvalidPeerKey)?,
            echo,
        );
        let answer = Rekey {
            answer: true,
            share: p.x25519_public(&secret),
            echo,
            switch_pn,
        };
        self.last = Some((request.share, answer));
        self.rolls = self.rolls.saturating_add(1);
        Ok(Answered { answer, dh: Some(dh) })
    }

    /// Take the answer to the request that is out.
    ///
    /// # Errors
    /// [`Failure::UnexpectedMessage`] for a request, when no request is out, or when the answer echoes another
    /// request (a stale or repeated answer; nothing changes);
    /// [`Failure::InvalidPeerKey`] for a share that gives no shared secret.
    pub fn on_answer<P: Provider>(&mut self, env: &Env<'_, P>, answer: &Rekey) -> Result<Completed, Failure> {
        if !answer.answer {
            return Err(Failure::UnexpectedMessage);
        }
        let State::Requested { seed, request } = &self.state else {
            return Err(Failure::UnexpectedMessage);
        };
        let id = request_id(&request.share);
        if !ct_eq(&answer.echo, &id) {
            return Err(Failure::UnexpectedMessage);
        }
        let p = env.provider;
        let dh = bind(
            &p.x25519_dh(&p.x25519_secret(seed.expose()), &answer.share)
                .map_err(|_| Failure::InvalidPeerKey)?,
            id,
        );
        self.state = State::Idle;
        self.last = None;
        self.rolls = self.rolls.saturating_add(1);
        Ok(Completed {
            dh,
            peer_switch_pn: answer.switch_pn,
        })
    }
}

/// When to roll: the keys of one connection direction pair, their age and the proactive packet count.
///
/// True when either key reached its AEAD limit ([`PacketKey::limit_reached`]: 2^22 AES-GCM packets sealed, or the
/// ChaCha20-Poly1305 failed-open count), when the sending key sealed `after` packets (a count at or below the AEAD
/// limit that keeps the roll ahead of it), or when the keys are [`MAX_KEY_AGE_NS`] old.
pub fn due<P: Provider>(send: &PacketKey<P>, recv: &PacketKey<P>, age_ns: u64, after: u64) -> bool {
    send.limit_reached() || recv.limit_reached() || send.sealed() >= after || age_ns >= MAX_KEY_AGE_NS
}
