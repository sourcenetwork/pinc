//! The protected carrier: a byte-stream session that handshakes to the peer's identity and then carries frames in
//! record protection.
//!
//! A [`ProtectedCarrier`] is a SANS-IO state machine over one ordered byte stream. The host pushes received bytes with
//! [`ProtectedCarrier::receive`], calls [`ProtectedCarrier::poll`] until it says [`Poll::Idle`], writes whatever
//! [`ProtectedCarrier::transmit`] yields, and seals outgoing frames with [`ProtectedCarrier::seal`]. The framing is
//! described in [the module above](super).
//!
//! Invariants:
//! - The peer is authenticated by the VINC handshake before the first frame is accepted: [`Poll::Frame`] is never
//!   returned before [`Poll::Open`], and [`Poll::Open`] carries the node id the handshake proved. A dialer names the
//!   relay it expects, and the handshake fails if another node answers.
//! - A record that fails authentication, a unit of the wrong size or a failed handshake ends the carrier for good:
//!   every later call returns [`CarrierError::Closed`] and the host closes the stream.
//! - A frame inside an authenticated record that does not decode is dropped and reported
//!   ([`CarrierError::Frame`]); the carrier stays usable.
//! - Packet numbers count records per direction from 0 and are never reused; a key that reaches its usage limit
//!   ends the carrier ([`CarrierError::KeyLimit`]) and the dialer reconnects with a fresh handshake.
//! - All buffers are inline and bounded; nothing allocates and nothing reads a clock or a random source (the
//!   handshake takes both through [`Env`]).

use core::fmt;

use vinc_crypto::{Aead, NodeId, Provider};
use vinc_security::message::MAX_MESSAGE_LEN;
use vinc_security::{
    AlpnList, ConnId, Env, Established, Event, Failure, Initiator, InitiatorParams, LocalIdentity, Output, PacketKey,
    RecordError, Responder, ResponderConfig, ResponderStores, SoftKeys,
};

use super::frame::{Frame, FrameError, MAX_FRAME_LEN};

/// The application protocol name both ends of a carrier handshake use.
pub const ALPN: &[u8] = b"vinc-carrier/1";
/// The longest unit after the 2-byte length: a record of the longest frame and its tag.
pub const MAX_UNIT_LEN: usize = MAX_FRAME_LEN + Aead::TAG_LEN;
/// The size of the inbound buffer.
pub const IN_LEN: usize = 2 + if MAX_UNIT_LEN > MAX_MESSAGE_LEN {
    MAX_UNIT_LEN
} else {
    MAX_MESSAGE_LEN
};
/// The size of the buffered handshake output: two full messages with their length prefixes.
pub const OUT_LEN: usize = 2 * (2 + MAX_MESSAGE_LEN);

const STEPS: usize = 8;

/// A responder configuration for a relay: serves [`ALPN`] and issues no resumption tickets.
///
/// # Errors
/// [`Failure::InvalidParameter`] if [`ALPN`] is not a valid protocol name (it always is).
pub fn responder_config(identity: LocalIdentity, scid: ConnId) -> Result<ResponderConfig, Failure> {
    let alpns = AlpnList::new(&[ALPN]).ok_or(Failure::InvalidParameter)?;
    let mut cfg = ResponderConfig::new(identity, scid, alpns);
    cfg.tickets_per_session = 0;
    Ok(cfg)
}

/// Why the carrier refused something.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CarrierError {
    /// The handshake failed or the peer sent a message that does not belong.
    Handshake(Failure),
    /// A unit is empty, too long, or its length is wrong for its kind.
    UnitSize,
    /// A record did not authenticate.
    Authentication,
    /// The packet key reached its usage limit.
    KeyLimit,
    /// A frame was sealed before the handshake completed.
    NotOpen,
    /// The handshake output buffer is full: call [`ProtectedCarrier::transmit`] more often.
    OutputFull,
    /// The output buffer given to [`ProtectedCarrier::seal`] is too small.
    NoRoom,
    /// A record carried a frame that does not decode; the record is dropped and the carrier lives on.
    Frame(FrameError),
    /// The primitive refused its input.
    Record(RecordError),
    /// The carrier already ended.
    Closed,
}

impl CarrierError {
    /// Whether the carrier ended: the host closes the stream.
    pub const fn is_fatal(&self) -> bool {
        !matches!(self, Self::Frame(_) | Self::NoRoom | Self::NotOpen | Self::OutputFull)
    }
}

impl fmt::Display for CarrierError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Handshake(e) => write!(f, "carrier handshake failed: {e}"),
            Self::UnitSize => f.write_str("carrier unit has an invalid size"),
            Self::Authentication => f.write_str("carrier record failed authentication"),
            Self::KeyLimit => f.write_str("carrier key reached its usage limit"),
            Self::NotOpen => f.write_str("carrier handshake has not completed"),
            Self::OutputFull => f.write_str("carrier handshake output is full"),
            Self::NoRoom => f.write_str("output buffer is too small"),
            Self::Frame(e) => write!(f, "carrier frame dropped: {e}"),
            Self::Record(e) => write!(f, "{e}"),
            Self::Closed => f.write_str("carrier already ended"),
        }
    }
}

impl core::error::Error for CarrierError {}

/// What a call to [`ProtectedCarrier::poll`] found.
#[derive(Debug)]
pub enum Poll<'a> {
    /// More bytes are needed.
    Idle,
    /// A handshake message was processed: call [`ProtectedCarrier::transmit`], then poll again.
    Handshake,
    /// The handshake completed; the peer is this authenticated node.
    Open(NodeId),
    /// A decoded frame, valid until the next call on the carrier.
    Frame(Frame<'a>),
}

#[allow(
    clippy::large_enum_variant,
    reason = "the machines live inline; boxing would allocate"
)]
enum Stage {
    Dialing(Initiator),
    Accepting(Responder),
    Open,
    Ended,
}

/// One end of a protected carrier.
pub struct ProtectedCarrier<P: Provider> {
    stage: Stage,
    send: Option<PacketKey<P>>,
    recv: Option<PacketKey<P>>,
    send_pn: u64,
    recv_pn: u64,
    peer: Option<NodeId>,
    input: [u8; IN_LEN],
    in_len: usize,
    consume: usize,
    out: [u8; OUT_LEN],
    out_len: usize,
}

impl<P: Provider> fmt::Debug for ProtectedCarrier<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ProtectedCarrier")
            .field("open", &matches!(self.stage, Stage::Open))
            .field("peer", &self.peer)
            .finish_non_exhaustive()
    }
}

/// Append handshake messages and collect the outcome of draining one machine.
macro_rules! drive {
    ($m:expr, $env:expr, $soft:expr, $out:expr, $out_len:expr) => {{
        let mut result: Result<Option<Established>, CarrierError> = Ok(None);
        if let Some(soft) = $soft {
            for _ in 0..STEPS {
                match $m.answer_soft($env, soft) {
                    Ok(true) => {}
                    Ok(false) => break,
                    Err(f) => {
                        result = Err(CarrierError::Handshake(f));
                        break;
                    }
                }
            }
        }
        while let Some(o) = $m.poll_output() {
            match o {
                Output::Send { data, .. } => {
                    let unit = u16::try_from(data.len()).map_err(|_| CarrierError::UnitSize);
                    let end = $out_len.saturating_add(2).saturating_add(data.len());
                    match (unit, $out.get_mut(*$out_len..end)) {
                        (Ok(n), Some(slot)) => {
                            let (head, body) = slot.split_at_mut(2);
                            head.copy_from_slice(&n.to_be_bytes());
                            body.copy_from_slice(data);
                            *$out_len = end;
                        }
                        (Err(e), _) => result = Err(e),
                        (_, None) => result = Err(CarrierError::OutputFull),
                    }
                }
                Output::Event(Event::Established(e)) => {
                    if result.is_ok() {
                        result = Ok(Some(e));
                    }
                }
                Output::Event(Event::Failed(f)) => result = Err(CarrierError::Handshake(f)),
                Output::Event(_) | Output::Key(_) => {}
            }
        }
        result
    }};
}

impl<P: Provider> ProtectedCarrier<P> {
    #[allow(
        clippy::large_stack_arrays,
        reason = "the buffers are inline by design; the host boxes the carrier if its stack is small"
    )]
    fn with(stage: Stage) -> Self {
        Self {
            stage,
            send: None,
            recv: None,
            send_pn: 0,
            recv_pn: 0,
            peer: None,
            input: [0; IN_LEN],
            in_len: 0,
            consume: 0,
            out: [0; OUT_LEN],
            out_len: 0,
        }
    }

    /// Start a dialer: queue the first handshake message toward `params.peer`, the relay's node id. The ALPN in
    /// `params` should be [`ALPN`].
    ///
    /// # Errors
    /// [`CarrierError::Handshake`] if the machine refuses the parameters or the generator fails.
    pub fn dial(env: &mut Env<'_, P>, params: InitiatorParams<'_>) -> Result<Self, CarrierError> {
        let mut m = Initiator::new(env, params).map_err(CarrierError::Handshake)?;
        let mut this = Self::with(Stage::Ended);
        let none: Option<&SoftKeys<'_, P>> = None;
        drive!(m, env, none, this.out, &mut this.out_len)?;
        this.stage = Stage::Dialing(m);
        Ok(this)
    }

    /// Start a listener with this configuration (see [`responder_config`]).
    pub fn accept(cfg: ResponderConfig) -> Self {
        Self::with(Stage::Accepting(Responder::new(cfg)))
    }

    /// Whether the handshake completed and the carrier has not ended.
    pub const fn is_open(&self) -> bool {
        matches!(self.stage, Stage::Open)
    }

    /// Whether the carrier ended; the host closes the stream.
    pub const fn is_ended(&self) -> bool {
        matches!(self.stage, Stage::Ended)
    }

    /// The authenticated peer, once open.
    pub const fn peer(&self) -> Option<NodeId> {
        self.peer
    }

    /// How many bytes [`ProtectedCarrier::receive`] would take now.
    pub const fn free(&self) -> usize {
        IN_LEN - self.in_len
    }

    /// Buffer received stream bytes and return how many were taken. Offer the rest again after polling: this is the
    /// backpressure of the bounded buffer.
    pub fn receive(&mut self, bytes: &[u8]) -> usize {
        self.release();
        let n = bytes.len().min(self.free());
        if let (Some(dst), Some(src)) = (self.input.get_mut(self.in_len..self.in_len + n), bytes.get(..n)) {
            dst.copy_from_slice(src);
            self.in_len += n;
        }
        n
    }

    /// Copy pending handshake bytes into `out` and return how many; call until it returns 0 after each poll.
    pub fn transmit(&mut self, out: &mut [u8]) -> usize {
        let n = out.len().min(self.out_len);
        if let (Some(dst), Some(src)) = (out.get_mut(..n), self.out.get(..n)) {
            dst.copy_from_slice(src);
        }
        self.out.copy_within(n..self.out_len, 0);
        self.out_len -= n;
        n
    }

    /// Bytes of handshake output waiting for [`ProtectedCarrier::transmit`].
    pub const fn pending_transmit(&self) -> usize {
        self.out_len
    }

    fn release(&mut self) {
        if self.consume > 0 {
            self.input.copy_within(self.consume..self.in_len, 0);
            self.in_len -= self.consume;
            self.consume = 0;
        }
    }

    fn end(&mut self, e: CarrierError) -> CarrierError {
        self.stage = Stage::Ended;
        self.send = None;
        self.recv = None;
        e
    }

    /// Process the next unit.
    ///
    /// `stores` and `soft` serve the listener's handshake (the dialer ignores `stores`); `soft` answers the key
    /// operations the handshake needs, so the identity key must be a software key.
    ///
    /// # Errors
    /// A [`CarrierError`]; [`CarrierError::is_fatal`] says whether the carrier ended.
    // vertexia: software keys only; a host with a TPM or HSM needs the machines' key requests passed through
    pub fn poll<const PK: usize, const TK: usize>(
        &mut self,
        env: &mut Env<'_, P>,
        stores: &mut ResponderStores<PK, TK>,
        soft: &SoftKeys<'_, P>,
    ) -> Result<Poll<'_>, CarrierError> {
        self.release();
        if matches!(self.stage, Stage::Ended) {
            return Err(CarrierError::Closed);
        }
        if matches!(self.stage, Stage::Open) {
            return self.poll_record(env.provider);
        }
        let Some(len) = self.unit_len(MAX_MESSAGE_LEN)? else {
            return Ok(Poll::Idle);
        };
        let end = 2 + len;
        let outcome = {
            let msg = self.input.get(2..end).unwrap_or_default();
            match &mut self.stage {
                Stage::Dialing(m) => m
                    .handle(env, msg)
                    .map_err(CarrierError::Handshake)
                    .and_then(|()| drive!(m, env, Some(soft), self.out, &mut self.out_len)),
                Stage::Accepting(m) => m
                    .handle(env, stores, msg)
                    .map_err(CarrierError::Handshake)
                    .and_then(|()| drive!(m, env, Some(soft), self.out, &mut self.out_len)),
                Stage::Open | Stage::Ended => Err(CarrierError::Closed),
            }
        };
        self.consume = end;
        match outcome {
            Err(e) => Err(self.end(e)),
            Ok(None) => Ok(Poll::Handshake),
            Ok(Some(est)) => {
                let keys = est
                    .traffic
                    .send_keys(env.provider)
                    .and_then(|s| est.traffic.recv_keys(env.provider).map(|r| (s, r)));
                match keys {
                    Ok((s, r)) => {
                        self.send = Some(s.packet);
                        self.recv = Some(r.packet);
                        self.peer = Some(est.peer);
                        self.stage = Stage::Open;
                        Ok(Poll::Open(est.peer))
                    }
                    Err(e) => Err(self.end(CarrierError::Handshake(Failure::Crypto(e)))),
                }
            }
        }
    }

    /// The length field of the next unit if the whole unit is buffered, validated against `max`.
    fn unit_len(&mut self, max: usize) -> Result<Option<usize>, CarrierError> {
        let Some(&[a, b]) = self.input.first_chunk::<2>().filter(|_| self.in_len >= 2) else {
            return Ok(None);
        };
        let len = usize::from(u16::from_be_bytes([a, b]));
        if len == 0 || len > max {
            return Err(self.end(CarrierError::UnitSize));
        }
        Ok((self.in_len >= 2 + len).then_some(len))
    }

    fn poll_record(&mut self, p: &P) -> Result<Poll<'_>, CarrierError> {
        let Some(len) = self.unit_len(MAX_UNIT_LEN)? else {
            return Ok(Poll::Idle);
        };
        if len <= Aead::TAG_LEN {
            return Err(self.end(CarrierError::UnitSize));
        }
        let plain_len = len - Aead::TAG_LEN;
        let pn = self.recv_pn;
        let opened = match (&mut self.recv, self.input.split_at_mut_checked(2)) {
            (Some(key), Some((aad, rest))) => match rest.get_mut(..len).and_then(|u| u.split_at_mut_checked(plain_len))
            {
                Some((ct, tag)) => match <[u8; Aead::TAG_LEN]>::try_from(&*tag) {
                    Ok(tag) => key.open(p, pn, aad, ct, &tag).map_err(|e| match e {
                        RecordError::Authentication => CarrierError::Authentication,
                        RecordError::KeyRollRequired => CarrierError::KeyLimit,
                        other => CarrierError::Record(other),
                    }),
                    Err(_) => Err(CarrierError::UnitSize),
                },
                None => Err(CarrierError::UnitSize),
            },
            _ => Err(CarrierError::NotOpen),
        };
        if let Err(e) = opened {
            return Err(self.end(e));
        }
        self.recv_pn += 1;
        self.consume = 2 + len;
        let plain = self.input.get(2..2 + plain_len).unwrap_or_default();
        Frame::decode(plain).map(Poll::Frame).map_err(CarrierError::Frame)
    }

    /// Encode and seal `frame` into `out` as one unit; returns the unit length.
    ///
    /// # Errors
    /// [`CarrierError::NotOpen`] before the handshake completes, [`CarrierError::NoRoom`] if `out` is short,
    /// [`CarrierError::Frame`] for a frame that cannot be encoded, [`CarrierError::KeyLimit`] at the key's limit.
    pub fn seal(&mut self, p: &P, frame: &Frame<'_>, out: &mut [u8]) -> Result<usize, CarrierError> {
        let body = out.get_mut(2..).ok_or(CarrierError::NoRoom)?;
        let n = frame.encode(body).map_err(|e| match e {
            FrameError::Wire(_) => CarrierError::NoRoom,
            other => CarrierError::Frame(other),
        })?;
        self.seal_in_place(p, out, n)
    }

    /// Seal already encoded frame bytes (for example a finished [`super::frame::BatchBuilder`]) as one unit.
    ///
    /// # Errors
    /// As [`ProtectedCarrier::seal`].
    pub fn seal_bytes(&mut self, p: &P, plain: &[u8], out: &mut [u8]) -> Result<usize, CarrierError> {
        if plain.is_empty() || plain.len() > MAX_FRAME_LEN {
            return Err(CarrierError::UnitSize);
        }
        let slot = out.get_mut(2..2 + plain.len()).ok_or(CarrierError::NoRoom)?;
        slot.copy_from_slice(plain);
        self.seal_in_place(p, out, plain.len())
    }

    fn seal_in_place(&mut self, p: &P, out: &mut [u8], n: usize) -> Result<usize, CarrierError> {
        if !matches!(self.stage, Stage::Open) {
            return Err(if matches!(self.stage, Stage::Ended) {
                CarrierError::Closed
            } else {
                CarrierError::NotOpen
            });
        }
        let unit = n + Aead::TAG_LEN;
        let unit16 = u16::try_from(unit).map_err(|_| CarrierError::UnitSize)?;
        let total = 2 + unit;
        let pn = self.send_pn;
        let key = self.send.as_mut().ok_or(CarrierError::NotOpen)?;
        let (aad, rest) = out.split_at_mut_checked(2).ok_or(CarrierError::NoRoom)?;
        aad.copy_from_slice(&unit16.to_be_bytes());
        let (body, tail) = rest.split_at_mut_checked(n).ok_or(CarrierError::NoRoom)?;
        let tag_slot = tail.get_mut(..Aead::TAG_LEN).ok_or(CarrierError::NoRoom)?;
        match key.seal(p, pn, aad, body) {
            Ok(tag) => {
                tag_slot.copy_from_slice(&tag);
                self.send_pn += 1;
                Ok(total)
            }
            Err(RecordError::KeyRollRequired) => Err(self.end(CarrierError::KeyLimit)),
            Err(e) => Err(self.end(CarrierError::Record(e))),
        }
    }
}
