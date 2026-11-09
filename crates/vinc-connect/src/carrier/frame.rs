//! The carrier frame codec: strict, zero-copy decode and bounded encode.
//!
//! # Wire format
//!
//! One frame is exactly one protected record (see [`super::session`]), or one entry of a BATCH. All integers are
//! big-endian; a node id is 33 bytes ([`super::node`]); `packet` runs to the end of the frame and is 1 to
//! [`MAX_PACKET_LEN`] bytes; `flag` is one opaque byte the relay passes through.
//!
//! | Type | Frame | Layout after the type byte |
//! |---|---|---|
//! | 2 | SEND | `dst(33) flag packet` |
//! | 3 | RECV | `src(33) flag packet` |
//! | 4 | PUB | the signed record ([`crate::record`]) |
//! | 5, 6 | PING, PONG | nothing |
//! | 7, 8 | SELF, SELFR | `packet`: the relay itself is the destination, or the source |
//! | 9 | SEND with a new alias | `dst(33) alias flag packet` |
//! | 10 | SEND by alias | `alias flag packet` |
//! | 11 | RECV with a new alias | `src(33) alias flag packet` |
//! | 12 | RECV by alias | `alias flag packet` |
//! | 13 | BATCH | `k(1)` with k in 2 to 64, then k varint lengths, then k frames; the frames total at most 16 KiB |
//! | 14 | DNSQ | `peer(33)` |
//! | 15 | DNSR | `peer(33) status(1)` then, when status is 1, the signed record. Status: 0 absent, 1 record, 2 too large |
//! | 16 | FWD | `src(33) dst(33) flag packet`, between authenticated relays only |
//! | 17 | SYNC | the signed record, between authenticated relays only |
//! | 18 | SLEEP | the signed sleep notice |
//!
//! Types 2 to 15 are the carrier frames of the algorithm this protocol ports (its hello frame, type 1, is replaced by
//! the handshake). Aliases are below 32. A decode never accepts trailing bytes after a fixed-size frame, an empty
//! packet, a nested batch, an unknown type or an unknown identity tag. Long-header packets (first byte with the high
//! bit set, the handshake packets of the transport) are never batched by the [`BatchBuilder`].

use core::fmt;

use vinc_wire::{Reader, WireError, Writer, varint};

use super::alias::ALIAS_MAX;
use super::node;
use crate::record::MAX_RECORD_LEN;
use vinc_crypto::NodeId;

/// The largest relayed packet, the transport's path MTU bound.
pub const MAX_PACKET_LEN: usize = 1452;
/// The most frames in one batch.
pub const BATCH_MAX_FRAMES: usize = 64;
/// The most bytes of frames in one batch.
pub const BATCH_MAX_BYTES: usize = 16_384;
/// The longest sleep notice a frame carries.
pub const MAX_NOTICE_LEN: usize = 8192;
/// The longest encoded frame (a full batch with its header).
pub const MAX_FRAME_LEN: usize = BATCH_MAX_BYTES + BATCH_HEAD_MAX;

const BATCH_MAX_FRAMES_U8: u8 = 64;
const BATCH_HEAD_MAX: usize = 2 + BATCH_MAX_FRAMES * 3;

/// The frame type bytes.
pub mod kind {
    /// SEND: a packet to a node by id.
    pub const SEND: u8 = 2;
    /// RECV: a packet from a node by id.
    pub const RECV: u8 = 3;
    /// PUB: publish this node's record.
    pub const PUB: u8 = 4;
    /// PING: carrier keepalive.
    pub const PING: u8 = 5;
    /// PONG: the answer to a PING.
    pub const PONG: u8 = 6;
    /// SELF: the relay itself is the destination.
    pub const SELF: u8 = 7;
    /// SELFR: the relay itself is the source.
    pub const SELFR: u8 = 8;
    /// SENDB: SEND that defines an alias.
    pub const SEND_NEW: u8 = 9;
    /// SENDA: SEND by alias.
    pub const SEND_ALIAS: u8 = 10;
    /// RECVB: RECV that defines an alias.
    pub const RECV_NEW: u8 = 11;
    /// RECVA: RECV by alias.
    pub const RECV_ALIAS: u8 = 12;
    /// BATCH: several frames in one record.
    pub const BATCH: u8 = 13;
    /// DNSQ: lookup query.
    pub const DNSQ: u8 = 14;
    /// DNSR: lookup answer.
    pub const DNSR: u8 = 15;
    /// FWD: relay-to-relay forward.
    pub const FWD: u8 = 16;
    /// SYNC: relay-to-relay record replication.
    pub const SYNC: u8 = 17;
    /// SLEEP: a signed sleep notice.
    pub const SLEEP: u8 = 18;
}

/// Why a frame was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrameError {
    /// A field is truncated, a buffer is too small or a varint is invalid.
    Wire(WireError),
    /// The type byte is not a frame.
    UnknownType(u8),
    /// Bytes follow a frame that has a fixed size.
    Trailing,
    /// An alias of [`ALIAS_MAX`] or more.
    Alias(u8),
    /// A packet that is empty or longer than [`MAX_PACKET_LEN`].
    PacketSize,
    /// A record or notice that is empty or too long.
    BodySize,
    /// An answer status that is not 0, 1 or 2.
    Status(u8),
    /// A malformed batch, with the reason.
    Batch(&'static str),
    /// The frame does not fit the output buffer or the batch.
    NoRoom,
}

impl From<WireError> for FrameError {
    fn from(e: WireError) -> Self {
        Self::Wire(e)
    }
}

impl fmt::Display for FrameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wire(e) => write!(f, "{e}"),
            Self::UnknownType(t) => write!(f, "unknown frame type {t}"),
            Self::Trailing => f.write_str("bytes after a fixed-size frame"),
            Self::Alias(a) => write!(f, "alias {a} is out of range"),
            Self::PacketSize => f.write_str("packet is empty or too long"),
            Self::BodySize => f.write_str("record or notice is empty or too long"),
            Self::Status(s) => write!(f, "unknown answer status {s}"),
            Self::Batch(why) => write!(f, "malformed batch: {why}"),
            Self::NoRoom => f.write_str("frame does not fit"),
        }
    }
}

impl core::error::Error for FrameError {}

/// The answer to a lookup.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DnsAnswer<'a> {
    /// No record is held for the peer.
    Absent,
    /// The peer's signed record.
    Record(&'a [u8]),
    /// A record is held but does not fit this transport; ask again over the carrier.
    TooLarge,
}

/// The frames of a batch, validated when the batch was decoded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Batch<'a> {
    count: u8,
    lens: &'a [u8],
    body: &'a [u8],
}

impl<'a> Batch<'a> {
    /// How many frames the batch holds (2 to 64).
    pub const fn len(&self) -> usize {
        self.count as usize
    }

    /// Always false: a decoded batch holds at least two frames.
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// The frames in order.
    pub const fn frames(&self) -> BatchIter<'a> {
        BatchIter {
            left: self.count,
            lens: self.lens,
            body: self.body,
        }
    }
}

/// The iterator over a [`Batch`].
#[derive(Debug, Clone, Copy)]
pub struct BatchIter<'a> {
    left: u8,
    lens: &'a [u8],
    body: &'a [u8],
}

#[allow(
    clippy::copy_iterator,
    reason = "the iterator is a pair of slices; copying it is how a batch is walked twice"
)]
impl<'a> Iterator for BatchIter<'a> {
    type Item = Frame<'a>;

    fn next(&mut self) -> Option<Frame<'a>> {
        if self.left == 0 {
            return None;
        }
        self.left -= 1;
        let (len, used) = varint::decode(self.lens).ok()?;
        self.lens = self.lens.get(used..)?;
        let (head, tail) = self.body.split_at_checked(usize::try_from(len).ok()?)?;
        self.body = tail;
        Frame::decode(head).ok()
    }
}

/// One carrier frame, borrowing its bytes from the record it was decoded from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Frame<'a> {
    /// A packet to `dst`.
    Send {
        /// The destination node.
        dst: NodeId,
        /// The opaque flag byte.
        flag: u8,
        /// The packet.
        packet: &'a [u8],
    },
    /// A packet from `src`.
    Recv {
        /// The source node.
        src: NodeId,
        /// The opaque flag byte.
        flag: u8,
        /// The packet.
        packet: &'a [u8],
    },
    /// A packet to `dst`, which also gets `alias` on this carrier.
    SendNew {
        /// The destination node.
        dst: NodeId,
        /// The alias defined for it.
        alias: u8,
        /// The opaque flag byte.
        flag: u8,
        /// The packet.
        packet: &'a [u8],
    },
    /// A packet to the node `alias` names on this carrier.
    SendAlias {
        /// The alias.
        alias: u8,
        /// The opaque flag byte.
        flag: u8,
        /// The packet.
        packet: &'a [u8],
    },
    /// A packet from `src`, which also gets `alias` on this carrier.
    RecvNew {
        /// The source node.
        src: NodeId,
        /// The alias defined for it.
        alias: u8,
        /// The opaque flag byte.
        flag: u8,
        /// The packet.
        packet: &'a [u8],
    },
    /// A packet from the node `alias` names on this carrier.
    RecvAlias {
        /// The alias.
        alias: u8,
        /// The opaque flag byte.
        flag: u8,
        /// The packet.
        packet: &'a [u8],
    },
    /// Publish the sender's signed record.
    Publish {
        /// The signed record bytes.
        record: &'a [u8],
    },
    /// Carrier keepalive probe.
    Ping,
    /// Carrier keepalive answer.
    Pong,
    /// A packet whose destination is the relay itself.
    SelfSend {
        /// The packet.
        packet: &'a [u8],
    },
    /// A packet whose source is the relay itself.
    SelfRecv {
        /// The packet.
        packet: &'a [u8],
    },
    /// Several frames in one record.
    Batch(Batch<'a>),
    /// Ask for the record of `peer`.
    DnsQuery {
        /// The node looked up.
        peer: NodeId,
    },
    /// The answer to a lookup.
    DnsReply {
        /// The node looked up.
        peer: NodeId,
        /// What is known.
        answer: DnsAnswer<'a>,
    },
    /// A relay-to-relay forward of a packet from `src` to `dst`.
    Forward {
        /// The original source.
        src: NodeId,
        /// The destination, homed at the receiving relay.
        dst: NodeId,
        /// The opaque flag byte.
        flag: u8,
        /// The packet.
        packet: &'a [u8],
    },
    /// A relay-to-relay record replication.
    Sync {
        /// The signed record bytes.
        record: &'a [u8],
    },
    /// A signed sleep notice.
    Sleep {
        /// The notice bytes.
        notice: &'a [u8],
    },
}
fn take_packet<'a>(r: &mut Reader<'a>) -> Result<&'a [u8], FrameError> {
    let n = r.remaining();
    if n == 0 || n > MAX_PACKET_LEN {
        return Err(FrameError::PacketSize);
    }
    Ok(r.read_bytes(n)?)
}

fn take_body<'a>(r: &mut Reader<'a>, max: usize) -> Result<&'a [u8], FrameError> {
    let n = r.remaining();
    if n == 0 || n > max {
        return Err(FrameError::BodySize);
    }
    Ok(r.read_bytes(n)?)
}

fn take_alias(r: &mut Reader<'_>) -> Result<u8, FrameError> {
    let a = r.read_u8()?;
    if usize::from(a) < ALIAS_MAX {
        Ok(a)
    } else {
        Err(FrameError::Alias(a))
    }
}

fn finish(r: &Reader<'_>) -> Result<(), FrameError> {
    if r.is_empty() {
        Ok(())
    } else {
        Err(FrameError::Trailing)
    }
}

impl<'a> Frame<'a> {
    /// Decode one frame from exactly `buf`.
    ///
    /// # Errors
    /// A [`FrameError`] naming what is wrong; nothing is allocated or consumed.
    pub fn decode(buf: &'a [u8]) -> Result<Self, FrameError> {
        let mut r = Reader::new(buf);
        let ty = r.read_u8()?;
        let f = match ty {
            kind::SEND => Self::Send {
                dst: node::read(&mut r)?,
                flag: r.read_u8()?,
                packet: take_packet(&mut r)?,
            },
            kind::RECV => Self::Recv {
                src: node::read(&mut r)?,
                flag: r.read_u8()?,
                packet: take_packet(&mut r)?,
            },
            kind::SEND_NEW => Self::SendNew {
                dst: node::read(&mut r)?,
                alias: take_alias(&mut r)?,
                flag: r.read_u8()?,
                packet: take_packet(&mut r)?,
            },
            kind::SEND_ALIAS => Self::SendAlias {
                alias: take_alias(&mut r)?,
                flag: r.read_u8()?,
                packet: take_packet(&mut r)?,
            },
            kind::RECV_NEW => Self::RecvNew {
                src: node::read(&mut r)?,
                alias: take_alias(&mut r)?,
                flag: r.read_u8()?,
                packet: take_packet(&mut r)?,
            },
            kind::RECV_ALIAS => Self::RecvAlias {
                alias: take_alias(&mut r)?,
                flag: r.read_u8()?,
                packet: take_packet(&mut r)?,
            },
            kind::PUB => Self::Publish {
                record: take_body(&mut r, MAX_RECORD_LEN)?,
            },
            kind::PING => Self::Ping,
            kind::PONG => Self::Pong,
            kind::SELF => Self::SelfSend {
                packet: take_packet(&mut r)?,
            },
            kind::SELFR => Self::SelfRecv {
                packet: take_packet(&mut r)?,
            },
            kind::BATCH => Self::Batch(decode_batch(&mut r)?),
            kind::DNSQ => Self::DnsQuery {
                peer: node::read(&mut r)?,
            },
            kind::DNSR => {
                let peer = node::read(&mut r)?;
                let answer = match r.read_u8()? {
                    0 => DnsAnswer::Absent,
                    1 => DnsAnswer::Record(take_body(&mut r, MAX_RECORD_LEN)?),
                    2 => DnsAnswer::TooLarge,
                    s => return Err(FrameError::Status(s)),
                };
                Self::DnsReply { peer, answer }
            }
            kind::FWD => Self::Forward {
                src: node::read(&mut r)?,
                dst: node::read(&mut r)?,
                flag: r.read_u8()?,
                packet: take_packet(&mut r)?,
            },
            kind::SYNC => Self::Sync {
                record: take_body(&mut r, MAX_RECORD_LEN)?,
            },
            kind::SLEEP => Self::Sleep {
                notice: take_body(&mut r, MAX_NOTICE_LEN)?,
            },
            t => return Err(FrameError::UnknownType(t)),
        };
        finish(&r)?;
        Ok(f)
    }

    /// The frame type byte.
    pub const fn kind(&self) -> u8 {
        match self {
            Self::Send { .. } => kind::SEND,
            Self::Recv { .. } => kind::RECV,
            Self::SendNew { .. } => kind::SEND_NEW,
            Self::SendAlias { .. } => kind::SEND_ALIAS,
            Self::RecvNew { .. } => kind::RECV_NEW,
            Self::RecvAlias { .. } => kind::RECV_ALIAS,
            Self::Publish { .. } => kind::PUB,
            Self::Ping => kind::PING,
            Self::Pong => kind::PONG,
            Self::SelfSend { .. } => kind::SELF,
            Self::SelfRecv { .. } => kind::SELFR,
            Self::Batch(_) => kind::BATCH,
            Self::DnsQuery { .. } => kind::DNSQ,
            Self::DnsReply { .. } => kind::DNSR,
            Self::Forward { .. } => kind::FWD,
            Self::Sync { .. } => kind::SYNC,
            Self::Sleep { .. } => kind::SLEEP,
        }
    }

    /// The relayed packet of a frame that carries one.
    pub const fn packet(&self) -> Option<&'a [u8]> {
        match self {
            Self::Send { packet, .. }
            | Self::Recv { packet, .. }
            | Self::SendNew { packet, .. }
            | Self::SendAlias { packet, .. }
            | Self::RecvNew { packet, .. }
            | Self::RecvAlias { packet, .. }
            | Self::SelfSend { packet }
            | Self::SelfRecv { packet }
            | Self::Forward { packet, .. } => Some(packet),
            _ => None,
        }
    }

    /// Whether the packet is a long-header packet (a transport handshake packet), which is never batched.
    pub fn is_long_header(&self) -> bool {
        self.packet().and_then(|p| p.first()).is_some_and(|b| b & 0x80 != 0)
    }

    /// Encode into `out` and return the length.
    ///
    /// # Errors
    /// [`FrameError::Wire`] if `out` is too small, [`FrameError::PacketSize`], [`FrameError::BodySize`] or
    /// [`FrameError::Alias`] for a field the decoder would refuse.
    pub fn encode(&self, out: &mut [u8]) -> Result<usize, FrameError> {
        let mut w = Writer::new(out);
        w.put_u8(self.kind())?;
        match *self {
            Self::Send { dst, flag, packet } => {
                node::write(&mut w, &dst)?;
                w.put_u8(flag)?;
                put_packet(&mut w, packet)?;
            }
            Self::Recv { src, flag, packet } => {
                node::write(&mut w, &src)?;
                w.put_u8(flag)?;
                put_packet(&mut w, packet)?;
            }
            Self::SendNew {
                dst,
                alias,
                flag,
                packet,
            } => {
                node::write(&mut w, &dst)?;
                put_alias(&mut w, alias)?;
                w.put_u8(flag)?;
                put_packet(&mut w, packet)?;
            }
            Self::RecvNew {
                src,
                alias,
                flag,
                packet,
            } => {
                node::write(&mut w, &src)?;
                put_alias(&mut w, alias)?;
                w.put_u8(flag)?;
                put_packet(&mut w, packet)?;
            }
            Self::SendAlias { alias, flag, packet } | Self::RecvAlias { alias, flag, packet } => {
                put_alias(&mut w, alias)?;
                w.put_u8(flag)?;
                put_packet(&mut w, packet)?;
            }
            Self::Publish { record } | Self::Sync { record } => put_body(&mut w, record, MAX_RECORD_LEN)?,
            Self::Ping | Self::Pong => {}
            Self::SelfSend { packet } | Self::SelfRecv { packet } => put_packet(&mut w, packet)?,
            Self::Batch(b) => {
                w.put_u8(b.count)?;
                w.put_slice(b.lens)?;
                w.put_slice(b.body)?;
            }
            Self::DnsQuery { peer } => node::write(&mut w, &peer)?,
            Self::DnsReply { peer, answer } => {
                node::write(&mut w, &peer)?;
                match answer {
                    DnsAnswer::Absent => w.put_u8(0)?,
                    DnsAnswer::Record(rec) => {
                        w.put_u8(1)?;
                        put_body(&mut w, rec, MAX_RECORD_LEN)?;
                    }
                    DnsAnswer::TooLarge => w.put_u8(2)?,
                }
            }
            Self::Forward { src, dst, flag, packet } => {
                node::write(&mut w, &src)?;
                node::write(&mut w, &dst)?;
                w.put_u8(flag)?;
                put_packet(&mut w, packet)?;
            }
            Self::Sleep { notice } => put_body(&mut w, notice, MAX_NOTICE_LEN)?,
        }
        Ok(w.written().len())
    }
}

fn put_packet(w: &mut Writer<'_>, packet: &[u8]) -> Result<(), FrameError> {
    if packet.is_empty() || packet.len() > MAX_PACKET_LEN {
        return Err(FrameError::PacketSize);
    }
    Ok(w.put_slice(packet)?)
}

fn put_body(w: &mut Writer<'_>, body: &[u8], max: usize) -> Result<(), FrameError> {
    if body.is_empty() || body.len() > max {
        return Err(FrameError::BodySize);
    }
    Ok(w.put_slice(body)?)
}

fn put_alias(w: &mut Writer<'_>, alias: u8) -> Result<(), FrameError> {
    if usize::from(alias) >= ALIAS_MAX {
        return Err(FrameError::Alias(alias));
    }
    Ok(w.put_u8(alias)?)
}

/// Validate a batch: the count, the lengths, and every frame inside.
fn decode_batch<'a>(r: &mut Reader<'a>) -> Result<Batch<'a>, FrameError> {
    let count = r.read_u8()?;
    if !(2..=BATCH_MAX_FRAMES_U8).contains(&count) {
        return Err(FrameError::Batch("frame count"));
    }
    let rest = r.read_bytes(r.remaining())?;
    let mut lr = Reader::new(rest);
    let mut total = 0usize;
    let mut lens_probe = [0usize; BATCH_MAX_FRAMES];
    for slot in lens_probe.iter_mut().take(usize::from(count)) {
        let len = usize::try_from(lr.read_varint()?).map_err(|_| FrameError::Batch("length"))?;
        if len == 0 {
            return Err(FrameError::Batch("empty frame"));
        }
        total = total.checked_add(len).ok_or(FrameError::Batch("length"))?;
        *slot = len;
    }
    let lens_len = lr.position();
    let (lens, body) = rest.split_at_checked(lens_len).ok_or(FrameError::Batch("length"))?;
    if total != body.len() || total > BATCH_MAX_BYTES {
        return Err(FrameError::Batch("size"));
    }
    let mut at = body;
    for len in lens_probe.iter().take(usize::from(count)) {
        let (head, tail) = at.split_at_checked(*len).ok_or(FrameError::Batch("size"))?;
        if head.first() == Some(&kind::BATCH) {
            return Err(FrameError::Batch("nested batch"));
        }
        Frame::decode(head)?;
        at = tail;
    }
    Ok(Batch { count, lens, body })
}

/// The result of offering a frame to a [`BatchBuilder`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Offer {
    /// The frame joined the batch.
    Added,
    /// The batch cannot take the frame (full, over the byte limit, a long-header packet, or a batch): close this
    /// batch with [`BatchBuilder::finish`] and send the frame alone or in the next batch.
    Refused,
}

/// Builds one record from frames queued back to back for one carrier.
///
/// Rules: at most [`BATCH_MAX_FRAMES`] frames and [`BATCH_MAX_BYTES`] bytes of frames, and a long-header packet is
/// never batched (it neither joins a batch nor starts one that takes others). One frame alone is emitted without a
/// batch header.
#[derive(Debug)]
pub struct BatchBuilder<'o> {
    out: &'o mut [u8],
    used: usize,
    lens: [u16; BATCH_MAX_FRAMES],
    count: usize,
}

impl<'o> BatchBuilder<'o> {
    /// A builder writing into `out`, which must hold [`MAX_FRAME_LEN`] bytes to take a full batch.
    pub const fn new(out: &'o mut [u8]) -> Self {
        Self {
            out,
            used: 0,
            lens: [0; BATCH_MAX_FRAMES],
            count: 0,
        }
    }

    /// Offer the next frame.
    ///
    /// # Errors
    /// The frame's own encode errors; a frame that merely does not fit is [`Offer::Refused`].
    pub fn offer(&mut self, frame: &Frame<'_>) -> Result<Offer, FrameError> {
        if matches!(frame, Frame::Batch(_)) || frame.is_long_header() || self.count >= BATCH_MAX_FRAMES {
            return Ok(Offer::Refused);
        }
        let start = BATCH_HEAD_MAX.saturating_add(self.used);
        let room = self.out.get_mut(start..).ok_or(FrameError::NoRoom)?;
        let n = match frame.encode(room) {
            Ok(n) => n,
            Err(FrameError::Wire(WireError::BufferTooSmall { .. })) if self.count > 0 => return Ok(Offer::Refused),
            Err(e) => return Err(e),
        };
        if self.used + n > BATCH_MAX_BYTES {
            return Ok(Offer::Refused);
        }
        let slot = self.lens.get_mut(self.count).ok_or(FrameError::NoRoom)?;
        *slot = u16::try_from(n).map_err(|_| FrameError::NoRoom)?;
        self.used += n;
        self.count += 1;
        Ok(Offer::Added)
    }

    /// How many frames were accepted.
    pub const fn len(&self) -> usize {
        self.count
    }

    /// Whether no frame was accepted.
    pub const fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Close the batch and return the record bytes: the single frame as is, or a BATCH frame. `None` if empty.
    ///
    /// # Errors
    /// [`FrameError::NoRoom`] if the buffer cannot hold the header.
    pub fn finish(self) -> Result<Option<&'o [u8]>, FrameError> {
        if self.count == 0 {
            return Ok(None);
        }
        let body_at = BATCH_HEAD_MAX;
        if self.count == 1 {
            return Ok(self.out.get(body_at..body_at + self.used));
        }
        let mut head = [0u8; BATCH_HEAD_MAX];
        let mut w = Writer::new(&mut head);
        w.put_u8(kind::BATCH)?;
        w.put_u8(u8::try_from(self.count).map_err(|_| FrameError::NoRoom)?)?;
        for len in self.lens.iter().take(self.count) {
            w.put_varint(u64::from(*len))?;
        }
        let head_len = w.written().len();
        let start = body_at - head_len;
        self.out
            .get_mut(start..body_at)
            .ok_or(FrameError::NoRoom)?
            .copy_from_slice(w.written());
        Ok(self.out.get(start..body_at + self.used))
    }
}
