//! The control datagrams of the UDP side of a relay.
//!
//! # Wire format
//!
//! The first byte is the type; integers are big-endian; a node id is 33 bytes.
//!
//! | Type | Datagram | Layout after the type byte |
//! |---|---|---|
//! | 1 | QAD | `nonce(8)` |
//! | 2 | QADR | `nonce(8) addr` (the address the query came from: tag 4 or 6, octets, port) |
//! | 3 | DNSQ | `peer(33)` |
//! | 4 | DNSR | `peer(33) status(1)` then, when status is 1, the signed record. Status: 0 absent, 1 record, 2 too large |
//! | 6 | SLEEP | the signed sleep notice ([`super::sleep`]) |
//! | 8 | SPL | `src(33) flag packet`: the hub tunnels a packet down to a member |
//! | 9 | SPU | `dst(33) flag packet`: a member tunnels a packet up to the hub |
//!
//! (Type 5, record replication, and type 7, forwarding, are carrier frames between authenticated relays instead.)
//! A SPL or SPU datagram, header included, is at most [`MAX_TUNNEL_DATAGRAM`] bytes, so it fits every UDP path.
//! A decode never accepts trailing bytes after a fixed-size datagram, an empty packet, or an unknown type.

use core::net::SocketAddr;

use pinc_crypto::NodeId;
use pinc_wire::{Reader, Writer};

use crate::carrier::frame::{DnsAnswer, FrameError, MAX_NOTICE_LEN, MAX_PACKET_LEN};
use crate::carrier::node;
use crate::record::{MAX_RECORD_LEN, RecordError, read_addr, write_addr};

/// The largest SPL or SPU datagram: the path MTU bound less the IPv6 and UDP headers.
pub const MAX_TUNNEL_DATAGRAM: usize = MAX_PACKET_LEN - 28;
/// The largest lookup answer datagram; a record that does not fit gets the "too large" status.
pub const MAX_DNS_DATAGRAM: usize = MAX_PACKET_LEN - 28;

/// The datagram type bytes.
pub mod kind {
    /// QAD: address discovery query.
    pub const QAD: u8 = 1;
    /// QADR: address discovery answer.
    pub const QADR: u8 = 2;
    /// DNSQ: lookup query.
    pub const DNSQ: u8 = 3;
    /// DNSR: lookup answer.
    pub const DNSR: u8 = 4;
    /// SLEEP: signed sleep notice.
    pub const SLEEP: u8 = 6;
    /// SPL: tunnelled packet, hub to member.
    pub const SPL: u8 = 8;
    /// SPU: tunnelled packet, member to hub.
    pub const SPU: u8 = 9;
}

/// A control datagram, borrowing its bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Datagram<'a> {
    /// Ask the relay which address this datagram came from.
    Qad {
        /// Echoed in the answer.
        nonce: [u8; 8],
    },
    /// The address the query came from.
    Qadr {
        /// The query's nonce.
        nonce: [u8; 8],
        /// The observed address.
        addr: SocketAddr,
    },
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
    /// A signed sleep notice.
    Sleep {
        /// The notice bytes.
        notice: &'a [u8],
    },
    /// A packet tunnelled down to a member.
    Spl {
        /// The original source.
        src: NodeId,
        /// The opaque flag byte.
        flag: u8,
        /// The packet.
        packet: &'a [u8],
    },
    /// A packet tunnelled up to the hub.
    Spu {
        /// The destination.
        dst: NodeId,
        /// The opaque flag byte.
        flag: u8,
        /// The packet.
        packet: &'a [u8],
    },
}

/// Why a datagram was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DatagramError {
    /// The type byte is not a datagram.
    UnknownType(u8),
    /// A field is malformed.
    Frame(FrameError),
    /// An address is malformed.
    Addr(RecordError),
    /// Bytes follow a fixed-size datagram.
    Trailing,
    /// A tunnelled packet that is empty or over the datagram bound.
    PacketSize,
}

impl From<pinc_wire::WireError> for DatagramError {
    fn from(e: pinc_wire::WireError) -> Self {
        Self::Frame(FrameError::Wire(e))
    }
}

fn packet<'a>(r: &mut Reader<'a>, max: usize) -> Result<&'a [u8], DatagramError> {
    let n = r.remaining();
    if n == 0 || n > max {
        return Err(DatagramError::PacketSize);
    }
    Ok(r.read_bytes(n)?)
}

/// A record or notice the decoder would accept: 1 to `max` bytes.
fn check_body(body: &[u8], max: usize) -> Result<(), DatagramError> {
    if body.is_empty() || body.len() > max {
        return Err(DatagramError::Frame(FrameError::BodySize));
    }
    Ok(())
}

/// A tunnelled packet the decoder would accept: at least one byte, and the header with it within the datagram bound.
fn check_tunnel_packet(packet: &[u8]) -> Result<(), DatagramError> {
    if packet.is_empty() || packet.len().saturating_add(35) > MAX_TUNNEL_DATAGRAM {
        return Err(DatagramError::PacketSize);
    }
    Ok(())
}

impl<'a> Datagram<'a> {
    /// Decode one datagram from exactly `buf`.
    ///
    /// # Errors
    /// A [`DatagramError`] naming what is wrong.
    pub fn decode(buf: &'a [u8]) -> Result<Self, DatagramError> {
        let mut r = Reader::new(buf);
        let d = match r.read_u8()? {
            kind::QAD => Self::Qad { nonce: r.read_array()? },
            kind::QADR => Self::Qadr {
                nonce: r.read_array()?,
                addr: read_addr(&mut r).map_err(DatagramError::Addr)?,
            },
            kind::DNSQ => Self::DnsQuery {
                peer: node::read(&mut r)?,
            },
            kind::DNSR => {
                let peer = node::read(&mut r)?;
                let answer = match r.read_u8()? {
                    0 => DnsAnswer::Absent,
                    1 => {
                        let n = r.remaining();
                        if n == 0 || n > MAX_RECORD_LEN {
                            return Err(DatagramError::Frame(FrameError::BodySize));
                        }
                        DnsAnswer::Record(r.read_bytes(n)?)
                    }
                    2 => DnsAnswer::TooLarge,
                    s => return Err(DatagramError::Frame(FrameError::Status(s))),
                };
                Self::DnsReply { peer, answer }
            }
            kind::SLEEP => {
                let n = r.remaining();
                if n == 0 || n > MAX_NOTICE_LEN {
                    return Err(DatagramError::Frame(FrameError::BodySize));
                }
                Self::Sleep {
                    notice: r.read_bytes(n)?,
                }
            }
            kind::SPL => Self::Spl {
                src: node::read(&mut r)?,
                flag: r.read_u8()?,
                packet: packet(&mut r, MAX_TUNNEL_DATAGRAM)?,
            },
            kind::SPU => Self::Spu {
                dst: node::read(&mut r)?,
                flag: r.read_u8()?,
                packet: packet(&mut r, MAX_TUNNEL_DATAGRAM)?,
            },
            t => return Err(DatagramError::UnknownType(t)),
        };
        if !r.is_empty() {
            return Err(DatagramError::Trailing);
        }
        if let Self::Spl { packet, .. } | Self::Spu { packet, .. } = d
            && 35 + packet.len() > MAX_TUNNEL_DATAGRAM
        {
            return Err(DatagramError::PacketSize);
        }
        Ok(d)
    }

    /// Encode into `out` and return the length.
    ///
    /// # Errors
    /// A [`DatagramError`] if `out` is short or a field would not decode (an empty or oversized packet, record or
    /// notice); nothing is returned for a datagram the decoder would refuse.
    pub fn encode(&self, out: &mut [u8]) -> Result<usize, DatagramError> {
        let mut w = Writer::new(out);
        match *self {
            Self::Qad { nonce } => {
                w.put_u8(kind::QAD)?;
                w.put_slice(&nonce)?;
            }
            Self::Qadr { nonce, addr } => {
                w.put_u8(kind::QADR)?;
                w.put_slice(&nonce)?;
                write_addr(&mut w, &addr)?;
            }
            Self::DnsQuery { peer } => {
                w.put_u8(kind::DNSQ)?;
                node::write(&mut w, &peer)?;
            }
            Self::DnsReply { peer, answer } => {
                w.put_u8(kind::DNSR)?;
                node::write(&mut w, &peer)?;
                match answer {
                    DnsAnswer::Absent => w.put_u8(0)?,
                    DnsAnswer::Record(rec) => {
                        w.put_u8(1)?;
                        check_body(rec, MAX_RECORD_LEN)?;
                        w.put_slice(rec)?;
                    }
                    DnsAnswer::TooLarge => w.put_u8(2)?,
                }
            }
            Self::Sleep { notice } => {
                w.put_u8(kind::SLEEP)?;
                check_body(notice, MAX_NOTICE_LEN)?;
                w.put_slice(notice)?;
            }
            Self::Spl { src, flag, packet } => {
                w.put_u8(kind::SPL)?;
                node::write(&mut w, &src)?;
                w.put_u8(flag)?;
                check_tunnel_packet(packet)?;
                w.put_slice(packet)?;
            }
            Self::Spu { dst, flag, packet } => {
                w.put_u8(kind::SPU)?;
                node::write(&mut w, &dst)?;
                w.put_u8(flag)?;
                check_tunnel_packet(packet)?;
                w.put_slice(packet)?;
            }
        }
        Ok(w.written().len())
    }
}
