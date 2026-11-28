//! The control datagrams of the UDP side of a relay.
//!
//! # Wire format
//!
//! The first byte is the type; integers are big-endian; a node id is 33 bytes.
//!
//! | Type | Datagram | Layout after the type byte |
//! |---|---|---|
//! | 1 | QAD | `nonce(8) zero(10)` |
//! | 2 | QADR | `nonce(8) addr` (the address the query came from: tag 4 or 6, octets, port) |
//! | 3 | DNSQ | `peer(33) zero(450)` |
//! | 4 | DNSR | `peer(33) status(1)` then, when status is 1, the signed record. Status: 0 absent, 1 record, 2 too large |
//! | 6 | SLEEP | the signed sleep notice ([`super::sleep`]) |
//! | 8 | SPL | `src(33) flag packet`: the hub tunnels a packet down to a member |
//! | 9 | SPU | `dst(33) flag packet`: a member tunnels a packet up to the hub |
//!
//! (Type 5, record replication, and type 7, forwarding, are carrier frames between authenticated relays instead.)
//! A QAD and a DNSQ are padded with zeros to [`QAD_LEN`] and [`DNSQ_LEN`], so three times the query pays for the
//! longest answer; a short or nonzero padding is refused.
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
/// The longest QADR: type, nonce, an IPv6 address (tag, 16 octets, port).
pub const MAX_QADR_LEN: usize = 1 + 8 + 19;
/// The least length of a query whose answer of `answer` bytes, with its 28 header bytes, is at most three times it:
/// what the ledger of the answering node lets go to a source that proved nothing.
#[allow(clippy::cast_possible_truncation, reason = "the overhead is 28 and the factor 3")]
pub const fn query_len(answer: usize) -> usize {
    (answer + pinc_core::DATAGRAM_OVERHEAD as usize).div_ceil(pinc_core::FACTOR as usize)
}
/// A QAD on the wire: type, nonce, zero padding (19 bytes).
pub const QAD_LEN: usize = query_len(MAX_QADR_LEN);
/// A DNSQ on the wire: type, node, zero padding (484 bytes).
pub const DNSQ_LEN: usize = query_len(MAX_DNS_DATAGRAM);
const _: () = assert!(QAD_LEN == 19 && DNSQ_LEN == 484);

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
    /// The padding of a query is not zero.
    Padding,
    /// A tunnelled packet that is empty or over the datagram bound.
    PacketSize,
}

impl From<pinc_wire::WireError> for DatagramError {
    fn from(e: pinc_wire::WireError) -> Self {
        Self::Frame(FrameError::Wire(e))
    }
}

/// Read the `n` padding bytes of a query and refuse a nonzero one.
fn zero_padding(r: &mut Reader<'_>, n: usize) -> Result<(), DatagramError> {
    if r.read_bytes(n)?.iter().any(|b| *b != 0) {
        return Err(DatagramError::Padding);
    }
    Ok(())
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
            kind::QAD => {
                let nonce = r.read_array()?;
                zero_padding(&mut r, QAD_LEN - 9)?;
                Self::Qad { nonce }
            }
            kind::QADR => Self::Qadr {
                nonce: r.read_array()?,
                addr: read_addr(&mut r).map_err(DatagramError::Addr)?,
            },
            kind::DNSQ => {
                let peer = node::read(&mut r)?;
                zero_padding(&mut r, DNSQ_LEN - 34)?;
                Self::DnsQuery { peer }
            }
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
                w.put_slice(&[0; QAD_LEN - 9])?;
            }
            Self::Qadr { nonce, addr } => {
                w.put_u8(kind::QADR)?;
                w.put_slice(&nonce)?;
                write_addr(&mut w, &addr)?;
            }
            Self::DnsQuery { peer } => {
                w.put_u8(kind::DNSQ)?;
                node::write(&mut w, &peer)?;
                w.put_slice(&[0; DNSQ_LEN - 34])?;
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

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]
mod tests {
    use alloc::vec;
    use alloc::vec::Vec;

    use pinc_wire::WireError;

    use super::*;

    fn node() -> NodeId {
        NodeId {
            alg: pinc_crypto::IdentityAlg::Ed25519,
            bytes: [7; 32],
        }
    }

    fn qad() -> Vec<u8> {
        let mut b = vec![0u8; QAD_LEN];
        let n = Datagram::Qad { nonce: [3; 8] }.encode(&mut b).unwrap();
        assert_eq!(n, QAD_LEN);
        b
    }

    fn dnsq() -> Vec<u8> {
        let mut b = vec![0u8; DNSQ_LEN];
        let peer = node();
        let n = Datagram::DnsQuery { peer }.encode(&mut b).unwrap();
        assert_eq!(n, DNSQ_LEN);
        b
    }

    fn truncated(missing: usize) -> DatagramError {
        DatagramError::Frame(FrameError::Wire(WireError::Truncated { needed: missing }))
    }

    #[test]
    fn a_query_is_padded_with_zeros_to_its_length() {
        let (q, d) = (qad(), dnsq());
        assert_eq!((q.len(), d.len()), (19, 484));
        assert!(q[9..].iter().all(|b| *b == 0) && d[34..].iter().all(|b| *b == 0));
        assert_eq!(Datagram::decode(&q), Ok(Datagram::Qad { nonce: [3; 8] }));
        assert!(matches!(Datagram::decode(&d), Ok(Datagram::DnsQuery { .. })));
    }

    #[test]
    fn an_unpadded_or_short_query_is_truncated() {
        assert_eq!(Datagram::decode(&qad()[..9]), Err(truncated(10)));
        assert_eq!(Datagram::decode(&dnsq()[..34]), Err(truncated(450)));
        assert_eq!(Datagram::decode(&qad()[..QAD_LEN - 1]), Err(truncated(1)));
        assert_eq!(Datagram::decode(&dnsq()[..DNSQ_LEN - 1]), Err(truncated(1)));
    }

    #[test]
    fn a_nonzero_padding_byte_or_a_trailing_byte_is_refused() {
        for (q, first) in [(qad(), 9), (dnsq(), 34)] {
            for at in [first, q.len() - 1] {
                let mut bad = q.clone();
                bad[at] = 1;
                assert_eq!(Datagram::decode(&bad), Err(DatagramError::Padding));
            }
            let mut more = q;
            more.push(0);
            assert_eq!(Datagram::decode(&more), Err(DatagramError::Trailing));
        }
    }

    #[test]
    fn a_query_that_does_not_fit_the_buffer_fails_with_the_shortfall_and_writes_no_padding() {
        let peer = node();
        for (d, len, fixed) in [
            (Datagram::Qad { nonce: [3; 8] }, QAD_LEN, 9),
            (Datagram::DnsQuery { peer }, DNSQ_LEN, 34),
        ] {
            let mut b = vec![0xAA; len - 1];
            assert_eq!(
                d.encode(&mut b),
                Err(DatagramError::Frame(FrameError::Wire(WireError::BufferTooSmall {
                    needed: 1
                })))
            );
            assert!(b[fixed..].iter().all(|x| *x == 0xAA), "padding was written");
        }
    }

    #[test]
    fn three_times_a_query_pays_for_its_longest_answer_and_no_shorter_query_does() {
        for (q, answer) in [(QAD_LEN, MAX_QADR_LEN), (DNSQ_LEN, MAX_DNS_DATAGRAM)] {
            assert!(q * 3 >= answer + 28);
            assert!((q - 1) * 3 < answer + 28);
        }
    }
}
