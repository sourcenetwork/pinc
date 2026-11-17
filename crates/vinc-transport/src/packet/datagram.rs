//! Coalesced datagrams and padding.

use vinc_wire::Writer;

use super::{ConnId, LongHeader, LongType, PacketError, short_dcid};

/// The header of a packet found in a datagram.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Header {
    /// A long-header packet; `header_len` is the offset of its body.
    Long {
        /// The parsed header.
        header: LongHeader,
        /// The encoded size of the header.
        header_len: usize,
    },
    /// A short-header packet.
    Short {
        /// The destination connection id.
        dcid: ConnId,
    },
}

/// One packet of a datagram, borrowed in place.
#[derive(Debug, PartialEq, Eq)]
pub struct Packet<'a> {
    /// What the unprotected part of the header says.
    pub header: Header,
    /// The whole packet, header included, ready for in-place header unprotection and open.
    pub bytes: &'a mut [u8],
}

impl Packet<'_> {
    /// Offset of the packet number: after the long header, or after the first byte and the dcid.
    pub fn pn_off(&self) -> usize {
        match self.header {
            Header::Long { header_len, .. } => header_len,
            Header::Short { dcid } => 1 + dcid.as_bytes().len(),
        }
    }
}

/// The iterator returned by [`packets`].
#[derive(Debug)]
pub struct Packets<'a> {
    rest: &'a mut [u8],
    dcid_len: usize,
}

/// Iterate over the packets of `datagram`: long packets, then at most one short packet whose dcid has `dcid_len`
/// bytes. A run of zero bytes after the last long packet is padding and ends the iteration. The iterator ends at the
/// first error; the packets are disjoint borrows of the datagram.
pub const fn packets(datagram: &mut [u8], dcid_len: usize) -> Packets<'_> {
    Packets {
        rest: datagram,
        dcid_len,
    }
}

impl<'a> Iterator for Packets<'a> {
    type Item = Result<Packet<'a>, PacketError>;

    fn next(&mut self) -> Option<Self::Item> {
        let rest = core::mem::take(&mut self.rest);
        let first = *rest.first()?;
        if first == 0 {
            return rest.iter().any(|b| *b != 0).then_some(Err(PacketError::Form));
        }
        if first & 0x80 == 0 {
            return Some(short_dcid(rest, self.dcid_len).map(|dcid| Packet {
                header: Header::Short { dcid },
                bytes: rest,
            }));
        }
        let (header, header_len) = match LongHeader::parse(rest) {
            Ok(parsed) => parsed,
            Err(e) => return Some(Err(e)),
        };
        // `parse` checked that the body fits, so the split cannot fail; stop cleanly if it somehow does.
        let (bytes, tail) = rest.split_at_mut_checked(header_len + header.body_len)?;
        self.rest = tail;
        Some(Ok(Packet {
            header: Header::Long { header, header_len },
            bytes,
        }))
    }
}

/// Append zero bytes to `w` until it holds `min_len` bytes. After a datagram that ends in a short packet, pad with
/// PADDING frames inside that packet instead. Nothing is written if the padding does not fit.
///
/// # Errors
/// A [`PacketError::Wire`] if the buffer cannot hold `min_len` bytes.
pub fn pad_to(w: &mut Writer<'_>, min_len: usize) -> Result<(), PacketError> {
    const ZEROS: [u8; 64] = [0; 64];
    let mut left = min_len.saturating_sub(w.written().len());
    w.ensure(left)?;
    while left > 0 {
        let n = left.min(ZEROS.len());
        w.put_slice(ZEROS.get(..n).unwrap_or_default())?;
        left -= n;
    }
    Ok(())
}

/// Write a long Handshake packet at the start of `window` that carries `bytes`, the part at offset `off` of a message
/// of `total` bytes, and return its length; `None` if it does not fit. The one framing of a handshake fragment: a
/// connection's flight and an endpoint's answer without a session are both written by it.
pub fn handshake_packet(
    window: &mut [u8],
    dcid: ConnId,
    scid: ConnId,
    total: usize,
    off: usize,
    bytes: &[u8],
) -> Option<usize> {
    let body_len =
        vinc_wire::varint::encoded_len(total as u64) + vinc_wire::varint::encoded_len(off as u64) + bytes.len();
    let header = LongHeader {
        ty: LongType::Handshake,
        dcid,
        scid,
        body_len,
    };
    let mut w = Writer::new(window);
    header.write(&mut w, 0).ok()?;
    w.put_varint(total as u64).ok()?;
    w.put_varint(off as u64).ok()?;
    w.put_slice(bytes).ok()?;
    Some(w.written().len())
}
