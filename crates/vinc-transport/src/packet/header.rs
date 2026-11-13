//! Long and short header encode and decode.

use vinc_wire::{Reader, WireError, Writer, varint};

use super::{ConnId, MAX_CID_LEN, PN_LEN_BASE, PacketError, VERSION};

/// The bit pattern of the first byte of a long header, before the type.
const LONG_FORM: u8 = 0b1100_0000;
/// The first byte of a short header, with the key phase and packet-number length cleared.
const SHORT_FORM: u8 = 0b0100_0000;
/// The key-phase bit of a short header.
const KEY_PHASE: u8 = 0b0001_0000;

/// The type of a long-header packet.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LongType {
    /// One unprotected handshake message.
    Handshake = 0,
    /// A packet under the early keys, carrying a packet number and frames.
    ZeroRtt = 1,
}

impl LongType {
    const fn from_bits(bits: u8) -> Option<Self> {
        match bits {
            0 => Some(Self::Handshake),
            1 => Some(Self::ZeroRtt),
            _ => None,
        }
    }
}

/// A long header.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LongHeader {
    /// The packet type.
    pub ty: LongType,
    /// The destination connection id.
    pub dcid: ConnId,
    /// The source connection id.
    pub scid: ConnId,
    /// The value of the length field: the bytes after the header. For a 0-RTT packet this includes the packet
    /// number and the tag.
    pub body_len: usize,
}

impl LongHeader {
    /// The encoded size of this header: everything before the body.
    pub fn header_len(&self) -> usize {
        1 + 1
            + 1
            + self.dcid.as_bytes().len()
            + 1
            + self.scid.as_bytes().len()
            + varint::encoded_len(self.body_len as u64)
    }

    /// Write the header. `pn_len` is the packet-number length of a 0-RTT packet (the base width) and must be 0 for
    /// the other types. Nothing is written on an error.
    ///
    /// # Errors
    /// [`PacketError::PnLength`] for a `pn_len` that does not fit the type; a [`PacketError::Wire`] if the buffer is
    /// too small or the body length is 2^63 or more, which no varint holds.
    pub fn write(&self, w: &mut Writer<'_>, pn_len: usize) -> Result<(), PacketError> {
        let low = match self.ty {
            LongType::ZeroRtt if pn_len == PN_LEN_BASE => u8::try_from(pn_len - 1).unwrap_or(0),
            LongType::ZeroRtt => return Err(PacketError::PnLength),
            _ if pn_len == 0 => 0,
            LongType::Handshake => return Err(PacketError::PnLength),
        };
        // `header_len` counts ten bytes for a body length no varint holds, so the room check would pass and the
        // length would be refused only after the bytes before it were written.
        if self.body_len as u64 >= 1 << 63 {
            return Err(PacketError::Wire(WireError::VarintOverflow));
        }
        w.ensure(self.header_len())?;
        w.put_u8(LONG_FORM | ((self.ty as u8) << 4) | low)?;
        w.put_u8(VERSION)?;
        for id in [&self.dcid, &self.scid] {
            let bytes = id.as_bytes();
            w.put_u8(u8::try_from(bytes.len()).map_err(|_| PacketError::ConnIdLength)?)?;
            w.put_slice(bytes)?;
        }
        w.put_varint(self.body_len as u64)?;
        Ok(())
    }

    /// Parse the header at the start of `packet` and return it with its encoded size. The body must fit in `packet`,
    /// which may hold more (coalesced packets follow). The low four bits of a 0-RTT first byte are still protected
    /// here and are checked after [`unprotect_header`](super::unprotect_header).
    ///
    /// # Errors
    /// [`PacketError::Form`] if the first byte is not a long header with the fixed bit,
    /// [`PacketError::LongType`], [`PacketError::Reserved`] (a non-zero low nibble on a handshake),
    /// [`PacketError::Version`], [`PacketError::ConnIdLength`], [`PacketError::Length`] or a [`PacketError::Wire`]
    /// for a truncated field.
    pub fn parse(packet: &[u8]) -> Result<(Self, usize), PacketError> {
        let mut r = Reader::new(packet);
        let first = r.read_u8()?;
        if first & LONG_FORM != LONG_FORM {
            return Err(PacketError::Form);
        }
        let ty = LongType::from_bits((first >> 4) & 0b11).ok_or(PacketError::LongType)?;
        if ty != LongType::ZeroRtt && first & 0x0f != 0 {
            return Err(PacketError::Reserved);
        }
        let version = r.read_u8()?;
        if version != VERSION {
            return Err(PacketError::Version(version));
        }
        let dcid = read_cid(&mut r)?;
        let scid = read_cid(&mut r)?;
        let body_len = usize::try_from(r.read_varint()?).map_err(|_| PacketError::Length)?;
        if body_len > r.remaining() {
            return Err(PacketError::Length);
        }
        Ok((
            Self {
                ty,
                dcid,
                scid,
                body_len,
            },
            r.position(),
        ))
    }
}

fn read_cid(r: &mut Reader<'_>) -> Result<ConnId, PacketError> {
    let len = usize::from(r.read_u8()?);
    if len > MAX_CID_LEN {
        return Err(PacketError::ConnIdLength);
    }
    ConnId::new(r.read_bytes(len)?).ok_or(PacketError::ConnIdLength)
}

/// A short header to write.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ShortHeader {
    /// The key phase of the keys that seal the packet.
    pub key_phase: bool,
    /// The destination connection id, of the length the receiver chose.
    pub dcid: ConnId,
}

impl ShortHeader {
    /// Write the header and the truncated packet number `pn` (2 or 3 bytes, from [`encode_pn`](super::encode_pn)).
    /// Nothing is written on an error.
    ///
    /// # Errors
    /// [`PacketError::PnLength`] if `pn` is not 2 or 3 bytes; a [`PacketError::Wire`] if the buffer is too small.
    pub fn write(&self, w: &mut Writer<'_>, pn: &[u8]) -> Result<(), PacketError> {
        if !(PN_LEN_BASE..=super::PN_LEN_WIDE).contains(&pn.len()) {
            return Err(PacketError::PnLength);
        }
        let dcid = self.dcid.as_bytes();
        w.ensure(short_header_len(dcid.len(), pn.len()))?;
        let phase = if self.key_phase { KEY_PHASE } else { 0 };
        w.put_u8(SHORT_FORM | phase | u8::try_from(pn.len() - 1).unwrap_or(0))?;
        w.put_slice(dcid)?;
        w.put_slice(pn)?;
        Ok(())
    }
}

/// The encoded size of a short header with a dcid of `dcid_len` bytes and a packet number of `pn_len` bytes.
pub const fn short_header_len(dcid_len: usize, pn_len: usize) -> usize {
    1 + dcid_len + pn_len
}

/// The destination connection id of a short-header packet whose dcid has the configured length `dcid_len`, read
/// without removing header protection (it is not protected). The packet number starts at offset `1 + dcid_len`.
///
/// # Errors
/// [`PacketError::Form`] if the first byte is not a short header (bit 7 clear, bit 6 set, bit 5 clear),
/// [`PacketError::ConnIdLength`] for a `dcid_len` above 20, [`PacketError::TooShort`] if the dcid does not fit.
pub fn short_dcid(packet: &[u8], dcid_len: usize) -> Result<ConnId, PacketError> {
    if dcid_len > MAX_CID_LEN {
        return Err(PacketError::ConnIdLength);
    }
    let (first, rest) = packet.split_first().ok_or(PacketError::TooShort)?;
    if first & 0b1110_0000 != SHORT_FORM {
        return Err(PacketError::Form);
    }
    let dcid = rest.get(..dcid_len).ok_or(PacketError::TooShort)?;
    ConnId::new(dcid).ok_or(PacketError::ConnIdLength)
}
