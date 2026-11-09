//! Header protection and in-place seal and open of whole packets.

use vinc_crypto::{Aead, Provider};
use vinc_security::{HeaderKey, PacketKey};
use vinc_wire::WireError;

use super::{MAX_PN, PacketError, decode_pn};

/// Bytes between the start of the packet number and the start of the header-protection sample: the longest packet-number
/// field plus one, so the sample never depends on the width.
pub const SAMPLE_SKIP: usize = 4;

/// Where the packet number sits in a packet, and which first-byte mask applies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PnLayout {
    /// Offset of the first packet-number byte from the start of the packet.
    pub pn_off: usize,
    /// Packet-number length, 2 or 3.
    pub pn_len: usize,
    /// Whether the packet has a long header (a 4-bit rather than a 5-bit first-byte mask).
    pub long: bool,
}

/// The packet-number field revealed by [`unprotect_header`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Unprotected {
    /// The first byte with the mask removed.
    pub first: u8,
    /// The packet-number length the first byte declares, 1 to 4 (the connection refuses any but its fixed width).
    pub pn_len: usize,
    /// The truncated packet number, to expand with [`decode_pn`].
    pub truncated: u32,
}

impl Unprotected {
    /// The key phase of a short header (bit 4 of the first byte).
    pub const fn key_phase(&self) -> bool {
        self.first & 0b0001_0000 != 0
    }
}

/// The result of [`open`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Opened {
    /// The full packet number.
    pub pn: u64,
    /// Offset of the first frame byte in the packet.
    pub payload_start: usize,
    /// Offset one past the last frame byte in the packet (the tag is not included).
    pub payload_end: usize,
}

/// The 16-byte header-protection sample of `packet`, which starts at the first byte of the packet and ends with it.
///
/// # Errors
/// [`PacketError::TooShort`] if fewer than 16 bytes follow `pn_off + 4`.
pub fn sample_at(packet: &[u8], pn_off: usize) -> Result<[u8; Aead::SAMPLE_LEN], PacketError> {
    let start = pn_off.checked_add(SAMPLE_SKIP).ok_or(PacketError::TooShort)?;
    packet
        .get(start..)
        .and_then(|s| s.first_chunk::<{ Aead::SAMPLE_LEN }>())
        .copied()
        .ok_or(PacketError::TooShort)
}

/// Apply header protection to a sealed packet. `packet` is exactly this packet (it must not run into a coalesced
/// one), with the packet number written at `layout`.
///
/// # Errors
/// [`PacketError::TooShort`] if the packet cannot be sampled, [`PacketError::Record`] for a bad packet-number length.
pub fn protect_header<P: Provider>(
    hk: &HeaderKey<P>,
    p: &P,
    packet: &mut [u8],
    layout: PnLayout,
) -> Result<(), PacketError> {
    let sample = sample_at(packet, layout.pn_off)?;
    let (head, tail) = packet
        .split_at_mut_checked(layout.pn_off)
        .ok_or(PacketError::TooShort)?;
    let first = head.first_mut().ok_or(PacketError::TooShort)?;
    let pn = tail.get_mut(..layout.pn_len).ok_or(PacketError::TooShort)?;
    hk.protect(p, first, pn, &sample, layout.long)?;
    Ok(())
}

/// Remove header protection from `packet` in place and read the packet-number field. The bytes are unspecified if
/// this fails.
///
/// # Errors
/// [`PacketError::TooShort`] if the packet cannot be sampled, [`PacketError::Reserved`] if a reserved bit (bits 3 and
/// 2 of the first byte) is set once unmasked.
pub fn unprotect_header<P: Provider>(
    hk: &HeaderKey<P>,
    p: &P,
    packet: &mut [u8],
    pn_off: usize,
    long: bool,
) -> Result<Unprotected, PacketError> {
    let sample = sample_at(packet, pn_off)?;
    let (head, tail) = packet.split_at_mut_checked(pn_off).ok_or(PacketError::TooShort)?;
    let first = head.first_mut().ok_or(PacketError::TooShort)?;
    let pn_len = hk.unprotect(p, first, tail, &sample, long)?;
    if *first & 0b0000_1100 != 0 {
        return Err(PacketError::Reserved);
    }
    let truncated = tail
        .get(..pn_len)
        .ok_or(PacketError::TooShort)?
        .iter()
        .fold(0u32, |acc, b| (acc << 8) | u32::from(*b));
    Ok(Unprotected {
        first: *first,
        pn_len,
        truncated,
    })
}

/// Seal a packet in place and protect its header; returns the packet length.
///
/// `packet` holds the unprotected header up to and including the truncated packet number (`layout.pn_off +
/// layout.pn_len` bytes), then `payload_len` bytes of frames, then room for the 16-byte tag. The header is the
/// associated data; the caller wrote the truncated form of `pn` into it.
///
/// # Errors
/// [`PacketError::TooShort`] if the packet number and payload together are under 4 bytes (no sample), a
/// [`PacketError::Wire`] if the buffer lacks room for the tag, [`PacketError::Record`] from the seal.
pub fn seal<P: Provider>(
    key: &mut PacketKey<P>,
    hk: &HeaderKey<P>,
    p: &P,
    packet: &mut [u8],
    layout: PnLayout,
    payload_len: usize,
    pn: u64,
) -> Result<usize, PacketError> {
    if layout.pn_len.saturating_add(payload_len) < SAMPLE_SKIP {
        return Err(PacketError::TooShort);
    }
    let header_len = layout.pn_off.saturating_add(layout.pn_len);
    let total = header_len.saturating_add(payload_len).saturating_add(Aead::TAG_LEN);
    let short = total.saturating_sub(packet.len());
    let whole = packet
        .get_mut(..total)
        .ok_or(WireError::BufferTooSmall { needed: short })?;
    let (header, body) = whole.split_at_mut_checked(header_len).ok_or(PacketError::TooShort)?;
    let (payload, tag_slot) = body.split_at_mut_checked(payload_len).ok_or(PacketError::TooShort)?;
    let tag = key.seal(p, pn, header, payload)?;
    tag_slot.copy_from_slice(&tag);
    protect_header(hk, p, whole, layout)?;
    Ok(total)
}

/// Verify and decrypt a packet in place after [`unprotect_header`]. `packet` is exactly this packet; `pn_off` is the
/// packet-number offset given to `unprotect_header`. The packet number is expanded against `largest_received`.
///
/// # Errors
/// [`PacketError::TooShort`] if the packet cannot hold a tag, [`PacketError::PacketNumber`] for a number of 2^62 or
/// more, [`PacketError::Record`] (authentication, key limits) from the open.
pub fn open<P: Provider>(
    key: &mut PacketKey<P>,
    p: &P,
    packet: &mut [u8],
    pn_off: usize,
    header: &Unprotected,
    largest_received: Option<u64>,
) -> Result<Opened, PacketError> {
    let pn = decode_pn(header.truncated, header.pn_len, largest_received);
    if pn > MAX_PN {
        return Err(PacketError::PacketNumber);
    }
    let header_len = pn_off.saturating_add(header.pn_len);
    let (aad, body) = packet.split_at_mut_checked(header_len).ok_or(PacketError::TooShort)?;
    let payload_len = body.len().checked_sub(Aead::TAG_LEN).ok_or(PacketError::TooShort)?;
    let (payload, tag) = body.split_at_mut(payload_len);
    let tag = tag
        .first_chunk::<{ Aead::TAG_LEN }>()
        .copied()
        .ok_or(PacketError::TooShort)?;
    key.open(p, pn, aad, payload, &tag)?;
    Ok(Opened {
        pn,
        payload_start: header_len,
        payload_end: header_len + payload_len,
    })
}
