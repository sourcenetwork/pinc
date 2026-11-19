//! Packet-number truncation and expansion over 62 bits, at a width fixed per connection.

use pinc_security::record::MAX_PACKET_NUMBER;

use super::PacketError;

/// The largest packet number: 2^62 - 1.
pub const MAX_PN: u64 = MAX_PACKET_NUMBER;
/// The packet-number width of a connection whose granted window is at most [`WIDE_WINDOW`]: 2 bytes.
pub const PN_LEN_BASE: usize = 2;
/// The packet-number width of a connection whose granted window is above [`WIDE_WINDOW`]: 3 bytes.
pub const PN_LEN_WIDE: usize = 3;
/// A granted window above this many bytes (40 MB) needs the wide packet number: more than 32,768 packets can be in
/// flight.
pub const WIDE_WINDOW: u64 = 40_000_000;

/// The packet-number width of a connection whose larger granted window is `window` bytes. Both ends know both
/// windows from the credit records, so both compute the same width.
pub const fn pn_len_for(window: u64) -> usize {
    if window > WIDE_WINDOW { PN_LEN_WIDE } else { PN_LEN_BASE }
}

/// Truncate `full` to `len` bytes (2 or 3) for the wire: the big-endian low bytes at the start of the array.
///
/// # Errors
/// [`PacketError::PacketNumber`] if `full` exceeds [`MAX_PN`], [`PacketError::PnLength`] if `len` is not 2 or 3.
pub fn encode_pn(full: u64, len: usize) -> Result<[u8; 3], PacketError> {
    if full > MAX_PN {
        return Err(PacketError::PacketNumber);
    }
    if !(PN_LEN_BASE..=PN_LEN_WIDE).contains(&len) {
        return Err(PacketError::PnLength);
    }
    let be = full.to_be_bytes();
    let low = be.get(be.len() - len..).ok_or(PacketError::PnLength)?;
    let mut out = [0u8; 3];
    out.get_mut(..len).ok_or(PacketError::PnLength)?.copy_from_slice(low);
    Ok(out)
}

/// Expand a truncated packet number of `len` bytes to the closest candidate to the next expected one. `len` is
/// clamped to 1 to 4.
///
/// The result can reach 2^62 or more only for input at the very edge of the space; sealing and opening refuse such a
/// number with a [`PacketError`].
pub fn decode_pn(truncated: u32, len: usize, largest_received: Option<u64>) -> u64 {
    let len = len.clamp(1, 4);
    let expected = largest_received.map_or(0, |l| l.saturating_add(1));
    let win = 1u64 << (8 * len);
    let half = win / 2;
    let mask = win - 1;
    let candidate = (expected & !mask) | (u64::from(truncated) & mask);
    if candidate.saturating_add(half) <= expected && candidate < (1u64 << 62) - win {
        candidate + win
    } else if candidate > expected.saturating_add(half) && candidate >= win {
        candidate - win
    } else {
        candidate
    }
}
