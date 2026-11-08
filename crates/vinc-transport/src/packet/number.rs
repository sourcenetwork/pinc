//! Packet-number truncation and expansion (RFC 9000 appendices A.2 and A.3) over 62 bits.

use vinc_security::record::MAX_PACKET_NUMBER;

use super::PacketError;

/// The largest packet number: 2^62 - 1.
pub const MAX_PN: u64 = MAX_PACKET_NUMBER;
/// The longest truncated packet number, in bytes.
pub const MAX_PN_LEN: usize = 4;

/// Truncate `full` for the wire, given the largest packet number the peer acknowledged (`None` if none yet).
///
/// The length is the smallest of 1 to 4 bytes that covers more than twice the distance to `largest_acked`
/// (RFC 9000 A.2). The result holds the big-endian low bytes at the start of the array, and the length.
///
/// # Errors
/// [`PacketError::PacketNumber`] if `full` exceeds [`MAX_PN`], or is not above `largest_acked`.
pub fn encode_pn(full: u64, largest_acked: Option<u64>) -> Result<([u8; MAX_PN_LEN], usize), PacketError> {
    if full > MAX_PN {
        return Err(PacketError::PacketNumber);
    }
    let unacked = match largest_acked {
        Some(acked) => full
            .checked_sub(acked)
            .filter(|d| *d > 0)
            .ok_or(PacketError::PacketNumber)?,
        None => full + 1,
    };
    let bits = unacked.bit_width() as usize + 1;
    let len = bits.div_ceil(8).clamp(1, MAX_PN_LEN);
    let be = full.to_be_bytes();
    let mut out = [0u8; MAX_PN_LEN];
    let low = be.get(be.len() - len..).ok_or(PacketError::PnLength)?;
    out.get_mut(..len).ok_or(PacketError::PnLength)?.copy_from_slice(low);
    Ok((out, len))
}

/// Expand a truncated packet number of `len` bytes to the closest candidate to the next expected one
/// (RFC 9000 A.3). `len` is clamped to 1 to 4.
///
/// The result can reach 2^62 or more only for input at the very edge of the space; sealing and opening refuse such a
/// number with a [`PacketError`].
pub fn decode_pn(truncated: u32, len: usize, largest_received: Option<u64>) -> u64 {
    let len = len.clamp(1, MAX_PN_LEN);
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
