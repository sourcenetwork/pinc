//! The multiformats unsigned varint (unsigned LEB128).
//!
//! Invariants: an encoding is at most 9 bytes, the value is below 2^63, and the encoding is minimal (no trailing
//! zero continuation byte). `decode` accepts exactly what `encode` produces.

use crate::error::WireError;

/// The longest valid varint, in bytes.
pub const MAX_LEN: usize = 9;

/// The first value that cannot be encoded.
const LIMIT: u64 = 1 << 63;

/// The encoded size of `value` in bytes; `value` must be below 2^63 to be encodable.
pub const fn encoded_len(value: u64) -> usize {
    let bits = value.bit_width() as usize;
    if bits == 0 { 1 } else { bits.div_ceil(7) }
}

/// Encode `value` into the start of `out` and return the number of bytes written.
///
/// # Errors
/// [`WireError::VarintOverflow`] if `value` is 2^63 or more, [`WireError::BufferTooSmall`] if `out` is short; in both
/// cases `out` is untouched.
#[allow(clippy::cast_possible_truncation, reason = "each group is masked to 7 bits")]
pub fn encode(value: u64, out: &mut [u8]) -> Result<usize, WireError> {
    if value >= LIMIT {
        return Err(WireError::VarintOverflow);
    }
    let n = encoded_len(value);
    let short = n.saturating_sub(out.len());
    let slot = out.get_mut(..n).ok_or(WireError::BufferTooSmall { needed: short })?;
    for (i, b) in slot.iter_mut().enumerate() {
        let group = ((value >> (7 * i)) & 0x7f) as u8;
        *b = if i + 1 < n { group | 0x80 } else { group };
    }
    Ok(n)
}

/// Decode a varint from the start of `input`, returning the value and the bytes consumed.
///
/// # Errors
/// [`WireError::Truncated`] if the input ends inside the varint, [`WireError::VarintTooLong`] past 9 bytes,
/// [`WireError::VarintNonMinimal`] for a trailing zero byte.
pub fn decode(input: &[u8]) -> Result<(u64, usize), WireError> {
    let mut value = 0u64;
    for (i, &b) in input.iter().take(MAX_LEN).enumerate() {
        value |= u64::from(b & 0x7f) << (7 * i);
        if b & 0x80 == 0 {
            if b == 0 && i > 0 {
                return Err(WireError::VarintNonMinimal);
            }
            return Ok((value, i + 1));
        }
    }
    if input.len() >= MAX_LEN {
        Err(WireError::VarintTooLong)
    } else {
        Err(WireError::Truncated { needed: 1 })
    }
}
