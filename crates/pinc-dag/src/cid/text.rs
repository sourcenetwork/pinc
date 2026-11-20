//! Multibase base32 lower (`b` prefix, RFC 4648 lowercase alphabet, no padding) of CID bytes.

use super::{CidError, MAX_LEN};

/// The longest text of a CID: the `b` prefix and the base32 digits of [`MAX_LEN`] bytes.
pub const MAX_TEXT_LEN: usize = 1 + (MAX_LEN * 8).div_ceil(5);

const ALPHABET: &[u8; 32] = b"abcdefghijklmnopqrstuvwxyz234567";

/// The text characters of `bytes`, prefix included, produced lazily.
pub(super) fn chars(bytes: &[u8]) -> impl Iterator<Item = u8> + '_ {
    let mut input = bytes.iter();
    let (mut acc, mut bits) = (0u16, 0u32);
    core::iter::once(b'b').chain(core::iter::from_fn(move || {
        while bits < 5 {
            let Some(&b) = input.next() else { break };
            acc = acc << 8 | u16::from(b);
            bits += 8;
        }
        let digit = if bits >= 5 {
            bits -= 5;
            acc >> bits
        } else if bits > 0 {
            let tail = acc << (5 - bits);
            bits = 0;
            tail
        } else {
            return None;
        };
        acc &= (1 << bits) - 1;
        ALPHABET.get(usize::from(digit & 31)).copied()
    }))
}

/// Write the text of `bytes` into `out` and return it as `&str`.
pub(super) fn encode<'o>(bytes: &[u8], out: &'o mut [u8]) -> Result<&'o str, CidError> {
    let n = 1 + (bytes.len() * 8).div_ceil(5);
    let short = n.saturating_sub(out.len());
    let dst = out.get_mut(..n).ok_or(CidError::BufferTooSmall { needed: short })?;
    for (slot, c) in dst.iter_mut().zip(chars(bytes)) {
        *slot = c;
    }
    core::str::from_utf8(dst).map_err(|_| CidError::BadText("not ASCII"))
}

/// Decode CID text into `out` and return the byte count.
pub(super) fn decode(text: &str, out: &mut [u8; MAX_LEN]) -> Result<usize, CidError> {
    let Some(digits) = text.as_bytes().strip_prefix(b"b") else {
        return Err(CidError::BadText("missing the b prefix"));
    };
    let (mut acc, mut bits, mut n) = (0u16, 0u32, 0usize);
    for &c in digits {
        let v = match c {
            b'a'..=b'z' => c - b'a',
            b'2'..=b'7' => c - b'2' + 26,
            _ => return Err(CidError::BadText("character outside the base32 lower alphabet")),
        };
        acc = acc << 5 | u16::from(v);
        bits += 5;
        if bits >= 8 {
            bits -= 8;
            let byte = u8::try_from(acc >> bits).map_err(|_| CidError::BadText("bad digit"))?;
            *out.get_mut(n).ok_or(CidError::BadText("longer than any CID"))? = byte;
            n += 1;
            acc &= (1 << bits) - 1;
        }
    }
    if bits >= 5 {
        return Err(CidError::BadText("the text is not a whole number of bytes"));
    }
    if acc != 0 {
        return Err(CidError::BadText("padding bits are not zero"));
    }
    Ok(n)
}
