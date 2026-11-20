//! The canonical encoder: minimal arguments, definite lengths, 64-bit floats, ordered map keys.

use super::{TAG_CID, check_key_order};
use crate::error::WireError;
use crate::writer::Writer;

/// Writes canonical DAG-CBOR into a caller buffer.
///
/// Every method is atomic: on [`WireError::BufferTooSmall`] nothing is written.
#[derive(Debug)]
pub struct Encoder<'a> {
    w: Writer<'a>,
}

/// `(initial-byte info, trailing argument bytes)` of the minimal header for `arg`.
#[allow(
    clippy::cast_possible_truncation,
    reason = "the argument is range-checked by the match arm"
)]
const fn head_shape(arg: u64) -> (u8, usize) {
    match arg {
        0..=23 => (arg as u8, 0),
        24..=0xff => (24, 1),
        0x100..=0xffff => (25, 2),
        0x1_0000..=0xffff_ffff => (26, 4),
        _ => (27, 8),
    }
}

/// The size of the minimal header (initial byte plus argument) the encoder writes for `arg`.
#[must_use]
pub const fn head_len(arg: u64) -> usize {
    1 + head_shape(arg).1
}

impl<'a> Encoder<'a> {
    /// An encoder at the start of `buf`.
    pub const fn new(buf: &'a mut [u8]) -> Self {
        Self { w: Writer::new(buf) }
    }

    /// The bytes encoded so far.
    pub fn written(&self) -> &[u8] {
        self.w.written()
    }

    /// Write a header; the caller has already checked that it fits.
    fn head(&mut self, major: u8, arg: u64) -> Result<(), WireError> {
        let (info, tail) = head_shape(arg);
        self.w.put_u8(major << 5 | info)?;
        self.w.put_slice(arg.to_be_bytes().get(8 - tail..).unwrap_or_default())
    }

    fn string(&mut self, major: u8, payload: &[u8]) -> Result<(), WireError> {
        let len = payload.len() as u64;
        self.w.ensure(head_len(len).saturating_add(payload.len()))?;
        self.head(major, len)?;
        self.w.put_slice(payload)
    }

    fn header(&mut self, major: u8, arg: u64) -> Result<(), WireError> {
        self.w.ensure(head_len(arg))?;
        self.head(major, arg)
    }

    /// Write an unsigned integer.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn unsigned(&mut self, n: u64) -> Result<(), WireError> {
        self.header(0, n)
    }

    /// Write the negative integer `-1 - n`.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn negative(&mut self, n: u64) -> Result<(), WireError> {
        self.header(1, n)
    }

    /// Write a byte string.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn bytes(&mut self, b: &[u8]) -> Result<(), WireError> {
        self.string(2, b)
    }

    /// Write a text string.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn text(&mut self, s: &str) -> Result<(), WireError> {
        self.string(3, s.as_bytes())
    }

    /// Write an array header for `len` elements, which the caller then writes.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn array(&mut self, len: u64) -> Result<(), WireError> {
        self.header(4, len)
    }

    /// Write a map header for `len` entries, which the caller then writes in canonical key order; prefer
    /// [`Encoder::ordered_map`] to have the order checked.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn map(&mut self, len: u64) -> Result<(), WireError> {
        self.header(5, len)
    }

    /// Write a CID: tag 42 over a byte string of `0x00` followed by `cid`.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn tag_cid(&mut self, cid: &[u8]) -> Result<(), WireError> {
        let len = cid.len() as u64 + 1;
        self.w.ensure(
            head_len(TAG_CID)
                .saturating_add(head_len(len))
                .saturating_add(cid.len() + 1),
        )?;
        self.head(6, TAG_CID)?;
        self.head(2, len)?;
        self.w.put_u8(0)?;
        self.w.put_slice(cid)
    }

    /// Write a boolean.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn bool(&mut self, v: bool) -> Result<(), WireError> {
        self.w.put_u8(0xf4 | u8::from(v))
    }

    /// Write null.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn null(&mut self) -> Result<(), WireError> {
        self.w.put_u8(0xf6)
    }

    /// Write a 64-bit float.
    ///
    /// # Errors
    /// [`WireError::NonCanonical`] for NaN or infinity, [`WireError::BufferTooSmall`] if it does not fit.
    pub fn float(&mut self, v: f64) -> Result<(), WireError> {
        if !v.is_finite() {
            return Err(WireError::NonCanonical("NaN and infinity are not allowed"));
        }
        self.w.ensure(9)?;
        self.w.put_u8(0xfb)?;
        self.w.put_u64(v.to_bits())
    }

    /// Write a map header for `len` entries and return the key-order tracker for it.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if the header does not fit.
    pub fn ordered_map<'k>(&mut self, len: u64) -> Result<MapKeys<'k>, WireError> {
        self.map(len)?;
        Ok(MapKeys {
            left: len,
            prev_key: None,
        })
    }
}

/// Tracks the keys of a map being written and rejects any that is out of canonical order or duplicated.
#[derive(Debug, Clone, Copy)]
pub struct MapKeys<'k> {
    left: u64,
    prev_key: Option<&'k str>,
}

impl<'k> MapKeys<'k> {
    /// Write the next key; the caller then writes its value.
    ///
    /// # Errors
    /// [`WireError::NonCanonical`] if `key` is a duplicate, out of order, or beyond the declared entry count;
    /// [`WireError::BufferTooSmall`] if it does not fit. Nothing is written on error.
    pub fn key(&mut self, enc: &mut Encoder<'_>, key: &'k str) -> Result<(), WireError> {
        if self.left == 0 {
            return Err(WireError::NonCanonical("more keys than the declared map length"));
        }
        check_key_order(self.prev_key, key)?;
        enc.text(key)?;
        self.prev_key = Some(key);
        self.left -= 1;
        Ok(())
    }

    /// Whether every declared key has been written.
    pub const fn is_complete(&self) -> bool {
        self.left == 0
    }
}
