//! The pull decoder: one item per call, parsed in place, every byte read once.

use super::{Item, MAX_DEPTH, TAG_CID, check_key_order};
use crate::error::WireError;
use crate::reader::Reader;

/// A strict DAG-CBOR pull decoder over borrowed bytes.
///
/// After an error the decoder position is unspecified; stop using it.
#[derive(Debug, Clone, Copy)]
pub struct Decoder<'a> {
    r: Reader<'a>,
    cid_pending: bool,
}

/// One open container in [`Decoder::skip_value`].
#[derive(Clone, Copy)]
struct Frame<'a> {
    /// Items still to read (a map counts a key and its value separately).
    left: u64,
    map: bool,
    prev_key: Option<&'a str>,
}

impl<'a> Decoder<'a> {
    /// A decoder at the start of `buf`.
    pub const fn new(buf: &'a [u8]) -> Self {
        Self {
            r: Reader::new(buf),
            cid_pending: false,
        }
    }

    /// Bytes not yet consumed.
    pub const fn remaining(&self) -> usize {
        self.r.remaining()
    }

    /// Bytes consumed so far.
    pub const fn position(&self) -> usize {
        self.r.position()
    }

    /// Whether every byte has been consumed.
    pub const fn is_empty(&self) -> bool {
        self.r.is_empty()
    }

    /// Decode the next item.
    ///
    /// # Errors
    /// [`WireError::Truncated`] on short input, [`WireError::NonCanonical`] on any DAG-CBOR strictness violation.
    pub fn next_item(&mut self) -> Result<Item<'a>, WireError> {
        let item = self.read_item()?;
        if core::mem::take(&mut self.cid_pending) && !matches!(item, Item::Bytes([0, ..])) {
            return Err(WireError::NonCanonical(
                "tag 42 content must be a byte string starting with 0x00",
            ));
        }
        self.cid_pending = matches!(item, Item::Tag(_));
        Ok(item)
    }

    /// Skip one complete item, nested arrays and maps included, validating all of it.
    ///
    /// Iterative: pending items are tracked on a fixed stack of [`MAX_DEPTH`] frames, never by recursion.
    ///
    /// # Errors
    /// Any [`Decoder::next_item`] error, [`WireError::DepthExceeded`] past [`MAX_DEPTH`] open containers, and
    /// [`WireError::NonCanonical`] for map keys that are not text, or are duplicated or out of order.
    pub fn skip_value(&mut self) -> Result<(), WireError> {
        // Scalars (majors 0-3 and 7) need no frame stack.
        if !matches!(self.r.peek_u8()? >> 5, 4..=6) {
            return self.next_item().map(drop);
        }
        let mut stack = [Frame {
            left: 0,
            map: false,
            prev_key: None,
        }; MAX_DEPTH];
        let mut depth = 0usize;
        loop {
            let top = depth.checked_sub(1);
            let key_turn = top.and_then(|i| stack.get(i)).is_some_and(|f| f.map && f.left % 2 == 0);
            let item = self.next_item()?;
            if let Some(frame) = top.and_then(|i| stack.get_mut(i)) {
                if key_turn {
                    let Item::Text(key) = item else {
                        return Err(WireError::NonCanonical("map keys must be text strings"));
                    };
                    check_key_order(frame.prev_key, key)?;
                    frame.prev_key = Some(key);
                }
                frame.left = frame.left.saturating_sub(1);
            }
            let (left, map) = match item {
                Item::Array(n) => (n, false),
                Item::Map(n) => (
                    n.checked_mul(2).ok_or(WireError::Truncated { needed: usize::MAX })?,
                    true,
                ),
                Item::Tag(_) => (1, false),
                _ => (0, false),
            };
            if left > 0 {
                *stack.get_mut(depth).ok_or(WireError::DepthExceeded)? = Frame {
                    left,
                    map,
                    prev_key: None,
                };
                depth += 1;
            }
            while let Some(i) = depth.checked_sub(1)
                && stack.get(i).is_some_and(|f| f.left == 0)
            {
                depth = i;
            }
            if depth == 0 {
                return Ok(());
            }
        }
    }

    fn read_item(&mut self) -> Result<Item<'a>, WireError> {
        let initial = self.r.read_u8()?;
        let (major, info) = (initial >> 5, initial & 0x1f);
        if major == 7 {
            return self.read_simple(info);
        }
        let arg = self.read_arg(info)?;
        Ok(match major {
            0 => Item::Unsigned(arg),
            1 => Item::Negative(arg),
            2 => Item::Bytes(self.read_payload(arg)?),
            3 => Item::Text(
                core::str::from_utf8(self.read_payload(arg)?)
                    .map_err(|_| WireError::NonCanonical("text is not valid UTF-8"))?,
            ),
            4 => Item::Array(arg),
            5 => Item::Map(arg),
            _ if arg == TAG_CID => Item::Tag(arg),
            _ => return Err(WireError::NonCanonical("only tag 42 is allowed")),
        })
    }

    /// The argument of a header, rejecting any non-minimal width and every non-definite form.
    fn read_arg(&mut self, info: u8) -> Result<u64, WireError> {
        const NON_MINIMAL: WireError = WireError::NonCanonical("argument is not minimally encoded");
        let (arg, min) = match info {
            0..=23 => return Ok(u64::from(info)),
            24 => (u64::from(self.r.read_u8()?), 24),
            25 => (u64::from(self.r.read_u16()?), 1 << 8),
            26 => (u64::from(self.r.read_u32()?), 1 << 16),
            27 => (self.r.read_u64()?, 1 << 32),
            28..=30 => return Err(WireError::NonCanonical("reserved additional information")),
            _ => return Err(WireError::NonCanonical("indefinite lengths are not allowed")),
        };
        if arg < min { Err(NON_MINIMAL) } else { Ok(arg) }
    }

    fn read_payload(&mut self, len: u64) -> Result<&'a [u8], WireError> {
        let n = usize::try_from(len).map_err(|_| WireError::Truncated { needed: usize::MAX })?;
        self.r.read_bytes(n)
    }

    fn read_simple(&mut self, info: u8) -> Result<Item<'a>, WireError> {
        match info {
            20 => Ok(Item::Bool(false)),
            21 => Ok(Item::Bool(true)),
            22 => Ok(Item::Null),
            25 | 26 => Err(WireError::NonCanonical("floats must be 64-bit")),
            27 => {
                let f = f64::from_bits(self.r.read_u64()?);
                if f.is_finite() {
                    Ok(Item::Float(f))
                } else {
                    Err(WireError::NonCanonical("NaN and infinity are not allowed"))
                }
            }
            28..=31 => Err(WireError::NonCanonical("reserved or indefinite form")),
            _ => Err(WireError::NonCanonical(
                "undefined and other simple values are not allowed",
            )),
        }
    }
}

/// Iterates the keys of one map, enforcing text keys, uniqueness and canonical order.
///
/// The caller must consume each value (decode it or [`Decoder::skip_value`]) before asking for the next key.
#[derive(Debug, Clone, Copy)]
pub struct MapReader<'a> {
    left: u64,
    prev_key: Option<&'a str>,
}

impl<'a> MapReader<'a> {
    /// Read a map header from `dec`.
    ///
    /// # Errors
    /// [`WireError::Unexpected`] if the next item is not a map, plus any [`Decoder::next_item`] error.
    pub fn new(dec: &mut Decoder<'a>) -> Result<Self, WireError> {
        match dec.next_item()? {
            Item::Map(left) => Ok(Self { left, prev_key: None }),
            _ => Err(WireError::Unexpected("expected a map")),
        }
    }

    /// Entries not yet read.
    pub const fn remaining(&self) -> u64 {
        self.left
    }

    /// The next key, or `None` once every entry has been read; the value follows in `dec`.
    ///
    /// # Errors
    /// [`WireError::NonCanonical`] for a non-text, duplicate or out-of-order key, plus any decode error.
    pub fn next_key(&mut self, dec: &mut Decoder<'a>) -> Result<Option<&'a str>, WireError> {
        if self.left == 0 {
            return Ok(None);
        }
        let Item::Text(key) = dec.next_item()? else {
            return Err(WireError::NonCanonical("map keys must be text strings"));
        };
        check_key_order(self.prev_key, key)?;
        self.prev_key = Some(key);
        self.left -= 1;
        Ok(Some(key))
    }
}
