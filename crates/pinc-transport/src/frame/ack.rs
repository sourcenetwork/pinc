//! The ACK frame: canonical range encoding and a validated, allocation-free range iterator.

use core::ops::RangeInclusive;

use pinc_wire::{Reader, Writer, varint};

use super::{FrameError, ty};
use crate::packet::MAX_PN;

/// The most ranges an ACK carries, on the wire and as encoded.
pub const MAX_ACK_RANGES: usize = 32;

/// A decoded ACK whose ranges were validated: it borrows the raw range bytes and yields them with [`Ack::ranges`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ack<'a> {
    largest: u64,
    first_range: u64,
    extra: usize,
    tail: &'a [u8],
}

impl<'a> Ack<'a> {
    /// The highest packet number acknowledged.
    pub const fn largest(&self) -> u64 {
        self.largest
    }

    /// How many ranges the ACK holds, 1 to [`MAX_ACK_RANGES`].
    pub const fn range_count(&self) -> usize {
        self.extra + 1
    }

    /// The acknowledged ranges, inclusive, highest first.
    pub fn ranges(&self) -> AckRanges<'a> {
        AckRanges {
            first: self.largest.checked_sub(self.first_range).map(|s| s..=self.largest),
            prev_start: self.largest,
            left: self.extra,
            r: Reader::new(self.tail),
        }
    }

    /// Decode the fields after the type, validating every range.
    pub(super) fn parse(r: &mut Reader<'a>) -> Result<Self, FrameError> {
        let largest = r.read_varint()?;
        if largest > MAX_PN {
            return Err(FrameError::Ack);
        }
        let extra = usize::try_from(r.read_varint()?).map_err(|_| FrameError::TooManyRanges)?;
        if extra >= MAX_ACK_RANGES {
            return Err(FrameError::TooManyRanges);
        }
        let first_range = r.read_varint()?;
        let mut prev_start = largest.checked_sub(first_range).ok_or(FrameError::Ack)?;
        let mut probe = *r;
        for _ in 0..extra {
            let gap = probe.read_varint()?;
            let len = probe.read_varint()?;
            let end = prev_start
                .checked_sub(gap)
                .and_then(|v| v.checked_sub(2))
                .ok_or(FrameError::Ack)?;
            prev_start = end.checked_sub(len).ok_or(FrameError::Ack)?;
        }
        let tail = r.read_bytes(probe.position().saturating_sub(r.position()))?;
        Ok(Self {
            largest,
            first_range,
            extra,
            tail,
        })
    }

    /// The encoded size after the type.
    pub(super) fn body_len(&self) -> usize {
        [self.largest, self.extra as u64, self.first_range]
            .iter()
            .map(|v| varint::encoded_len(*v))
            .sum::<usize>()
            + self.tail.len()
    }

    /// Write the fields after the type; the room was checked.
    pub(super) fn write_body(&self, w: &mut Writer<'_>) -> Result<(), FrameError> {
        w.put_varint(self.largest)?;
        w.put_varint(self.extra as u64)?;
        w.put_varint(self.first_range)?;
        w.put_slice(self.tail)?;
        Ok(())
    }
}

/// The inclusive packet-number ranges of an [`Ack`], highest first.
#[derive(Debug, Clone)]
pub struct AckRanges<'a> {
    first: Option<RangeInclusive<u64>>,
    prev_start: u64,
    left: usize,
    r: Reader<'a>,
}

impl Iterator for AckRanges<'_> {
    type Item = RangeInclusive<u64>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(first) = self.first.take() {
            self.prev_start = *first.start();
            return Some(first);
        }
        if self.left == 0 {
            return None;
        }
        self.left -= 1;
        let gap = self.r.read_varint().ok()?;
        let len = self.r.read_varint().ok()?;
        let end = self.prev_start.checked_sub(gap)?.checked_sub(2)?;
        let start = end.checked_sub(len)?;
        self.prev_start = start;
        Some(start..=end)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.left + usize::from(self.first.is_some());
        (n, Some(n))
    }
}

/// The wire fields of the ranges: the first item is `(largest, first_range)`, every later one `(gap, length)`.
/// At most [`MAX_ACK_RANGES`] ranges are taken; a malformed one yields [`FrameError::Ack`].
fn wire_fields(
    ranges: impl Iterator<Item = RangeInclusive<u64>>,
) -> impl Iterator<Item = Result<(u64, u64), FrameError>> {
    let mut prev_start: Option<u64> = None;
    ranges.take(MAX_ACK_RANGES).map(move |r| {
        let (start, end) = (*r.start(), *r.end());
        if start > end || end > MAX_PN {
            return Err(FrameError::Ack);
        }
        let item = match prev_start {
            None => (end, end - start),
            Some(prev) => {
                let gap = prev
                    .checked_sub(end)
                    .and_then(|d| d.checked_sub(2))
                    .ok_or(FrameError::Ack)?;
                (gap, end - start)
            }
        };
        prev_start = Some(start);
        Ok(item)
    })
}

/// Validate `ranges` and return how many will be written and the encoded size of the frame after the type.
fn shape(ranges: impl Iterator<Item = RangeInclusive<u64>>) -> Result<(usize, usize), FrameError> {
    let (mut count, mut len, mut largest, mut first_range) = (0usize, 0usize, 0u64, 0u64);
    for item in wire_fields(ranges) {
        let (a, b) = item?;
        if count == 0 {
            (largest, first_range) = (a, b);
        } else {
            len += varint::encoded_len(a) + varint::encoded_len(b);
        }
        count += 1;
    }
    if count == 0 {
        return Err(FrameError::Ack);
    }
    let head = [largest, (count - 1) as u64, first_range];
    Ok((count, len + head.iter().map(|v| varint::encoded_len(*v)).sum::<usize>()))
}

/// The encoded size of an ACK frame (type included) for `ranges`, highest first, trimmed to [`MAX_ACK_RANGES`].
///
/// # Errors
/// [`FrameError::Ack`] if the ranges are empty, an empty range, above 2^62 - 1, out of order, touching or
/// overlapping (adjacent ranges must be merged by the caller).
pub fn ack_len<I>(ranges: I) -> Result<usize, FrameError>
where
    I: IntoIterator<Item = RangeInclusive<u64>>,
{
    Ok(1 + shape(ranges.into_iter())?.1)
}

/// Encode an ACK frame for `ranges`, highest first, trimmed to the first [`MAX_ACK_RANGES`]. The range iterator is walked twice: once to validate and size, once to
/// write. Nothing is written on an error.
///
/// # Errors
/// As [`ack_len`], and a [`FrameError::Wire`] if the buffer is too small.
pub fn write_ack<I>(w: &mut Writer<'_>, ranges: I) -> Result<(), FrameError>
where
    I: IntoIterator<Item = RangeInclusive<u64>>,
    I::IntoIter: Clone,
{
    let ranges = ranges.into_iter();
    let (count, body) = shape(ranges.clone())?;
    w.ensure(1 + body)?;
    let mut fields = wire_fields(ranges);
    let (largest, first_range) = fields.next().ok_or(FrameError::Ack)??;
    w.put_varint(ty::ACK)?;
    w.put_varint(largest)?;
    w.put_varint((count - 1) as u64)?;
    w.put_varint(first_range)?;
    for item in fields {
        let (gap, len) = item?;
        w.put_varint(gap)?;
        w.put_varint(len)?;
    }
    Ok(())
}
