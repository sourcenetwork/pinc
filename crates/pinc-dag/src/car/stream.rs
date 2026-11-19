//! Decoding a CAR from streamed input, one frame at a time.

use super::reader::parse_header;
use super::{CarError, Frame, Roots, frame, split_section};
use crate::cid::CidRef;

/// What [`CarDecoder::decode`] found at the start of its input.
#[derive(Debug, Clone)]
pub enum Decoded<'a> {
    /// The frame is incomplete: append at least this many more bytes to the input and call again.
    NeedMore(usize),
    /// The header, which took `consumed` bytes.
    Header {
        /// Bytes to drop from the front of the input.
        consumed: usize,
        /// The roots, borrowed from the input.
        roots: Roots<'a>,
    },
    /// One section, which took `consumed` bytes.
    Section {
        /// Bytes to drop from the front of the input.
        consumed: usize,
        /// The section CID, borrowed from the input.
        cid: CidRef<'a>,
        /// The block, borrowed from the input.
        block: &'a [u8],
    },
}

/// An incremental CAR decoder that keeps no input of its own.
///
/// Contract: the caller owns one buffer holding the not yet consumed bytes. It calls [`CarDecoder::decode`] on that
/// buffer; on [`Decoded::NeedMore`] it reads at least that many more bytes onto the end of the buffer and calls again,
/// and on [`Decoded::Header`] or [`Decoded::Section`] it uses the borrowed result, then drops `consumed` bytes from
/// the front. The length prefix is checked against the maximum as soon as it is complete, before the body is
/// requested, so the buffer never needs more than `max_section` plus a 9 byte prefix: memory is bounded by one
/// section whatever the stream holds. The header comes first, then sections; end of stream between frames is a
/// complete CAR, end of stream inside a frame is a truncation the caller reports.
#[derive(Debug, Clone, Copy)]
pub struct CarDecoder {
    max: usize,
    verify: bool,
    header_done: bool,
}

impl CarDecoder {
    /// A decoder expecting the header first; `max_section` bounds the header and every section.
    pub const fn new(max_section: usize) -> Self {
        Self {
            max: max_section,
            verify: false,
            header_done: false,
        }
    }

    /// Check every section's block against its CID (off by default).
    #[must_use]
    pub const fn with_verify(mut self, verify: bool) -> Self {
        self.verify = verify;
        self
    }

    /// Decode the next frame at the start of `input`.
    ///
    /// # Errors
    /// [`CarError::TooLarge`] past the maximum, [`CarError::BadHeader`], [`CarError::Wire`] and [`CarError::Cid`] for
    /// malformed frames. After an error the stream cannot be resynchronised; stop.
    pub fn decode<'a>(&mut self, input: &'a [u8]) -> Result<Decoded<'a>, CarError> {
        match frame(input, self.max)? {
            Frame::Need(n) => Ok(Decoded::NeedMore(n)),
            Frame::Ready { consumed, body } if self.header_done => {
                let (cid, block) = split_section(body, self.verify)?;
                Ok(Decoded::Section { consumed, cid, block })
            }
            Frame::Ready { consumed, body } => {
                let roots = parse_header(body)?;
                self.header_done = true;
                Ok(Decoded::Header { consumed, roots })
            }
        }
    }
}
