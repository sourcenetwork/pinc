//! Reading a CAR from one complete borrowed buffer.

use vinc_wire::cbor::{Decoder, Item, MapReader};

use super::{CarError, Frame, Roots, frame, split_section};
use crate::cid::CidRef;

/// Parse a header body into its roots, requiring exactly `roots` and `version` 1.
pub(super) fn parse_header(body: &[u8]) -> Result<Roots<'_>, CarError> {
    let mut dec = Decoder::new(body);
    let mut map = MapReader::new(&mut dec)?;
    let (mut roots, mut version) = (None, false);
    while let Some(key) = map.next_key(&mut dec)? {
        match key {
            "roots" => roots = Some(Roots::read(&mut dec, body)?),
            "version" => match dec.next_item()? {
                Item::Unsigned(1) => version = true,
                _ => return Err(CarError::BadHeader("version is not 1")),
            },
            _ => return Err(CarError::BadHeader("unknown key")),
        }
    }
    if !dec.is_empty() {
        return Err(CarError::BadHeader("bytes follow the header map"));
    }
    match roots {
        Some(roots) if version => Ok(roots),
        _ => Err(CarError::BadHeader("roots and version are required")),
    }
}

/// A CAR v1 in one borrowed buffer, with its header already parsed.
#[derive(Debug, Clone)]
pub struct CarReader<'a> {
    roots: Roots<'a>,
    rest: &'a [u8],
    max: usize,
    verify: bool,
}

impl<'a> CarReader<'a> {
    /// Parse the header of the CAR in `buf`; no section is read yet.
    ///
    /// `max_section` bounds the header and every section, counted in bytes after the length prefix.
    ///
    /// # Errors
    /// [`CarError::Truncated`] if the header is cut short, [`CarError::TooLarge`] past `max_section`,
    /// [`CarError::BadHeader`] and [`CarError::Wire`] for a malformed header, [`CarError::Cid`] for a bad root.
    pub fn new(buf: &'a [u8], max_section: usize) -> Result<Self, CarError> {
        match frame(buf, max_section)? {
            Frame::Need(needed) => Err(CarError::Truncated { needed }),
            Frame::Ready { consumed, body } => Ok(Self {
                roots: parse_header(body)?,
                rest: buf.get(consumed..).unwrap_or_default(),
                max: max_section,
                verify: false,
            }),
        }
    }

    /// Check every section's block against its CID while iterating (off by default).
    #[must_use]
    pub const fn with_verify(mut self, verify: bool) -> Self {
        self.verify = verify;
        self
    }

    /// The roots named by the header.
    pub fn roots(&self) -> Roots<'a> {
        self.roots.clone()
    }

    /// The sections, in order. Each call starts again from the first section.
    pub fn sections(&self) -> Sections<'a> {
        Sections {
            rest: self.rest,
            max: self.max,
            verify: self.verify,
        }
    }
}

/// Iterator over the sections of a [`CarReader`]: the CID and the block bytes.
///
/// After an error the iterator ends. Input that stops exactly between two sections is a complete, shorter CAR.
#[derive(Debug, Clone)]
pub struct Sections<'a> {
    rest: &'a [u8],
    max: usize,
    verify: bool,
}

impl<'a> Iterator for Sections<'a> {
    type Item = Result<(CidRef<'a>, &'a [u8]), CarError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.rest.is_empty() {
            return None;
        }
        let step = match frame(self.rest, self.max) {
            Ok(Frame::Ready { consumed, body }) => {
                self.rest = self.rest.get(consumed..).unwrap_or_default();
                split_section(body, self.verify)
            }
            Ok(Frame::Need(needed)) => Err(CarError::Truncated { needed }),
            Err(e) => Err(e),
        };
        if step.is_err() {
            self.rest = &[];
        }
        Some(step)
    }
}
