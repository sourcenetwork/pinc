//! Tickets: what one node hands another so the other can reach it.
//!
//! A [`Ticket`] holds a node id and optional hints: its home relay and up to [`MAX_ADDRS`] addresses. The binary form
//! is compact and versioned; the text form is that binary in base32 (RFC 4648 alphabet, lowercase, no padding), safe
//! to put in a link or a QR code and read back in either case.
//!
//! Binary: `version(1) flags(1) node(33) [home(33)] addrs`. Version is 1. `flags` bit 0 says a home relay follows
//! the node, bits 1 to 3 hold the address count (0 to 4), the rest are zero. An address is `tag(1) ip(4 or 16)
//! port(2)` as in a record.
//!
//! A ticket carries no signature and no checksum: it only says where to try. A wrong or forged ticket costs one
//! failed handshake, because the handshake proves the node id. Invariants: [`Ticket::parse`] accepts exactly what
//! [`Ticket::encode`] writes (no trailing bytes, no reserved bit, no unknown version); the text form round-trips.

#![allow(clippy::doc_markdown, reason = "rule names are written as the rules call them")]

use core::net::SocketAddr;

use vinc_crypto::NodeId;
use vinc_wire::{Reader, WireError, Writer};

use crate::carrier::node;
use crate::record::{RecordError, read_addr, write_addr};

/// The current version.
pub const VERSION: u8 = 1;
/// The most addresses a ticket holds.
pub const MAX_ADDRS: usize = 4;
/// The longest binary ticket.
pub const MAX_LEN: usize = 2 + 2 * node::NODE_ID_LEN + MAX_ADDRS * 19;
/// The longest text ticket.
pub const MAX_TEXT: usize = MAX_LEN.div_ceil(5) * 8;

const ALPHABET: &[u8; 32] = b"abcdefghijklmnopqrstuvwxyz234567";

/// Why a ticket was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TicketError {
    /// The version is not 1.
    Version(u8),
    /// A reserved flag bit is set, or the address count is above [`MAX_ADDRS`].
    Flags(u8),
    /// A field is truncated, has trailing bytes after it, or the output is too small.
    Wire(WireError),
    /// An address is malformed.
    Addr(RecordError),
    /// The text holds a character outside the alphabet or has an impossible length.
    Text,
    /// More addresses than a ticket holds.
    TooManyAddrs,
}

impl From<WireError> for TicketError {
    fn from(e: WireError) -> Self {
        Self::Wire(e)
    }
}

impl core::fmt::Display for TicketError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Version(v) => write!(f, "ticket version {v} is not supported"),
            Self::Flags(_) => f.write_str("ticket flags are invalid"),
            Self::Wire(e) => write!(f, "ticket is malformed: {e}"),
            Self::Addr(e) => write!(f, "ticket address is malformed: {e}"),
            Self::Text => f.write_str("ticket text is not valid"),
            Self::TooManyAddrs => f.write_str("a ticket holds at most four addresses"),
        }
    }
}

impl core::error::Error for TicketError {}

/// A node id with optional hints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ticket {
    /// The node the ticket reaches.
    pub node: NodeId,
    /// The node's home relay, if the issuer knows it.
    pub home: Option<NodeId>,
    addrs: [Option<SocketAddr>; MAX_ADDRS],
}

impl Ticket {
    /// A ticket for `node` with no hints.
    pub const fn new(node: NodeId) -> Self {
        Self {
            node,
            home: None,
            addrs: [None; MAX_ADDRS],
        }
    }

    /// Add a hint address.
    ///
    /// # Errors
    /// [`TicketError::TooManyAddrs`] when [`MAX_ADDRS`] are already held.
    pub fn with_addr(mut self, a: SocketAddr) -> Result<Self, TicketError> {
        let slot = self
            .addrs
            .iter_mut()
            .find(|s| s.is_none())
            .ok_or(TicketError::TooManyAddrs)?;
        *slot = Some(a);
        Ok(self)
    }

    /// Set the home relay hint.
    #[must_use]
    pub const fn with_home(mut self, home: NodeId) -> Self {
        self.home = Some(home);
        self
    }

    /// The hint addresses.
    pub fn addrs(&self) -> impl Iterator<Item = SocketAddr> + '_ {
        self.addrs.iter().flatten().copied()
    }

    /// Write the binary form; returns its length.
    ///
    /// # Errors
    /// [`TicketError::Wire`] if `out` is too small.
    pub fn encode(&self, out: &mut [u8]) -> Result<usize, TicketError> {
        let n = self.addrs.iter().flatten().count();
        let mut w = Writer::new(out);
        w.put_u8(VERSION)?;
        w.put_u8(u8::from(self.home.is_some()) | (u8::try_from(n).unwrap_or(0) << 1))?;
        node::write(&mut w, &self.node)?;
        if let Some(h) = &self.home {
            node::write(&mut w, h)?;
        }
        for a in self.addrs.iter().flatten() {
            write_addr(&mut w, a)?;
        }
        Ok(w.written().len())
    }

    /// Read the binary form.
    ///
    /// # Errors
    /// A [`TicketError`] for anything [`Ticket::encode`] would not write.
    pub fn parse(bytes: &[u8]) -> Result<Self, TicketError> {
        let mut r = Reader::new(bytes);
        let v = r.read_u8()?;
        if v != VERSION {
            return Err(TicketError::Version(v));
        }
        let flags = r.read_u8()?;
        let count = usize::from(flags >> 1 & 7);
        if flags & 0xf0 != 0 || count > MAX_ADDRS {
            return Err(TicketError::Flags(flags));
        }
        let mut t = Self::new(node::read(&mut r)?);
        if flags & 1 != 0 {
            t.home = Some(node::read(&mut r)?);
        }
        for s in t.addrs.iter_mut().take(count) {
            *s = Some(read_addr(&mut r).map_err(TicketError::Addr)?);
        }
        if !r.is_empty() {
            return Err(TicketError::Wire(WireError::Unexpected("trailing bytes")));
        }
        Ok(t)
    }

    /// Write the text form (base32); returns its length.
    ///
    /// # Errors
    /// [`TicketError::Wire`] if `out` is too small.
    pub fn to_text(&self, out: &mut [u8]) -> Result<usize, TicketError> {
        let mut bin = [0u8; MAX_LEN];
        let n = self.encode(&mut bin)?;
        let (mut acc, mut bits, mut len) = (0u32, 0u32, 0usize);
        for &b in bin.get(..n).unwrap_or_default() {
            acc = acc << 8 | u32::from(b);
            bits += 8;
            while bits >= 5 {
                bits -= 5;
                put(out, &mut len, sym(acc >> bits))?;
            }
        }
        if bits > 0 {
            put(out, &mut len, sym(acc << (5 - bits)))?;
        }
        Ok(len)
    }

    /// Read the text form, in either case.
    ///
    /// # Errors
    /// [`TicketError::Text`] for a bad character, a length no ticket has, or non-zero padding bits; otherwise as
    /// [`Ticket::parse`].
    pub fn from_text(text: &[u8]) -> Result<Self, TicketError> {
        let mut bin = [0u8; MAX_LEN];
        let (mut acc, mut bits, mut len) = (0u32, 0u32, 0usize);
        for &c in text {
            let v = match c.to_ascii_lowercase() {
                x @ b'a'..=b'z' => x - b'a',
                x @ b'2'..=b'7' => x - b'2' + 26,
                _ => return Err(TicketError::Text),
            };
            acc = acc << 5 | u32::from(v);
            bits += 5;
            if bits >= 8 {
                bits -= 8;
                *bin.get_mut(len).ok_or(TicketError::Text)? = u8::try_from(acc >> bits & 0xff).unwrap_or(0);
                len += 1;
            }
        }
        if bits >= 5 || acc & ((1 << bits) - 1) != 0 {
            return Err(TicketError::Text);
        }
        Self::parse(bin.get(..len).unwrap_or_default())
    }
}

/// The base32 symbol of the low five bits of `v`.
fn sym(v: u32) -> u8 {
    ALPHABET.get((v & 31) as usize).copied().unwrap_or(b'a')
}

fn put(out: &mut [u8], len: &mut usize, c: u8) -> Result<(), TicketError> {
    *out.get_mut(*len)
        .ok_or(TicketError::Wire(WireError::BufferTooSmall { needed: *len + 1 }))? = c;
    *len += 1;
    Ok(())
}
