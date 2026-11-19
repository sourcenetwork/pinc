//! Packets: long and short headers, fixed-width packet numbers, header protection, in-place seal and open, coalesced
//! datagrams and padding.
//!
//! # Wire layouts
//!
//! All integers are big-endian except the lengths written as varints, which are the `pinc-wire` varint.
//!
//! Long header (handshake, 0-RTT and retry):
//!
//! ```text
//! 0b11TT_xxxx | version(1) | dcid_len(1) dcid | scid_len(1) scid | length(varint) | body(length)
//! ```
//!
//! `TT` is 0 for [`LongType::Handshake`] and 1 for [`LongType::ZeroRtt`]; 2 and 3 are errors. The version is [`VERSION`],
//! one byte. Each connection id is 0 to 20 bytes. `xxxx` is zero for a handshake packet. For a 0-RTT packet bits 3
//! and 2 are zero and bits 1 and 0 hold the packet-number length minus one, always the base width; the body is the
//! packet number, the sealed frames and the 16-byte tag, so `length` counts the packet number too. The low four bits
//! of the first byte and the packet number of a 0-RTT packet are header protected (mask `0x0f`).
//!
//! Short header (1-RTT):
//!
//! ```text
//! 0b01_0_K_00_LL | dcid | pn(width) | sealed frames | tag(16)
//! ```
//!
//! Bit 7 is zero, bit 6 (the fixed bit) is one, bit 5 is zero, `K` (bit 4) is the key phase, bits 3 and 2 are zero and
//! `LL` is the packet-number width minus one. The width is fixed for the connection: 2 bytes, or 3 when the granted
//! window exceeds [`WIDE_WINDOW`] (see [`pn_len_for`]); a packet whose `LL` differs is refused. The dcid has the length the receiving endpoint chose. Header
//! protection masks the low five bits of the first byte and the packet number.
//!
//! Coalesced datagram: long packets back to back, then at most one short packet, then optional zero padding bytes
//! after the last long packet.
//!
//! # Invariants
//!
//! Every parser checks every length before it reads and reports a [`PacketError`]; none panics, indexes or allocates.
//! A datagram iterator makes progress on every call and ends at the first error. Sealing and opening run in place
//! over the caller's buffer with the unprotected header as associated data. A packet number is 62 bits, truncated to
//! the connection's fixed width and expanded to the closest value to the next expected one. The connection id type is the one of `pinc-security` (0 to 20
//! bytes, inline); a zero-length id is accepted at this layer.

mod datagram;
mod error;
mod header;
mod number;
mod protect;

pub use datagram::{Header, Packet, Packets, handshake_packet, packets, pad_to};
pub use error::PacketError;
pub use header::{LongHeader, LongType, ShortHeader, short_dcid, short_header_len};
pub use number::{MAX_PN, PN_LEN_BASE, PN_LEN_WIDE, WIDE_WINDOW, decode_pn, encode_pn, pn_len_for};
pub use protect::{
    Opened, PnLayout, SAMPLE_SKIP, Unprotected, open, protect_header, sample_at, seal, unprotect_header,
};
/// The version the long header carries: one byte, the handshake's version.
pub const VERSION: u8 = pinc_security::VERSION;
pub use pinc_security::ids::{ConnId, MAX_CID_LEN};
