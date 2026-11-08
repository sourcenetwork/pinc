//! Packets: long and short headers, packet numbers, header protection, in-place seal and open, coalesced
//! datagrams, padding and stateless reset.
//!
//! # Wire layouts
//!
//! All integers are big-endian except the lengths written as varints, which are the `vinc-wire` varint.
//!
//! Long header (handshake, 0-RTT and retry):
//!
//! ```text
//! 0b11TT_xxxx | version(4) | dcid_len(1) dcid | scid_len(1) scid | length(varint) | body(length)
//! ```
//!
//! `TT` is 0 for [`LongType::Handshake`], 1 for [`LongType::ZeroRtt`] and 2 for [`LongType::Retry`]; 3 is an error.
//! The version is [`VERSION`]. Each connection id is 0 to 20 bytes. `xxxx` is zero for a handshake or retry packet.
//! For a 0-RTT packet bits 3 and 2 are zero and bits 1 and 0 hold the packet-number length minus one; the body is the
//! packet number (1 to 4 bytes), the sealed frames and the 16-byte tag, so `length` counts the packet number too. The
//! low four bits of the first byte and the packet number of a 0-RTT packet are header protected (mask `0x0f`).
//!
//! Short header (1-RTT):
//!
//! ```text
//! 0b01_0_K_00_LL | dcid | pn(LL + 1) | sealed frames | tag(16)
//! ```
//!
//! Bit 7 is zero, bit 6 (the fixed bit) is one, bit 5 is zero, `K` (bit 4) is the key phase, bits 3 and 2 are zero and
//! `LL` is the packet-number length minus one. The dcid has the length the receiving endpoint chose. Header
//! protection masks the low five bits of the first byte and the packet number.
//!
//! Stateless reset: a datagram of at least [`MIN_RESET_LEN`] bytes whose first byte is `0b01xx_xxxx` and whose last 16
//! bytes are the reset token. Coalesced datagram: long packets back to back, then at most one short packet, then
//! optional zero padding bytes after the last long packet.
//!
//! # Invariants
//!
//! Every parser checks every length before it reads and reports a [`PacketError`]; none panics, indexes or allocates.
//! A datagram iterator makes progress on every call and ends at the first error. Sealing and opening run in place
//! over the caller's buffer with the unprotected header as associated data. A packet number is 62 bits, truncated and
//! expanded as in RFC 9000 appendices A.2 and A.3. The connection id type is the one of `vinc-security` (0 to 20
//! bytes, inline); a zero-length id is accepted at this layer.

mod datagram;
mod error;
mod header;
mod number;
mod protect;
mod reset;

pub use datagram::{Header, Packet, Packets, packets, pad_to};
pub use error::PacketError;
pub use header::{LongHeader, LongType, ShortHeader, short_dcid, short_header_len};
pub use number::{MAX_PN, MAX_PN_LEN, decode_pn, encode_pn};
pub use protect::{
    Opened, PnLayout, SAMPLE_SKIP, Unprotected, open, protect_header, sample_at, seal, unprotect_header,
};
pub use reset::{MIN_RESET_LEN, RESET_TOKEN_LEN, build_stateless_reset, is_stateless_reset};
/// The version the long header carries, still four bytes wide. The handshake's version is one byte
/// ([`vinc_security::VERSION`]); the header narrows to that byte when the packet layer is reworked.
#[allow(clippy::cast_lossless, reason = "u32::from is not const")]
pub const VERSION: u32 = vinc_security::VERSION as u32;
pub use vinc_security::ids::{ConnId, MAX_CID_LEN};
