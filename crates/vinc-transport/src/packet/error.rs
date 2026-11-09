//! The error type of the packet layer.

use core::fmt;

use vinc_security::RecordError;
use vinc_wire::WireError;

/// Why a packet was refused. It is `Copy` and carries no heap data.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PacketError {
    /// A length, varint or buffer bound of the wire layer was violated.
    Wire(WireError),
    /// Sealing or opening was refused by the record layer.
    Record(RecordError),
    /// The first byte does not have the shape of the packet being parsed.
    Form,
    /// The long-header type bits are 3, which is not assigned.
    LongType,
    /// The version is not [`crate::packet::VERSION`].
    Version(u8),
    /// A connection id is longer than 20 bytes.
    ConnIdLength,
    /// A reserved bit of the first byte is set.
    Reserved,
    /// The packet number is out of range, or not above the largest acknowledged.
    PacketNumber,
    /// The packet number field does not have the connection's fixed width, or does not match the packet kind.
    PnLength,
    /// The packet is too short to sample for header protection or to hold a tag.
    TooShort,
    /// A length field is larger than what the datagram holds.
    Length,
}

impl From<WireError> for PacketError {
    fn from(e: WireError) -> Self {
        Self::Wire(e)
    }
}

impl From<RecordError> for PacketError {
    fn from(e: RecordError) -> Self {
        Self::Record(e)
    }
}

impl fmt::Display for PacketError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wire(e) => write!(f, "{e}"),
            Self::Record(e) => write!(f, "{e}"),
            Self::Form => f.write_str("the first byte does not fit the packet form"),
            Self::LongType => f.write_str("unassigned long-header packet type"),
            Self::Version(v) => write!(f, "unsupported version {v}"),
            Self::ConnIdLength => f.write_str("connection id is longer than 20 bytes"),
            Self::Reserved => f.write_str("a reserved header bit is set"),
            Self::PacketNumber => f.write_str("packet number out of range"),
            Self::PnLength => f.write_str("packet number length is invalid for this packet"),
            Self::TooShort => f.write_str("packet is too short"),
            Self::Length => f.write_str("a length field exceeds the datagram"),
        }
    }
}

impl core::error::Error for PacketError {}
