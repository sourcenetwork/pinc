//! The public types of the values layer: what a fetch is asked to get, why it could not start, and the fetch limit.

use core::fmt;

use vinc_membership::NodeId;
use vinc_values::span::Span;

use crate::config::Nanos;

/// The most fetches running at once.
pub const FETCHES: usize = 8;

/// What a fetch is asked to get.
#[derive(Debug, Clone, Copy)]
pub struct ValuesRequest<'a> {
    /// The root of the value.
    pub root: [u8; 32],
    /// The value length in bytes.
    pub length: u64,
    /// The byte ranges wanted; empty means the whole value.
    pub ranges: &'a [Span],
    /// The providers, by node id; the first four count.
    pub providers: &'a [NodeId],
    /// The node time after which the fetch fails, if any.
    pub deadline: Option<Nanos>,
}

/// Why a fetch could not start or be found.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValuesError {
    /// The host did not enable the values layer.
    Off,
    /// [`FETCHES`] fetches are running.
    Busy,
    /// More than 32 ranges were asked for.
    TooManyRanges,
    /// A range runs past the end of the value.
    OutOfBounds,
    /// The provider table is full.
    Providers,
}

impl fmt::Display for ValuesError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Off => "the values layer is not enabled on this node",
            Self::Busy => "too many fetches are running",
            Self::TooManyRanges => "a fetch takes at most 32 ranges",
            Self::OutOfBounds => "a range runs past the end of the value",
            Self::Providers => "too many providers are known to this node",
        })
    }
}

impl core::error::Error for ValuesError {}
