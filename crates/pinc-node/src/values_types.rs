//! The public types of the values layer: what a fetch is asked to get, why it could not start, and the fetch limit.

use core::fmt;

use pinc_membership::NodeId;
use pinc_values::span::Span;

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
    /// The node time after which the fetch fails, if any. Nothing else ends a fetch whose providers stop answering:
    /// a provider whose session closed is dialled again for as long as the fetch runs, and one that is connected and
    /// sends nothing is waited for with no timer. A fetch that must not wait gives a deadline.
    pub deadline: Option<Nanos>,
}

/// Why a fetch could not start or be found.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValuesError {
    /// The host did not enable the values layer.
    Off,
    /// [`FETCHES`] fetches are running.
    Busy,
    /// More than 255 ranges were asked for.
    TooManyRanges,
    /// A range runs past the end of the value.
    OutOfBounds,
    /// The provider table is full: as many providers are in use at once as the node can number, and the fetch names one
    /// that is not among them. Fetches and streams that finish give their providers back.
    Providers,
}

impl fmt::Display for ValuesError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Off => "the values layer is not enabled on this node; enable it before fetching",
            Self::Busy => "too many fetches are running; retry when one has ended",
            Self::TooManyRanges => "a fetch takes at most 255 ranges; ask for fewer",
            Self::OutOfBounds => "a range runs past the end of the value; ask for ranges inside it",
            Self::Providers => "this node is at its provider limit; retry when a fetch has ended",
        })
    }
}

impl core::error::Error for ValuesError {}

/// What the values layer counts: the providers in use now and the fetches refused since the node started; all zero
/// while the layer is off.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ValuesStats {
    /// The providers in use now: peers a running fetch or a stream of the layer refers to.
    pub providers_in_use: usize,
    /// Fetches refused because the node was at its provider limit ([`ValuesError::Providers`]).
    pub providers_refused: u64,
}
