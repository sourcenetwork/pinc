//! What the machines tell the host: application events and trace records.
//!
//! Every state transition of the fetcher and the server is reported through [`Out`] as a plain `Copy` value, in the
//! order it happens, with the time of the call. The trace is the deterministic record the proofs replay: a run with
//! the same inputs and the same clock produces the same trace. The host may ignore it (`()` implements [`Out`]).

use crate::session::Provider;
use vinc_transport::stream::StreamId;

/// Why a fetch failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FailReason {
    /// The fetch named no provider.
    NoProvider,
    /// Every provider sent bytes that failed verification.
    EveryProviderLied,
    /// The deadline passed.
    Deadline,
    /// The store refused verified bytes.
    Store,
    /// A zero-length value was asked for under a root that is not the hash of the empty value.
    BadRoot,
}

/// What the application is told.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// Verified bytes `[off, off + len)` are in the store and may be read.
    Readable {
        /// The first byte.
        off: u64,
        /// The number of bytes.
        len: u64,
    },
    /// Every wanted byte is verified and in the store.
    Complete,
    /// The fetch failed.
    Failed(FailReason),
}

/// Why the first granule was delivered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Release {
    /// Enough verified bytes stand behind it.
    Buffered,
    /// The value ends inside the buffer.
    Tail,
    /// Enough later granules verified.
    Granules,
    /// It waited the longest allowed.
    Timeout,
    /// Nothing else is missing.
    Done,
}

/// Why a provider was evicted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiarWhy {
    /// A group or proof failed its hash.
    Hash,
    /// The bytes broke the wire format or the request.
    Protocol,
}

/// A transition, reported to [`Out::trace`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trace {
    /// A fetch started with `wanted` bytes missing over `providers`, striped or split.
    FetchStart {
        /// The bytes missing.
        wanted: u64,
        /// The providers in use.
        providers: u8,
        /// Whether the work is pulled from one offset-ordered queue.
        striped: bool,
    },
    /// A session to a provider was asked for.
    Dial(Provider),
    /// A request went out on a stream.
    Requested {
        /// The provider.
        provider: Provider,
        /// The stream.
        stream: StreamId,
        /// The ranges in the request.
        ranges: u8,
        /// The bytes asked for.
        bytes: u64,
    },
    /// A provider was topped up from the queue.
    TopUp {
        /// The provider.
        provider: Provider,
        /// The bytes taken.
        bytes: u64,
        /// The outstanding target at the time.
        target: u64,
    },
    /// The tail of one provider's work moved to an idle one.
    Steal {
        /// The provider robbed.
        from: Provider,
        /// The provider that took the tail.
        to: Provider,
        /// The bytes moved.
        bytes: u64,
    },
    /// A group verified and reached the store.
    Verified {
        /// The provider that sent it.
        provider: Provider,
        /// The group's offset.
        off: u64,
        /// The group's length.
        len: u64,
        /// Whether it was verified out of order against a range proof.
        ahead: bool,
    },
    /// The first granule verified and is held back.
    Held {
        /// Its offset.
        off: u64,
    },
    /// The first granule was delivered.
    Released {
        /// Its offset.
        off: u64,
        /// Why now.
        why: Release,
    },
    /// A provider was evicted.
    Liar {
        /// The provider.
        provider: Provider,
        /// Why.
        why: LiarWhy,
    },
    /// A dropped or failed session will be dialled again after a delay.
    Retry(Provider),
    /// No verified granule arrived within the stall wait; the sessions were redialled.
    StallRedial {
        /// The wait that expired.
        wait: u64,
        /// The wait now.
        next: u64,
    },
    /// An out-of-order group could not be checked against a range proof.
    ProofRejected {
        /// The stream.
        stream: StreamId,
    },
    /// The server began a response.
    Serving {
        /// The stream.
        stream: StreamId,
        /// The ranges served.
        ranges: u8,
        /// The response length.
        bytes: u64,
    },
    /// The server refused a request with a reset code.
    Refused {
        /// The stream.
        stream: StreamId,
        /// The reset code.
        code: u64,
    },
    /// The server sent a range proof.
    ProofSent {
        /// The stream.
        stream: StreamId,
        /// The first value offset covered.
        start: u64,
        /// The bytes covered.
        bytes: u32,
    },
}

/// The sink of events and trace records. Both methods take the time of the call.
pub trait Out {
    /// An application event.
    fn event(&mut self, now: u64, ev: Event);
    /// A trace record. The default drops it.
    fn trace(&mut self, _now: u64, _t: Trace) {}
}

impl Out for () {
    fn event(&mut self, _now: u64, _ev: Event) {}
}
