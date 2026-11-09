//! The tuned numbers of the value protocol, in one place.
//!
//! Every constant here is a rule of the multi-provider fetch or of the server, with the unit in its name or doc.
//! Times are nanoseconds, sizes are bytes. Nothing here is read from configuration: the fetch and the serve side
//! must agree on them, so they are constants.

use vinc_dag::tree::{CHUNK_LEN, DEFAULT_GROUP_LOG};

/// One millisecond in nanoseconds.
pub const MS: u64 = 1_000_000;
/// One second in nanoseconds.
pub const NS: u64 = 1_000_000_000;

/// The group-size log of every value: groups of 16 chunks.
pub const GROUP_LOG: u32 = DEFAULT_GROUP_LOG;
/// The group size in bytes (16 KiB): the unit of verification, of a GROUP frame and of every request range.
pub const GROUP: u64 = CHUNK_LEN << GROUP_LOG;
/// [`GROUP`] as a `usize`.
pub const GROUP_BYTES: usize = 16 * 1024;

/// The most providers one fetch uses.
pub const MAX_PROVIDERS: usize = 4;
/// The most ranges in one request (and in one fetch).
pub const MAX_REQ_RANGES: usize = 32;
/// The group frames the server prepares per step: the size of the frame window a response source keeps.
pub const SERVE_BATCH: usize = 16;

/// DEADLINE_STRIPE: the outstanding target before 500 ms of samples exist (768 KiB).
pub const TGT0: u64 = 786_432;
/// ARRIVAL_CURVE: the largest outstanding target of a provider (1.5 MiB).
pub const TGT_MAX: u64 = 1_572_864;
/// ARRIVAL_CURVE: the outstanding target is the provider's verified rate times this horizon, in milliseconds.
pub const RATE_HORIZON: u64 = 1000;
/// ARRIVAL_CURVE: the samples a provider's rate needs before it replaces [`TGT0`].
pub const RATE_WARMUP: u64 = 500 * MS;
/// TAIL_SHRINK: a top-up takes at most a share of the queue once less than this many chunks per provider remain.
pub const STRIPE_CHUNK: u64 = 1_048_576;
/// The fewest groups an outstanding target, and a tail-shrunk top-up, may hold.
pub const MIN_TARGET_GROUPS: u64 = 4;
/// STEAL: the least a busy provider must still hold before an idle one steals from it.
pub const STEAL_MIN: u64 = 262_144;
/// STEAL: a provider with no verified progress for this long is stolen from regardless of its rate.
pub const STEAL_IDLE: u64 = 2 * NS;
/// STEAL: the earliest expected completion, in milliseconds, worth stealing from.
pub const STEAL_ETA_MS: u64 = 800;
/// STEAL: the expected completion of a stalled provider, in milliseconds (effectively never).
pub const STEAL_ETA_STALLED_MS: u64 = 1 << 40;

/// HEAD_HOLD: verified bytes that must stand behind the first granule before it is delivered (96 KiB).
pub const HOLD_B: u64 = 98_304;
/// HEAD_HOLD: later verified granules after which the first is delivered anyway.
pub const HOLD_NV: u32 = 40;
/// HEAD_HOLD: the longest the first granule is held.
pub const HOLD_MAX: u64 = 2 * NS;

/// STALL_REDIAL: the first wait for a verified granule before a fresh dial.
pub const STALL_WAIT: u64 = 4 * NS;
/// STALL_REDIAL: the wait after doubling stops.
pub const STALL_CAP: u64 = 16 * NS;
/// ARK_PACE: the cap of a stall wait that follows the transfer's own granule pace.
pub const ARK_PACE_CAP: u64 = 40 * NS;
/// BYTE_LIVE: the cap of a stall wait that follows the stream's own burst gaps.
pub const BYTE_GAP_CAP: u64 = 60 * NS;
/// STALL_RTT: the stall wait is at least this many round trips.
pub const STALL_RTT: u64 = 4;
/// STALL_RTT: the cap of that wait.
pub const STALL_RTT_CAP: u64 = 60 * NS;
/// STALL_LIVE: the round trip from which a session counts as slow.
pub const SLOW_RTT: u64 = 250 * MS;
/// STALL_LIVE: no slow session is considered live after this long without a verified granule.
pub const LIVE_CAP: u64 = 90 * NS;
/// The round trip assumed for a session with no sample yet.
pub const ASSUMED_RTT: u64 = NS;
/// The delay before a failed connection or a closed one is dialled again.
pub const REDIAL_DELAY: u64 = NS;
/// The delay before a refused stream open is tried again.
pub const OPEN_RETRY: u64 = 200 * MS;
/// The delay before a provider whose streams all ended is asked again.
pub const RESTREAM_DELAY: u64 = 500 * MS;
/// The urgency of a value request stream.
pub const URGENCY: u8 = 4;

/// WRITE_THROUGH: the range-proof bytes the receiver asks for beyond the out-of-order frontier (128 KiB).
pub const WT_AHEAD: u64 = 131_072;
/// WRITE_THROUGH: the largest range-proof frame body.
pub const WT_PMAX: usize = 1100;
/// WRITE_THROUGH: the range-proof frames per loss event.
pub const WT_MAXF: usize = 48;
/// WRITE_THROUGH: the fewest groups per proof frame; a deeper tree gets no write-through.
pub const WT_MIN_K: u64 = 4;
/// WRITE_THROUGH: the most groups per proof frame.
pub const WT_MAX_K: u64 = 16;
/// WRITE_THROUGH: the range proofs a fetch keeps.
pub const WT_KEEP: usize = 24;
/// WRITE_THROUGH: the proactive proofs lead the sent value bytes by at most this (512 KiB).
pub const WT_LEAD: u64 = 524_288;

/// The stream reset codes of the value protocol.
pub mod code {
    /// The peer broke the wire format.
    pub const PROTOCOL: u64 = 1;
    /// The value or a requested range is not available here.
    pub const UNAVAILABLE: u64 = 2;
    /// The provider sent bytes that failed verification.
    pub const LIAR: u64 = 3;
    /// A newer request for the same bytes superseded this stream.
    pub const SUPERSEDED: u64 = 4;
    /// The tail of the stream's work was stolen by an idle provider.
    pub const STOLEN: u64 = 5;
    /// The serve side has no room for another request.
    pub const BUSY: u64 = 6;
    /// The requester no longer needs the stream.
    pub const CANCELLED: u64 = 0;
}
