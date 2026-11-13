//! The numbers of the protocol, in nanoseconds unless stated.

use vinc_membership::Nanos;

const S: Nanos = 1_000_000_000;

/// A publisher retries an unacknowledged message on the next hub this often.
pub const PUB_RETRY: Nanos = 3 * S;
/// A publisher gives up on an unacknowledged message this long after it published it.
pub const PUB_GIVEUP: Nanos = 90 * S;
/// A hub keeps a message in a topic log this long.
pub const LOG_WINDOW: Nanos = 120 * S;
/// A subscriber that is behind and owed a message older than this stops pacing the topic: the hub lets it go, so the
/// log may evict what it is owed, and tells it with RESTORED once it caught up if it did.
pub const PUSH_OWED_MAX: Nanos = 30 * S;
/// A subscriber that is behind and whose stream took nothing for this long (milliseconds) is let go the same way.
pub const PUSH_STALL_MS: u64 = 2_000;
/// A hub keeps at most this many messages per topic.
pub const LOG_CAP: usize = 2048;
/// A node remembers a message id this long, so it delivers it at most once.
pub const SEEN_TTL: Nanos = 600 * S;
/// The most message ids one topic remembers; a message that would exceed it is not delivered.
pub const SEEN_CAP: usize = 8192;
// An id the log evicts must still be in the dedupe set afterwards, so that a late copy is a duplicate. One store can
// evict the whole log, and the inserts of that step drop the oldest records of a full set: the set must hold at least
// twice what the log holds (`BroadcastNode.evictedSeen` in the proofs; `BroadcastNode_evictCap.cfg` is the
// counterexample below that).
const _: () = assert!(SEEN_CAP >= 2 * LOG_CAP);
/// Hubs tell each other the ids of their log this often.
pub const HUB_AE: Nanos = 5 * S;
/// The hub-to-hub id exchange covers messages logged between this long ago...
pub const AE_FROM: Nanos = 30 * S;
/// ...and this long ago.
pub const AE_TO: Nanos = S;
/// The most ids one HAVE or GET carries.
pub const HAVE_MAX: usize = 512;
/// A subscriber asks for the ids of the recent log this often while the topic is live.
pub const GAP_EVERY: Nanos = 20 * S;
/// A topic is live while it had traffic within this long.
pub const GAP_LIVE: Nanos = 60 * S;
/// The span a periodic gap check asks the hub about.
pub const GAP_SPAN: Nanos = 25 * S;
/// A restarted member gives up collecting the hub floors after this long.
pub const FLOOR_WAIT: Nanos = 15 * S;
/// The most messages held for the replay floors, and the most held for an access check.
pub const FHOLD_MAX: usize = 256;
/// The most messages held until an access-control answer arrives.
pub const HELD_MAX: usize = 64;
/// The most access checks outstanding.
pub const CHECKS_MAX: usize = 256;
/// An access-control answer is trusted this long, measured on the local clock.
pub const ACP_CAP: Nanos = 30 * S;
/// The most unacknowledged publishes a node tracks.
pub const PENDING_MAX: usize = 1024;
/// The most subscribers, tracked members, origins or revoked nodes in any one table.
pub const TABLE_MAX: usize = 4096;
/// The most origins one member's origin floor lists.
pub const ORIGIN_MAX: usize = 128;
/// A subscribing member asks for the log back to this long before its last received message (milliseconds).
pub const RESUB_BACK_MS: u64 = 15_000;
/// A message older than this before the node started is not new (milliseconds).
pub const OLD_SLACK_MS: u64 = 2_000;
/// A `REPLAY_PUSH` carries at most this many messages.
pub const REPLAY_PUSH_MAX: usize = 256;

/// The default largest message body (matches the default maximum message size of common gossip stacks).
pub const DEFAULT_MAX_BODY: usize = 65_536;
/// The default most topics one node tracks.
pub const DEFAULT_MAX_TOPICS: usize = 128;
/// The default bytes of message data one topic log holds.
pub const DEFAULT_LOG_BYTES: usize = 4 << 20;
/// The longest topic.
pub const MAX_TOPIC: usize = 255;
/// The default most subscribers a node learns for one topic, for the member-to-member fallback.
pub const DEFAULT_MAX_SUBSCRIBERS: usize = 256;
/// The fallback sends a message to at most this many subscribers per pacing step.
pub const FALLBACK_BATCH: usize = 8;
/// A remote timestamp more than this far ahead of the local wall clock does not advance the local clock (ms).
pub const HLC_DRIFT_MS: u64 = 60_000;
/// The most trace records queued between two polls.
pub const QUEUE_CAP: usize = 8192;
