//! The numbers of the protocol, in nanoseconds unless stated.

use crate::session::Nanos;

const S: Nanos = 1_000_000_000;
const MS: Nanos = 1_000_000;

/// A hub drops a member this long after its last renewal.
pub const LEASE: Nanos = 80 * S;
/// A member renews its lease on every hub this often; a hub refreshes a lease from transport evidence once it is
/// this stale.
pub const RENEW: Nanos = 25 * S;
/// A hub silent this long is stale: its roster copy is dropped while another hub is fresh.
pub const HUB_STALE: Nanos = 75 * S;
/// A periodic HELLO is skipped while the hub session has no probe timeout and received within this.
pub const PULSE_FRESH: Nanos = 67 * S;
/// Removals queued by a late timer or a heal are re-checked after this.
pub const QUIET: Nanos = 10 * S;
/// A second look before a deferred removal is reported.
pub const RECHECK_GAP: Nanos = 5 * S;
/// A tick later than this means the process was suspended.
pub const WAKE_GAP: Nanos = 2 * S;
/// A sleep notice this close before a carrier drop marks it as a suspension.
pub const SLEEP_WIN: Nanos = 10 * S;
/// A probe gets at least this long to be answered.
pub const PROBE_WAIT_MIN: Nanos = 250 * MS;
/// A carrier gone and a member silent this long, at least, before it is confirmed down.
pub const CONFIRM: Nanos = S;
/// A member's session-management cadence.
pub const SLOW_TICK: Nanos = 5 * S;
/// A member's fast tick.
pub const NODE_TICK: Nanos = 500 * MS;
/// A hub's tick.
pub const HUB_TICK: Nanos = S;
/// A HELLO unanswered this long means the session is dead.
pub const ACK_WAIT: Nanos = 6 * S;
/// A fresh hub session is spared the HELLO watchdog this long.
pub const HS_GRACE: Nanos = 30 * S;
/// Hub session samples taken only while no more than this many bytes are in flight.
pub const RTT_QUIET: u32 = 4000;
/// A hub that returns after silence this long (the transport gives a path up after about a minute of probe
/// timeouts) means a partition healed.
pub const HEAL_SILENCE: Nanos = 60 * S;
/// The absolute part of the primary-hub hysteresis.
pub const HYST_ABS: Nanos = 20 * MS;
/// An RTT sample older than this round trip is ignored.
pub const RTT_SAMPLE_MAX: Nanos = 5 * S;
/// The longest a change of the group (a join, a leave or a crash) takes to reach every live member: the service level
/// the layer states, which the scenario suite checks.
pub const AWARENESS_BOUND: Nanos = 145 * S;
/// The false suspicions of live members per member hour the layer states it stays under.
pub const FALSE_SUSPICION_PER_MEMBER_HOUR: f64 = 1.0;
/// The most entries any one table holds.
pub const MAX_TABLE: usize = 4096;
/// The most hubs.
pub const MAX_HUBS: usize = 64;
/// The most events and traces queued between two polls.
pub const QUEUE_CAP: usize = 8192;
/// The largest FLOOR body the broadcast layer may write.
pub const FLOOR_MAX: usize = 4096;
