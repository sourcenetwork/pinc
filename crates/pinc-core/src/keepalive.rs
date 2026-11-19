//! The keepalive schedule of a session, by role.
//!
//! A session is quiet when its role is hub or member (a long-lived session whose traffic is mostly control); any
//! other session is plain. The schedule, all in nanoseconds of local time:
//!
//! - every validated path is pinged 5 s after its last send while the application moved data in the last 20 s;
//! - the active path is also pinged after 60 s without a send on the dialing side of a quiet session, 70 s on the
//!   accepting side (so only the dialer's ping flows), and 40 s on a plain session; a plain session stops this 90 s
//!   after the application's last data and is left to lapse at the idle timeout;
//! - the dialing side of a quiet session pings an active direct path that neither sent nor heard for 14 s while the
//!   application moved data in the last 120 s;
//! - after a resume, no ping at all is sent until 10 s have passed, unless something is in flight.
//!
//! A late-start rule defers the first path MTU probe of a quiet session by 3 s when the node's first dial came after
//! 10 s of running.
//!
//! Invariants: [`Plan`] is a pure function of the inputs; `ping_at` never precedes `now`; `review_at` is the first
//! instant after `now` at which the answer can change without any input changing.

/// A session's place in the node, set by the layer above. Defaults to [`Role::Other`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Role {
    /// A session to a hub.
    Hub,
    /// A session a hub keeps with one of its members.
    Member,
    /// Any other session.
    #[default]
    Other,
}

impl Role {
    /// Whether the session is quiet (hub or member).
    pub const fn quiet(self) -> bool {
        !matches!(self, Self::Other)
    }
}

/// Ping every validated path after this long without a send (5 s).
pub const PATH_KEEP: u64 = 5_000_000_000;
/// The application moved data within this long: paths are kept alive (20 s).
pub const ACTIVE_KEEP: u64 = 20_000_000_000;
/// The active path of a plain session is pinged after this long without a send (40 s).
pub const IDLE_KEEP: u64 = 40_000_000_000;
/// The same, on the dialing side of a quiet session (60 s).
pub const QUIET_KEEP_DIALER: u64 = 60_000_000_000;
/// The same, on the accepting side of a quiet session (70 s).
pub const QUIET_KEEP_ACCEPTOR: u64 = 70_000_000_000;
/// A plain session without application data for this long stops idle pings (90 s).
pub const IDLE_DROP: u64 = 90_000_000_000;
/// A quiet dialing session pings a silent direct path after this long (14 s).
pub const DIRECT_SILENCE: u64 = 14_000_000_000;
/// ...while the application moved data within this long (120 s).
pub const HOLD_WINDOW: u64 = 120_000_000_000;
/// After a resume no ping is sent for this long unless something is in flight (10 s).
pub const RESUME_QUIET: u64 = 10_000_000_000;
/// A node whose first dial came after this long is a late start (10 s).
pub const LATE_START: u64 = 10_000_000_000;
/// A late-start quiet session defers its first path MTU probe by this long (3 s).
pub const MTU_PROBE_DELAY: u64 = 3_000_000_000;

/// What the schedule reads about one session.
#[derive(Debug, Clone, Copy)]
pub struct Inputs {
    /// The session's role.
    pub role: Role,
    /// Whether this side dialed.
    pub dialer: bool,
    /// Whether the active path is a direct UDP path.
    pub direct: bool,
    /// The current time.
    pub now: u64,
    /// When the last datagram left on any path.
    pub last_tx: u64,
    /// When the last datagram arrived on the active path.
    pub last_rx: u64,
    /// When the application last moved data.
    pub last_app: u64,
    /// No ping before this time unless something is in flight.
    pub quiet_until: u64,
    /// Whether packets are in flight.
    pub in_flight: bool,
}

/// What to do about keepalives next.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Plan {
    /// When the next ping on the active path is due, if any.
    pub ping_at: Option<u64>,
    /// When to compute the plan again if no input changes.
    pub review_at: Option<u64>,
}

/// The time a path last sent at, for a standby path: the next ping is due 5 s after, while the application moved data
/// in the last 20 s. `None` when the window has closed.
pub fn standby_due(now: u64, path_last_tx: u64, last_app: u64) -> Option<u64> {
    let due = path_last_tx.saturating_add(PATH_KEEP).max(now);
    (due < last_app.saturating_add(ACTIVE_KEEP)).then_some(due)
}

impl Inputs {
    /// The idle ping interval of this session's active path.
    fn idle_keep(&self) -> u64 {
        match (self.role.quiet(), self.dialer) {
            (true, true) => QUIET_KEEP_DIALER,
            (true, false) => QUIET_KEEP_ACCEPTOR,
            (false, _) => IDLE_KEEP,
        }
    }

    /// Compute the plan.
    pub fn plan(&self) -> Plan {
        let now = self.now;
        let after = |t: u64| t.max(now);
        let earliest = |p: Option<u64>, t: u64| Some(p.map_or(t, |c| c.min(t)));
        let mut ping: Option<u64> = None;
        // The moments the answer can change by itself: a window of the schedule closing, or the quiet period ending.
        // A moment already past is not waited for.
        let mut review: Option<u64> = None;
        let mut change = |t: u64| {
            if t > now {
                review = earliest(review, t);
            }
        };

        // Per validated path: 5 s after the last send, while data moved in the last 20 s.
        if let Some(due) = standby_due(now, self.last_tx, self.last_app) {
            ping = earliest(ping, due);
        }
        change(self.last_app.saturating_add(ACTIVE_KEEP));

        // The active path after the long idle interval; a plain session also stops 90 s after the last data.
        let idle_due = after(self.last_tx.saturating_add(self.idle_keep()));
        if self.role.quiet() || idle_due < self.last_app.saturating_add(IDLE_DROP) {
            ping = earliest(ping, idle_due);
        }
        if !self.role.quiet() {
            change(self.last_app.saturating_add(IDLE_DROP));
        }

        // A silent direct path of a quiet dialing session.
        if self.role.quiet() && self.dialer && self.direct {
            let due = after(self.last_rx.max(self.last_tx).saturating_add(DIRECT_SILENCE));
            if due < self.last_app.saturating_add(HOLD_WINDOW) {
                ping = earliest(ping, due);
            }
            change(self.last_app.saturating_add(HOLD_WINDOW));
        }

        // Right after a resume nothing is pinged unless packets are in flight.
        if now < self.quiet_until && !self.in_flight {
            ping = ping.map(|p| p.max(self.quiet_until));
            change(self.quiet_until);
        }
        Plan {
            ping_at: ping,
            review_at: review,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const S: u64 = 1_000_000_000;

    fn base(role: Role, dialer: bool) -> Inputs {
        Inputs {
            role,
            dialer,
            direct: true,
            now: 100 * S,
            last_tx: 100 * S,
            last_rx: 100 * S,
            last_app: 100 * S,
            quiet_until: 0,
            in_flight: false,
        }
    }

    #[test]
    fn active_data_pings_every_five_seconds() {
        let p = base(Role::Other, true).plan();
        assert_eq!(p.ping_at, Some(105 * S));
        assert_eq!(p.review_at, Some(120 * S));
    }

    #[test]
    fn after_twenty_seconds_the_idle_intervals_apply_by_role() {
        let at = |role, dialer| {
            let mut i = base(role, dialer);
            i.now = 130 * S;
            i.last_tx = 130 * S;
            i.last_rx = 130 * S;
            i.plan().ping_at
        };
        assert_eq!(at(Role::Other, true), Some(130 * S + 40 * S));
        assert_eq!(at(Role::Hub, true), Some(130 * S + 14 * S));
        assert_eq!(at(Role::Hub, false), Some(130 * S + 70 * S));
        assert_eq!(at(Role::Member, false), Some(130 * S + 70 * S));
    }

    #[test]
    fn a_plain_session_stops_after_ninety_idle_seconds_and_a_quiet_one_does_not() {
        let mut i = base(Role::Other, true);
        i.now = 195 * S;
        i.last_tx = 190 * S;
        i.last_rx = 190 * S;
        assert_eq!(i.plan().ping_at, None);
        i.role = Role::Hub;
        i.dialer = false;
        assert_eq!(i.plan().ping_at, Some(260 * S));
    }

    #[test]
    fn the_dialing_quiet_session_holds_a_silent_direct_path_for_two_minutes() {
        let mut i = base(Role::Hub, true);
        i.now = 150 * S;
        i.last_tx = 140 * S;
        i.last_rx = 140 * S;
        assert_eq!(i.plan().ping_at, Some(154 * S));
        i.now = 230 * S;
        i.last_tx = 230 * S;
        i.last_rx = 230 * S;
        assert_eq!(i.plan().ping_at, Some(290 * S));
        i.direct = false;
        i.now = 150 * S;
        i.last_tx = 140 * S;
        i.last_rx = 140 * S;
        assert_eq!(i.plan().ping_at, Some(200 * S));
    }

    #[test]
    fn a_resume_silences_pings_for_ten_seconds_unless_something_is_in_flight() {
        let mut i = base(Role::Other, true);
        i.quiet_until = 110 * S;
        assert_eq!(i.plan().ping_at, Some(110 * S));
        i.in_flight = true;
        assert_eq!(i.plan().ping_at, Some(105 * S));
    }

    #[test]
    fn standby_paths_are_pinged_only_while_data_moves() {
        assert_eq!(standby_due(100 * S, 98 * S, 99 * S), Some(103 * S));
        assert_eq!(standby_due(100 * S, 50 * S, 99 * S), Some(100 * S));
        assert_eq!(standby_due(100 * S, 98 * S, 70 * S), None);
    }
}
