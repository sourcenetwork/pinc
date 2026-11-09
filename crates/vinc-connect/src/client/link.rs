//! The client end of one relay carrier: dial, retry, watchdog, keepalive and the lease.
//!
//! A [`Link`] is the timing state machine of one carrier to one relay. It owns no stream and no key; the host
//! reports what happened (a stream opened, closed, was heard from, was written to) and acts on the [`Act`] a call
//! returns. [`Shared`] holds what every carrier of the node shares: the phone flag, the time a carrier last died
//! silently, the learned lease and the restart defer.
//!
//! The rules, in nanoseconds:
//! - **States.** `Down`, `Dialing`, `Open`. A dial that fails or a stream that closes retries after 1 s, then 2 s,
//!   and stays at 2 s until a stream opens (which resets the wait to 1 s).
//! - **Dial watchdog.** A dial that has not opened `max(8 s, 8 x rtt)` after it started (never more than 30 s) is
//!   closed and tried again at once. `rtt` is the larger of the node's two round-trip figures.
//! - **Keepalive (KEEP_SENSE).** A silent open carrier is checked after 30 s on a phone or within 10 minutes of a
//!   carrier dying silently, and after 65 s otherwise. Only the home carrier is checked for its own sake; another
//!   carrier is checked only while a session rides it.
//! - **Learned keepalive (KEEP_LEARN).** When enabled, every carrier that dies silently sets `keep_iv` to half the
//!   silence it had endured (at least 15 s, never rising above half of an earlier value); every keepalive wait is
//!   then at most `keep_iv`.
//! - **Check.** A PING that nothing answers within `max(3 s, 3 x rtt)` resets the carrier. A session packet that
//!   leaves on the carrier may carry the check instead (CHECK_RIDE): its acknowledgement is the answer, and if
//!   none comes a real PING follows. CARRIER_PULSE is the same PING and PONG serving a quiet hub session
//!   ([`Link::pulse`]).
//! - **Lease (CARRIER_LEASE), only while no UDP datagram was ever heard.** `hlt` is the last write. A PING that
//!   fails, was not ridden and followed an idle gap of at least 15 s sets `lease_hi = min(lease_hi, gap)`. Once a
//!   lease is known the keepalive gap is [`lease_keep`], and a send onto a carrier idle both ways for `lease_hi`
//!   resets it first (STALE_SEND).
//! - **Restart defer (CARRIER_DEFER).** After a restart the home carrier's own dial waits 600 ms; a frame to send
//!   cancels the wait.
//!
//! Invariants: `lease_hi` never rises; the retry wait is 1 s or 2 s; `Open` is reached only through
//! [`Link::opened`]; every deadline returned by [`Link::next_deadline`] is the first instant [`Link::tick`] can act.

/// One second.
const SEC: u64 = 1_000_000_000;

/// The rule numbers.
pub mod rule {
    use super::SEC;
    /// The first wait before a dial is retried.
    pub const RETRY_MIN: u64 = SEC;
    /// The longest wait before a dial is retried.
    pub const RETRY_MAX: u64 = 2 * SEC;
    /// The floor of the dial watchdog.
    pub const DIAL_WAIT_MIN: u64 = 8 * SEC;
    /// The dial watchdog in round trips.
    pub const DIAL_WAIT_RTTS: u64 = 8;
    /// The ceiling of the dial watchdog.
    pub const DIAL_CAP: u64 = 30 * SEC;
    /// Silence before the home carrier is checked on a phone or after a recent death.
    pub const HOME_KEEP: u64 = 30 * SEC;
    /// Silence before any other check.
    pub const RELAY_KEEP: u64 = 65 * SEC;
    /// How long a silent carrier death keeps the short check.
    pub const KEEP_MEMORY: u64 = 600 * SEC;
    /// The floor of the wait for a PING to be answered.
    pub const CHECK_MIN: u64 = 3 * SEC;
    /// The wait for a PING in round trips.
    pub const CHECK_RTTS: u64 = 3;
    /// The floor of the learned keepalive (KEEP_LEARN).
    pub const KEEP_FLOOR: u64 = 15 * SEC;
    /// The floor of the keepalive gap on a lease, and the shortest idle gap that counts as a death.
    pub const LEASE_FLOOR: u64 = 15 * SEC;
    /// The wait before the home carrier dials after a restart.
    pub const DEFER: u64 = 600_000_000;
}

/// The dial watchdog for a node whose round trip is `rtt`: `max(8 s, 8 x rtt)`, at most 30 s.
pub const fn dial_wait(rtt: u64) -> u64 {
    let w = rtt.saturating_mul(rule::DIAL_WAIT_RTTS);
    let w = if w > rule::DIAL_WAIT_MIN {
        w
    } else {
        rule::DIAL_WAIT_MIN
    };
    if w > rule::DIAL_CAP { rule::DIAL_CAP } else { w }
}

/// The wait for a PING to be answered: `max(3 s, 3 x rtt)`.
pub const fn check_wait(rtt: u64) -> u64 {
    let w = rtt.saturating_mul(rule::CHECK_RTTS);
    if w > rule::CHECK_MIN { w } else { rule::CHECK_MIN }
}

/// The keepalive gap once the shortest dead idle gap is `hi`: `max(15 s, min(7/8 x hi, (15 s + hi) / 2))`.
pub const fn lease_keep(hi: u64) -> u64 {
    let a = hi.saturating_mul(7) / 8;
    let b = (rule::LEASE_FLOOR.saturating_add(hi)) / 2;
    let m = if a < b { a } else { b };
    if m > rule::LEASE_FLOOR { m } else { rule::LEASE_FLOOR }
}

/// What every carrier of the node shares.
#[derive(Debug, Clone, Copy, Default)]
pub struct Shared {
    /// The node is a phone: its NATs rebind TCP mappings silently, so the home carrier is checked early.
    pub phone: bool,
    /// When a carrier last died silently (a check went unanswered), if one did.
    pub keep_fail: Option<u64>,
    /// The shortest idle gap that killed a carrier, 0 until one did. Never rises.
    pub lease_hi: u64,
    /// Learn the keepalive interval from silent deaths (KEEP_LEARN).
    pub keep_learn: bool,
    /// The learned keepalive interval, 0 until a carrier died silently with KEEP_LEARN on.
    pub keep_iv: u64,
    /// The node just restarted: the home carrier dial waits [`rule::DEFER`].
    pub restarted: bool,
    /// When the restart defer ends, set by the first dial attempt after a restart.
    pub defer_until: Option<u64>,
}

/// What the node tells a link about itself on every call that needs it.
#[derive(Debug, Clone, Copy)]
#[allow(
    clippy::struct_excessive_bools,
    reason = "independent facts the node reads, not a state"
)]
pub struct Ctx {
    /// This carrier leads to the home relay.
    pub home: bool,
    /// The larger of the node's round trip figures; 0 when none is known.
    pub rtt: u64,
    /// A UDP datagram was ever heard: the lease rules do not apply.
    pub udp_any: bool,
    /// A session rides this carrier.
    pub rides: bool,
    /// Frames wait for this carrier to open.
    pub queued: bool,
}

/// The state of a carrier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum State {
    /// No stream; a dial is wanted at [`Link::next_deadline`].
    Down,
    /// A stream is being opened.
    Dialing,
    /// The handshake completed and frames flow.
    Open,
}

/// What [`Link::pulse`] decided.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pulse {
    /// The carrier is not open: the session sends its own PING.
    Closed,
    /// A check is already outstanding: the carrier's answer will serve the session.
    Waiting,
    /// Write a PING on the carrier.
    Ping,
}

/// What the host must do.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Act {
    /// Open a stream to the relay.
    Dial,
    /// Close the stream (a watchdog, a failed check or a stale send).
    Close,
    /// Write a PING.
    Ping,
    /// The carrier is silent: write a PING, or let the next ack-eliciting session packet that leaves on it carry the
    /// check and call [`Link::check`] with `ridden`.
    Check,
}

/// One carrier's timing state.
#[derive(Debug, Clone, Copy)]
pub struct Link {
    state: State,
    retry: u64,
    at: u64,
    dial_start: u64,
    chk: u64,
    ride: bool,
    gap: u64,
    lrx: u64,
    hlt: u64,
    defer: bool,
    was_open: bool,
}

impl Default for Link {
    fn default() -> Self {
        Self::new()
    }
}

impl Link {
    /// A carrier that is down and may dial at once.
    pub const fn new() -> Self {
        Self {
            state: State::Down,
            retry: rule::RETRY_MIN,
            at: 0,
            dial_start: 0,
            chk: 0,
            ride: false,
            gap: 0,
            lrx: 0,
            hlt: 0,
            defer: false,
            was_open: false,
        }
    }

    /// The state.
    pub const fn state(&self) -> State {
        self.state
    }

    /// Whether the carrier is open.
    pub const fn is_open(&self) -> bool {
        matches!(self.state, State::Open)
    }

    /// Whether this carrier was open before the stream that is open now (a reopened carrier resends what waited).
    pub const fn was_open(&self) -> bool {
        self.was_open
    }

    /// When the carrier last heard anything.
    pub const fn last_heard(&self) -> u64 {
        self.lrx
    }

    /// When the carrier was last written to.
    pub const fn last_written(&self) -> u64 {
        self.hlt
    }

    /// The wait before the next dial, 1 s or 2 s.
    pub const fn retry(&self) -> u64 {
        self.retry
    }

    /// A dial is wanted if the carrier is down and a frame waits or this is the home carrier. Starts it when its
    /// time has come and returns [`Act::Dial`].
    pub fn want_dial(&mut self, now: u64, sh: &mut Shared, ctx: &Ctx) -> Option<Act> {
        if self.state != State::Down {
            return None;
        }
        if sh.restarted {
            let until = *sh.defer_until.get_or_insert(now.saturating_add(rule::DEFER));
            if !ctx.queued && ctx.home && now < until {
                self.at = self.at.max(until);
                self.defer = true;
                return None;
            }
            if ctx.queued && self.defer {
                self.defer = false;
                self.at = self.at.min(now);
            }
        }
        if self.at <= now && (ctx.queued || ctx.home) {
            self.state = State::Dialing;
            self.dial_start = now;
            return Some(Act::Dial);
        }
        None
    }

    /// The stream opened and the handshake completed. Returns whether the carrier was open before.
    pub fn opened(&mut self, now: u64) -> bool {
        let was = self.was_open;
        self.state = State::Open;
        self.retry = rule::RETRY_MIN;
        self.chk = 0;
        self.ride = false;
        self.lrx = now;
        self.hlt = now;
        self.was_open = true;
        was
    }

    /// The stream closed or the dial failed: wait, then dial again.
    pub fn closed(&mut self, now: u64) {
        self.state = State::Down;
        self.at = now.saturating_add(self.retry);
        self.retry = self.retry.saturating_mul(2).min(rule::RETRY_MAX);
        self.chk = 0;
    }

    /// Anything arrived on the carrier: it is alive, no check is outstanding.
    pub fn heard(&mut self, now: u64) {
        self.lrx = now;
        self.chk = 0;
    }

    /// The host wrote to the carrier.
    pub fn wrote(&mut self, now: u64) {
        self.hlt = now;
    }

    /// CARRIER_PULSE: a quiet hub session riding this relay's own carrier is kept alive by a carrier PING and PONG
    /// instead of a session PING. Starts a check when none is outstanding. [`Pulse::Closed`] means the carrier is not
    /// open and the session must send its own PING.
    pub fn pulse(&mut self, now: u64, ctx: &Ctx) -> Pulse {
        if !self.is_open() {
            return Pulse::Closed;
        }
        match self.check(now, ctx, false) {
            Some(_) => Pulse::Ping,
            None => Pulse::Waiting,
        }
    }

    /// Close the stream and dial again at once.
    pub fn reset(&mut self, now: u64) -> Act {
        self.state = State::Down;
        self.at = now;
        self.chk = 0;
        self.lrx = now;
        Act::Close
    }

    /// A frame is about to be written. A carrier idle both ways for the learned lease is reset first (STALE_SEND);
    /// the frame waits for the reopened carrier. Returns [`Act::Close`] when it did.
    pub fn before_send(&mut self, now: u64, sh: &Shared, ctx: &Ctx) -> Option<Act> {
        let hi = sh.lease_hi;
        (self.is_open() && hi != 0 && !ctx.udp_any && now - self.hlt >= hi && now - self.lrx >= hi)
            .then(|| self.reset(now))
    }

    /// Start a check now. With `ridden` an ack-eliciting session packet left on the carrier in this step and its
    /// acknowledgement is the answer; otherwise a PING is written. Returns [`Act::Ping`] when one must be written.
    pub fn check(&mut self, now: u64, ctx: &Ctx, ridden: bool) -> Option<Act> {
        if !self.is_open() || self.chk != 0 {
            return None;
        }
        self.chk = now.saturating_add(check_wait(ctx.rtt));
        self.ride = ridden;
        if ridden {
            return None;
        }
        self.gap = now.saturating_sub(self.hlt);
        Some(Act::Ping)
    }

    fn keep_after(now: u64, sh: &Shared, ctx: &Ctx) -> u64 {
        let base = if ctx.home && (sh.phone || sh.keep_fail.is_some_and(|t| now.saturating_sub(t) < rule::KEEP_MEMORY))
        {
            rule::HOME_KEEP
        } else {
            rule::RELAY_KEEP
        };
        if sh.keep_iv == 0 { base } else { base.min(sh.keep_iv) }
    }

    /// Run the timers at `now`. Returns what the host must do, if anything; call again until it returns `None`.
    pub fn tick(&mut self, now: u64, sh: &mut Shared, ctx: &Ctx) -> Option<Act> {
        match self.state {
            State::Dialing => {
                if now.saturating_sub(self.dial_start) > dial_wait(ctx.rtt) {
                    self.state = State::Down;
                    self.at = now;
                    return Some(Act::Close);
                }
                None
            }
            State::Down => self.want_dial(now, sh, ctx),
            State::Open => self.tick_open(now, sh, ctx),
        }
    }

    fn tick_open(&mut self, now: u64, sh: &mut Shared, ctx: &Ctx) -> Option<Act> {
        let lease = sh.lease_hi != 0 && !ctx.udp_any;
        if self.chk != 0 && now >= self.chk {
            if self.ride {
                self.chk = 0;
                return self.check(now, ctx, false);
            }
            sh.keep_fail = Some(now);
            if sh.keep_learn {
                let silence = now.saturating_sub(self.lrx);
                let seen = if sh.keep_iv == 0 {
                    silence
                } else {
                    sh.keep_iv.min(silence)
                };
                sh.keep_iv = (seen / 2).max(rule::KEEP_FLOOR);
            }
            if !ctx.udp_any && self.gap >= rule::LEASE_FLOOR {
                sh.lease_hi = if sh.lease_hi == 0 {
                    self.gap
                } else {
                    sh.lease_hi.min(self.gap)
                };
            }
            return Some(self.reset(now));
        }
        if self.chk != 0 {
            return None;
        }
        if lease && (ctx.home || ctx.rides) && now.saturating_sub(self.hlt) >= lease_keep(sh.lease_hi) {
            return self.check(now, ctx, false);
        }
        if (ctx.home || ctx.rides) && now.saturating_sub(self.lrx) >= Self::keep_after(now, sh, ctx) {
            return Some(Act::Check);
        }
        None
    }

    /// The first instant [`Link::tick`] can act, or `None` when nothing is scheduled.
    pub fn next_deadline(&self, now: u64, sh: &Shared, ctx: &Ctx) -> Option<u64> {
        match self.state {
            State::Dialing => Some(self.dial_start.saturating_add(dial_wait(ctx.rtt)).saturating_add(1)),
            State::Down => (ctx.queued || ctx.home).then_some(self.at),
            State::Open => {
                if self.chk != 0 {
                    return Some(self.chk);
                }
                if !(ctx.home || ctx.rides) {
                    return None;
                }
                let silent = self.lrx.saturating_add(Self::keep_after(now, sh, ctx));
                if sh.lease_hi != 0 && !ctx.udp_any {
                    return Some(self.hlt.saturating_add(lease_keep(sh.lease_hi)).min(silent));
                }
                Some(silent)
            }
        }
    }
}
