//! Hole punching: the candidate exchange and when to try again.
//!
//! Punching is an upgrade of a relayed session to a direct path and never a requirement: the relay path stays open
//! throughout. Once a session is established over a relay, each side sends a REACH_OUT ([`encode`]) with its own
//! candidate addresses (its reflexive addresses first, then its local ones, at most 8) and, on receiving the peer's,
//! starts probing them. The probe schedule itself belongs to the transport: 9 probes, the first after
//! `max(33.3 ms, srtt / 8)` and the gap doubling up to 2 s ([`probe_gaps`] writes it down).
//!
//! A [`Puncher`] decides when a session punches: 1 ms after it is established, then every 60 s, except that a session
//! whose active path is direct and answers in 10 ms or less stops, a session with no application data for 20 s only
//! waits another 60 s, and a session inside a quiet window after a resume whose direct path already carries it waits
//! for the window to end.
//!
//! Wire format of a REACH_OUT body: `n(1)` then `n` addresses of `tag(1) ip(4 or 16) port(2)` as in a record, at
//! most 8. Invariants: [`decode`] accepts exactly what [`encode`] writes and never reads past the body.

use core::net::SocketAddr;

use pinc_wire::{Reader, Writer};

use crate::record::{MAX_ADDRS, read_addr, write_addr};

/// Probes sent to a new candidate.
pub const PROBES: u32 = 9;
/// The first probe gap floor.
pub const PROBE_BASE: u64 = 33_300_000;
/// The largest probe gap.
pub const PROBE_CAP: u64 = 2_000_000_000;
/// The wait between punch rounds.
pub const UPGRADE_INTERVAL: u64 = 60_000_000_000;
/// The delay before a session punches again after the node's address changed.
pub const LINK_PUNCH: u64 = 100_000_000;
/// A direct path at least this fast is good enough.
pub const GOOD_LATENCY: u64 = 10_000_000;
/// The delay before the first punch of an established session.
pub const FIRST_DELAY: u64 = 1_000_000;
/// The delay before the punch timer fires after a session fell back to its relay path.
pub const FALLBACK_PUNCH: u64 = 2_000_000_000;
/// Application silence after which a session only waits another interval.
pub const ACTIVE_KEEP: u64 = 20_000_000_000;
/// The delay before the first punch of a late-start node's hub session that already runs on a direct path.
pub const MTU_DEFER: u64 = 3_000_000_000;

/// How a session that just came up is placed for the punch timer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Born {
    /// An ordinary session, or a sub-session born on a relay path: punch [`FIRST_DELAY`] later.
    Plain,
    /// A hub session this node dialed after a late start, already on a direct path: the hub's other addresses are
    /// validated [`MTU_DEFER`] later, outside the window in which the application's first bytes flow.
    LateHubDirect,
    /// A sub-session born on a validated direct path: nothing to upgrade, the timer stays off.
    SubDirect,
}

/// The gaps between the [`PROBES`] probes of a path whose smoothed round trip is `srtt`.
pub fn probe_gaps(srtt: u64) -> [u64; PROBES as usize] {
    let mut gap = PROBE_BASE.max(srtt / 8);
    let mut out = [0; PROBES as usize];
    for g in &mut out {
        *g = gap;
        gap = gap.saturating_mul(2).min(PROBE_CAP);
    }
    out
}

/// Encode `cands` (the first [`MAX_ADDRS`]) into `out`; returns the length.
pub fn encode(cands: &[SocketAddr], out: &mut [u8]) -> Option<usize> {
    let n = cands.len().min(MAX_ADDRS);
    let mut w = Writer::new(out);
    w.put_u8(u8::try_from(n).ok()?).ok()?;
    for a in cands.iter().take(n) {
        write_addr(&mut w, a).ok()?;
    }
    Some(w.written().len())
}

/// Decode a REACH_OUT body into `out`; returns how many addresses. `None` if the body is malformed.
pub fn decode(body: &[u8], out: &mut [SocketAddr; MAX_ADDRS]) -> Option<usize> {
    let mut r = Reader::new(body);
    let n = usize::from(r.read_u8().ok()?);
    if n > MAX_ADDRS {
        return None;
    }
    for d in out.iter_mut().take(n) {
        *d = read_addr(&mut r).ok()?;
    }
    r.is_empty().then_some(n)
}

/// What a session shows when its punch time comes.
#[derive(Debug, Clone, Copy)]
pub struct View {
    /// Time since the application last moved data on the session.
    pub app_idle: u64,
    /// The active path is direct and validated.
    pub direct: bool,
    /// The smoothed round trip of the active path, 0 if unknown.
    pub rtt: u64,
    /// The end of a quiet window after a resume, 0 if none.
    pub quiet_until: u64,
}

/// What a due punch does.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Step {
    /// Send REACH_OUT and probe; the next round follows [`UPGRADE_INTERVAL`] later unless the path is good.
    Punch,
    /// Nothing to do now.
    Wait,
}

/// The punch timer of one session.
#[derive(Debug, Clone, Copy, Default)]
pub struct Puncher {
    at: u64,
}

impl Puncher {
    /// A timer that is off.
    pub const fn off() -> Self {
        Self { at: 0 }
    }

    /// The session was established: punch [`FIRST_DELAY`] later.
    pub const fn established(&mut self, now: u64) {
        self.at = now.saturating_add(FIRST_DELAY);
    }

    /// The timer of a session that just came up, by how it was born.
    pub const fn born(now: u64, how: Born) -> Self {
        match how {
            Born::Plain => Self {
                at: now.saturating_add(FIRST_DELAY),
            },
            Born::LateHubDirect => Self {
                at: now.saturating_add(MTU_DEFER),
            },
            Born::SubDirect => Self::off(),
        }
    }

    /// Punch at `at` (for example 100 ms after a resume).
    pub const fn arm(&mut self, at: u64) {
        self.at = at;
    }

    /// When the timer fires, if it is on.
    pub const fn deadline(&self) -> Option<u64> {
        if self.at == 0 { None } else { Some(self.at) }
    }

    /// Run the timer at `now`.
    pub fn due(&mut self, now: u64, v: &View) -> Step {
        if self.at == 0 || now < self.at {
            return Step::Wait;
        }
        if now < v.quiet_until && v.direct {
            self.at = v.quiet_until.saturating_add(1);
            return Step::Wait;
        }
        if v.app_idle >= ACTIVE_KEEP {
            self.at = now.saturating_add(UPGRADE_INTERVAL);
            return Step::Wait;
        }
        self.at = if v.direct && v.rtt != 0 && v.rtt <= GOOD_LATENCY {
            0
        } else {
            now.saturating_add(UPGRADE_INTERVAL)
        };
        Step::Punch
    }
}
