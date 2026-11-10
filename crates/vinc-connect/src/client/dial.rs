//! Pending dials, DIAL_PRUNE and the first-flight rules (B8 and B9).
//!
//! **Pending dials.** A dial to a peer whose address is unknown waits for a lookup. [`Pending`] keeps, per peer, the
//! sessions that wait. On every timeout [`Pending::prune`] keeps only the sessions still in handshake and drops the
//! peer, and its lookup, when none is left (DIAL_PRUNE: without it a UDP-blocked node asked again every 300 ms for a
//! peer whose dial had already ended).
//!
//! **The first flight.** [`select`] picks the candidate paths one handshake try is sent on:
//! - *B8, HUB_DIRECT_FIRST* ([`direct_first`]): a late-starting node (its first dial came after 10 s) sends the
//!   first flight to a hub on its known UDP address only, and the relay copy joins at the first resend 300 ms later.
//! - *B9, THIN_HS0*: while a hub-session Initial is resent under the 4 s wait, only relay paths carry it.
//! - *B9, RLY_ONCE*: on a slow link a flight already handed to a relay carrier that was not reset since is not
//!   queued again for `min(30 s, max(4 s, 3 x link rtt))`; the carrier's stream delivers it.
//! - *B9, THIN_HS*: on a slow uplink (link rtt of 250 ms or more, or two tries with no round trip known at all)
//!   with several paths, a try goes out on one path, rotating by try number, because parallel 1.2 kB copies queue
//!   behind each other on the same slow link.
//!
//! Invariants: [`select`] returns a non-empty subset of the candidates whenever there are candidates, in candidate
//! order; every table is bounded.

use vinc_crypto::NodeId;

/// The wait before the relay copy joins a direct-first flight.
pub const HUB_RELAY_DELAY: u64 = 300_000_000;
/// A node whose first dial came after this long is a late start.
pub const LATE_START: u64 = 10_000_000_000;
/// A direct-first hub session gets its relay path this long after its creation.
pub const HUB_RELAY_PATH_DELAY: u64 = 2_000_000_000;
/// Direct addresses in a direct-first flight.
pub const HUB_FIRST_ADDRS: usize = 1;
/// The link round trip from which a link is slow.
pub const TG_SLOW: u64 = 250_000_000;
/// The longest a relayed flight is not queued again.
pub const RLY_ONCE: u64 = 30_000_000_000;
/// THIN_HS0: a hub-session Initial resent within this long of the dial goes by relay paths only.
pub const THIN_HS0_WAIT: u64 = 4_000_000_000;
/// The floor of that wait.
pub const RLY_ONCE_MIN: u64 = 4_000_000_000;

/// A candidate path of a flight.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cand {
    /// A UDP address.
    Udp(core::net::SocketAddr),
    /// Through the relay in this table position.
    Relay(u8),
}

/// B8: whether the first flight of this dial goes to the hub's direct address only.
pub const fn direct_first(first_try: bool, is_hub: bool, first_dial_at: u64, started: u64) -> bool {
    first_try && is_hub && first_dial_at.saturating_sub(started) > LATE_START
}

/// What a flight knows about the relay carrier a relay candidate would use.
#[derive(Debug, Clone, Copy)]
pub struct RelayView {
    /// The carrier is open or dialing.
    pub live: bool,
    /// The stream generation of the carrier: changes when it is reset.
    pub generation: u64,
}

/// What one handshake try reads.
#[derive(Debug, Clone, Copy)]
pub struct Try {
    /// The current time.
    pub now: u64,
    /// This is the dialer's handshake.
    pub dialer: bool,
    /// Sends so far, counting this try.
    pub tries: u32,
    /// The link round trip (QAD or handshake, never a queue-bloated figure); 0 when unknown.
    pub link_rtt: u64,
    /// No round trip of any kind is known.
    pub no_rtt: bool,
    /// THIN_HS0: this send is a hub-session Initial resend under the 4 s wait.
    pub hs0: bool,
    /// The relay and stream generation that carried the last flight, and when.
    pub last_relay: Option<(u8, u64, u64)>,
}

/// Choose the candidates this try is sent on, writing them to `out`; returns how many. `relay` describes a relay's
/// carrier. Also reports the relay that now carries the flight.
pub fn select(
    cands: &[Cand],
    t: &Try,
    relay: impl Fn(u8) -> Option<RelayView>,
    out: &mut [Cand],
) -> (usize, Option<(u8, u64)>) {
    let mut kept = [Cand::Relay(0); 16];
    let mut n = 0;
    let slow = t.link_rtt >= TG_SLOW;
    for c in cands.iter().take(kept.len()) {
        let drop = match c {
            Cand::Udp(_) => t.hs0 && t.dialer,
            Cand::Relay(r) => {
                t.dialer
                    && slow
                    && relay(*r).is_some_and(|v| {
                        v.live
                            && t.last_relay.is_some_and(|(lr, gen_, at)| {
                                lr == *r
                                    && gen_ == v.generation
                                    && t.now.saturating_sub(at)
                                        < RLY_ONCE.min(RLY_ONCE_MIN.max(t.link_rtt.saturating_mul(3)))
                            })
                    })
            }
        };
        if !drop && let Some(k) = kept.get_mut(n) {
            *k = *c;
            n += 1;
        }
    }
    let thin = t.dialer && n > 1 && (slow || (t.tries >= 2 && t.no_rtt));
    let picked: &[Cand] = if thin {
        let at = t.tries as usize % n;
        kept.get(at..=at).unwrap_or_default()
    } else {
        kept.get(..n).unwrap_or_default()
    };
    let mut m = 0;
    let mut carried = None;
    for (d, c) in out.iter_mut().zip(picked) {
        *d = *c;
        m += 1;
        if let Cand::Relay(r) = c {
            carried = Some((*r, relay(*r).map_or(0, |v| v.generation)));
        }
    }
    (m, carried)
}

#[derive(Debug, Clone, Copy)]
struct Entry<T: Copy, const H: usize> {
    peer: NodeId,
    waiting: [Option<T>; H],
}

/// Sessions waiting for the address of up to `N` peers, `H` sessions each.
#[derive(Debug, Clone, Copy)]
pub struct Pending<T: Copy + PartialEq, const N: usize, const H: usize> {
    items: [Option<Entry<T, H>>; N],
}

impl<T: Copy + PartialEq, const N: usize, const H: usize> Default for Pending<T, N, H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Copy + PartialEq, const N: usize, const H: usize> Pending<T, N, H> {
    /// Nothing waits.
    pub const fn new() -> Self {
        Self { items: [None; N] }
    }

    /// Whether any session waits for `peer`.
    pub fn contains(&self, peer: &NodeId) -> bool {
        self.items.iter().flatten().any(|e| e.peer == *peer)
    }

    /// The peers that have waiting sessions.
    pub fn peers(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.items.iter().flatten().map(|e| e.peer)
    }

    /// Wait for `peer`'s address with `session`. Returns false if the table or the peer's list is full.
    pub fn add(&mut self, peer: NodeId, session: T) -> bool {
        let at = self.items.iter().position(|e| e.is_some_and(|e| e.peer == peer));
        let slot = match at {
            Some(p) => p,
            None => match self.items.iter().position(Option::is_none) {
                Some(p) => p,
                None => return false,
            },
        };
        let Some(s) = self.items.get_mut(slot) else {
            return false;
        };
        let e = s.get_or_insert(Entry {
            peer,
            waiting: [None; H],
        });
        if e.waiting.contains(&Some(session)) {
            return true;
        }
        match e.waiting.iter_mut().find(|w| w.is_none()) {
            Some(w) => {
                *w = Some(session);
                true
            }
            None => false,
        }
    }

    /// The address of `peer` arrived: the sessions that waited, to dial now.
    pub fn take(&mut self, peer: &NodeId) -> [Option<T>; H] {
        for s in &mut self.items {
            if s.is_some_and(|e| e.peer == *peer) {
                return s.take().map_or([None; H], |e| e.waiting);
            }
        }
        [None; H]
    }

    /// DIAL_PRUNE: keep only the sessions for which `in_handshake` holds. A peer left with none is dropped and passed
    /// to `dropped` (the caller drops its lookup).
    pub fn prune(&mut self, mut in_handshake: impl FnMut(T) -> bool, mut dropped: impl FnMut(&NodeId)) {
        for s in &mut self.items {
            let Some(e) = s.as_mut() else { continue };
            for w in &mut e.waiting {
                if w.is_some_and(|t| !in_handshake(t)) {
                    *w = None;
                }
            }
            if e.waiting.iter().all(Option::is_none) {
                dropped(&e.peer);
                *s = None;
            }
        }
    }
}
