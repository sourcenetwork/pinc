//! Pending dials, DIAL_PRUNE and the first-flight rules (B8 and B9).
//!
//! **Pending dials.** A dial to a peer whose address is unknown waits for a lookup. [`Pending`] keeps, per peer, the
//! sessions that wait. On every timeout [`Pending::prune`] keeps only the sessions still in handshake and drops the
//! peer, and its lookup, when none is left (DIAL_PRUNE: without it a UDP-blocked node asked again every 300 ms for a
//! peer whose dial had already ended).
//!
//! **The first flight.** [`select`] picks the candidate paths one handshake try is sent on:
//! - *B8, HUB_DIRECT_FIRST* ([`direct_first`]): a late-starting node (its first dial came after 10 s) or a node
//!   that just restarted sends the first flight to a hub on its known UDP address only, and the relay copy joins at
//!   the first resend 300 ms later.
//! - *B9, THIN_HS0*: while a hub-session Initial is resent under the 4 s wait, only relay paths carry it, but only on
//!   a node that has heard nothing yet (no round trip of any kind).
//! - *Relay path of a direct-first session*: it is withheld at creation and registered 2 s later on an established
//!   session ([`HUB_RELAY_PATH_DELAY`]).
//! - *B9, RLY_ONCE*: on a slow link a flight already handed to a relay carrier that was not reset since is not
//!   queued again for `min(30 s, max(4 s, 3 x link rtt))`; the carrier's stream delivers it.
//! - *B9, THIN_HS*: on a slow uplink (link rtt of 250 ms or more, or two tries with no round trip known at all)
//!   with several paths, a try goes out on one path, rotating by try number, because parallel 1.2 kB copies queue
//!   behind each other on the same slow link.
//!
//! THIN_HS0 never leaves no path: when it would drop every candidate it is not applied. RLY_ONCE may leave none while
//! the relay holds the flight: the carrier's stream delivers it.
//!
//! Invariants: [`select`] returns an ordered subset of the candidates, non-empty whenever there are candidates unless
//! RLY_ONCE drops every kept relay; every table is bounded.

use pinc_crypto::NodeId;

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
/// A session that heard nothing for this long is pinged when its carrier comes back.
pub const REVERIFY_AGE: u64 = 10_000_000_000;

/// A candidate path of a flight.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cand {
    /// A UDP address.
    Udp(core::net::SocketAddr),
    /// Through the relay in this table position.
    Relay(u8),
}

/// The relays a flight to a peer goes through: the peer's own relay, when the record named one, then ours when the
/// dial started without a usable record (the first flight of `RELAY_FORWARD` reaches the peer's relay through ours). The order is fixed, whether or not a carrier to the
/// peer's relay is open, and it matters on a slow link: a node that sends one path per try takes the second relay on its
/// first try and the first on its next, so its first try goes through its own relay, which it has a carrier to. A relay
/// named twice is listed once.
pub const fn flight_relays(peer: Option<u8>, own: Option<u8>) -> [Option<u8>; 2] {
    match (peer, own) {
        (Some(p), Some(o)) if p != o => [Some(p), Some(o)],
        (Some(p), _) => [Some(p), None],
        (None, o) => [o, None],
    }
}

/// B8: whether the node counts as late at `first_dial_at`: a node that just restarted always does, it never
/// satisfies the 10 s test, so the restart flag stands beside it. The one copy of the test: the dial's first
/// flight ([`direct_first`]) and the punch's birth (`Connectivity::late_start`) both read it.
pub const fn late_start(restarted: bool, first_dial_at: u64, started: u64) -> bool {
    restarted || first_dial_at.saturating_sub(started) > LATE_START
}

/// B8: whether the first flight of this dial goes to the hub's direct address only. A node that just restarted
/// counts as late from its first dial: it never satisfies the 10 s test, so the restart flag stands beside it.
pub const fn direct_first(first_try: bool, is_hub: bool, restarted: bool, first_dial_at: u64, started: u64) -> bool {
    first_try && is_hub && late_start(restarted, first_dial_at, started)
}

/// Whether this send of a hub-session Initial goes by relay paths only: a resend inside the first
/// [`THIN_HS0_WAIT`] of the dial, on a node that has not heard a round trip of any kind yet.
pub const fn hs0(hub: bool, tries: u32, since_dial: u64, heard_nothing: bool) -> bool {
    hub && tries > 1 && since_dial < THIN_HS0_WAIT && heard_nothing
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
    let window = || cands.iter().take(kept.len());
    let hs0_drop = |c: &Cand| matches!(c, Cand::Udp(_)) && t.hs0 && t.dialer;
    let once_drop = |c: &Cand| match c {
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
        Cand::Udp(_) => false,
    };
    // THIN_HS0 never leaves no path: with no relay candidate the resend goes out on the UDP paths. RLY_ONCE always
    // applies: the relay holds the flight, and a resend would put another full Initial on its stream.
    let use_hs0 = !window().all(hs0_drop);
    for c in window() {
        if (use_hs0 && hs0_drop(c)) || once_drop(c) {
            continue;
        }
        if let Some(k) = kept.get_mut(n) {
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

    /// Whether `session` waits for its peer's address.
    pub fn holds(&self, session: T) -> bool {
        self.items.iter().flatten().any(|e| e.waiting.contains(&Some(session)))
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

#[cfg(test)]
#[allow(clippy::indexing_slicing, reason = "tests assert")]
mod tests {
    use core::net::{Ipv4Addr, SocketAddr};

    use super::*;

    const NOW: u64 = 1_000_000_000_000;

    fn u(port: u16) -> Cand {
        Cand::Udp(SocketAddr::from((Ipv4Addr::new(198, 51, 100, 7), port)))
    }

    /// A try with the THIN_HS0 flag `hs0` and, when `once`, the flight of relay 1 just handed to its live carrier on a
    /// slow link (RLY_ONCE); `tries` is 0 so no other rule thins the choice.
    fn run<'a>(cands: &[Cand], hs0: bool, once: bool, out: &'a mut [Cand; 16]) -> &'a [Cand] {
        let t = Try {
            now: NOW,
            dialer: true,
            tries: 0,
            link_rtt: if once { TG_SLOW } else { 0 },
            no_rtt: false,
            hs0,
            last_relay: once.then_some((1, 7, NOW)),
        };
        let (n, _) = select(
            cands,
            &t,
            |_| {
                Some(RelayView {
                    live: true,
                    generation: 7,
                })
            },
            out,
        );
        &out[..n]
    }

    /// What `run` returns, for the three combinations a test names.
    fn got(cands: &[Cand], hs0: bool, once: bool) -> ([Cand; 16], usize) {
        let mut out = [Cand::Relay(0); 16];
        let n = run(cands, hs0, once, &mut out).len();
        (out, n)
    }

    fn same(cands: &[Cand], hs0: bool, once: bool, want: &[Cand]) {
        let (out, n) = got(cands, hs0, once);
        assert_eq!(&out[..n], want, "{cands:?} hs0={hs0} once={once}");
    }

    #[test]
    fn thin_hs0_that_would_drop_every_candidate_is_not_applied() {
        same(&[u(1)], true, false, &[u(1)]);
        // the slow link of `once` also thins the flight to one path, try 0 taking the first (THIN_HS)
        same(&[u(1), u(2)], true, true, &[u(1)]);
        same(&[u(1), u(2)], true, false, &[u(1), u(2)]);
    }

    #[test]
    fn rly_once_drops_the_only_relay_candidate_while_the_relay_holds_the_flight() {
        let r1 = Cand::Relay(1);
        same(&[r1], false, true, &[]);
        same(&[r1, r1], false, true, &[]);
        // THIN_HS0 leaves the relay, which RLY_ONCE then drops: nothing is sent
        same(&[u(1), r1], true, true, &[]);
        // the window the relay holds the flight for ends: the same candidate is sent again
        same(&[r1], false, false, &[r1]);
    }

    #[test]
    fn a_rule_that_leaves_a_candidate_is_applied_as_before() {
        let (ur, r1, r2) = (u(1), Cand::Relay(1), Cand::Relay(2));
        same(&[ur, r1], true, false, &[r1]);
        same(&[ur, r1], false, true, &[ur]);
        same(&[r1, r2], false, true, &[r2]);
        same(&[ur, u(2), r2], true, false, &[r2]);
        same(&[ur, r2], false, false, &[ur, r2]);
    }

    #[test]
    fn every_combination_of_rules_over_one_or_two_candidates_returns_a_subset_in_order() {
        let kinds = [u(1), u(2), Cand::Relay(1), Cand::Relay(2)];
        for hs0 in [false, true] {
            for once in [false, true] {
                for a in 0..kinds.len() {
                    for b in a..kinds.len() {
                        let pair = [kinds[a], kinds[b]];
                        for cands in [core::slice::from_ref(&kinds[a]), &pair[..]] {
                            let (out, n) = got(cands, hs0, once);
                            // RLY_ONCE alone may leave none: every kept candidate is the relay holding the flight
                            let held = |c: &Cand| *c == Cand::Relay(1) || (hs0 && matches!(c, Cand::Udp(_)));
                            assert!(
                                n > 0 || (once && cands.iter().all(held)),
                                "{cands:?} hs0={hs0} once={once}"
                            );
                            let mut it = cands.iter();
                            assert!(
                                out[..n].iter().all(|g| it.any(|c| c == g)),
                                "{:?} is not an ordered subset of {cands:?}",
                                &out[..n]
                            );
                        }
                    }
                }
            }
        }
    }
}
