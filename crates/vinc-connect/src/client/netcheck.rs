//! Address discovery, home relay selection and reachability classification.
//!
//! The node sends a QAD probe with a fresh nonce to every relay's UDP address. An answer carries the address the
//! relay saw ([`crate::relay::datagram::Datagram::Qadr`]): that is the node's reflexive address, and the time the
//! answer took is the round trip to that relay. The home relay is the one with the lowest round trip; a node whose
//! probes all went unanswered picks the first relay by identity after three tries (so it is never homeless).
//!
//! The reachability class ([`classify`]) is read from what was observed, never configured:
//! 1. **UDP blocked**: no UDP datagram was ever heard and every probe went unanswered for `watchdog` since the first.
//! 2. **Public**: a reflexive address equals a local address (IPv4 or IPv6).
//! 3. **Port-mapped**: a reflexive address equals the external address of a port mapping the host holds.
//! 4. **Carrier-grade NAT**: a reflexive IPv4 address in the shared range 100.64.0.0/10, or two relays saw different
//!    addresses (a symmetric mapping, which hole punching cannot predict).
//! 5. **Behind NAT**: a reflexive address that differs from every local address and is the same at every relay that
//!    answered. With one answer this is the best the node can say; a second relay may correct it to carrier-grade.
//!
//! Invariants: the nonce of an answer must match the probe sent to that relay, and a probe is answered at most once;
//! the round trip of a relay is the last measured one; [`Netcheck::home`] is stable until a strictly lower round trip
//! is measured.

use core::net::{IpAddr, SocketAddr};

use crate::record::Reach;

/// The attempts to learn a home relay before the node takes the first one.
pub const HOME_TRIES: u8 = 3;
/// The wait between those attempts.
pub const HOME_RETRY_NS: u64 = 2_000_000_000;

/// Whether `ip` is in the shared address space of carrier-grade NAT (100.64.0.0/10).
pub const fn is_shared(ip: &IpAddr) -> bool {
    match ip {
        IpAddr::V4(v) => {
            let o = v.octets();
            o[0] == 100 && o[1] & 0xc0 == 64
        }
        IpAddr::V6(_) => false,
    }
}

/// What the node observed, for [`classify`].
#[derive(Debug, Clone, Copy)]
pub struct Observed<'a> {
    /// The node's own addresses.
    pub local: &'a [SocketAddr],
    /// The address each answering relay reported.
    pub reflexive: &'a [SocketAddr],
    /// The external addresses of the port mappings the host holds.
    pub mapped: &'a [SocketAddr],
    /// A UDP datagram was ever heard.
    pub udp_heard: bool,
    /// Time since the first probe went out.
    pub since_probe: u64,
    /// The watchdog: how long unanswered probes may take before UDP counts as blocked.
    pub watchdog: u64,
}

/// The class a node's observations give, or `None` while they say nothing yet.
pub fn classify(o: &Observed<'_>) -> Option<Reach> {
    let Some(first) = o.reflexive.first() else {
        return (!o.udp_heard && o.since_probe >= o.watchdog).then_some(Reach::UdpBlocked);
    };
    if o.reflexive.iter().any(|r| o.local.contains(r)) {
        return Some(Reach::Public);
    }
    if o.reflexive.iter().any(|r| o.mapped.contains(r)) {
        return Some(Reach::PortMapped);
    }
    if o.reflexive.iter().any(|r| is_shared(&r.ip())) || o.reflexive.iter().any(|r| r != first) {
        return Some(Reach::Cgnat);
    }
    Some(Reach::Nat)
}

#[derive(Debug, Clone, Copy)]
struct Probe {
    nonce: [u8; 8],
    sent: u64,
}

/// Probe state for `R` relays.
#[derive(Debug, Clone, Copy)]
pub struct Netcheck<const R: usize> {
    probes: [Option<Probe>; R],
    rtt: [u64; R],
    reflexive: [Option<SocketAddr>; R],
    home: Option<usize>,
    tries: u8,
    first_probe: Option<u64>,
}

impl<const R: usize> Default for Netcheck<R> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const R: usize> Netcheck<R> {
    /// No probes sent, no home.
    pub const fn new() -> Self {
        Self {
            probes: [None; R],
            rtt: [0; R],
            reflexive: [None; R],
            home: None,
            tries: 0,
            first_probe: None,
        }
    }

    /// Record a probe sent to relay `relay` at `now` with `nonce`.
    pub fn probe_sent(&mut self, now: u64, relay: usize, nonce: [u8; 8]) {
        if let Some(p) = self.probes.get_mut(relay) {
            *p = Some(Probe { nonce, sent: now });
            self.first_probe.get_or_insert(now);
        }
    }

    /// An answer arrived from `relay` for `nonce`, reporting `addr`. Returns the relay's round trip when the nonce
    /// matched an outstanding probe.
    pub fn answered(&mut self, now: u64, relay: usize, nonce: [u8; 8], addr: SocketAddr) -> Option<u64> {
        let p = self.probes.get_mut(relay)?;
        let sent = p.filter(|p| p.nonce == nonce)?.sent;
        *p = None;
        let rtt = now.saturating_sub(sent);
        *self.rtt.get_mut(relay)? = rtt;
        *self.reflexive.get_mut(relay)? = Some(addr);
        let best = (0..R)
            .filter(|i| self.reflexive.get(*i).is_some_and(Option::is_some))
            .min_by_key(|i| self.rtt.get(*i).copied().unwrap_or(u64::MAX));
        if let Some(b) = best
            && self.home != Some(b)
            && self.home.is_none_or(|h| self.rtt.get(b) < self.rtt.get(h))
        {
            self.home = Some(b);
        }
        Some(rtt)
    }

    /// The home relay chosen by round trip, once any probe was answered.
    pub const fn home(&self) -> Option<usize> {
        self.home
    }

    /// The round trip measured to `relay`, if any.
    pub fn rtt(&self, relay: usize) -> Option<u64> {
        self.reflexive_of(relay)?;
        self.rtt.get(relay).copied()
    }

    /// The lowest round trip measured to any relay.
    pub fn best_rtt(&self) -> u64 {
        (0..R)
            .filter(|i| self.reflexive.get(*i).is_some_and(Option::is_some))
            .filter_map(|i| self.rtt.get(i).copied())
            .min()
            .unwrap_or(0)
    }

    /// The reflexive address `relay` reported.
    pub fn reflexive_of(&self, relay: usize) -> Option<SocketAddr> {
        self.reflexive.get(relay).copied().flatten()
    }

    /// The reflexive addresses learned, in relay order, written to `out`; returns how many.
    pub fn reflexive_into(&self, out: &mut [SocketAddr]) -> usize {
        let mut n = 0;
        for (d, a) in out.iter_mut().zip(self.reflexive.iter().flatten()) {
            *d = *a;
            n += 1;
        }
        n
    }

    /// Forget every answer (the link changed): the next round of probes starts over. The home stays until a lower
    /// round trip is measured.
    pub fn restart(&mut self) {
        self.probes = [None; R];
        self.reflexive = [None; R];
        self.first_probe = None;
        self.tries = 0;
    }

    /// No home after a round of probes: count it. After [`HOME_TRIES`] the first relay in `order` is taken. Returns
    /// the relay chosen by this fallback, and otherwise whether to probe again.
    pub fn home_missing(&mut self, first: Option<usize>) -> HomeStep {
        if self.home.is_some() {
            return HomeStep::Done;
        }
        self.tries = self.tries.saturating_add(1);
        if self.tries >= HOME_TRIES
            && let Some(f) = first
        {
            self.home = Some(f);
            return HomeStep::Fallback(f);
        }
        HomeStep::Again
    }

    /// When the first probe of this round went out.
    pub const fn first_probe(&self) -> Option<u64> {
        self.first_probe
    }
}

/// What [`Netcheck::home_missing`] decided.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HomeStep {
    /// A home is known.
    Done,
    /// Probe again after [`HOME_RETRY_NS`].
    Again,
    /// Three rounds went unanswered: this relay is the home.
    Fallback(usize),
}
