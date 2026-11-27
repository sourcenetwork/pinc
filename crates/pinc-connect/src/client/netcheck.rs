//! Address discovery, home relay selection and reachability classification.
//!
//! The node sends a QAD probe with a fresh nonce to every relay's UDP address. An answer carries the address the
//! relay saw ([`crate::relay::datagram::Datagram::Qadr`]): that is the node's reflexive address, and the time the
//! answer took is the round trip to that relay. The home relay is the one with the lowest last-measured round trip
//! among the relays that ever answered, re-chosen at every answer (a tie goes to the relay that answered first); a node
//! whose probes all went unanswered takes the relay with the lowest id after three tries (so it is never homeless),
//! and the first answer that comes later moves it to the measured relay.
//!
//! The reachability class ([`classify`]) is read from what was observed, never configured:
//! 1. **UDP blocked**: no UDP datagram was ever heard and every probe went unanswered for `watchdog` since the first.
//! 2. **Public**: a reflexive address equals a local address (IPv4 or IPv6).
//! 3. **Port-mapped**: a port mapping the host holds has the external IP a relay saw the node at ([`mapped_seen`]; the
//!    mapping's port need not be the one the node's own traffic leaves from).
//! 4. **Carrier-grade NAT**: a reflexive IPv4 address in the shared range 100.64.0.0/10, or two relays saw different
//!    addresses (a symmetric mapping, which hole punching cannot predict).
//! 5. **Behind NAT**: a reflexive address that differs from every local address and is the same at every relay that
//!    answered. With one answer this is the best the node can say; a second relay may correct it to carrier-grade.
//!
//! An IPv4 address in its mapped IPv6 form is the IPv4 address in every rule ([`canonical`]).
//!
//! **Failover.** A relay that failed [`MISS_LIMIT`] times in a row (probes sent while the last was unanswered, or
//! carrier dials that never opened) is unhealthy. When the home relay is unhealthy the home moves only to a relay
//! known to work: the one with the lowest round trip among those that answered a probe since they last failed, else
//! the next one by table position whose carrier is open. A relay that merely has not failed yet is no target, and with
//! none the home stays. Any answer or opened carrier makes a relay healthy again.
//!
//! **Pinned home.** A deployment that runs its own relay pins it ([`Netcheck::pin`]): once the pinned relay has
//! answered a probe and is healthy, an answer makes it the home whatever its round trip. While it is unhealthy the
//! home is chosen and fails over as without a pin, and its next answer brings the home back to it. A node that hears
//! no answer at all falls back to the pinned relay instead of the one with the lowest id.
//!
//! Invariants: the nonce of an answer must match the probe sent to that relay, and a probe is answered at most once;
//! the round trip of a relay is the last measured one; [`Netcheck::home`] is the best relay of the last answer (the
//! healthy pinned relay once it answered, else the lowest round trip), so it follows the measurements without a margin.

use core::net::{IpAddr, SocketAddr};

use crate::record::Reach;

/// The attempts to learn a home relay before the node takes the one with the lowest id.
pub const HOME_TRIES: u8 = 3;
/// The wait between those attempts.
pub const HOME_RETRY_NS: u64 = 2_000_000_000;
/// Failures in a row after which a relay is unhealthy.
pub const MISS_LIMIT: u8 = 3;

/// The address as the endpoint sees it: an IPv4-mapped IPv6 address (what a dual-stack socket reports for an IPv4
/// peer) is the IPv4 address; every other address is unchanged. The one place that decides it: the hosts apply it to
/// the source of every datagram, and [`classify`] and [`Netcheck`] to every address they compare or keep.
pub const fn canonical(a: SocketAddr) -> SocketAddr {
    SocketAddr::new(a.ip().to_canonical(), a.port())
}

/// Whether `ip` (in either form of an IPv4 address) is in the shared address space of carrier-grade NAT
/// (100.64.0.0/10).
pub const fn is_shared(ip: &IpAddr) -> bool {
    match ip.to_canonical() {
        IpAddr::V4(v) => {
            let o = v.octets();
            o[0] == 100 && o[1] & 0xc0 == 64
        }
        IpAddr::V6(_) => false,
    }
}

/// Whether a relay saw the node at the external IP of the port mapping `m`: `reflexive` holds the addresses the relays
/// reported since the link last changed. A mapped address that fails this is held but never published, and never
/// decides the class; the one rule [`classify`] and the node's published addresses share.
pub fn mapped_seen(reflexive: &[SocketAddr], m: &SocketAddr) -> bool {
    reflexive.iter().any(|r| r.ip().to_canonical() == m.ip().to_canonical())
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
    if o.reflexive
        .iter()
        .any(|r| o.local.iter().any(|l| canonical(*l) == canonical(*r)))
    {
        return Some(Reach::Public);
    }
    if o.mapped.iter().any(|m| mapped_seen(o.reflexive, m)) {
        return Some(Reach::PortMapped);
    }
    if o.reflexive.iter().any(|r| is_shared(&r.ip())) || o.reflexive.iter().any(|r| canonical(*r) != canonical(*first))
    {
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
    /// The place of each relay in the order of first answers (0: never answered); kept across [`Netcheck::restart`].
    order: [u32; R],
    reflexive: [Option<SocketAddr>; R],
    home: Option<usize>,
    missed: [u8; R],
    /// Whether a probe was answered since the relay last failed ([`Netcheck::failover`]'s measured choice).
    ok_since_fail: [bool; R],
    tries: u8,
    first_probe: Option<u64>,
    pin: Option<usize>,
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
            order: [0; R],
            reflexive: [None; R],
            home: None,
            missed: [0; R],
            ok_since_fail: [false; R],
            tries: 0,
            first_probe: None,
            pin: None,
        }
    }

    /// Pin `relay` as the home (see the module docs); a position past the table is ignored.
    pub const fn pin(&mut self, relay: usize) {
        if relay < R {
            self.pin = Some(relay);
        }
    }

    /// The pinned relay, if any.
    pub const fn pinned(&self) -> Option<usize> {
        self.pin
    }

    /// Record a probe sent to relay `relay` at `now` with `nonce`. An unanswered earlier probe counts as a failure
    /// when `udp_works` (a node that never heard UDP expects none).
    pub fn probe_sent(&mut self, now: u64, relay: usize, nonce: [u8; 8], udp_works: bool) {
        if udp_works && self.probes.get(relay).copied().flatten().is_some() {
            self.failed(relay);
        }
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
        if let Some(m) = self.missed.get_mut(relay) {
            *m = 0;
        }
        if let Some(ok) = self.ok_since_fail.get_mut(relay) {
            *ok = true;
        }
        let rtt = now.saturating_sub(sent);
        *self.rtt.get_mut(relay)? = rtt;
        *self.reflexive.get_mut(relay)? = Some(canonical(addr));
        if self.order.get(relay) == Some(&0) {
            let next = self.order.iter().max().map_or(1, |m| m.saturating_add(1));
            *self.order.get_mut(relay)? = next;
        }
        // Every relay that ever answered counts, not only those since the last link change; an unhealthy one does not.
        let measured = |i: usize| self.order.get(i).is_some_and(|o| *o > 0) && !self.unhealthy(i);
        let pinned = self.pin.filter(|p| measured(*p));
        let best = pinned.or_else(|| {
            (0..R).filter(|i| measured(*i)).min_by_key(|i| {
                (
                    self.rtt.get(*i).copied().unwrap_or(u64::MAX),
                    self.order.get(*i).copied(),
                )
            })
        });
        if best.is_some() {
            self.home = best;
        }
        Some(rtt)
    }

    /// A probe or a carrier dial of `relay` failed.
    pub fn failed(&mut self, relay: usize) {
        if let Some(m) = self.missed.get_mut(relay) {
            *m = m.saturating_add(1);
        }
        if let Some(ok) = self.ok_since_fail.get_mut(relay) {
            *ok = false;
        }
    }

    /// A carrier to `relay` opened: it is healthy (it is not thereby known to answer probes).
    pub fn healthy(&mut self, relay: usize) {
        if let Some(m) = self.missed.get_mut(relay) {
            *m = 0;
        }
    }

    /// Whether `relay` failed [`MISS_LIMIT`] times in a row.
    pub fn unhealthy(&self, relay: usize) -> bool {
        self.missed.get(relay).is_some_and(|m| *m >= MISS_LIMIT)
    }

    /// Move the home away from an unhealthy relay, only to one known to work: a probe answered since it last failed
    /// (lowest round trip first), else an `open` carrier (next by table position). `usable` says which relays are
    /// configured. With no such relay the home stays. Returns the new home.
    pub fn failover(&mut self, usable: impl Fn(usize) -> bool, open: impl Fn(usize) -> bool) -> Option<usize> {
        let home = self.home?;
        if !self.unhealthy(home) {
            return None;
        }
        let measured = (0..R)
            .filter(|i| {
                *i != home
                    && usable(*i)
                    && self.missed.get(*i) == Some(&0)
                    && self.ok_since_fail.get(*i) == Some(&true)
                    && self.reflexive.get(*i).is_some_and(Option::is_some)
            })
            .min_by_key(|i| self.rtt.get(*i).copied().unwrap_or(u64::MAX));
        let next = measured.or_else(|| {
            (1..R)
                .map(|k| (home + k) % R)
                .find(|i| usable(*i) && open(*i) && !self.unhealthy(*i))
        })?;
        self.home = Some(next);
        Some(next)
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

    /// The distinct reflexive addresses learned, in relay order, written to `out`; returns how many. An address that
    /// several relays report is listed once.
    pub fn reflexive_into(&self, out: &mut [SocketAddr]) -> usize {
        let mut n = 0;
        for a in self.reflexive.iter().flatten() {
            if !out.get(..n).unwrap_or_default().contains(a)
                && let Some(d) = out.get_mut(n)
            {
                *d = *a;
                n += 1;
            }
        }
        n
    }

    /// Forget every answer since the link changed: the next round of probes starts over. The home stays until a round
    /// trip measured later names another, and the count of rounds without a home is kept: a node that moved with two
    /// silent rounds behind it takes the fallback after one more.
    pub fn restart(&mut self) {
        self.probes = [None; R];
        self.reflexive = [None; R];
        self.first_probe = None;
    }

    /// No home after a round of probes: count it. After [`HOME_TRIES`] `first`, the relay with the lowest id, is taken. Returns
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

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::cast_possible_truncation, reason = "tests assert")]
mod tests {
    use core::net::Ipv4Addr;

    use super::*;

    fn v4(a: u8, b: u8, c: u8, d: u8) -> SocketAddr {
        SocketAddr::from((Ipv4Addr::new(a, b, c, d), 4000))
    }

    fn mapped(a: u8, b: u8, c: u8, d: u8) -> SocketAddr {
        SocketAddr::new(Ipv4Addr::new(a, b, c, d).to_ipv6_mapped().into(), 4000)
    }

    fn class(local: &[SocketAddr], reflexive: &[SocketAddr], mapped: &[SocketAddr]) -> Option<Reach> {
        classify(&Observed {
            local,
            reflexive,
            mapped,
            udp_heard: true,
            since_probe: 0,
            watchdog: 8_000_000_000,
        })
    }

    #[test]
    fn a_mapped_address_is_its_ipv4_address_and_nothing_else_changes() {
        assert_eq!(canonical(mapped(1, 2, 3, 4)), v4(1, 2, 3, 4));
        assert_eq!(canonical(v4(1, 2, 3, 4)), v4(1, 2, 3, 4));
        let v6 = SocketAddr::new("2001:db8::1".parse().unwrap(), 9);
        assert_eq!(canonical(v6), v6);
    }

    #[test]
    fn each_rule_gives_the_same_class_in_either_form() {
        let me = v4(198, 51, 100, 7);
        let nat_local = v4(192, 168, 1, 2);
        for (local, reflexive, mapped_ext, want) in [
            // blocked: nothing reported
            (nat_local, None, None, None),
            // public
            (me, Some([mapped(198, 51, 100, 7)]), None, Some(Reach::Public)),
            (mapped(198, 51, 100, 7), Some([me]), None, Some(Reach::Public)),
            // port-mapped
            (
                nat_local,
                Some([mapped(203, 0, 113, 9)]),
                Some(v4(203, 0, 113, 9)),
                Some(Reach::PortMapped),
            ),
            (
                nat_local,
                Some([v4(203, 0, 113, 9)]),
                Some(mapped(203, 0, 113, 9)),
                Some(Reach::PortMapped),
            ),
            // shared range
            (nat_local, Some([mapped(100, 64, 0, 1)]), None, Some(Reach::Cgnat)),
            (nat_local, Some([v4(100, 64, 0, 1)]), None, Some(Reach::Cgnat)),
            // behind NAT
            (nat_local, Some([mapped(203, 0, 113, 9)]), None, Some(Reach::Nat)),
        ] {
            let reflexive: &[SocketAddr] = reflexive.as_ref().map_or(&[], |r| r);
            let mapped_ext: &[SocketAddr] = mapped_ext.as_slice();
            assert_eq!(class(&[local], reflexive, mapped_ext), want, "{local} {reflexive:?}");
        }
    }

    #[test]
    fn two_relays_that_report_one_address_in_two_forms_agree_and_two_addresses_do_not() {
        let local = [v4(192, 168, 1, 2)];
        assert_eq!(
            class(&local, &[v4(203, 0, 113, 9), mapped(203, 0, 113, 9)], &[]),
            Some(Reach::Nat)
        );
        assert_eq!(
            class(&local, &[mapped(203, 0, 113, 9), v4(203, 0, 113, 8)], &[]),
            Some(Reach::Cgnat)
        );
        let v6 = SocketAddr::new("2001:db8::1".parse().unwrap(), 4000);
        assert_eq!(class(&[v6], &[v6], &[]), Some(Reach::Public));
        assert_eq!(class(&local, &[v6, mapped(203, 0, 113, 9)], &[]), Some(Reach::Cgnat));
    }

    #[test]
    fn the_table_keeps_the_canonical_address() {
        let mut n = Netcheck::<2>::new();
        n.probe_sent(0, 0, [1; 8], true);
        n.probe_sent(0, 1, [2; 8], true);
        n.answered(10, 0, [1; 8], mapped(203, 0, 113, 9)).unwrap();
        n.answered(10, 1, [2; 8], v4(203, 0, 113, 9)).unwrap();
        assert_eq!(n.reflexive_of(0), Some(v4(203, 0, 113, 9)));
        let mut out = [v4(0, 0, 0, 0); 2];
        assert_eq!(n.reflexive_into(&mut out), 1, "one address in two forms is listed once");
    }
    #[test]
    fn a_relay_whose_carrier_opened_after_its_failure_is_not_a_measured_failover_target() {
        let mut n = Netcheck::<3>::new();
        for r in 0..3 {
            n.probe_sent(0, r, [r as u8; 8], true);
            n.answered(10 * (r as u64 + 1), r, [r as u8; 8], v4(203, 0, 113, 9))
                .unwrap();
        }
        assert_eq!(n.home(), Some(0));
        // relay 1 failed since its answer, then a carrier opened and closed: healthy, but no answer since the failure
        n.failed(1);
        n.healthy(1);
        for _ in 0..MISS_LIMIT {
            n.failed(0);
        }
        assert_eq!(
            n.failover(|_| true, |_| false),
            Some(2),
            "only relay 2 answered since it last failed"
        );
    }

    #[test]
    fn an_answer_after_the_failure_makes_the_relay_a_target_and_the_lowest_round_trip_wins() {
        let mut n = Netcheck::<3>::new();
        for r in 0..3 {
            n.probe_sent(0, r, [r as u8; 8], true);
            n.answered(10 * (r as u64 + 1), r, [r as u8; 8], v4(203, 0, 113, 9))
                .unwrap();
        }
        n.failed(1);
        n.healthy(1);
        n.probe_sent(100, 1, [9; 8], true);
        n.answered(115, 1, [9; 8], v4(203, 0, 113, 9)).unwrap();
        for _ in 0..MISS_LIMIT {
            n.failed(0);
        }
        // relay 1 now has a round trip of 15, relay 2 of 30
        assert_eq!(n.failover(|_| true, |_| false), Some(1));
    }

    #[test]
    fn with_no_measured_relay_failover_takes_an_open_carrier_or_stays() {
        let mut n = Netcheck::<2>::new();
        n.probe_sent(0, 0, [1; 8], true);
        n.answered(10, 0, [1; 8], v4(203, 0, 113, 9)).unwrap();
        n.healthy(1);
        for _ in 0..MISS_LIMIT {
            n.failed(0);
        }
        assert_eq!(n.failover(|_| true, |_| false), None);
        assert_eq!(n.home(), Some(0));
        assert_eq!(n.failover(|_| true, |i| i == 1), Some(1));
    }
}
