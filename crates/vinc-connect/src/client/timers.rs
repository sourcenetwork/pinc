//! The timers of [`Connectivity`]: carrier links, lookups, address discovery, the record, beacons and suspension.

use vinc_core::LATE_START;
use vinc_crypto::Provider;
use vinc_security::Env;

use super::conn::{Connectivity, Notice};
use super::netcheck::{HOME_RETRY_NS, HomeStep};
use crate::relay::rule;

/// The wait before address discovery starts again after the node's link changed.
const NETCHECK_DELAY: u64 = 50_000_000;

impl<P: Provider, const R: usize, const PEERS: usize> Connectivity<P, R, PEERS> {
    /// The first instant [`Connectivity::tick`] has something to do.
    pub fn next_deadline(&self, now: u64) -> Option<u64> {
        let mut t = if self.has_relays() { self.next_probe } else { u64::MAX };
        for i in 0..R {
            let ctx = self.ctx(i);
            if let Some(r) = self.rly.get(i).filter(|r| r.cfg.is_some())
                && let Some(d) = r.link.next_deadline(now, &self.shared, &ctx)
            {
                t = t.min(d);
            }
        }
        for d in [
            self.lookups.next_deadline(),
            // A record due while the home carrier is not open waits for the carrier: its opening re-arms the time.
            Some(self.next_publish).filter(|p| *p != 0 && *p != u64::MAX && self.can_publish()),
            Some(self.duty.deadline()).filter(|_| self.beacons_on),
            self.close_deadline(),
            self.session_deadline(),
        ]
        .into_iter()
        .flatten()
        {
            t = t.min(d);
        }
        // Until a class is known, the watchdog that declares UDP blocked is a deadline of its own.
        if self.class.is_none()
            && let Some(first) = self.net.first_probe()
        {
            let at = first
                .saturating_add(super::link::dial_wait(self.net.best_rtt()))
                .saturating_add(1);
            if at > now {
                t = t.min(at);
            }
        }
        (t != u64::MAX).then_some(t)
    }

    /// Set the node's round trip figures: the larger of the endpoint's `tgr` and `lrtt`, and `tgr` itself.
    pub fn set_node_rtt(&mut self, rtt: u64, peak: u64) {
        self.node_rtt = rtt;
        self.node_tgr = peak;
    }

    /// Say which relays a session rides (their carriers are kept checked).
    pub fn set_rides(&mut self, relay: usize, rides: bool) {
        if let Some(r) = self.rly.get_mut(relay) {
            r.rides = rides;
        }
    }

    /// Run every timer at `now`. `wall_ms` is the node's wall clock in milliseconds; with it the layer asks the host
    /// to sign its record ([`Connectivity::sign_request`]), without it nothing is signed.
    pub fn tick(&mut self, now: u64, env: &mut Env<'_, P>, wall_ms: Option<u64>) {
        self.clock = self.clock.max(now);
        if wall_ms.is_some() {
            self.sign.wall_ms = wall_ms;
        }
        for i in 0..R {
            if self.rly.get(i).is_none_or(|r| r.cfg.is_none()) {
                continue;
            }
            for _ in 0..4 {
                let ctx = self.ctx(i);
                let act = {
                    let Some(r) = self.rly.get_mut(i) else { break };
                    r.link.tick(now, &mut self.shared, &ctx)
                };
                match act {
                    Some(a) => self.act_pub(now, i, a),
                    None => break,
                }
            }
        }
        if now >= self.next_probe {
            self.probe_all(now, env);
            self.check_failover(now);
            self.next_probe = now.saturating_add(HOME_RETRY_NS);
            if self.net.home().is_none() {
                // A node none of whose relays takes UDP (a browser) has no probe to wait for: its first relay is home.
                let configured = |i: &usize| self.rly.get(*i).is_some_and(|r| r.cfg.is_some());
                let first = (0..R)
                    .find(|i| self.rly.get(*i).is_some_and(|r| r.cfg.is_some_and(|c| c.udp.is_some())))
                    .or_else(|| (0..R).find(configured));
                if let HomeStep::Fallback(f) = self.net.home_missing(first) {
                    self.notice(Notice::Home(f));
                }
            } else {
                // Probing goes on at the record's pace once a home is known.
                self.next_probe = now.saturating_add(rule::RECORD_REPUBLISH_NS / 30);
            }
        }
        let due: [Option<vinc_crypto::NodeId>; 4] = {
            let mut a = [None; 4];
            for (d, p) in a.iter_mut().zip(self.lookups.due(now)) {
                *d = Some(p);
            }
            a
        };
        for p in due.into_iter().flatten() {
            self.lookup(now, &p);
        }
        self.close_for_suspend(now);
        self.update_class(now);
        self.publish(now);
        self.start_jobs(now);
    }

    /// Ask for the signed record when it is due (the class or home changed, the carrier opened, or 1800 s passed)
    /// and the home carrier is open.
    fn publish(&mut self, now: u64) {
        if self.next_publish == 0
            || self.next_publish == u64::MAX
            || now < self.next_publish
            || self.sign.record_wanted()
        {
            return;
        }
        if self.can_publish() {
            self.sign.want_record();
            // Disarmed until the signature is answered.
            self.next_publish = u64::MAX;
        }
    }

    /// Whether a record can be asked for now: the class is known and the carrier of the home relay is open. The one
    /// rule the publish step and its deadline share.
    fn can_publish(&self) -> bool {
        self.class.is_some()
            && self
                .net
                .home()
                .and_then(|h| self.rly.get(h))
                .is_some_and(|r| r.link.is_open())
    }

    pub(super) fn me_addr_pub(&self) -> core::net::SocketAddr {
        core::net::SocketAddr::new(core::net::IpAddr::V4(core::net::Ipv4Addr::UNSPECIFIED), 0)
    }

    /// The node is about to be suspended: tell every relay with an open carrier, twice over UDP, so the carrier close
    /// that follows is not taken as a crash; then the carriers close. `wall_ms` is the node's clock in milliseconds.
    /// The notices are signed by the host's key ([`Connectivity::sign_request`]); the carriers close once all of them
    /// were answered.
    pub fn suspend(&mut self, now: u64, wall_ms: u64) {
        let mut relays = 0u32;
        for i in 0..R.min(32) {
            if self.relay_cfg(i).is_some_and(|c| c.udp.is_some()) && self.rly.get(i).is_some_and(|r| r.link.is_open()) {
                relays |= 1 << i;
            }
        }
        self.sign.wall_ms = Some(wall_ms);
        self.sign.begin_suspend(relays, wall_ms);
        self.start_jobs(now);
        self.maybe_close_for_suspend(now);
    }

    /// The node resumed. Carriers that the system closed during the suspension are dialed again; open ones are
    /// checked at once.
    pub fn resume(&mut self, now: u64) {
        self.sign.cancel_suspend();
        self.net.restart();
        self.next_probe = now.saturating_add(10_000_000);
        self.duty.restart(now);
        for i in 0..R {
            let ctx = self.ctx(i);
            let act = self.rly.get_mut(i).and_then(|r| {
                if r.link.is_open() {
                    r.link.check(now, &ctx, false)
                } else {
                    r.link.want_dial(now, &mut self.shared, &ctx)
                }
            });
            if let Some(a) = act {
                self.act_pub(now, i, a);
            }
        }
    }

    /// The link of the node changed (an interface came up or changed address): discover the address again and
    /// beacon again.
    pub fn link_changed(&mut self, now: u64) {
        self.net.restart();
        self.next_probe = now.saturating_add(NETCHECK_DELAY);
        self.duty.restart(now);
        for i in 0..R {
            self.check_carrier(now, i);
        }
        self.arm_punches(now);
    }

    /// Sessions of this protocol carry broadcast traffic: the endpoint flushes them after the others.
    pub fn set_gossip_alpn(&mut self, alpn: &[u8]) {
        self.gossip_alpn = vinc_security::Alpn::new(alpn);
    }

    /// Whether the node's first dial counts as a late start.
    pub const fn late_start(&self, first_dial: u64) -> bool {
        first_dial.saturating_sub(self.start) > LATE_START
    }
}
