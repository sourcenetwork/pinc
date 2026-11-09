//! The timers of [`Connectivity`]: carrier links, lookups, address discovery, the record, beacons and suspension.

use vinc_core::LATE_START;
use vinc_crypto::{Keypair, Provider};
use vinc_security::Env;

use super::conn::{Connectivity, Notice};
use super::link::State;
use super::netcheck::{HOME_RETRY_NS, HomeStep};
use crate::carrier::Frame;
use crate::record::{self, MAX_ADDRS, RecordFields};
use crate::relay::datagram::Datagram;
use crate::relay::{rule, sleep};

impl<P: Provider, const R: usize, const PEERS: usize> Connectivity<P, R, PEERS> {
    /// The first instant [`Connectivity::tick`] has something to do.
    pub fn next_deadline(&self, now: u64) -> Option<u64> {
        let mut t = self.next_probe;
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
            Some(self.next_publish).filter(|p| *p != 0 && self.class.is_some()),
            Some(self.duty.deadline()),
        ]
        .into_iter()
        .flatten()
        {
            t = t.min(d);
        }
        Some(t)
    }

    /// Set the larger of the node's round trip figures (the endpoint's `tgr` and `lrtt`).
    pub fn set_node_rtt(&mut self, rtt: u64) {
        self.node_rtt = rtt;
    }

    /// Say which relays a session rides (their carriers are kept checked).
    pub fn set_rides(&mut self, relay: usize, rides: bool) {
        if let Some(r) = self.rly.get_mut(relay) {
            r.rides = rides;
        }
    }

    /// Run every timer at `now`. `signer` publishes the record (a software key; see the crate docs).
    pub fn tick(&mut self, now: u64, env: &mut Env<'_, P>, signer: Option<(&Keypair, u64)>) {
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
            self.next_probe = now.saturating_add(HOME_RETRY_NS);
            if self.net.home().is_none() {
                let first = (0..R).find(|i| self.rly.get(*i).is_some_and(|r| r.cfg.is_some_and(|c| c.udp.is_some())));
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
        self.publish(now, signer);
    }

    /// Publish the signed record on the home carrier when it is due (the class or home changed, the carrier opened,
    /// or 1800 s passed).
    fn publish(&mut self, now: u64, signer: Option<(&Keypair, u64)>) {
        let (Some((kp, wall_ms)), Some(home), Some(class)) = (signer, self.net.home(), self.class) else {
            return;
        };
        if self.next_publish == 0 || now < self.next_publish {
            return;
        }
        let Some(home_id) = self.relay_cfg(home).map(|c| c.id) else {
            return;
        };
        let mut addrs = [self
            .local
            .iter()
            .flatten()
            .next()
            .copied()
            .unwrap_or(self.me_addr_pub()); MAX_ADDRS];
        let n = self.candidates(&mut addrs);
        let fields = RecordFields {
            home: home_id,
            seq: wall_ms,
            reach: class,
            addrs: addrs.get(..n).unwrap_or_default(),
            hints: &[],
        };
        let mut buf = [0u8; record::MAX_RECORD_LEN];
        let Ok(len) = record::sign(kp, &fields, &mut buf) else {
            return;
        };
        if self.rly.get(home).is_some_and(|r| r.link.is_open()) {
            let frame = Frame::Publish {
                record: buf.get(..len).unwrap_or_default(),
            };
            if self.frame_to(now, home, &frame) {
                self.next_publish = now.saturating_add(rule::RECORD_REPUBLISH_NS);
            }
        }
    }

    pub(super) fn me_addr_pub(&self) -> core::net::SocketAddr {
        core::net::SocketAddr::new(core::net::IpAddr::V4(core::net::Ipv4Addr::UNSPECIFIED), 0)
    }

    /// The node is about to be suspended: tell every relay with an open carrier, twice over UDP, so the carrier close
    /// that follows is not taken as a crash; then the carriers close. `wall_ms` is the node's clock in milliseconds.
    pub fn suspend(&mut self, now: u64, kp: &Keypair, wall_ms: u64) {
        let mut notice = [0u8; sleep::MAX_LEN];
        for i in 0..R {
            let Some(cfg) = self.relay_cfg(i) else { continue };
            if !self.rly.get(i).is_some_and(|r| r.link.is_open()) {
                continue;
            }
            if let (Some(udp), Ok(n)) = (cfg.udp, sleep::sign(kp, &cfg.id, wall_ms, &mut notice)) {
                let d = Datagram::Sleep {
                    notice: notice.get(..n).unwrap_or_default(),
                };
                for _ in 0..2 {
                    self.enqueue_udp_pub(udp, &d);
                }
            }
        }
        self.hold_close = true;
        for i in 0..R {
            if self.rly.get(i).is_some_and(|r| r.link.state() != State::Down) {
                self.close_pub(i);
            }
        }
        let _ = now;
    }

    /// The node resumed. Carriers that the system closed during the suspension are dialed again; open ones are
    /// checked at once.
    pub fn resume(&mut self, now: u64) {
        self.hold_close = false;
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
            match act {
                Some(a) => self.act_pub(now, i, a),
                None => {}
            }
        }
    }

    /// The link of the node changed (an interface came up or changed address): discover the address again and
    /// beacon again.
    pub fn link_changed(&mut self, now: u64) {
        self.net.restart();
        self.next_probe = now;
        self.duty.restart(now);
    }

    /// Whether the node's first dial counts as a late start.
    pub const fn late_start(&self, first_dial: u64) -> bool {
        first_dial.saturating_sub(self.start) > LATE_START
    }
}
