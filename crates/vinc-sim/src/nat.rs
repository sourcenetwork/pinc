//! A NAT: translation of private sources to a public address, with endpoint-independent or endpoint-dependent
//! mapping and three filtering behaviours.
//!
//! Mappings are created by outbound datagrams and expire `mapping_timeout` after their last outbound use (strictly
//! more than the timeout idle). A mapping expired or moved by a rebind returns a different external port. A mapping
//! remembers at most 64 contacted remotes; beyond that new remotes are never admitted back. Hairpinning (a private
//! host addressing the NAT's own public address) is not modelled: such a datagram fails the filter.

use std::collections::{BTreeMap, BTreeSet};
use std::net::{IpAddr, SocketAddr};

use crate::Time;
use crate::rng::Random;

/// How a NAT maps and filters. The first four are the classic kinds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NatKind {
    /// Endpoint-independent mapping; any outside host may send to it.
    FullCone,
    /// Endpoint-independent mapping; only addresses the socket has sent to may reply (any port).
    AddressRestricted,
    /// Endpoint-independent mapping; only address and port pairs the socket has sent to may reply.
    PortRestricted,
    /// Endpoint-dependent mapping (one per destination); only that destination may reply.
    Symmetric,
    /// Endpoint-dependent mapping; any outside host may send to a mapping.
    DependentOpen,
    /// Endpoint-dependent mapping; only contacted addresses (any port) may reply.
    DependentAddress,
}

impl NatKind {
    const fn dependent(self) -> bool {
        matches!(self, Self::Symmetric | Self::DependentOpen | Self::DependentAddress)
    }
}

/// How external ports are chosen.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PortPolicy {
    /// Consecutive ports from `port_base`, skipping ports in use.
    Sequential,
    /// A random start in `[20000, 40000)`, each allocation advancing by 1 to 7, wrapping above 65000 to a random port
    /// in `[20000, 21000)` with no collision check after a wrap.
    Randomized,
}

/// The settings of a NAT.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NatConfig {
    /// The mapping and filtering behaviour.
    pub kind: NatKind,
    /// The public address.
    pub ext_ip: IpAddr,
    /// Idle time after which a mapping disappears, in nanoseconds (a short value models a firewall's UDP timeout).
    pub mapping_timeout: Time,
    /// Whether inbound datagrams also keep a mapping alive (otherwise only outbound ones do).
    pub refresh_on_inbound: bool,
    /// The first external port handed out under [`PortPolicy::Sequential`].
    pub port_base: u16,
    /// How external ports are chosen.
    pub ports: PortPolicy,
    /// Admit inbound datagrams only from public sources (hosts that are not behind a NAT).
    pub no_punch: bool,
}

type Key = (SocketAddr, Option<SocketAddr>);

struct Mapping {
    port: u16,
    last: Time,
    created: u64,
    allowed: BTreeSet<SocketAddr>,
}

/// Contacted remotes remembered per mapping.
const MAX_REMOTES: usize = 64;

pub(crate) struct Nat<R: Random> {
    pub(crate) cfg: NatConfig,
    rng: R,
    by_key: BTreeMap<Key, Mapping>,
    by_port: BTreeMap<u16, Key>,
    next_port: u16,
    created: u64,
    sweep_at: usize,
    /// Inbound datagrams admitted from sources that are behind a NAT themselves.
    pub(crate) punched: u64,
}

impl<R: Random> Nat<R> {
    pub(crate) fn new(cfg: NatConfig, mut rng: R) -> Self {
        let next_port = match cfg.ports {
            PortPolicy::Sequential => cfg.port_base.max(1),
            PortPolicy::Randomized => 20_000 + rng.below(20_000) as u16,
        };
        Self {
            cfg,
            rng,
            by_key: BTreeMap::new(),
            by_port: BTreeMap::new(),
            next_port,
            created: 0,
            sweep_at: 64,
            punched: 0,
        }
    }

    pub(crate) fn mappings(&self) -> usize {
        self.by_key.len()
    }

    /// Moves every mapping to a new external port (old inbound entries vanish), as a NAT reboot does; the public
    /// address may change too.
    pub(crate) fn rebind(&mut self, new_ip: Option<IpAddr>) {
        let mut keys: Vec<(u64, Key)> = self.by_key.iter().map(|(k, m)| (m.created, *k)).collect();
        keys.sort_unstable();
        self.by_port.clear();
        for (_, k) in keys {
            let port = self.alloc_port();
            self.by_port.insert(port, k);
            if let Some(m) = self.by_key.get_mut(&k) {
                m.port = port;
            }
        }
        if let Some(ip) = new_ip {
            self.cfg.ext_ip = ip;
        }
    }

    fn sweep(&mut self, now: Time) {
        let timeout = self.cfg.mapping_timeout;
        let by_port = &mut self.by_port;
        self.by_key.retain(|_, m| {
            let keep = now.saturating_sub(m.last) <= timeout;
            if !keep {
                by_port.remove(&m.port);
            }
            keep
        });
        self.sweep_at = (self.by_key.len() * 2).max(64);
    }

    fn alloc_port(&mut self) -> u16 {
        match self.cfg.ports {
            PortPolicy::Randomized => {
                let p = self.next_port;
                let next = u32::from(p) + 1 + self.rng.below(7) as u32;
                self.next_port = if next > 65_000 {
                    20_000 + self.rng.below(1000) as u16
                } else {
                    next as u16
                };
                p
            }
            PortPolicy::Sequential => {
                let base = self.cfg.port_base.max(1);
                for _ in 0..=u32::from(u16::MAX - base) {
                    let p = self.next_port;
                    self.next_port = if p == u16::MAX { base } else { p + 1 };
                    if !self.by_port.contains_key(&p) {
                        return p;
                    }
                }
                // Every port is mapped and live: reuse the next one, evicting its owner.
                let p = self.next_port;
                if let Some(k) = self.by_port.remove(&p) {
                    self.by_key.remove(&k);
                }
                p
            }
        }
    }

    /// Translates a datagram going out; returns the public source address.
    pub(crate) fn outbound(&mut self, now: Time, src: SocketAddr, dst: SocketAddr) -> SocketAddr {
        let key = (src, self.cfg.kind.dependent().then_some(dst));
        let peer = match self.cfg.kind {
            NatKind::AddressRestricted | NatKind::DependentAddress => SocketAddr::new(dst.ip(), 0),
            _ => dst,
        };
        let timeout = self.cfg.mapping_timeout;
        let live = self
            .by_key
            .get(&key)
            .is_some_and(|m| now.saturating_sub(m.last) <= timeout);
        if !live {
            if let Some(old) = self.by_key.remove(&key)
                && self.by_port.get(&old.port) == Some(&key)
            {
                self.by_port.remove(&old.port);
            }
            if self.by_key.len() >= self.sweep_at {
                self.sweep(now);
            }
            let port = self.alloc_port();
            self.by_port.insert(port, key);
            self.created += 1;
            self.by_key.insert(
                key,
                Mapping {
                    port,
                    last: now,
                    created: self.created,
                    allowed: BTreeSet::new(),
                },
            );
        }
        let ext = self.cfg.ext_ip;
        let Some(m) = self.by_key.get_mut(&key) else {
            return SocketAddr::new(ext, 0);
        };
        m.last = now;
        if m.allowed.len() < MAX_REMOTES || m.allowed.contains(&peer) {
            m.allowed.insert(peer);
        }
        SocketAddr::new(ext, m.port)
    }

    /// Translates a datagram coming in to external `port` from `from`; `None` when the NAT drops it.
    /// `public_src` tells whether the sender is a public host (not behind a NAT).
    pub(crate) fn inbound(&mut self, now: Time, port: u16, from: SocketAddr, public_src: bool) -> Option<SocketAddr> {
        let key = *self.by_port.get(&port)?;
        let (refresh, timeout, kind, no_punch) = (
            self.cfg.refresh_on_inbound,
            self.cfg.mapping_timeout,
            self.cfg.kind,
            self.cfg.no_punch,
        );
        let m = self.by_key.get_mut(&key)?;
        if m.port != port || now.saturating_sub(m.last) > timeout || (no_punch && !public_src) {
            return None;
        }
        let pass = match kind {
            NatKind::FullCone | NatKind::DependentOpen => true,
            NatKind::AddressRestricted | NatKind::DependentAddress => {
                m.allowed.contains(&SocketAddr::new(from.ip(), 0))
            }
            NatKind::PortRestricted | NatKind::Symmetric => m.allowed.contains(&from),
        };
        if pass && refresh {
            m.last = now;
        }
        if pass && !public_src {
            self.punched += 1;
        }
        pass.then_some(key.0)
    }
}
