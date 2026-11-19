//! A NAT: translation of private sources to a public address, with endpoint-independent or endpoint-dependent
//! mapping and three filtering behaviours.
//!
//! Mappings are created by outbound datagrams and segments and expire after their last outbound use (strictly more
//! than `mapping_timeout` idle for datagrams, `tcp_timeout` for stream segments; the two kinds of traffic have
//! separate mappings). A mapping expired or moved by a rebind returns a different external port. A mapping remembers
//! at most 64 contacted remotes (address and port); beyond that new remotes are never admitted back. Hairpinning (a
//! private host addressing the NAT's own public address) is not modelled: such a datagram fails the filter.
//!
//! Port allocation under [`PortPolicy::Randomized`] advances the counter first and returns the new value; a rebind
//! walks the mappings in the order their keys were first created, expired ones included, and gives each a new port.

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
    /// A random start in `[20000, 40000)`; each allocation first advances the counter by 1 to 7 and returns the new
    /// value, wrapping above 65000 to a random port in `[20000, 21000)`. There is no collision check.
    Randomized,
}

/// The settings of a NAT.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NatConfig {
    /// The mapping and filtering behaviour.
    pub kind: NatKind,
    /// The public address.
    pub ext_ip: IpAddr,
    /// Idle time after which a datagram mapping disappears, in nanoseconds (a short value models a firewall's UDP
    /// timeout).
    pub mapping_timeout: Time,
    /// Idle time after which a stream (TCP) mapping disappears, in nanoseconds; the reference uses 7200 s.
    pub tcp_timeout: Time,
    /// Whether inbound datagrams also keep a mapping alive (otherwise only outbound ones do).
    pub refresh_on_inbound: bool,
    /// The first external port handed out under [`PortPolicy::Sequential`].
    pub port_base: u16,
    /// How external ports are chosen.
    pub ports: PortPolicy,
    /// Admit inbound datagrams only from public sources (hosts that are not behind a NAT).
    pub no_punch: bool,
}

/// The kind of traffic a mapping serves; each has its own mappings, ports and timeout.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Proto {
    Udp,
    Tcp,
}

type Key = (Proto, SocketAddr, Option<SocketAddr>);

struct Mapping {
    port: u16,
    last: Time,
    /// When the key was first created; a replaced (expired) mapping keeps its key's place in the rebind order.
    order: u64,
    allowed: BTreeSet<SocketAddr>,
}

/// Contacted remotes remembered per mapping.
const MAX_REMOTES: usize = 64;

pub(crate) struct Nat<R: Random> {
    pub(crate) cfg: NatConfig,
    rng: R,
    by_key: BTreeMap<Key, Mapping>,
    by_port: BTreeMap<(Proto, u16), Key>,
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
    /// address may change too. Mappings are visited in the order their keys were first created.
    pub(crate) fn rebind(&mut self, new_ip: Option<IpAddr>) {
        let mut keys: Vec<(u64, Key)> = self.by_key.iter().map(|(k, m)| (m.order, *k)).collect();
        keys.sort_unstable();
        for (_, k) in keys {
            let Some(old) = self.by_key.get(&k).map(|m| m.port) else {
                continue;
            };
            self.by_port.remove(&(k.0, old));
            let port = self.alloc_port();
            self.by_port.insert((k.0, port), k);
            if let Some(m) = self.by_key.get_mut(&k) {
                m.port = port;
            }
        }
        if let Some(ip) = new_ip {
            self.cfg.ext_ip = ip;
        }
    }

    /// Forgets expired mappings so a long run holds only live ones. The reference keeps them forever, so a rebind
    /// after a sweep skips them (one port draw each fewer); this only matters once a NAT holds over 64 mappings.
    // vertexia: the reference never forgets a mapping; exact rebind order beyond 64 mappings needs an unbounded table.
    fn sweep(&mut self, now: Time) {
        let (udp, tcp) = (self.cfg.mapping_timeout, self.cfg.tcp_timeout);
        let by_port = &mut self.by_port;
        self.by_key.retain(|k, m| {
            let keep = now.saturating_sub(m.last) <= if k.0 == Proto::Udp { udp } else { tcp };
            if !keep {
                by_port.remove(&(k.0, m.port));
            }
            keep
        });
        self.sweep_at = (self.by_key.len() * 2).max(64);
    }

    fn alloc_port(&mut self) -> u16 {
        match self.cfg.ports {
            PortPolicy::Randomized => {
                let next = u32::from(self.next_port) + 1 + self.rng.below(7) as u32;
                self.next_port = if next > 65_000 {
                    20_000 + self.rng.below(1000) as u16
                } else {
                    next as u16
                };
                self.next_port
            }
            PortPolicy::Sequential => {
                let base = self.cfg.port_base.max(1);
                for _ in 0..=u32::from(u16::MAX - base) {
                    let p = self.next_port;
                    self.next_port = if p == u16::MAX { base } else { p + 1 };
                    if !self.by_port.contains_key(&(Proto::Udp, p)) && !self.by_port.contains_key(&(Proto::Tcp, p)) {
                        return p;
                    }
                }
                // Every port is mapped and live: reuse the next one, evicting its owner.
                let p = self.next_port;
                for proto in [Proto::Udp, Proto::Tcp] {
                    if let Some(k) = self.by_port.remove(&(proto, p)) {
                        self.by_key.remove(&k);
                    }
                }
                p
            }
        }
    }

    fn timeout_of(&self, proto: Proto) -> Time {
        match proto {
            Proto::Udp => self.cfg.mapping_timeout,
            Proto::Tcp => self.cfg.tcp_timeout,
        }
    }

    /// Translates a datagram or segment going out; returns the public source address.
    pub(crate) fn outbound(&mut self, now: Time, proto: Proto, src: SocketAddr, dst: SocketAddr) -> SocketAddr {
        let key = (proto, src, self.cfg.kind.dependent().then_some(dst));
        let timeout = self.timeout_of(proto);
        let live = self
            .by_key
            .get(&key)
            .is_some_and(|m| now.saturating_sub(m.last) <= timeout);
        if !live {
            let order = if let Some(old) = self.by_key.remove(&key) {
                self.by_port.remove(&(proto, old.port));
                old.order
            } else {
                self.created += 1;
                self.created
            };
            if self.by_key.len() >= self.sweep_at {
                self.sweep(now);
            }
            let port = self.alloc_port();
            self.by_port.insert((proto, port), key);
            self.by_key.insert(
                key,
                Mapping {
                    port,
                    last: now,
                    order,
                    allowed: BTreeSet::new(),
                },
            );
        }
        let ext = self.cfg.ext_ip;
        let Some(m) = self.by_key.get_mut(&key) else {
            return SocketAddr::new(ext, 0);
        };
        m.last = now;
        if m.allowed.len() < MAX_REMOTES {
            m.allowed.insert(dst);
        }
        SocketAddr::new(ext, m.port)
    }

    /// Translates a datagram or segment coming in to external `port` from `from`; `None` when the NAT drops it.
    /// `public_src` tells whether the sender is a public host (not behind a NAT).
    pub(crate) fn inbound(
        &mut self,
        now: Time,
        proto: Proto,
        port: u16,
        from: SocketAddr,
        public_src: bool,
    ) -> Option<SocketAddr> {
        let key = *self.by_port.get(&(proto, port))?;
        let (refresh, timeout, kind, no_punch) = (
            self.cfg.refresh_on_inbound,
            self.timeout_of(proto),
            self.cfg.kind,
            self.cfg.no_punch,
        );
        let m = self.by_key.get_mut(&key)?;
        if m.port != port || now.saturating_sub(m.last) > timeout || (no_punch && !public_src) {
            return None;
        }
        let pass = match kind {
            NatKind::FullCone | NatKind::DependentOpen => true,
            NatKind::AddressRestricted | NatKind::DependentAddress => m.allowed.iter().any(|r| r.ip() == from.ip()),
            NatKind::PortRestricted | NatKind::Symmetric => m.allowed.contains(&from),
        };
        if pass && refresh {
            m.last = now;
        }
        if pass && !public_src {
            self.punched += 1;
        }
        pass.then_some(key.1)
    }
}
