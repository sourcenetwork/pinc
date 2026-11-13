//! Scenario scaffolding for the connectivity tests in the simulator: a world with relays and clients placed behind
//! NATs and middleboxes, and the checks the scenarios share.
#![allow(
    dead_code,
    unreachable_pub,
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::type_complexity
)]

use std::net::{IpAddr, SocketAddr};

use vinc_connect::client::Notice;
use vinc_core::{Event, SessionId};
use vinc_sim::{
    LanConfig, LanId, LinkConfig, MS, NatConfig, NatId, NatKind, NodeId, PortPolicy, SEC, Sim, SimConfig, Time,
};
use vinc_tests::{CNode, ClientSpec, Cmd, Ev, RelaySpec, add_relay, ip4, spec};

pub const OWD: Time = 10 * MS;

/// Run a scenario on a thread with a large stack: the carriers and the layer hold their buffers inline.
pub fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

pub struct World {
    pub sim: Sim<CNode>,
}

pub fn link(delay: Time) -> LinkConfig {
    LinkConfig {
        delay,
        ..LinkConfig::default()
    }
}

impl World {
    pub fn new(seed: u64) -> Self {
        Self {
            sim: Sim::with_config(
                seed,
                SimConfig {
                    default_link: Some(link(OWD / 2)),
                    trace: true,
                    ..SimConfig::default()
                },
            ),
        }
    }

    pub fn relay(&mut self, tag: u8, ip: IpAddr) -> (NodeId, RelaySpec) {
        add_relay(&mut self.sim, tag, ip)
    }

    /// A NAT of `kind` with external address `ext`.
    pub fn nat(&mut self, kind: NatKind, ext: IpAddr, timeout: Time, tcp_timeout: Time) -> NatId {
        self.sim.add_nat(NatConfig {
            kind,
            ext_ip: ext,
            mapping_timeout: timeout,
            tcp_timeout,
            refresh_on_inbound: true,
            port_base: 20_000,
            ports: PortPolicy::Sequential,
            no_punch: false,
        })
    }

    /// A client behind `nat`.
    pub fn client_behind(&mut self, s: &ClientSpec, nat: NatId) -> NodeId {
        let c = vinc_tests::Client::new(s);
        let n = self.sim.add_node(CNode::Client(Box::new(c)));
        self.sim.add_iface_behind(n, s.addr.ip(), nat);
        self.sim.command(s.start, n, Cmd::Tick);
        n
    }

    /// A client with a public address.
    pub fn client_public(&mut self, s: &ClientSpec) -> NodeId {
        let c = vinc_tests::Client::new(s);
        let n = self.sim.add_node_at(CNode::Client(Box::new(c)), s.addr.ip());
        self.sim.command(s.start, n, Cmd::Tick);
        n
    }

    /// A client on a LAN.
    pub fn client_in(&mut self, s: &ClientSpec, lan: LanId) -> NodeId {
        let c = vinc_tests::Client::new(s);
        let n = self.sim.add_node(CNode::Client(Box::new(c)));
        self.sim.add_iface_in(n, s.addr.ip(), lan);
        self.sim.command(s.start, n, Cmd::Tick);
        n
    }

    /// A compact dump of a node's events, for a failing scenario.
    pub fn dump(&self, n: NodeId) -> String {
        use std::fmt::Write as _;
        let mut out = String::new();
        for (t, e) in self.sim.events(n) {
            let _ = writeln!(out, "{:>9.3} ms {e:?}", *t as f64 / 1e6);
        }
        out
    }

    pub fn client(&self, n: NodeId) -> &vinc_tests::Client {
        self.sim.node(n).client()
    }

    pub fn relay_node(&self, n: NodeId) -> &vinc_tests::RelayNode {
        self.sim.node(n).relay()
    }

    pub fn run(&mut self, until: Time) {
        self.sim.run_until(until);
    }

    pub fn dial(&mut self, at: Time, from: NodeId, to: NodeId, hints: Vec<SocketAddr>) {
        let node = self.sim.node(to).client().host.me;
        self.sim.command(
            at,
            from,
            Cmd::Dial {
                node,
                hints,
                role: vinc_core::Role::Other,
            },
        );
    }

    /// The time of the first event of `n` that satisfies `f`.
    pub fn when(&self, n: NodeId, f: impl Fn(&Ev) -> bool) -> Option<Time> {
        self.sim.events(n).iter().find(|(_, e)| f(e)).map(|(t, _)| *t)
    }

    pub fn count(&self, n: NodeId, f: impl Fn(&Ev) -> bool) -> usize {
        self.sim.events(n).iter().filter(|(_, e)| f(e)).count()
    }

    pub fn notices(&self, n: NodeId) -> Vec<(Time, Notice)> {
        self.sim
            .events(n)
            .iter()
            .filter_map(|(t, e)| if let Ev::Notice(x) = e { Some((*t, *x)) } else { None })
            .collect()
    }

    pub fn connected(&self, n: NodeId) -> Option<SessionId> {
        self.sim.events(n).iter().find_map(|(_, e)| match e {
            Ev::Ep(Event::Connected { session, .. }) => Some(*session),
            _ => None,
        })
    }

    pub fn incoming(&self, n: NodeId) -> Option<SessionId> {
        self.sim.events(n).iter().find_map(|(_, e)| match e {
            Ev::Ep(Event::Incoming { session, .. }) => Some(*session),
            _ => None,
        })
    }
}

pub fn priv_addr(n: u8) -> SocketAddr {
    SocketAddr::new(ip4(192, 168, n, 2), 4433)
}

pub fn ext(n: u8) -> IpAddr {
    ip4(198, 51, 100, n)
}

pub fn relay_ip(n: u8) -> IpAddr {
    ip4(203, 0, 113, n)
}

pub fn client_spec(tag: u8, addr: SocketAddr, relays: &[RelaySpec]) -> ClientSpec {
    spec(tag, addr, relays)
}

pub const fn secs(n: u64) -> Time {
    n * SEC
}

pub fn default_lan() -> LanConfig {
    LanConfig::default()
}

/// The two relays ordered by id, lowest first: a node that hears no relay takes the lowest id as its home, so the
/// tests that mean "the first relay is the home" list them this way.
pub fn by_id<N>(a: (N, RelaySpec), b: (N, RelaySpec)) -> ((N, RelaySpec), (N, RelaySpec)) {
    if a.1.id.bytes <= b.1.id.bytes { (a, b) } else { (b, a) }
}
