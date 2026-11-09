//! Scenario scaffolding for the node tests: hubs and members as real `vinc_node::Node`s in the simulator.
#![allow(
    dead_code,
    unreachable_pub,
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::type_complexity
)]

use std::collections::BTreeSet;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use vinc_broadcast::Limits;
use vinc_membership::Event as MEvent;
use vinc_node::NodeEvent;
use vinc_sim::{LinkConfig, MS, NodeId as SimId, SEC, Sim, SimConfig, StreamKind, Time};
use vinc_tests::{HubAddr, NCmd, NEv, NodeSpec, SimNode, hub_addr, id_of};

pub const OWD: Time = 10 * MS;

/// Run a scenario on a thread with a large stack: the nodes hold their buffers inline.
pub fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

pub fn ip(a: u8, b: u8, c: u8, d: u8) -> IpAddr {
    IpAddr::V4(Ipv4Addr::new(a, b, c, d))
}

pub struct World {
    pub sim: Sim<SimNode>,
    pub hubs: Vec<(SimId, HubAddr)>,
    pub members: Vec<SimId>,
    pub persist: bool,
    pub limits: Limits,
    pub trace: bool,
}

impl World {
    pub fn new(seed: u64) -> Self {
        Self {
            sim: Sim::with_config(
                seed,
                SimConfig {
                    default_link: Some(LinkConfig {
                        delay: OWD / 2,
                        ..LinkConfig::default()
                    }),
                    ..SimConfig::default()
                },
            ),
            hubs: Vec::new(),
            members: Vec::new(),
            persist: false,
            limits: Limits::default(),
            trace: false,
        }
    }

    /// `h` hubs and `m` members, all started at time 0 with the members listing every hub.
    pub fn build(seed: u64, h: usize, m: usize) -> Self {
        Self::build_with(seed, h, m, |_| {})
    }

    pub fn build_with(seed: u64, h: usize, m: usize, tweak: impl Fn(&mut World)) -> Self {
        let mut w = Self::new(seed);
        tweak(&mut w);
        let addrs: Vec<HubAddr> = (0..h).map(|i| hub_addr(0x10 + i as u8, ip(203, 0, 113, 10 + i as u8))).collect();
        for (i, a) in addrs.iter().enumerate() {
            let spec = NodeSpec {
                tag: 0x10 + i as u8,
                addr: a.udp,
                hubs: addrs.clone(),
                is_hub: true,
                persist: w.persist,
                limits: w.limits,
                trace: w.trace,
                start: 0,
            };
            let n = w.sim.add_node_at(SimNode::new(&spec), a.udp.ip());
            w.sim.listen(n, a.tcp, StreamKind::Tcp);
            w.sim.listen(n, a.ws, StreamKind::Ws);
            w.sim.command(0, n, NCmd::Tick);
            w.hubs.push((n, *a));
        }
        for j in 0..m {
            w.add_member(0x40 + j as u8, &addrs, 0);
        }
        w
    }

    pub fn add_member(&mut self, tag: u8, hubs: &[HubAddr], start: Time) -> SimId {
        let addr = SocketAddr::new(ip(198, 51, 100, tag), 4433);
        let spec = NodeSpec {
            tag,
            addr,
            hubs: hubs.to_vec(),
            is_hub: false,
            persist: self.persist,
            limits: self.limits,
            trace: self.trace,
            start,
        };
        let n = self.sim.add_node_at(SimNode::new(&spec), addr.ip());
        self.sim.command(start, n, NCmd::Tick);
        self.members.push(n);
        n
    }

    pub fn id(&self, n: SimId) -> [u8; 32] {
        self.sim.node(n).me.bytes
    }

    pub fn hub_addrs(&self) -> Vec<HubAddr> {
        self.hubs.iter().map(|(_, a)| *a).collect()
    }

    pub fn run(&mut self, until: Time) {
        self.sim.run_until(until);
    }

    pub fn view(&self, n: SimId) -> BTreeSet<[u8; 32]> {
        self.sim.node(n).node.membership().members().map(|(m, _)| *m).collect()
    }

    /// The members of the view of `n` plus `n` itself.
    pub fn everyone(&self) -> BTreeSet<[u8; 32]> {
        self.hubs.iter().map(|(n, _)| *n).chain(self.members.iter().copied()).map(|n| self.id(n)).collect()
    }

    pub fn member_events(&self, n: SimId) -> Vec<(Time, MEvent)> {
        self.sim
            .events(n)
            .iter()
            .filter_map(|(t, e)| match e {
                NEv::Node(NodeEvent::Member(m)) => Some((*t, *m)),
                _ => None,
            })
            .collect()
    }

    /// How many times `n` confirmed `target` down.
    pub fn confirmed_down(&self, n: SimId, target: &[u8; 32]) -> Vec<Time> {
        self.member_events(n)
            .into_iter()
            .filter_map(|(t, e)| matches!(e, MEvent::MemberConfirmedDown { member } if member == *target).then_some(t))
            .collect()
    }

    pub fn left(&self, n: SimId, target: &[u8; 32]) -> Vec<Time> {
        self.member_events(n)
            .into_iter()
            .filter_map(|(t, e)| matches!(e, MEvent::MemberLeft { member } if member == *target).then_some(t))
            .collect()
    }

    pub fn messages(&self, n: SimId) -> Vec<(Time, Vec<u8>, [u8; 32], Vec<u8>)> {
        self.sim
            .events(n)
            .iter()
            .filter_map(|(t, e)| match e {
                NEv::Node(NodeEvent::Message { topic, origin, body, .. }) => {
                    Some((*t, topic.clone(), *origin, body.clone()))
                }
                _ => None,
            })
            .collect()
    }

    /// The node ids of every node but `n`.
    pub fn others(&self, n: SimId) -> BTreeSet<[u8; 32]> {
        let mut e = self.everyone();
        e.remove(&self.id(n));
        e
    }
}

pub fn secs(n: u64) -> Time {
    n * SEC
}

pub fn tag_id(tag: u8) -> [u8; 32] {
    id_of(tag).bytes
}
