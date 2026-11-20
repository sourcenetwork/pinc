//! Scaffolding for the layer tests: hubs and members as real `pinc_node::Node`s with values, reconcile and
//! delay-tolerant delivery enabled on the members.
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

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use pinc_broadcast::Limits;
use pinc_node::{Enabled, NodeEvent};
use pinc_sim::{LinkConfig, Loss, MS, NodeId as SimId, SEC, Sim, SimConfig, StreamKind, Time};
use pinc_tests::{HubAddr, LayerApps, NCmd, NEv, NodeSpec, SimNode, hub_addr, id_of};

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

pub fn secs(n: u64) -> Time {
    n * SEC
}

fn ip(a: u8, b: u8, c: u8, d: u8) -> IpAddr {
    IpAddr::V4(Ipv4Addr::new(a, b, c, d))
}

pub struct LWorld {
    pub sim: Sim<SimNode<LayerApps>>,
    pub hubs: Vec<(SimId, HubAddr)>,
    pub members: Vec<SimId>,
    pub tags: Vec<u8>,
}

impl LWorld {
    /// `h` hubs and `m` members; `mk` gives the stores of a member from its tag.
    pub fn build(seed: u64, h: usize, m: usize, mk: impl Fn(u8) -> LayerApps) -> Self {
        Self::build_with(seed, h, m, 0, false, mk)
    }

    /// As [`LWorld::build`] with a line rate in bits per second (0 for none) and optional node traces.
    pub fn build_with(seed: u64, h: usize, m: usize, bps: u64, trace: bool, mk: impl Fn(u8) -> LayerApps) -> Self {
        Self::build_lossy(seed, h, m, bps, trace, Loss::None, mk)
    }

    /// As [`LWorld::build_with`] with a loss model on every link.
    pub fn build_lossy(
        seed: u64,
        h: usize,
        m: usize,
        bps: u64,
        trace: bool,
        loss: Loss,
        mk: impl Fn(u8) -> LayerApps,
    ) -> Self {
        let mut sim = Sim::with_config(
            seed,
            SimConfig {
                default_link: Some(LinkConfig {
                    delay: OWD / 2,
                    bandwidth_bps: bps,
                    queue_bytes: 4 << 20,
                    loss,
                    ..LinkConfig::default()
                }),
                ..SimConfig::default()
            },
        );
        let addrs: Vec<HubAddr> = (0..h)
            .map(|i| hub_addr(0x10 + i as u8, ip(203, 0, 113, 10 + i as u8)))
            .collect();
        let mut hubs = Vec::new();
        for (i, a) in addrs.iter().enumerate() {
            let spec = NodeSpec {
                tag: 0x10 + i as u8,
                addr: a.udp,
                hubs: addrs.clone(),
                is_hub: true,
                persist: false,
                limits: Limits::default(),
                trace,
                start: 0,
            };
            let apps = LayerApps::new(spec.tag, Enabled::NONE);
            let n = sim.add_node_at(SimNode::with_apps(&spec, apps), a.udp.ip());
            sim.listen(n, a.tcp, StreamKind::Tcp);
            sim.listen(n, a.ws, StreamKind::Ws);
            sim.command(0, n, NCmd::Tick);
            hubs.push((n, *a));
        }
        let mut members = Vec::new();
        let mut tags = Vec::new();
        for j in 0..m {
            let tag = 0x40 + j as u8;
            let addr = SocketAddr::new(ip(198, 51, 100, tag), 4433);
            let spec = NodeSpec {
                tag,
                addr,
                hubs: addrs.clone(),
                is_hub: false,
                persist: false,
                limits: Limits::default(),
                trace,
                start: 0,
            };
            let n = sim.add_node_at(SimNode::with_apps(&spec, mk(tag)), addr.ip());
            sim.command(0, n, NCmd::Tick);
            members.push(n);
            tags.push(tag);
        }
        Self {
            sim,
            hubs,
            members,
            tags,
        }
    }

    pub fn id(&self, n: SimId) -> [u8; 32] {
        self.sim.node(n).me.bytes
    }

    pub fn run(&mut self, until: Time) {
        self.sim.run_until(until);
    }

    /// Put `value` in the store of `n` and register its root for serving; returns the root.
    pub fn provide(&mut self, n: SimId, value: Vec<u8>) -> [u8; 32] {
        let root = self.apps(n).values.provide(value);
        assert!(self.sim.node_mut(n).node.values_provide(&root));
        root
    }

    pub fn apps(&mut self, n: SimId) -> &mut LayerApps {
        self.sim.node_mut(n).node.apps_mut()
    }

    pub fn node_events(&self, n: SimId) -> Vec<(Time, NodeEvent)> {
        self.sim
            .events(n)
            .iter()
            .filter_map(|(t, e)| match e {
                NEv::Node(e) => Some((*t, e.clone())),
                _ => None,
            })
            .collect()
    }
}

pub fn tag_id(tag: u8) -> [u8; 32] {
    id_of(tag).bytes
}

use std::collections::BTreeSet;

use pinc_tests::{Lie, SplitMix64};

/// A world where every layer has worked and is idle: a value fetched, a set reconciled, a bundle held with no
/// contact to carry it. Returns the world after `until`.
pub fn all_layers(seed: u64, until: Time) -> LWorld {
    let mut w = LWorld::build(seed, 2, 4, |tag| {
        let mut apps = LayerApps::new(tag, Enabled::ALL);
        apps.dtn.windows = Some(vec![]);
        apps
    });
    let m = w.members.clone();
    let mut value = vec![0u8; 200 << 10];
    SplitMix64::new(seed).fill(&mut value);
    let mut root = [0; 32];
    for p in &m[1..3] {
        root = w.provide(*p, value.clone());
    }
    w.apps(m[2]).values.lie(Some(Lie::EveryRead));
    let providers = vec![w.id(m[1]), w.id(m[2])];
    w.sim.command(
        secs(30),
        m[0],
        NCmd::ValuesFetch {
            root,
            length: value.len() as u64,
            ranges: vec![],
            providers,
            deadline: None,
        },
    );
    let mut rng = SplitMix64::new(seed ^ 0xabc);
    let mut base: BTreeSet<Vec<u8>> = BTreeSet::new();
    while base.len() < 300 {
        let mut v = vec![0; 24];
        rng.fill(&mut v);
        base.insert(v);
    }
    let mine: Vec<Vec<u8>> = base.iter().cloned().collect();
    let mut theirs = mine.clone();
    theirs.truncate(290);
    theirs.push(vec![7; 24]);
    w.apps(m[0]).sets.insert(b"s", &mine);
    w.apps(m[3]).sets.insert(b"s", &theirs);
    let peer = w.id(m[3]);
    w.sim.command(
        secs(35),
        m[0],
        NCmd::SetsStart {
            peer,
            set_ref: b"s".to_vec(),
        },
    );
    let keys = w.apps(m[1]).dtn.keys();
    w.sim.command(
        secs(40),
        m[0],
        NCmd::DtnSend {
            to: Box::new(keys),
            payload: vec![5; 2000],
            plan: pinc_node::DtnPlan {
                lifetime_ms: 3_600_000,
                copies: 4,
                k: 2,
                m: 1,
                slice_log: 2,
            },
        },
    );
    w.run(until);
    w
}

/// A member with the values layer enabled and nothing else.
pub fn values_on(tag: u8) -> LayerApps {
    LayerApps::new(
        tag,
        Enabled {
            values: true,
            ..Enabled::NONE
        },
    )
}

/// `len` bytes drawn from `seed`.
pub fn data(seed: u64, len: usize) -> Vec<u8> {
    let mut v = vec![0; len];
    SplitMix64::new(seed).fill(&mut v);
    v
}

/// The node ids of `nodes`.
pub fn ids(w: &LWorld, nodes: &[SimId]) -> Vec<[u8; 32]> {
    nodes.iter().map(|n| w.id(*n)).collect()
}

/// How many fetches completed on node `n`.
pub fn completes(w: &LWorld, n: SimId) -> usize {
    w.node_events(n)
        .iter()
        .filter(|(_, e)| matches!(e, NodeEvent::ValueComplete { .. }))
        .count()
}
