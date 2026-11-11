//! What the dashboard draws while a run goes: the topology as built (once), and a sample of every node and every
//! shaper twice a second (CPU from the node's cgroup, bytes on its interface, bytes, drops and queue of each shaper).

use std::collections::BTreeMap;
use std::time::Duration;

use serde::{Deserialize, Serialize};
use tokio::sync::broadcast;

use crate::backend::containers::Containers;
use crate::metrics::Reading;
use crate::orchestrate::Event;
use crate::plan::Plan;
use crate::scenario::{Nat, Role, Shape};

/// How often the dashboard is sampled.
pub const EVERY: Duration = Duration::from_millis(500);

/// A site as built.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TSite {
    /// Its name.
    pub name: String,
    /// Its translation.
    pub nat: Nat,
    /// Its LAN.
    pub lan: String,
    /// Where the scenario places it on the diagram.
    pub pos: Option<[f64; 2]>,
}

/// A node as built.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TNode {
    /// Its name.
    pub name: String,
    /// Its site's index.
    pub site: usize,
    /// Its address.
    pub ip: String,
    /// Its CPU set.
    pub cpus: String,
    /// Its memory limit.
    pub memory_mib: u32,
    /// Its role.
    pub role: Role,
    /// Its access link.
    pub link: Shape,
}

/// A link between sites as built.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TLink {
    /// The first site.
    pub a: usize,
    /// The second site.
    pub b: usize,
    /// a to b.
    pub forward: Shape,
    /// b to a.
    pub reverse: Shape,
}

/// What a shaper shapes.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ShaperOf {
    /// The router-to-node direction of a node's access link.
    Down {
        /// The node.
        node: usize,
    },
    /// The node-to-router direction.
    Up {
        /// The node.
        node: usize,
    },
    /// One direction of a link between sites.
    Link {
        /// The link.
        link: usize,
        /// a to b when true.
        forward: bool,
    },
}

/// A shaper: the device in a router that shapes one direction of one link.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TShaper {
    /// The router's site.
    pub site: usize,
    /// The device.
    pub dev: String,
    /// What it shapes.
    pub of: ShaperOf,
}

/// The network of a run, as built.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Topology {
    /// The sites.
    pub sites: Vec<TSite>,
    /// The nodes.
    pub nodes: Vec<TNode>,
    /// The links.
    pub links: Vec<TLink>,
    /// The shapers.
    pub shapers: Vec<TShaper>,
}

impl Topology {
    /// The topology of a plan.
    pub fn of(plan: &Plan, pos: &[Option<[f64; 2]>]) -> Self {
        let mut shapers = Vec::new();
        for (i, n) in plan.nodes.iter().enumerate() {
            shapers.push(TShaper {
                site: n.site,
                dev: n.port.clone(),
                of: ShaperOf::Down { node: i },
            });
            shapers.push(TShaper {
                site: n.site,
                dev: n.ifb.clone(),
                of: ShaperOf::Up { node: i },
            });
        }
        for (k, l) in plan.links.iter().enumerate() {
            shapers.push(TShaper {
                site: l.a,
                dev: l.dev.clone(),
                of: ShaperOf::Link { link: k, forward: true },
            });
            shapers.push(TShaper {
                site: l.b,
                dev: l.dev.clone(),
                of: ShaperOf::Link {
                    link: k,
                    forward: false,
                },
            });
        }
        Self {
            sites: plan
                .sites
                .iter()
                .enumerate()
                .map(|(i, s)| TSite {
                    name: s.name.clone(),
                    nat: s.nat,
                    lan: format!("{}/24", s.lan),
                    pos: pos.get(i).copied().flatten(),
                })
                .collect(),
            nodes: plan
                .nodes
                .iter()
                .map(|n| TNode {
                    name: n.name.clone(),
                    site: n.site,
                    ip: n.ip.to_string(),
                    cpus: n.container.cpus.clone(),
                    memory_mib: n.container.memory_mib,
                    role: n.role,
                    link: n.link,
                })
                .collect(),
            links: plan
                .links
                .iter()
                .map(|l| TLink {
                    a: l.a,
                    b: l.b,
                    forward: l.forward,
                    reverse: l.reverse,
                })
                .collect(),
            shapers,
        }
    }
}

/// One node in a sample.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct NodeSample {
    /// CPU use in percent of one CPU since the last sample.
    pub cpu: Option<f64>,
    /// Bits per second received.
    pub rx_bps: Option<f64>,
    /// Bits per second sent.
    pub tx_bps: Option<f64>,
}

/// One shaper in a sample.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ShaperSample {
    /// Bits per second it let through.
    pub bps: f64,
    /// Packets per second it dropped.
    pub drops_ps: f64,
    /// Bytes waiting in it.
    pub backlog: u64,
}

/// A sample of the whole network.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Sample {
    /// Milliseconds since the network came up.
    pub t_ms: u64,
    /// The nodes, in topology order.
    pub nodes: Vec<NodeSample>,
    /// The shapers, in topology order.
    pub shapers: Vec<ShaperSample>,
}

/// Sample every node and shaper until dropped.
/// The reading before this one: when it was taken, each node's reading and each interface's byte counters.
type Previous = (
    tokio::time::Instant,
    Vec<Reading>,
    BTreeMap<(usize, String), (u64, u64)>,
);

pub(crate) async fn sampler(b: &Containers, topo: &Topology, tx: broadcast::Sender<Event>) {
    let start = tokio::time::Instant::now();
    let mut tick = tokio::time::interval(EVERY);
    tick.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
    let mut last: Option<Previous> = None;
    loop {
        tick.tick().await;
        let now = tokio::time::Instant::now();
        let mut readings = Vec::with_capacity(topo.nodes.len());
        for i in 0..topo.nodes.len() {
            readings.push(b.reading(i).await.unwrap_or_default());
        }
        let mut q: BTreeMap<(usize, String), (u64, u64, u64)> = BTreeMap::new();
        for s in 0..topo.sites.len() {
            for d in b
                .shapers(s)
                .await
                .unwrap_or_default()
                .into_iter()
                .filter(|d| d.kind == "netem")
            {
                q.insert((s, d.dev), (d.bytes, d.drops, d.backlog));
            }
        }
        if let Some((t0, prev, prev_q)) = &last {
            let secs = now.duration_since(*t0).as_secs_f64().max(1e-3);
            // Counter deltas over half a second fit an f64's integer range.
            #[allow(clippy::cast_precision_loss)]
            let rate = |a: u64, b: u64| a.saturating_sub(b) as f64 / secs;
            let nodes = readings
                .iter()
                .zip(prev)
                .map(|(r, p)| NodeSample {
                    cpu: r.cpu_usec.zip(p.cpu_usec).map(|(a, b)| rate(a, b) / 1e4),
                    rx_bps: r.eth0.zip(p.eth0).map(|(a, b)| rate(a.rx_bytes, b.rx_bytes) * 8.0),
                    tx_bps: r.eth0.zip(p.eth0).map(|(a, b)| rate(a.tx_bytes, b.tx_bytes) * 8.0),
                })
                .collect();
            let shapers = topo
                .shapers
                .iter()
                .map(|s| {
                    let key = (s.site, s.dev.clone());
                    match (q.get(&key), prev_q.get(&key)) {
                        (Some(c), Some(p)) => ShaperSample {
                            bps: rate(c.0, p.0) * 8.0,
                            drops_ps: rate(c.1, p.1),
                            backlog: c.2,
                        },
                        _ => ShaperSample::default(),
                    }
                })
                .collect();
            let t_ms = u64::try_from(now.duration_since(start).as_millis()).unwrap_or(u64::MAX);
            let _ = tx.send(Event::Sample(Box::new(Sample { t_ms, nodes, shapers })));
        }
        last = Some((now, readings, q.into_iter().map(|(k, v)| (k, (v.0, v.1))).collect()));
    }
}
