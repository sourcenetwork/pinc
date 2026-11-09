//! The network of a world: sites as LANs, NATs, nodes with their interfaces, clocks, CPUs, partitions and the
//! adversary, built in the reference harness's order so that every random stream lands on the index the reference
//! seeds it with.
//!
//! Streams are seeded by index: a LAN by its site number, a NAT by its number from 1. NAT number 0 does not exist in
//! a world, so a NAT nobody uses takes index 0 and every real NAT keeps its own number as its index.
//!
//! Invariants: nodes are added in world order, so a node's simulator id equals its world index; a node that can change
//! site gets one interface per family and site, all but the current ones down; addresses are those of
//! [`iface_ip`] and of the reference's after-handover formulas.

use std::rc::Rc;

use crate::reference::RefRng;
use crate::suite::node::{Shared, SuiteCost, SuiteNode, iface_ip};
use crate::suite::proto::Stack;
use crate::suite::world::model::{Addr, EnvArg, EnvKind, IfaceSpec, NatSpec, NodeSpec, World};
use crate::{
    Clock, IfaceId, LanConfig, LanId, LinkConfig, NatConfig, NatId, NatKind, NodeId, PortPolicy, Sim, SimConfig,
    StreamPolicy, TapSpec,
};

use super::RunError;

/// The simulator type of a suite run.
pub type SuiteSim = Sim<SuiteNode<Stack>, RefRng, SuiteCost>;

/// The interfaces of one node at one site.
#[derive(Clone, Debug)]
pub struct SiteIfaces {
    /// The site.
    pub site: usize,
    /// `(interface, is IPv6)` for each UDP interface of the node at this site.
    pub ifaces: Vec<(IfaceId, bool)>,
}

/// The network of a run.
pub struct Net {
    /// The simulator.
    pub sim: SuiteSim,
    /// The node ids, by world index.
    pub ids: Vec<NodeId>,
    /// The LANs, by site number.
    pub lans: Vec<LanId>,
    /// The NATs, by NAT number (index 0 is unused).
    pub nats: Vec<NatId>,
    /// Per node, the interface sets of the sites it can be at.
    pub at_site: Vec<Vec<SiteIfaces>>,
}

fn nat_kind(n: &NatSpec) -> Result<NatKind, RunError> {
    Ok(match (n.mapping.as_str(), n.filtering.as_str()) {
        ("eim", "eif") => NatKind::FullCone,
        ("eim", "adf") => NatKind::AddressRestricted,
        ("eim", "apdf") => NatKind::PortRestricted,
        ("edm", "apdf") => NatKind::Symmetric,
        ("edm", "eif") => NatKind::DependentOpen,
        ("edm", "adf") => NatKind::DependentAddress,
        _ => return Err(RunError::Unsupported(format!("NAT {}/{}", n.mapping, n.filtering))),
    })
}

/// The address a private interface of node `idx` has at `site` after a handover at time `t_ns`.
pub fn moved_addr(f: &IfaceSpec, idx: usize, site: usize, t_ns: u64) -> Addr {
    let host = match f.kind.as_str() {
        "udp6" => 6_000_000 + idx as u64 * 1000 + (t_ns / 1_000_000_000) % 1000,
        _ => 3_000_000 + site as u64 * 256 + idx as u64 % 250,
    };
    Addr {
        kind: f.addr.kind.clone(),
        host,
        port: f.addr.port,
    }
}

fn clock_of(n: &NodeSpec) -> Option<Clock> {
    n.clock.as_ref().map(|c| Clock {
        offset: c.offset_ns,
        drift_ppm: c.drift_ppm,
        jumps: c.jumps.iter().map(|&(t, d)| (t, d.cast_signed())).collect(),
    })
}

/// Builds the network of `world`; `make` makes the layers of a node.
pub fn build(
    world: &World,
    shared: &Rc<Shared>,
    cfg: SimConfig,
    mut make: impl FnMut(usize) -> Stack,
) -> Result<Net, RunError> {
    let mut sim = SuiteSim::with_parts(world.seed, cfg, SuiteCost);
    let v6_public_site: Vec<bool> = (0..world.sites.len())
        .map(|s| {
            world
                .nodes
                .iter()
                .any(|n| n.site == s && n.ifaces.iter().any(|f| f.kind == "udp6" && f.public))
        })
        .collect();
    let mut lans = Vec::with_capacity(world.sites.len());
    for (sid, s) in world.sites.iter().enumerate() {
        let queue = usize::try_from(s.queue_bytes).unwrap_or(usize::MAX);
        let mb = s.middlebox.as_ref();
        lans.push(sim.add_lan(LanConfig {
            up: LinkConfig::reference(s.up_bps, s.up_delay_ns, queue, s.loss, s.burst_ns),
            down: LinkConfig::reference(s.down_bps, s.down_delay_ns, queue, s.loss, s.burst_ns),
            region: u32::try_from(s.region).map_err(|_| RunError::Unsupported("a region number".to_owned()))?,
            mtu: s.mtu as usize,
            udp_block: mb.is_some_and(|m| m.udp_block),
            stream: mb.map(|m| StreamPolicy {
                ports: Some(m.tcp_ports.clone()),
                tls_only: m.tls_only,
                reject: m.fw_reject,
            }),
            v6_firewall: !s.v6_open && !v6_public_site.get(sid).copied().unwrap_or(false),
        }));
    }
    for (a, row) in world.region_delay_ns.iter().enumerate() {
        for (b, &d) in row.iter().enumerate() {
            sim.set_region_delay(a as u32, b as u32, d);
        }
    }
    // NAT 0 is never used; see the module docs.
    let unused = iface_ip(&Addr {
        kind: "udp4".to_owned(),
        host: 0xFF_FFFF,
        port: 0,
    })
    .ok_or_else(|| RunError::Unsupported("an address".to_owned()))?;
    let mut nats = vec![sim.add_nat(NatConfig {
        kind: NatKind::FullCone,
        ext_ip: unused,
        mapping_timeout: 0,
        tcp_timeout: 0,
        refresh_on_inbound: false,
        port_base: 1,
        ports: PortPolicy::Sequential,
        no_punch: false,
    })];
    let mut nat_of_site: Vec<Option<NatId>> = vec![None; world.sites.len()];
    for (sid, s) in world.sites.iter().enumerate() {
        if s.nats.len() > 1 {
            return Err(RunError::Unsupported("a site with more than one NAT".to_owned()));
        }
        for n in &s.nats {
            if n.nid != nats.len() {
                return Err(RunError::Unsupported(
                    "NAT numbers that are not consecutive from 1".to_owned(),
                ));
            }
            let ext_ip = iface_ip(&Addr {
                kind: "udp4".to_owned(),
                host: n.ext_ip,
                port: 0,
            })
            .ok_or_else(|| RunError::Unsupported("a NAT address".to_owned()))?;
            let id = sim.add_nat_in(
                NatConfig {
                    kind: nat_kind(n)?,
                    ext_ip,
                    mapping_timeout: n.timeout_ns,
                    tcp_timeout: n.tcp_timeout_ns.unwrap_or(7_200_000_000_000),
                    refresh_on_inbound: false,
                    port_base: 20_000,
                    ports: PortPolicy::Randomized,
                    no_punch: n.no_punch,
                },
                lans[sid],
            );
            nats.push(id);
            nat_of_site[sid] = Some(id);
        }
    }
    let mut ids = Vec::with_capacity(world.nodes.len());
    let mut at_site = Vec::with_capacity(world.nodes.len());
    for (i, spec) in world.nodes.iter().enumerate() {
        let node = SuiteNode::new(Rc::clone(shared), i, make(i))?;
        let id = sim.add_node(node);
        let mut sites = vec![spec.site];
        for e in world.env.iter().filter(|e| e.kind == EnvKind::Handover && e.node == i) {
            if let EnvArg::SiteGap(s, _) = e.arg
                && !sites.contains(&s)
            {
                sites.push(s);
            }
        }
        let mut per_site = Vec::new();
        for (k, &site) in sites.iter().enumerate() {
            let mut ifaces = Vec::new();
            for f in spec.ifaces.iter().filter(|f| f.kind.starts_with("udp")) {
                let v6 = f.kind == "udp6";
                let addr = if k == 0 {
                    f.addr.clone()
                } else if v6 {
                    // Replaced by the handover's own address before the interface is first used.
                    Addr {
                        host: 6_900_000 + i as u64 * 4 + k as u64,
                        ..f.addr.clone()
                    }
                } else {
                    moved_addr(f, i, site, 0)
                };
                let ip = iface_ip(&addr).ok_or_else(|| RunError::Unsupported("an interface address".to_owned()))?;
                let lan = lans
                    .get(site)
                    .copied()
                    .ok_or_else(|| RunError::Unsupported("a site number".to_owned()))?;
                let iface = match (f.public || v6, nat_of_site.get(site).copied().flatten()) {
                    (false, Some(nat)) => sim.add_iface_behind(id, ip, nat),
                    _ => sim.add_iface_in(id, ip, lan),
                };
                sim.set_iface_mtu(iface, f.mtu as usize);
                if k != 0 {
                    let idx = iface.idx;
                    sim.set_iface_up(0, id, idx, false);
                }
                ifaces.push((iface, v6));
            }
            per_site.push(SiteIfaces { site, ifaces });
        }
        sim.set_cpu(
            id,
            SuiteCost::cpu(spec.cpu_factor.map_or(1000, |f| f.saturating_mul(1000))),
        );
        if let Some(c) = clock_of(spec) {
            sim.set_clock(id, c);
        }
        if let Some(p) = world
            .sites
            .get(spec.site)
            .and_then(|s| s.middlebox.as_ref())
            .and_then(|m| m.portal_ns)
        {
            sim.set_portal(id, p);
        }
        ids.push(id);
        at_site.push(per_site);
    }
    for c in &world.partitions {
        let pick = |v: &[usize]| v.iter().filter_map(|&s| lans.get(s).copied()).collect::<Vec<_>>();
        sim.partition_lans(c.from, c.to, &pick(&c.x), &pick(&c.y), c.both);
    }
    if let Some(a) = &world.adversary {
        sim.tap_inbound(TapSpec {
            victims: a.victims.iter().filter_map(|&v| ids.get(v).copied()).collect(),
            replay: a.replay,
            modify: a.modify,
            capture_min: 1000,
            capture_prob: 0.2,
            capture_max: 64,
            first_flights_only: true,
        });
    }
    Ok(Net {
        sim,
        ids,
        lans,
        nats,
        at_site,
    })
}
