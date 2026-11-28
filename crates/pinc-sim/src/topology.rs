//! Building the topology: LANs, nodes, interfaces, NATs, hosts, links and observers.
//!
//! Invariants: ids are indexes in creation order; a site is created once per interface, NAT, host or LAN downlink; no
//! call here schedules an event.

use std::collections::BTreeMap;
use std::net::IpAddr;

use crate::Time;
use crate::adversary::Observer;
use crate::clock::Clock;
use crate::config::{CostModel, Cpu, LanConfig, LanDir, NodeState};
use crate::ids::{HostId, IfaceId, LanId, NatId, NodeId, ObsId, SiteId};
use crate::link::{Link, LinkConfig};
use crate::metrics::NodeMetrics;
use crate::nat::{Nat, NatConfig};
use crate::node::Node;
use crate::rng::{Random, Stream};
use crate::sim::{HostSlot, Iface, Lan, NatSlot, Sim, SiteKind, SiteRef, Slot};

impl<N: Node, R: Random, C: CostModel> Sim<N, R, C> {
    fn add_site(&mut self, kind: SiteKind) -> u32 {
        self.sites.push(kind);
        (self.sites.len() - 1) as u32
    }

    /// Adds a LAN (a site with its own uplink and downlink). Interfaces and NATs join it with
    /// [`Sim::add_iface_in`] and [`Sim::add_nat_in`].
    pub fn add_lan(&mut self, cfg: LanConfig) -> LanId {
        let id = self.lans.len() as u32;
        let down_site = self.add_site(SiteKind::LanDown(id));
        let up = Link::new(cfg.up.clone(), R::derive(self.seed, Stream::LanUp(id)));
        let down = Link::new(cfg.down.clone(), R::derive(self.seed, Stream::LanDown(id)));
        self.lans.push(Lan {
            cfg,
            up,
            down,
            down_site,
            fw: BTreeMap::new(),
        });
        LanId(id)
    }

    /// Sets the one-way delay from datagrams leaving a LAN of region `from` to reaching a LAN of region `to`.
    pub fn set_region_delay(&mut self, from: u32, to: u32, delay: Time) {
        self.region_delay.insert((from, to), delay);
    }

    /// Adds a node with no interface yet; give it one with [`Sim::add_iface`] or [`Sim::add_iface_behind`].
    pub fn add_node(&mut self, node: N) -> NodeId {
        let id = self.nodes.len() as u32;
        self.nodes.push(Slot {
            node,
            state: NodeState::Up,
            ifaces: Vec::new(),
            persisted: Vec::new(),
            log: Vec::new(),
            timer_gen: 0,
            timer_at: None,
            timer_last: None,
            timer_left: false,
            busy_until: 0,
            cpu: None,
            clock: Clock::default(),
            group: 0,
            portal_ns: 0,
            portal_until: 0,
            incarnation: 0,
            streams: BTreeMap::new(),
            next_stream: 1,
            slept_streams: Vec::new(),
        });
        self.metrics.nodes.push(NodeMetrics::default());
        NodeId(id)
    }

    /// Adds a node with one publicly addressed interface.
    pub fn add_node_at(&mut self, node: N, ip: IpAddr) -> NodeId {
        let id = self.add_node(node);
        self.add_iface(id, ip);
        id
    }

    /// Gives `node` an interface with a public address.
    pub fn add_iface(&mut self, node: NodeId, ip: IpAddr) -> IfaceId {
        self.new_iface(node, ip, None, None)
    }

    /// Gives `node` an interface with a public address on a LAN.
    pub fn add_iface_in(&mut self, node: NodeId, ip: IpAddr, lan: LanId) -> IfaceId {
        self.new_iface(node, ip, None, Some(lan.0))
    }

    /// Gives `node` an interface with a private address behind `nat`.
    pub fn add_iface_behind(&mut self, node: NodeId, ip: IpAddr, nat: NatId) -> IfaceId {
        self.new_iface(node, ip, Some(nat.0), None)
    }

    fn new_iface(&mut self, node: NodeId, ip: IpAddr, via: Option<u32>, lan: Option<u32>) -> IfaceId {
        let idx = self.nodes[node.index()].ifaces.len() as u32;
        let site = self.add_site(SiteKind::Iface { node: node.0, idx });
        self.nodes[node.index()].ifaces.push(Iface {
            site,
            addr: ip,
            via,
            lan,
            up: true,
            mtu: usize::MAX,
        });
        match via {
            Some(n) => {
                self.nats[n as usize].lan_map.insert(ip, site);
            }
            None => {
                self.addr_map.insert(ip, site);
            }
        }
        IfaceId { node, idx }
    }

    /// Limits the datagram size of an interface (its own MTU, on top of the LAN's).
    pub fn set_iface_mtu(&mut self, id: IfaceId, mtu: usize) {
        self.nodes[id.node.index()].ifaces[id.idx as usize].mtu = mtu;
    }

    /// Adds a NAT with a public address, connected to nothing but pair links.
    pub fn add_nat(&mut self, cfg: NatConfig) -> NatId {
        self.new_nat(cfg, None)
    }

    /// Adds a NAT whose public side is on a LAN.
    pub fn add_nat_in(&mut self, cfg: NatConfig, lan: LanId) -> NatId {
        self.new_nat(cfg, Some(lan.0))
    }

    fn new_nat(&mut self, cfg: NatConfig, lan: Option<u32>) -> NatId {
        let id = self.nats.len() as u32;
        let site = self.add_site(SiteKind::Nat(id));
        self.addr_map.insert(cfg.ext_ip, site);
        let nat = Nat::new(cfg, R::derive(self.seed, Stream::Nat(id)));
        self.nats.push(NatSlot {
            site,
            nat,
            lan_map: BTreeMap::new(),
            lan,
        });
        NatId(id)
    }

    /// Adds an adversary host with a public address; it can inject and receive datagrams.
    pub fn add_host(&mut self, ip: IpAddr) -> HostId {
        let id = self.hosts.len() as u32;
        let site = self.add_site(SiteKind::Host(id));
        self.addr_map.insert(ip, site);
        self.hosts.push(HostSlot { site, received: 0 });
        HostId(id)
    }

    /// The site of an interface, a NAT or a host.
    pub fn site(&self, of: impl Into<SiteRef>) -> SiteId {
        SiteId(match of.into() {
            SiteRef::Iface(i) => self.nodes[i.node.index()].ifaces[i.idx as usize].site,
            SiteRef::Nat(n) => self.nats[n.index()].site,
            SiteRef::Host(h) => self.hosts[h.index()].site,
            SiteRef::Site(s) => s.0,
        })
    }

    /// Sets the configuration of the link carrying datagrams from `from` to `to` (one direction).
    pub fn set_link(&mut self, from: impl Into<SiteRef>, to: impl Into<SiteRef>, cfg: LinkConfig) {
        let key = (self.site(from).0, self.site(to).0);
        if let Some(l) = self.links.get_mut(&key) {
            l.cfg = cfg;
        } else {
            let rng = R::derive(self.seed, Stream::Link { from: key.0, to: key.1 });
            self.links.insert(key, Link::new(cfg, rng));
        }
    }

    /// Sets both directions of a path; `ab` carries `a` to `b`, `ba` carries `b` to `a`.
    pub fn set_link_pair(
        &mut self,
        a: impl Into<SiteRef> + Copy,
        b: impl Into<SiteRef> + Copy,
        ab: LinkConfig,
        ba: LinkConfig,
    ) {
        self.set_link(a, b, ab);
        self.set_link(b, a, ba);
    }

    /// Sets the CPU parameters of `node`; its calls then take time and queue behind each other.
    pub fn set_cpu(&mut self, node: NodeId, cpu: Cpu) {
        self.nodes[node.index()].cpu = Some(cpu);
    }

    /// Sets the clock model of `node` and tells the node.
    pub fn set_clock(&mut self, node: NodeId, clock: Clock) {
        let now = self.now;
        let slot = &mut self.nodes[node.index()];
        slot.node.clock_changed(now, &clock);
        slot.clock = clock;
    }

    /// Makes UDP unusable for `node` for `portal` nanoseconds after every start of the node, the first start being
    /// time 0 (a captive portal).
    pub fn set_portal(&mut self, node: NodeId, portal: Time) {
        let slot = &mut self.nodes[node.index()];
        slot.portal_ns = portal;
        slot.portal_until = portal;
    }

    /// Attaches an observer to the link from `from` to `to`; `None` when that pair has no link to watch.
    /// It records the first `header_len` bytes of each datagram the link accepts, and all bytes if `keep_payload`.
    pub fn observe(
        &mut self,
        from: impl Into<SiteRef>,
        to: impl Into<SiteRef>,
        header_len: usize,
        keep_payload: bool,
    ) -> Option<ObsId> {
        let key = (self.site(from).0, self.site(to).0);
        let id = self.observers.len() as u32;
        self.link_entry(key.0, key.1)?.observer = Some(id);
        self.observers.push(Observer::new(header_len, keep_payload));
        Some(ObsId(id))
    }

    /// Attaches an observer to the uplink or downlink of a LAN (`Up` or `Down`; `Both` watches the uplink).
    pub fn observe_lan(&mut self, lan: LanId, dir: LanDir, header_len: usize, keep_payload: bool) -> ObsId {
        let id = self.observers.len() as u32;
        let l = &mut self.lans[lan.index()];
        match dir {
            LanDir::Down => l.down.observer = Some(id),
            LanDir::Up | LanDir::Both => l.up.observer = Some(id),
        }
        self.observers.push(Observer::new(header_len, keep_payload));
        ObsId(id)
    }
}
