//! The engine: one event queue ordered by (time, sequence), the topology tables, and the loop that drives nodes.
//!
//! Invariants: virtual time never goes back; events at the same time run in the order they were scheduled; nothing
//! iterates a hash map; every random draw comes from a stream seeded by the run's seed. The same seed and the same
//! scenario calls therefore give a byte-identical trace.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap};
use std::fmt;
use std::net::{IpAddr, SocketAddr};

use crate::adversary::{Flood, Observer, Replay};
use crate::ids::{HostId, IfaceId, LanId, NatId, NodeId, ObsId, SiteId};
use crate::link::{Link, LinkChange, LinkConfig};
use crate::metrics::{Metrics, NodeMetrics};
use crate::nat::{Nat, NatConfig};
use crate::node::{Node, Work};
use crate::rng::{Random, Rng, Stream};
use crate::{Clock, Time, WALL_EPOCH};

/// Datagrams one node may hand over in a single turn before the engine yields and continues at the same instant.
const TX_BURST: usize = 4096;
/// The largest datagram buffer given to `poll_transmit`.
const BUF_LEN: usize = 65_536;
/// Recycled datagram buffers kept for reuse.
pub(crate) const POOL_MAX: usize = 4096;

/// How the harness drives a node after a command.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Driver {
    /// Poll the node to quiescence (events, transmits, timer) after every command.
    #[default]
    Vinc,
    /// As the reference harness does: poll after [`Sim::command`], but not after [`Sim::command_nopump`] (a harness intent).
    /// Output produced by such a command waits for the node's next datagram, timer or pumped command.
    Reference,
}

/// Settings fixed when a simulator is created.
#[derive(Clone, Debug, Default)]
pub struct SimConfig {
    /// How nodes are driven after commands.
    pub driver: Driver,
    /// The link used between two sites that have no explicit link; `None` means such a pair cannot talk.
    pub default_link: Option<LinkConfig>,
    /// Record the ndjson trace.
    pub trace: bool,
    /// Include every datagram (tx, rx, drop) in the trace, not only node events and faults.
    pub trace_packets: bool,
    /// Keep every delivery latency so quantiles can be read; otherwise only count, sum, min and max.
    pub latency_samples: bool,
}

/// The run state of a node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NodeState {
    /// Running.
    Up,
    /// Crashed; waiting for a restart.
    Crashed,
    /// Suspended; waiting for a resume.
    Suspended,
}

/// A node's CPU parameters. The simulator's [`CostModel`] turns them into a cost per call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cpu {
    /// Speed factor in thousandths: 1000 is the model's speed, 4000 is a node four times slower.
    pub factor_milli: u32,
    /// Fixed cost of a call in nanoseconds (used by [`FlatCost`]).
    pub per_call: Time,
    /// Cost per KiB of datagram handled, in nanoseconds (used by [`FlatCost`]).
    pub per_kib: Time,
}

/// What kind of call a cost is for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Call {
    /// A datagram arrived.
    Datagram,
    /// A timer fired.
    Timer,
    /// A scenario command.
    Command,
}

/// Turns one call of a node into busy time. A node is busy until its calls' cost has passed: later datagrams and
/// timers wait, and what the call transmits leaves at the end.
pub trait CostModel {
    /// Nanoseconds the call costs on a node with these CPU parameters, with the node's own work report.
    fn cost(&self, cpu: &Cpu, call: Call, bytes: usize, work: Work) -> Time;
}

/// The default cost model: `(per_call + bytes * per_kib / 1024 + work.ns) * factor_milli / 1000`; ticks are ignored.
#[derive(Clone, Copy, Debug, Default)]
pub struct FlatCost;

impl CostModel for FlatCost {
    fn cost(&self, cpu: &Cpu, _call: Call, bytes: usize, work: Work) -> Time {
        let base = u128::from(cpu.per_call) + bytes as u128 * u128::from(cpu.per_kib) / 1024 + u128::from(work.ns);
        (base * u128::from(cpu.factor_milli) / 1000) as Time
    }
}

/// The shape of a LAN (a site): its uplink and downlink, region, path MTU and middlebox settings.
#[derive(Clone, Debug)]
pub struct LanConfig {
    /// The uplink, shared by every datagram leaving the LAN.
    pub up: LinkConfig,
    /// The downlink, shared by every datagram entering the LAN.
    pub down: LinkConfig,
    /// The region, for the delay between regions.
    pub region: u32,
    /// The site MTU in bytes; the datagram limit is this minus 28 (IPv4) or 48 (IPv6).
    pub mtu: usize,
    /// Drop all UDP in and out of the LAN.
    pub udp_block: bool,
    /// A stateful IPv6 firewall: inbound IPv6 is admitted only from remotes the host sent to (at most 256 each).
    pub v6_firewall: bool,
}

impl Default for LanConfig {
    fn default() -> Self {
        Self {
            up: LinkConfig::default(),
            down: LinkConfig::default(),
            region: 0,
            mtu: 1500,
            udp_block: false,
            v6_firewall: false,
        }
    }
}

/// Which link of a LAN.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LanDir {
    /// The uplink.
    Up,
    /// The downlink.
    Down,
    /// Both.
    Both,
}

pub(crate) struct Lan<R: Random> {
    pub(crate) cfg: LanConfig,
    pub(crate) up: Link<R>,
    pub(crate) down: Link<R>,
    pub(crate) down_site: u32,
    pub(crate) fw: BTreeMap<IpAddr, BTreeSet<SocketAddr>>,
}

/// A scheduled partition between sets of LANs, judged at the uplink send time.
pub(crate) struct LanPartition {
    pub(crate) from: Time,
    pub(crate) to: Time,
    pub(crate) x: Vec<u32>,
    pub(crate) y: Vec<u32>,
    pub(crate) both: bool,
}

pub(crate) struct Iface {
    pub(crate) site: u32,
    pub(crate) addr: IpAddr,
    pub(crate) via: Option<u32>,
    pub(crate) lan: Option<u32>,
    pub(crate) up: bool,
    pub(crate) mtu: usize,
}

pub(crate) struct Slot<N: Node> {
    pub(crate) node: N,
    pub(crate) state: NodeState,
    pub(crate) ifaces: Vec<Iface>,
    pub(crate) persisted: Vec<u8>,
    pub(crate) log: Vec<(Time, N::Event)>,
    pub(crate) timer_gen: u64,
    pub(crate) timer_at: Option<Time>,
    pub(crate) busy_until: Time,
    pub(crate) cpu: Option<Cpu>,
    pub(crate) clock: Clock,
    pub(crate) group: u32,
    pub(crate) portal_ns: Time,
    pub(crate) portal_until: Time,
}

#[derive(Clone, Copy)]
pub(crate) enum SiteKind {
    Iface { node: u32, idx: u32 },
    Nat(u32),
    Host(u32),
    LanDown(u32),
}

pub(crate) struct NatSlot<R: Random> {
    pub(crate) site: u32,
    pub(crate) nat: Nat<R>,
    pub(crate) lan_map: BTreeMap<IpAddr, u32>,
    pub(crate) lan: Option<u32>,
}

pub(crate) struct HostSlot {
    pub(crate) site: u32,
    pub(crate) received: u64,
}

pub(crate) struct Packet {
    pub(crate) src: SocketAddr,
    pub(crate) dst: SocketAddr,
    pub(crate) data: Vec<u8>,
    pub(crate) origin: Option<u32>,
    pub(crate) sent_at: Time,
}

#[derive(Clone, Copy)]
pub(crate) enum IfaceChange {
    Up,
    Down,
    Addr(IpAddr),
}

pub(crate) enum Ev<C> {
    Arrive {
        site: u32,
        pkt: u32,
    },
    Timer {
        node: u32,
        epoch: u64,
    },
    Wake {
        node: u32,
    },
    Command {
        node: u32,
        cmd: C,
        pump: bool,
    },
    Link {
        from: u32,
        to: u32,
        change: Box<LinkChange>,
    },
    LanLink {
        lan: u32,
        dir: LanDir,
        change: Box<LinkChange>,
    },
    LanBlock {
        lan: u32,
        block: bool,
    },
    Crash(u32),
    Restart(u32),
    Suspend(u32),
    Resume(u32),
    Iface {
        node: u32,
        idx: u32,
        change: IfaceChange,
    },
    Partition(Vec<(u32, u32)>),
    NatRebind {
        nat: u32,
        ip: Option<IpAddr>,
    },
    ClockDrift {
        node: u32,
        ppm: i64,
    },
    FloodTick(u32),
    ReplayStep(u32),
}

pub(crate) struct Entry<C> {
    pub(crate) t: Time,
    pub(crate) seq: u64,
    pub(crate) ev: Ev<C>,
}

impl<C> PartialEq for Entry<C> {
    fn eq(&self, o: &Self) -> bool {
        (self.t, self.seq) == (o.t, o.seq)
    }
}
impl<C> Eq for Entry<C> {}
impl<C> PartialOrd for Entry<C> {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl<C> Ord for Entry<C> {
    fn cmp(&self, o: &Self) -> Ordering {
        (o.t, o.seq).cmp(&(self.t, self.seq))
    }
}

/// The simulator: a topology of nodes of one type `N`, the network between them, and the clock that drives both.
/// `R` is the random source and `C` the CPU cost model; the defaults are [`Rng`] and [`FlatCost`].
pub struct Sim<N: Node, R: Random = Rng, C: CostModel = FlatCost> {
    pub(crate) seed: u64,
    pub(crate) cfg: SimConfig,
    pub(crate) cost: C,
    pub(crate) now: Time,
    pub(crate) seq: u64,
    pub(crate) processed: u64,
    pub(crate) queue: BinaryHeap<Entry<N::Cmd>>,
    pub(crate) nodes: Vec<Slot<N>>,
    pub(crate) sites: Vec<SiteKind>,
    pub(crate) nats: Vec<NatSlot<R>>,
    pub(crate) hosts: Vec<HostSlot>,
    pub(crate) lans: Vec<Lan<R>>,
    pub(crate) lan_parts: Vec<LanPartition>,
    pub(crate) region_delay: BTreeMap<(u32, u32), Time>,
    pub(crate) addr_map: BTreeMap<IpAddr, u32>,
    pub(crate) links: BTreeMap<(u32, u32), Link<R>>,
    pub(crate) pkts: Vec<Option<Packet>>,
    pub(crate) free_pkts: Vec<u32>,
    pub(crate) pool: Vec<Vec<u8>>,
    pub(crate) observers: Vec<Observer>,
    pub(crate) floods: Vec<Flood<R>>,
    pub(crate) replays: Vec<Replay>,
    pub(crate) metrics: Metrics,
    pub(crate) trace: Option<String>,
    pub(crate) buf: Vec<u8>,
}

impl<N: Node> Sim<N> {
    /// A simulator with the default settings: no default link, no trace, the default random source and cost model.
    pub fn new(seed: u64) -> Self {
        Self::with_config(seed, SimConfig::default())
    }

    /// A simulator with explicit settings, the default random source and the default cost model.
    pub fn with_config(seed: u64, cfg: SimConfig) -> Self {
        Self::with_parts(seed, cfg, FlatCost)
    }
}

impl<N: Node, R: Random, C: CostModel> Sim<N, R, C> {
    /// A simulator with explicit settings and cost model; the random source is the type parameter `R`.
    pub fn with_parts(seed: u64, cfg: SimConfig, cost: C) -> Self {
        Self {
            seed,
            now: 0,
            seq: 0,
            processed: 0,
            queue: BinaryHeap::new(),
            nodes: Vec::new(),
            sites: Vec::new(),
            nats: Vec::new(),
            hosts: Vec::new(),
            lans: Vec::new(),
            lan_parts: Vec::new(),
            region_delay: BTreeMap::new(),
            addr_map: BTreeMap::new(),
            links: BTreeMap::new(),
            pkts: Vec::new(),
            free_pkts: Vec::new(),
            pool: Vec::new(),
            observers: Vec::new(),
            floods: Vec::new(),
            replays: Vec::new(),
            metrics: Metrics::default(),
            trace: cfg.trace.then(String::new),
            buf: vec![0; BUF_LEN],
            cost,
            cfg,
        }
    }

    // ---- topology ----

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
            busy_until: 0,
            cpu: None,
            clock: Clock::default(),
            group: 0,
            portal_ns: 0,
            portal_until: 0,
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

    // ---- scheduling and running ----

    pub(crate) fn push(&mut self, at: Time, ev: Ev<N::Cmd>) {
        self.seq += 1;
        self.queue.push(Entry {
            t: at.max(self.now),
            seq: self.seq,
            ev,
        });
    }

    /// Schedules `cmd` for `node` at time `at`; the node is polled afterwards.
    pub fn command(&mut self, at: Time, node: NodeId, cmd: N::Cmd) {
        self.push(
            at,
            Ev::Command {
                node: node.0,
                cmd,
                pump: true,
            },
        );
    }

    /// Schedules `cmd` as a harness intent: under [`Driver::Reference`] the node is not polled afterwards, so what the
    /// command makes it want to send waits for its next datagram, timer or pumped command. Under [`Driver::Vinc`]
    /// it behaves like [`Sim::command`].
    pub fn command_nopump(&mut self, at: Time, node: NodeId, cmd: N::Cmd) {
        self.push(
            at,
            Ev::Command {
                node: node.0,
                cmd,
                pump: false,
            },
        );
    }

    /// Runs one event; false when none is left.
    pub fn step(&mut self) -> bool {
        let Some(e) = self.queue.pop() else { return false };
        self.now = self.now.max(e.t);
        self.processed += 1;
        self.dispatch(e);
        true
    }

    /// Runs every event up to and including `t`, then sets the time to `t`.
    pub fn run_until(&mut self, t: Time) {
        while self.queue.peek().is_some_and(|e| e.t <= t) {
            self.step();
        }
        self.now = self.now.max(t);
    }

    /// Runs until `pred` holds (checked before the first event and after each one) or time `limit` passes.
    /// Returns whether `pred` held.
    pub fn run_until_pred(&mut self, limit: Time, mut pred: impl FnMut(&Self) -> bool) -> bool {
        loop {
            if pred(self) {
                return true;
            }
            if self.queue.peek().is_none_or(|e| e.t > limit) {
                self.now = self.now.max(limit);
                return false;
            }
            self.step();
        }
    }

    /// Runs until no event is left or time `limit` passes; returns whether the queue drained.
    pub fn run_idle(&mut self, limit: Time) -> bool {
        self.run_until(limit);
        self.queue.is_empty()
    }

    fn dispatch(&mut self, e: Entry<N::Cmd>) {
        let Entry { t, seq, ev } = e;
        let gated = match &ev {
            Ev::Arrive { site, .. } => match self.sites[*site as usize] {
                SiteKind::Iface { node, .. } => Some(node),
                _ => None,
            },
            Ev::Timer { node, .. } => Some(*node),
            _ => None,
        };
        if let Some(n) = gated {
            let busy = self.nodes[n as usize].busy_until;
            if t < busy {
                // The node is still working on an earlier call: wait behind it, keeping the original order.
                self.queue.push(Entry { t: busy, seq, ev });
                return;
            }
        }
        match ev {
            Ev::Arrive { site, pkt } => self.on_arrive(t, site, pkt),
            Ev::Timer { node, epoch } => self.on_timer(t, node as usize, epoch),
            Ev::Wake { node } => {
                if self.nodes[node as usize].state == NodeState::Up {
                    let busy = self.nodes[node as usize].busy_until;
                    self.drive(node as usize, t, t.max(busy), false);
                }
            }
            Ev::Command { node, cmd, pump } => self.on_command(t, node as usize, cmd, pump),
            Ev::Link { from, to, change } => {
                if let Some(l) = self.link_entry(from, to) {
                    l.apply(*change);
                }
            }
            Ev::LanLink { lan, dir, change } => self.on_lan_link(lan as usize, dir, *change),
            Ev::LanBlock { lan, block } => self.lans[lan as usize].cfg.udp_block = block,
            Ev::Crash(n) => self.on_crash(t, n as usize),
            Ev::Restart(n) => self.on_restart(t, n as usize),
            Ev::Suspend(n) => self.on_suspend(t, n as usize),
            Ev::Resume(n) => self.on_resume(t, n as usize),
            Ev::Iface { node, idx, change } => self.on_iface(t, node as usize, idx as usize, change),
            Ev::Partition(groups) => self.on_partition(t, &groups),
            Ev::NatRebind { nat, ip } => self.on_nat_rebind(t, nat as usize, ip),
            Ev::ClockDrift { node, ppm } => self.on_clock_drift(t, node as usize, ppm),
            Ev::FloodTick(i) => self.on_flood(t, i as usize),
            Ev::ReplayStep(i) => self.on_replay(t, i as usize),
        }
    }

    /// Ends a call of `node` that started at `start`: the node's work is turned into busy time, and the time its
    /// output may leave is returned (the end of the busy period, or `start` for a node without a CPU model).
    pub(crate) fn finish_call(&mut self, node: usize, start: Time, call: Call, bytes: usize) -> Time {
        let slot = &mut self.nodes[node];
        let work = slot.node.take_work();
        let Some(cpu) = slot.cpu else { return start };
        let done = slot.busy_until.max(start) + self.cost.cost(&cpu, call, bytes, work);
        slot.busy_until = done;
        done
    }

    fn on_timer(&mut self, t: Time, n: usize, epoch: u64) {
        let slot = &mut self.nodes[n];
        if slot.state != NodeState::Up || slot.timer_gen != epoch {
            return;
        }
        slot.timer_at = None;
        let due = slot.node.poll_timeout().is_some_and(|d| d <= t);
        if due {
            slot.node.handle_timeout(t);
        }
        let send_at = self.finish_call(n, t, Call::Timer, 0);
        self.drive(n, t, send_at, due);
    }

    fn on_command(&mut self, t: Time, n: usize, cmd: N::Cmd, pump: bool) {
        if self.nodes[n].state != NodeState::Up {
            self.trace_line(format_args!("{{\"t\":{t},\"k\":\"cmd_lost\",\"n\":{n}}}"));
            return;
        }
        self.nodes[n].node.command(t, cmd);
        let send_at = self.finish_call(n, t, Call::Command, 0);
        if pump || self.cfg.driver == Driver::Vinc {
            self.drive(n, t, send_at, false);
        }
    }

    /// Collects a node's events and transmits after one of its calls at `now`, sends the transmits at `send_at`, and
    /// re-arms its timer. `after_timeout` applies the rule that a timeout must lie strictly after a timer call.
    pub(crate) fn drive(&mut self, n: usize, now: Time, send_at: Time, after_timeout: bool) {
        let mut buf = std::mem::take(&mut self.buf);
        self.drain_events(n, now);
        let mut sent = 0;
        while sent < TX_BURST {
            let Some(tx) = self.nodes[n].node.poll_transmit(now, &mut buf) else {
                break;
            };
            let len = tx.len.min(buf.len());
            let at = send_at.max(tx.send_at.unwrap_or(0));
            self.emit(n, at, tx.local, tx.remote, &buf[..len]);
            sent += 1;
        }
        if sent == TX_BURST {
            self.push(now, Ev::Wake { node: n as u32 });
        }
        self.drain_events(n, now);
        self.buf = buf;
        self.rearm(n, now, after_timeout);
    }

    pub(crate) fn drain_events(&mut self, n: usize, now: Time) {
        while let Some(ev) = self.nodes[n].node.poll_event() {
            if self.trace.is_some() {
                let text = escape(&format!("{ev:?}"));
                self.trace_line(format_args!("{{\"t\":{now},\"k\":\"ev\",\"n\":{n},\"e\":\"{text}\"}}"));
            }
            self.nodes[n].log.push((now, ev));
        }
    }

    /// Arms the node's timer at its next timeout, no earlier than now or the end of its busy period. A timeout that
    /// is not strictly after a timer call is a violation: it is counted and replaced by `now + 1 ms`.
    pub(crate) fn rearm(&mut self, n: usize, now: Time, after_timeout: bool) {
        let slot = &mut self.nodes[n];
        let Some(mut d) = slot.node.poll_timeout() else { return };
        if after_timeout && d <= now {
            self.metrics.timer_violations += 1;
            d = now + 1_000_000;
        }
        let d = d.max(now).max(slot.busy_until);
        if slot.timer_at.is_none_or(|a| d < a) {
            slot.timer_gen += 1;
            slot.timer_at = Some(d);
            let epoch = slot.timer_gen;
            self.push(d, Ev::Timer { node: n as u32, epoch });
        }
    }

    pub(crate) fn trace_line(&mut self, args: fmt::Arguments<'_>) {
        if let Some(s) = self.trace.as_mut() {
            use fmt::Write;
            // Writing to a String cannot fail.
            let _ = s.write_fmt(args);
            s.push('\n');
        }
    }

    // ---- inspection ----

    /// The current virtual time in nanoseconds.
    pub const fn now(&self) -> Time {
        self.now
    }

    /// How many events the engine has run (stale timers included).
    pub const fn events_processed(&self) -> u64 {
        self.processed
    }

    /// How many events are waiting.
    pub fn pending(&self) -> usize {
        self.queue.len()
    }

    /// A node, for inspection.
    pub fn node(&self, id: NodeId) -> &N {
        &self.nodes[id.index()].node
    }

    /// A node, mutably. Schedule a wake afterwards so its output is polled.
    pub fn node_mut(&mut self, id: NodeId) -> &mut N {
        &mut self.nodes[id.index()].node
    }

    /// Polls `node` for transmits, events and its timer at time `at`.
    pub fn wake(&mut self, at: Time, node: NodeId) {
        self.push(at, Ev::Wake { node: node.0 });
    }

    /// The run state of a node.
    pub fn state(&self, id: NodeId) -> NodeState {
        self.nodes[id.index()].state
    }

    /// The events a node reported, each with the time it was collected.
    pub fn events(&self, id: NodeId) -> &[(Time, N::Event)] {
        &self.nodes[id.index()].log
    }

    /// The current address of an interface.
    pub fn iface_addr(&self, id: IfaceId) -> IpAddr {
        self.nodes[id.node.index()].ifaces[id.idx as usize].addr
    }

    /// The counters of the run.
    pub const fn metrics(&self) -> &Metrics {
        &self.metrics
    }

    /// An observer and what it recorded.
    pub fn observer(&self, id: ObsId) -> &Observer {
        &self.observers[id.index()]
    }

    /// Datagrams a host has received.
    pub fn host_received(&self, id: HostId) -> u64 {
        self.hosts[id.index()].received
    }

    /// Live and expired-but-unswept mappings of a NAT.
    pub fn nat_mappings(&self, id: NatId) -> usize {
        self.nats[id.index()].nat.mappings()
    }

    /// Inbound datagrams a NAT admitted from sources that are themselves behind a NAT.
    pub fn nat_punched(&self, id: NatId) -> u64 {
        self.nats[id.index()].nat.punched
    }

    /// The public address of a NAT.
    pub fn nat_ext_ip(&self, id: NatId) -> IpAddr {
        self.nats[id.index()].nat.cfg.ext_ip
    }

    /// The clock model of a node.
    pub fn clock(&self, id: NodeId) -> &Clock {
        &self.nodes[id.index()].clock
    }

    /// The local clock reading of a node now, in nanoseconds; negative values are possible.
    pub fn local_time(&self, id: NodeId) -> i64 {
        self.nodes[id.index()].clock.local(self.now)
    }

    /// The wall clock a node reads now (Unix epoch plus its local clock), with skew, drift and jumps; protocol
    /// timers must not use it.
    pub fn wall_time(&self, id: NodeId) -> u64 {
        (i128::from(WALL_EPOCH) + i128::from(self.local_time(id))).clamp(0, i128::from(u64::MAX)) as u64
    }

    /// The trace so far (empty when tracing is off).
    pub fn trace(&self) -> &str {
        self.trace.as_deref().unwrap_or("")
    }

    /// Takes the trace out, leaving an empty one in place.
    pub fn take_trace(&mut self) -> String {
        self.trace.as_mut().map(std::mem::take).unwrap_or_default()
    }
}

/// Anything that names a site: an interface, a NAT or a host.
#[derive(Clone, Copy, Debug)]
pub enum SiteRef {
    /// A node interface.
    Iface(IfaceId),
    /// A NAT.
    Nat(NatId),
    /// An adversary host.
    Host(HostId),
    /// A site by its id.
    Site(SiteId),
}

impl From<IfaceId> for SiteRef {
    fn from(v: IfaceId) -> Self {
        Self::Iface(v)
    }
}
impl From<NatId> for SiteRef {
    fn from(v: NatId) -> Self {
        Self::Nat(v)
    }
}
impl From<HostId> for SiteRef {
    fn from(v: HostId) -> Self {
        Self::Host(v)
    }
}
impl From<SiteId> for SiteRef {
    fn from(v: SiteId) -> Self {
        Self::Site(v)
    }
}
impl From<NodeId> for SiteRef {
    /// A node stands for its first interface.
    fn from(v: NodeId) -> Self {
        Self::Iface(IfaceId { node: v, idx: 0 })
    }
}

/// JSON string escaping for trace text.
fn escape(s: &str) -> String {
    use fmt::Write;
    let mut o = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            c if (c as u32) < 0x20 => {
                let _ = write!(o, "\\u{:04x}", c as u32);
            }
            c => o.push(c),
        }
    }
    o
}
