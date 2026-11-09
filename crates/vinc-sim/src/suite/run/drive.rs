//! The schedule of a run and the actions that need the live state of the simulation.
//!
//! Everything the simulator can do on its own is pushed before the run in the reference's order: the environment
//! actions (sorted), the intents, the persist ticks every 60 s below the duration. What depends on the state a node is
//! in when the action comes (suspend, handover, revoke, rebind, outage, the adversary's floods, the compromise) waits
//! in an agenda; the run stops at each agenda time, lets the simulator reach it, and then acts with the state in front
//! of it. An agenda action runs after the simulator's own events of the same instant.
//!
//! Invariants: the agenda is ordered by `(time, insertion)`; an action beyond the duration never runs; a node that is
//! not running is told about address changes and moves through [`crate::suite::node::SuiteNode::set_iface_up`] and
//! [`crate::suite::node::SuiteNode::mark_moved`], so its next incarnation starts from the right interfaces.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::net::SocketAddr;
use std::rc::Rc;

use super::net::Net;
use crate::reference::RefRng;
use crate::suite::crypto::Registry;
use crate::suite::node::{Cmd, Shared, iface_ip};
use crate::suite::proto::host::Layers;
use crate::suite::rec::{NS, Rec};
use crate::suite::world::model::{Addr, AdvKind, EnvArg, EnvKind, World};
use crate::{NodeState, Random};

/// Seconds between persist ticks.
const PERSIST_EVERY: u64 = 60 * NS;
/// A node that upgrades is back this long after it left.
const UPGRADE_DOWNTIME: u64 = 2 * NS;
const MS: u64 = 1_000_000;

enum Act {
    Revoke(usize),
    Suspend { node: usize, dur: u64 },
    Resumed(usize),
    HandoverStart { node: usize, site: usize, gap: u64 },
    HandoverEnd { node: usize, to: usize, started: u64 },
    Rebind(usize),
    Outage { node: usize, dur: u64 },
    OutageEnd(usize),
    Adversary(AdvKind, usize),
    Compromise(usize),
}

/// The state of a run in progress.
pub struct Exec<'a> {
    pub(super) net: Net,
    world: &'a World,
    rec: Rc<RefCell<Rec>>,
    reg: &'static Registry,
    agenda: BTreeMap<(u64, u64), Act>,
    seq: u64,
    /// The site each node is at (or moving to).
    pub(super) cur_site: Vec<usize>,
    active: Vec<usize>,
    pending_revokes: Vec<Vec<usize>>,
    rng: RefRng,
}

fn sock(kind: &str, host: u64, port: u16) -> Option<SocketAddr> {
    iface_ip(&Addr {
        kind: kind.to_owned(),
        host,
        port,
    })
    .map(|ip| SocketAddr::new(ip, port))
}

impl<'a> Exec<'a> {
    /// A run of `world` on `net`, reporting to `rec`.
    pub fn new(world: &'a World, net: Net, shared: &Rc<Shared>) -> Self {
        let n = world.nodes.len();
        Self {
            net,
            world,
            rec: Rc::clone(&shared.rec),
            reg: shared.registry,
            agenda: BTreeMap::new(),
            seq: 0,
            cur_site: world.nodes.iter().map(|s| s.site).collect(),
            active: vec![0; n],
            pending_revokes: vec![Vec::new(); n],
            rng: RefRng::derive(world.seed, crate::Stream::Adversary),
        }
    }

    fn at(&mut self, t: u64, act: Act) {
        self.seq += 1;
        self.agenda.insert((t, self.seq), act);
    }

    /// Pushes the whole schedule: simulator events now, agenda actions for later.
    pub fn schedule(&mut self, intents: &[usize]) {
        let w = self.world;
        for id in self.net.ids.clone() {
            self.net.sim.crash(0, id);
        }
        for a in &w.env {
            let Some(&id) = self.net.ids.get(a.node) else {
                if a.kind == EnvKind::Rebind {
                    self.at(a.t, Act::Rebind(a.node));
                }
                continue;
            };
            match (a.kind, a.arg) {
                (EnvKind::Start | EnvKind::Restart, _) => self.net.sim.restart(a.t, id),
                (EnvKind::Crash, _) => self.net.sim.crash(a.t, id),
                (EnvKind::Leave | EnvKind::Upgrade, _) => {
                    self.net.sim.command(a.t, id, Cmd::Shutdown);
                    self.net.sim.crash(a.t, id);
                    if a.kind == EnvKind::Upgrade {
                        self.net.sim.restart(a.t + UPGRADE_DOWNTIME, id);
                    }
                }
                (EnvKind::Revoke, _) => self.at(a.t, Act::Revoke(a.node)),
                (EnvKind::Suspend, EnvArg::Num(dur)) => self.at(a.t, Act::Suspend { node: a.node, dur }),
                (EnvKind::Handover, EnvArg::SiteGap(site, gap)) => self.at(
                    a.t,
                    Act::HandoverStart {
                        node: a.node,
                        site,
                        gap,
                    },
                ),
                (EnvKind::Rebind, _) => self.at(a.t, Act::Rebind(a.node)),
                (EnvKind::Outage, EnvArg::Num(dur)) => self.at(a.t, Act::Outage { node: a.node, dur }),
                _ => {}
            }
        }
        for &i in intents {
            if let Some(it) = w.intents.get(i)
                && let Some(&id) = self.net.ids.get(it.node)
            {
                self.net.sim.command_nopump(it.t, id, Cmd::Intent(Box::new(it.clone())));
            }
        }
        let mut t = PERSIST_EVERY;
        while t < w.duration_ns {
            for id in self.net.ids.clone() {
                self.net.sim.command_nopump(t, id, Cmd::Persist);
            }
            t += PERSIST_EVERY;
        }
        for &(t, kind, node) in &w.adversary_env {
            self.at(t, Act::Adversary(kind, node));
        }
        for &(t, node) in &w.compromise {
            self.at(t, Act::Compromise(node));
        }
    }

    /// Runs to the end of the world.
    pub fn run(&mut self) {
        let end = self.world.duration_ns;
        while let Some((&(t, _), _)) = self.agenda.first_key_value() {
            if t > end {
                break;
            }
            self.net.sim.run_until(t);
            if let Some((_, act)) = self.agenda.pop_first() {
                self.exec(t, act);
            }
        }
        self.net.sim.run_until(end);
    }

    fn exec(&mut self, t: u64, act: Act) {
        match act {
            Act::Revoke(x) => self.revoke(t, x),
            Act::Suspend { node, dur } => self.suspend(t, node, dur),
            Act::Resumed(node) => {
                let Some(&id) = self.net.ids.get(node) else { return };
                for x in std::mem::take(&mut self.pending_revokes[node]) {
                    if self.net.sim.state(id) == NodeState::Up {
                        self.net.sim.command(t, id, Cmd::Revoke(x));
                    }
                }
            }
            Act::HandoverStart { node, site, gap } => self.handover_start(t, node, site, gap),
            Act::HandoverEnd { node, to, started } => self.handover_end(t, node, to, started),
            Act::Rebind(nid) => {
                if let Some(&nat) = self.net.nats.get(nid) {
                    self.net.sim.nat_rebind(t, nat, None);
                    self.rec.borrow_mut().nat_rebind(nid, t);
                }
            }
            Act::Outage { node, dur } => {
                if let Some(&lan) = self.cur_site.get(node).and_then(|&s| self.net.lans.get(s)) {
                    self.net.sim.lan_outage(lan, t, t + dur);
                    self.at(t + dur, Act::OutageEnd(node));
                }
            }
            Act::OutageEnd(node) => {
                if let Some(&id) = self.net.ids.get(node) {
                    let open = self.net.sim.node(id).layers().has_open_intents(t);
                    self.rec.borrow_mut().link_returned(node, t, open);
                }
            }
            Act::Adversary(kind, node) => self.adversary(t, kind, node),
            Act::Compromise(node) => self.compromise(t, node),
        }
    }

    fn revoke(&mut self, t: u64, x: usize) {
        self.rec.borrow_mut().revoke(x, t);
        for (j, &id) in self.net.ids.clone().iter().enumerate().filter(|(j, _)| *j != x) {
            match self.net.sim.state(id) {
                NodeState::Up => self.net.sim.command(t, id, Cmd::Revoke(x)),
                NodeState::Suspended => self.pending_revokes[j].push(x),
                NodeState::Crashed => {}
            }
        }
    }

    fn suspend(&mut self, t: u64, node: usize, dur: u64) {
        let Some(&id) = self.net.ids.get(node) else { return };
        if self.net.sim.state(id) != NodeState::Up {
            return;
        }
        self.rec.borrow_mut().suspended(node, t, dur);
        self.net.sim.suspend(t, id);
        self.net.sim.resume(t + dur, id);
        self.at(t + dur, Act::Resumed(node));
    }

    fn handover_start(&mut self, t: u64, node: usize, site: usize, gap: u64) {
        let Some(&id) = self.net.ids.get(node) else { return };
        let st = self.net.sim.state(id);
        if st == NodeState::Crashed {
            return;
        }
        let Some(to) = self.net.at_site[node].iter().position(|s| s.site == site) else {
            return;
        };
        self.rec.borrow_mut().address_change(node, t);
        let from = self.active[node];
        for &(f, _) in &self.net.at_site[node][from].ifaces.clone() {
            let ip = self.net.sim.iface_addr(f);
            self.net.sim.set_iface_up(t, id, f.idx, false);
            if st == NodeState::Suspended {
                self.net.sim.node_mut(id).set_iface_up(ip, false);
            }
        }
        if let Some(&lan) = self.net.lans.get(site) {
            self.net.sim.lan_outage(lan, t, t + gap);
        }
        self.cur_site[node] = site;
        self.active[node] = to;
        self.at(t + gap, Act::HandoverEnd { node, to, started: t });
    }

    fn handover_end(&mut self, t: u64, node: usize, to: usize, started: u64) {
        let Some(&id) = self.net.ids.get(node) else { return };
        let st = self.net.sim.state(id);
        let set = self.net.at_site[node][to].clone();
        let mut ips = Vec::new();
        for &(f, v6) in &set.ifaces {
            if v6 {
                let port = self.world.nodes[node]
                    .ifaces
                    .iter()
                    .find(|x| x.kind == "udp6")
                    .map_or(4433, |x| x.addr.port);
                let host = 6_000_000 + node as u64 * 1000 + (started / NS) % 1000;
                if let Some(a) = sock("udp6", host, port) {
                    self.net.sim.set_iface_addr(t, id, f.idx, a.ip());
                }
            }
            self.net.sim.set_iface_up(t, id, f.idx, true);
            ips.push((f, v6));
        }
        if st != NodeState::Up {
            for (f, v6) in ips {
                let ip = if v6 {
                    let port = self.world.nodes[node].ifaces.first().map_or(4433, |x| x.addr.port);
                    sock("udp6", 6_000_000 + node as u64 * 1000 + (started / NS) % 1000, port).map(|a| a.ip())
                } else {
                    Some(self.net.sim.iface_addr(f))
                };
                if let Some(ip) = ip {
                    self.net.sim.node_mut(id).set_iface_up(ip, true);
                }
            }
            if st == NodeState::Suspended {
                self.net.sim.node_mut(id).mark_moved();
            }
        }
    }

    fn compromise(&mut self, t: u64, node: usize) {
        let Some(&id) = self.net.ids.get(node) else { return };
        if self.net.sim.state(id) == NodeState::Up {
            self.net.sim.command_nopump(t, id, Cmd::Compromise);
        } else {
            let n = self.net.sim.node(id);
            self.reg.note_compromise(node, t, &n.identity_seed(), n.exported());
        }
    }

    /// The first IPv4 (else IPv6) UDP address a node has at its current site, as a destination for injections.
    fn dst_of(&self, node: usize) -> Option<SocketAddr> {
        let set = self.net.at_site.get(node)?.get(*self.active.get(node)?)?;
        let (f, _) = set.ifaces.first()?;
        let port = self
            .world
            .nodes
            .get(node)?
            .ifaces
            .iter()
            .find(|x| x.kind.starts_with("udp"))?
            .addr
            .port;
        Some(SocketAddr::new(self.net.sim.iface_addr(*f), port))
    }

    fn adversary(&mut self, t: u64, kind: AdvKind, node: usize) {
        let Some(&id) = self.net.ids.get(node) else { return };
        if self.net.sim.state(id) != NodeState::Up {
            return;
        }
        let Some(dst) = self.dst_of(node) else { return };
        match kind {
            AdvKind::Garbage => {
                for _ in 0..8 {
                    let n = 1 + self.rng.below(1200) as usize;
                    let mut junk = vec![0u8; n];
                    let head = n.min(64);
                    self.rng.fill(&mut junk[..head]);
                    let (host, port) = (9_000_000 + self.rng.below(1000), 1 + self.rng.below(60_000) as u16);
                    if let Some(src) = sock("udp4", host, port) {
                        self.net.sim.inject_at(t, id, src, dst, junk);
                        self.rec.borrow_mut().adversary_action("inject");
                    }
                }
            }
            AdvKind::Amplify => {
                // A real reflection replays a first flight that reached this very server; the flights other servers
                // received are the fallback, as the reference's only choice.
                let all = self.net.sim.tap_captured();
                let own: Vec<usize> = (0..all.len()).filter(|&i| all[i].node == id).collect();
                let other: Vec<usize> = (0..all.len()).filter(|&i| all[i].node != id).collect();
                let pool = if own.is_empty() { other } else { own };
                if pool.is_empty() {
                    return;
                }
                let pick = pool[self.rng.below(pool.len() as u64) as usize];
                let data = all[pick].data.clone();
                let host = 8_000_000 + self.rng.below(1000);
                if let Some(spoof) = sock("udp4", host, 4433) {
                    self.rec.borrow_mut().amp_probe(node, spoof);
                    self.net.sim.inject_at(t, id, spoof, dst, data);
                    self.rec.borrow_mut().adversary_action("inject");
                }
            }
            AdvKind::Eclipse => {
                for k in 0..32u64 {
                    let all = self.net.sim.tap_captured();
                    if all.is_empty() {
                        return;
                    }
                    let data = all[self.rng.below(all.len() as u64) as usize].data.clone();
                    let (host, port) = (7_000_000 + self.rng.below(4096), 1024 + self.rng.below(60_000) as u16);
                    if let Some(spoof) = sock("udp4", host, port) {
                        self.rec.borrow_mut().amp_probe(node, spoof);
                        self.net.sim.inject_at(t + k * MS, id, spoof, dst, data);
                        self.rec.borrow_mut().adversary_action("inject");
                    }
                }
            }
        }
    }
}
