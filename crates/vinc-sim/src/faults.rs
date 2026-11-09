//! Scheduled changes to the world: link changes, partitions, NAT rebinding, node lifecycle, interface and clock
//! faults, and the adversaries. Each `at` is a virtual time; a time in the past runs at the current time.

use std::net::IpAddr;

use crate::Time;
use crate::adversary::{Flood, FloodPayload, FloodSpec, Replay};
use crate::ids::{HostId, LanId, NatId, NodeId, ObsId};
use crate::link::LinkChange;
use crate::node::{IfaceEvent, Node};
use crate::rng::{Random, Stream};
use crate::sim::{CostModel, Ev, IfaceChange, LanDir, LanPartition, NodeState, Sim, SiteRef};

impl<N: Node, R: Random, C: CostModel> Sim<N, R, C> {
    /// Changes the link from `from` to `to` at time `at` (an outage, an MTU change, a bandwidth step, ...).
    pub fn link_change(&mut self, at: Time, from: impl Into<SiteRef>, to: impl Into<SiteRef>, change: LinkChange) {
        let (f, t) = (self.site(from).0, self.site(to).0);
        self.push(
            at,
            Ev::Link {
                from: f,
                to: t,
                change: Box::new(change),
            },
        );
    }

    /// Blocks both directions between `a` and `b` from `start` to `end`.
    pub fn outage(&mut self, a: impl Into<SiteRef> + Copy, b: impl Into<SiteRef> + Copy, start: Time, end: Time) {
        for (x, y) in [(a.into(), b.into()), (b.into(), a.into())] {
            self.link_change(start, x, y, LinkChange::Blocked(true));
            self.link_change(end, x, y, LinkChange::Blocked(false));
        }
    }

    /// Splits the nodes into groups at `at`: nodes in different groups cannot reach each other, judged when a
    /// datagram arrives. Nodes not listed form one more group. Adversary hosts are never partitioned.
    pub fn partition(&mut self, at: Time, groups: &[&[NodeId]]) {
        let map = groups
            .iter()
            .enumerate()
            .flat_map(|(g, ns)| ns.iter().map(move |n| (n.0, g as u32 + 1)))
            .collect();
        self.push(at, Ev::Partition(map));
    }

    /// Ends every partition at `at`.
    pub fn heal(&mut self, at: Time) {
        self.push(at, Ev::Partition(Vec::new()));
    }

    /// Clears every mapping of `nat` at `at`, optionally moving it to a new public address.
    pub fn nat_rebind(&mut self, at: Time, nat: NatId, new_ip: Option<IpAddr>) {
        self.push(at, Ev::NatRebind { nat: nat.0, ip: new_ip });
    }

    /// Crashes `node` at `at`: volatile state is lost, datagrams to it are dropped, only its persisted bytes survive.
    pub fn crash(&mut self, at: Time, node: NodeId) {
        self.push(at, Ev::Crash(node.0));
    }

    /// Restarts a crashed `node` at `at` with the bytes it persisted. Does nothing if the node is not crashed.
    pub fn restart(&mut self, at: Time, node: NodeId) {
        self.push(at, Ev::Restart(node.0));
    }

    /// Suspends a running `node` at `at`. Does nothing if the node is not running.
    pub fn suspend(&mut self, at: Time, node: NodeId) {
        self.push(at, Ev::Suspend(node.0));
    }

    /// Resumes a suspended `node` at `at`. Does nothing if the node is not suspended.
    pub fn resume(&mut self, at: Time, node: NodeId) {
        self.push(at, Ev::Resume(node.0));
    }

    /// Brings interface `idx` of `node` up or down at `at`.
    pub fn set_iface_up(&mut self, at: Time, node: NodeId, idx: u32, up: bool) {
        let change = if up { IfaceChange::Up } else { IfaceChange::Down };
        self.push(
            at,
            Ev::Iface {
                node: node.0,
                idx,
                change,
            },
        );
    }

    /// Gives interface `idx` of `node` a new address at `at`.
    pub fn set_iface_addr(&mut self, at: Time, node: NodeId, idx: u32, ip: IpAddr) {
        self.push(
            at,
            Ev::Iface {
                node: node.0,
                idx,
                change: IfaceChange::Addr(ip),
            },
        );
    }

    /// Jumps the local clock of `node` by `delta` nanoseconds from time `at`; protocol timers are unaffected.
    pub fn clock_jump(&mut self, at: Time, node: NodeId, delta: i64) {
        let now = self.now;
        let slot = &mut self.nodes[node.index()];
        slot.clock.jumps.push((at, delta));
        slot.node.clock_changed(now, &slot.clock);
    }

    /// Sets the clock drift of `node` to `ppm` parts per million at `at`, keeping the reading continuous.
    pub fn clock_drift(&mut self, at: Time, node: NodeId, ppm: i64) {
        self.push(at, Ev::ClockDrift { node: node.0, ppm });
    }

    pub(crate) fn on_clock_drift(&mut self, t: Time, n: usize, ppm: i64) {
        let slot = &mut self.nodes[n];
        let old = slot.clock.drift_ppm;
        slot.clock.offset += (i128::from(t) * i128::from(old - ppm)).div_euclid(1_000_000) as i64;
        slot.clock.drift_ppm = ppm;
        slot.node.clock_changed(t, &slot.clock);
    }

    /// Changes the uplink, the downlink or both of a LAN at `at` (an outage, an MTU change, a bandwidth step, ...).
    pub fn lan_link_change(&mut self, at: Time, lan: LanId, dir: LanDir, change: LinkChange) {
        self.push(
            at,
            Ev::LanLink {
                lan: lan.0,
                dir,
                change: Box::new(change),
            },
        );
    }

    pub(crate) fn on_lan_link(&mut self, lan: usize, dir: LanDir, change: LinkChange) {
        let l = &mut self.lans[lan];
        if dir != LanDir::Down {
            l.up.apply(change.clone());
        }
        if dir != LanDir::Up {
            l.down.apply(change);
        }
    }

    /// Drops everything the LAN's links carry, in both directions, from `start` to `end`; no line time is used.
    pub fn lan_outage(&mut self, lan: LanId, start: Time, end: Time) {
        self.lan_link_change(start, lan, LanDir::Both, LinkChange::Blocked(true));
        self.lan_link_change(end, lan, LanDir::Both, LinkChange::Blocked(false));
    }

    /// Blocks or unblocks all UDP in and out of a LAN (a middlebox) at `at`.
    pub fn set_udp_block(&mut self, at: Time, lan: LanId, block: bool) {
        self.push(at, Ev::LanBlock { lan: lan.0, block });
    }

    /// A partition between LAN sets: a datagram from a LAN in `x` to one in `y` is dropped if its uplink send time is
    /// in `[from, to)`, after the uplink took it; also from `y` to `x` when `both`.
    pub fn partition_lans(&mut self, from: Time, to: Time, x: &[LanId], y: &[LanId], both: bool) {
        let ids = |v: &[LanId]| v.iter().map(|l| l.0).collect();
        self.lan_parts.push(LanPartition {
            from,
            to,
            x: ids(x),
            y: ids(y),
            both,
        });
    }

    /// Starts a spoofed flood from `host`.
    pub fn flood(&mut self, host: HostId, spec: FloodSpec) {
        let id = self.floods.len() as u32;
        let rng = R::derive(self.seed, Stream::Flood(id));
        let start = spec.start;
        self.floods.push(Flood {
            host: host.0,
            spec,
            sent: 0,
            rng,
        });
        self.push(start, Ev::FloodTick(id));
    }

    /// From `at`, re-sends the datagrams `observer` recorded at indexes `first..end`, one per `spacing`, from `host`
    /// with their original source and destination. The observer must keep payloads.
    pub fn replay(&mut self, at: Time, host: HostId, observer: ObsId, first: usize, end: usize, spacing: Time) {
        let id = self.replays.len() as u32;
        self.replays.push(Replay {
            host: host.0,
            obs: observer.0,
            next: first,
            end,
            spacing,
        });
        self.push(at, Ev::ReplayStep(id));
    }

    pub(crate) fn on_flood(&mut self, t: Time, i: usize) {
        let f = &mut self.floods[i];
        if f.spec.rate_pps == 0 || t >= f.spec.end || f.spec.spoof.is_empty() {
            return;
        }
        let src = f.spec.spoof[(f.sent % f.spec.spoof.len() as u64) as usize];
        let mut data = match &f.spec.payload {
            FloodPayload::Fixed(b) => b.clone(),
            FloodPayload::Random(n) => vec![0; *n],
        };
        if matches!(f.spec.payload, FloodPayload::Random(_)) {
            f.rng.fill(&mut data);
        }
        f.sent += 1;
        let next = f.spec.start + (u128::from(f.sent) * 1_000_000_000 / u128::from(f.spec.rate_pps)) as Time;
        let (host, dst) = (f.host, f.spec.dst);
        self.inject(t, host, src, dst, &data);
        self.push(next, Ev::FloodTick(i as u32));
    }

    pub(crate) fn on_replay(&mut self, t: Time, i: usize) {
        let r = &mut self.replays[i];
        let Some(rec) = self.observers[r.obs as usize].records.get(r.next) else {
            return;
        };
        let (Some(data), true) = (rec.payload.clone(), r.next < r.end) else {
            return;
        };
        let (src, dst, host, spacing) = (rec.src, rec.dst, r.host, r.spacing);
        r.next += 1;
        self.inject(t, host, src, dst, &data);
        self.push(t + spacing, Ev::ReplayStep(i as u32));
    }

    pub(crate) fn on_crash(&mut self, t: Time, n: usize) {
        let slot = &mut self.nodes[n];
        if slot.state == NodeState::Crashed {
            return;
        }
        slot.persisted = slot.node.crash(t);
        slot.state = NodeState::Crashed;
        slot.timer_gen += 1;
        slot.timer_at = None;
        slot.busy_until = 0;
        self.trace_line(format_args!("{{\"t\":{t},\"k\":\"crash\",\"n\":{n}}}"));
    }

    pub(crate) fn on_restart(&mut self, t: Time, n: usize) {
        let slot = &mut self.nodes[n];
        if slot.state != NodeState::Crashed {
            return;
        }
        slot.state = NodeState::Up;
        slot.busy_until = t;
        slot.portal_until = t + slot.portal_ns;
        slot.node.restart(t, &slot.persisted);
        self.trace_line(format_args!("{{\"t\":{t},\"k\":\"restart\",\"n\":{n}}}"));
        self.drive(n, t, t, false);
    }

    pub(crate) fn on_suspend(&mut self, t: Time, n: usize) {
        let slot = &mut self.nodes[n];
        if slot.state != NodeState::Up {
            return;
        }
        slot.node.suspend(t);
        slot.state = NodeState::Suspended;
        slot.timer_gen += 1;
        slot.timer_at = None;
        self.drain_events(n, t);
        self.trace_line(format_args!("{{\"t\":{t},\"k\":\"suspend\",\"n\":{n}}}"));
    }

    pub(crate) fn on_resume(&mut self, t: Time, n: usize) {
        let slot = &mut self.nodes[n];
        if slot.state != NodeState::Suspended {
            return;
        }
        slot.state = NodeState::Up;
        slot.node.resume(t);
        self.trace_line(format_args!("{{\"t\":{t},\"k\":\"resume\",\"n\":{n}}}"));
        self.drive(n, t, t, false);
    }

    pub(crate) fn on_iface(&mut self, t: Time, n: usize, idx: usize, change: IfaceChange) {
        let old = self.nodes[n].ifaces[idx].addr;
        let via = self.nodes[n].ifaces[idx].via;
        let site = self.nodes[n].ifaces[idx].site;
        let event = match change {
            IfaceChange::Up => {
                self.nodes[n].ifaces[idx].up = true;
                IfaceEvent::Up(old)
            }
            IfaceChange::Down => {
                self.nodes[n].ifaces[idx].up = false;
                IfaceEvent::Down(old)
            }
            IfaceChange::Addr(new) => {
                self.nodes[n].ifaces[idx].addr = new;
                if let Some(nat) = via {
                    let lan = &mut self.nats[nat as usize].lan_map;
                    lan.remove(&old);
                    lan.insert(new, site);
                } else {
                    self.addr_map.remove(&old);
                    self.addr_map.insert(new, site);
                }
                IfaceEvent::Changed { old, new }
            }
        };
        self.trace_line(format_args!(
            "{{\"t\":{t},\"k\":\"iface\",\"n\":{n},\"i\":{idx},\"e\":\"{event:?}\"}}"
        ));
        if self.nodes[n].state == NodeState::Up {
            self.nodes[n].node.iface_event(t, event);
            self.drive(n, t, t, false);
        }
    }

    pub(crate) fn on_partition(&mut self, t: Time, groups: &[(u32, u32)]) {
        let parts = groups.iter().map(|g| g.1).max().unwrap_or(0);
        for s in &mut self.nodes {
            s.group = 0;
        }
        for (n, g) in groups {
            self.nodes[*n as usize].group = *g;
        }
        self.trace_line(format_args!("{{\"t\":{t},\"k\":\"partition\",\"groups\":{parts}}}"));
    }

    pub(crate) fn on_nat_rebind(&mut self, t: Time, nat: usize, ip: Option<IpAddr>) {
        let old = self.nats[nat].nat.cfg.ext_ip;
        self.nats[nat].nat.rebind(ip);
        if let Some(new) = ip {
            let site = self.nats[nat].site;
            self.addr_map.remove(&old);
            self.addr_map.insert(new, site);
        }
        self.trace_line(format_args!("{{\"t\":{t},\"k\":\"nat_rebind\",\"nat\":{nat}}}"));
    }
}
