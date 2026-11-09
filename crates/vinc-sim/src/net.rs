//! The path of a datagram: from a node's interface across NATs, links and LANs to the receiving node.
//!
//! A datagram sent from a LAN goes, in one step: v6 firewall bookkeeping, NAT translation, middlebox check, the LAN
//! uplink, destination lookup, partition check; then an event at uplink exit plus the region delay enters the
//! destination LAN's downlink; an event at downlink exit delivers it (NAT inbound, firewall, middlebox, node).
//! Interfaces without a LAN use pair links between sites instead. Datagram buffers live in a slab and are recycled,
//! so a steady run allocates nothing per datagram.

use std::collections::btree_map::Entry as MapEntry;
use std::net::SocketAddr;

use crate::Time;
use crate::config::{Call, CostModel, NodeState};
use crate::link::{Fate, Link, LinkConfig};
use crate::metrics::DropReason;
use crate::node::Node;
use crate::rng::{Random, Stream};
use crate::sim::{Ev, POOL_MAX, Packet, Sim, SiteKind};

/// Remotes the stateful IPv6 firewall remembers per host.
const FW_REMOTES: usize = 256;

impl<N: Node, R: Random, C: CostModel> Sim<N, R, C> {
    pub(crate) fn alloc_pkt(
        &mut self,
        src: SocketAddr,
        dst: SocketAddr,
        data: &[u8],
        origin: Option<u32>,
        sent_at: Time,
    ) -> u32 {
        let mut buf = self.pool.pop().unwrap_or_default();
        buf.clear();
        buf.extend_from_slice(data);
        let p = Packet {
            src,
            dst,
            data: buf,
            origin,
            sent_at,
        };
        if let Some(i) = self.free_pkts.pop() {
            self.pkts[i as usize] = Some(p);
            i
        } else {
            self.pkts.push(Some(p));
            (self.pkts.len() - 1) as u32
        }
    }

    pub(crate) fn recycle(&mut self, pkt: u32, p: Packet) {
        self.free_pkts.push(pkt);
        if self.pool.len() < POOL_MAX {
            self.pool.push(p.data);
        }
    }

    fn count_drop(&mut self, t: Time, why: DropReason, len: usize) {
        self.metrics.drops[why as usize] += 1;
        if self.cfg.trace_packets {
            let name = why.name();
            self.trace_line(format_args!(
                "{{\"t\":{t},\"k\":\"drop\",\"why\":\"{name}\",\"len\":{len}}}"
            ));
        }
    }

    pub(crate) fn drop_pkt(&mut self, t: Time, pkt: u32, why: DropReason) {
        let Some(p) = self.pkts[pkt as usize].take() else {
            return;
        };
        self.count_drop(t, why, p.data.len());
        self.recycle(pkt, p);
    }

    /// The pair link from `from` to `to`, created from the default link if it does not exist yet.
    pub(crate) fn link_entry(&mut self, from: u32, to: u32) -> Option<&mut Link<R>> {
        match self.links.entry((from, to)) {
            MapEntry::Occupied(e) => Some(e.into_mut()),
            MapEntry::Vacant(v) => {
                let cfg: LinkConfig = self.cfg.default_link.clone()?;
                Some(v.insert(Link::new(cfg, R::derive(self.seed, Stream::Link { from, to }))))
            }
        }
    }

    /// The LAN a site's datagrams leave through, if any.
    fn lan_of(&self, site: u32) -> Option<u32> {
        match self.sites[site as usize] {
            SiteKind::Iface { node, idx } => {
                let i = &self.nodes[node as usize].ifaces[idx as usize];
                i.via.map_or(i.lan, |n| self.nats[n as usize].lan)
            }
            SiteKind::Nat(n) => self.nats[n as usize].lan,
            SiteKind::Host(_) | SiteKind::LanDown(_) => None,
        }
    }

    /// The first site a datagram for `ip` reaches: its LAN's downlink if it has one, else its owner.
    fn entry_for(&self, ip: std::net::IpAddr) -> Option<(u32, u32)> {
        let owner = *self.addr_map.get(&ip)?;
        Some((
            owner,
            self.lan_of(owner).map_or(owner, |l| self.lans[l as usize].down_site),
        ))
    }

    /// A node hands a datagram to the network at time `t0` through the interface owning `local`'s address.
    pub(crate) fn emit(&mut self, n: usize, t0: Time, local: SocketAddr, remote: SocketAddr, data: &[u8]) {
        let Some(ii) = self.nodes[n].ifaces.iter().position(|i| i.up && i.addr == local.ip()) else {
            self.count_drop(t0, DropReason::NoIface, data.len());
            return;
        };
        let (site, imtu) = (self.nodes[n].ifaces[ii].site, self.nodes[n].ifaces[ii].mtu);
        let hdr = if local.is_ipv4() { 28 } else { 48 };
        let mtu = self
            .lan_of(site)
            .map_or(usize::MAX, |l| self.lans[l as usize].cfg.mtu.saturating_sub(hdr))
            .min(imtu);
        if data.len() > mtu {
            self.count_drop(t0, DropReason::Mtu, data.len());
            return;
        }
        let m = &mut self.metrics.nodes[n];
        m.sent_packets += 1;
        m.sent_bytes += data.len() as u64;
        m.wire_bytes += (data.len() + hdr) as u64;
        if self.cfg.trace_packets {
            let len = data.len();
            self.trace_line(format_args!("{{\"t\":{t0},\"k\":\"tx\",\"n\":{n},\"len\":{len}}}"));
        }
        let (via, lan) = (self.nodes[n].ifaces[ii].via, self.nodes[n].ifaces[ii].lan);
        if let (None, Some(l), false) = (via, lan, local.is_ipv4()) {
            let fw = &mut self.lans[l as usize];
            if fw.cfg.v6_firewall {
                let set = fw.fw.entry(local.ip()).or_default();
                if set.len() < FW_REMOTES || set.contains(&remote) {
                    set.insert(remote);
                }
            }
        }
        let pkt = self.alloc_pkt(local, remote, data, Some(n as u32), t0);
        self.route_from(t0, site, pkt);
    }

    /// Sends the datagram on from `site`: through its NAT and LAN uplink, or over a pair link.
    pub(crate) fn route_from(&mut self, t: Time, site: u32, pkt: u32) {
        match self.sites[site as usize] {
            SiteKind::Iface { node, idx } => {
                let i = &self.nodes[node as usize].ifaces[idx as usize];
                match (i.via, i.lan) {
                    (Some(nat), _) => self.nat_step(t, nat as usize, pkt),
                    (None, Some(l)) => self.lan_up(t, l as usize, pkt),
                    (None, None) => self.pair_forward(t, site, pkt),
                }
            }
            SiteKind::Nat(n) => match self.nats[n as usize].lan {
                Some(l) => self.lan_up(t, l as usize, pkt),
                None => self.pair_forward(t, site, pkt),
            },
            SiteKind::Host(_) => self.pair_forward(t, site, pkt),
            SiteKind::LanDown(_) => {}
        }
    }

    fn pair_forward(&mut self, t: Time, from: u32, pkt: u32) {
        let Some(dst) = self.pkts[pkt as usize].as_ref().map(|p| p.dst.ip()) else {
            return;
        };
        let Some((_, entry)) = self.entry_for(dst) else {
            self.drop_pkt(t, pkt, DropReason::NoRoute);
            return;
        };
        let Some(len) = self.pkts[pkt as usize].as_ref().map(|p| p.data.len()) else {
            return;
        };
        let Some(link) = self.link_entry(from, entry) else {
            self.drop_pkt(t, pkt, DropReason::NoRoute);
            return;
        };
        let (fate, obs) = (link.send(t, len), link.observer);
        self.finish_hop(t, pkt, entry, fate, obs, 0);
    }

    /// Records, duplicates and schedules a datagram a link accepted, or drops it.
    fn finish_hop(&mut self, t: Time, pkt: u32, to: u32, fate: Fate, obs: Option<u32>, extra: Time) {
        match fate {
            Fate::Drop(why) => self.drop_pkt(t, pkt, why),
            Fate::Sent { at, dup_at } => {
                if let (Some(o), Some(p)) = (obs, self.pkts[pkt as usize].as_ref()) {
                    self.observers[o as usize].record(t, p.src, p.dst, &p.data);
                }
                if let (Some(d), Some(p)) = (dup_at, self.pkts[pkt as usize].as_ref()) {
                    let (src, dst, origin, sent_at) = (p.src, p.dst, p.origin, p.sent_at);
                    let data = p.data.clone();
                    let copy = self.alloc_pkt(src, dst, &data, origin, sent_at);
                    self.metrics.duplicated += 1;
                    self.push(d + extra, Ev::Arrive { site: to, pkt: copy });
                }
                self.push(at + extra, Ev::Arrive { site: to, pkt });
            }
        }
    }

    /// The middlebox and uplink stages of a LAN, then lookup, partition and the region delay.
    fn lan_up(&mut self, t: Time, l: usize, pkt: u32) {
        let Some(p) = self.pkts[pkt as usize].as_ref() else {
            return;
        };
        let (len, dst, origin) = (p.data.len(), p.dst.ip(), p.origin);
        let portal = origin.is_some_and(|o| self.nodes[o as usize].portal_until > t);
        if portal || self.lans[l].cfg.udp_block {
            self.drop_pkt(t, pkt, DropReason::Middlebox);
            return;
        }
        let up = &mut self.lans[l].up;
        let (fate, obs) = (up.send(t, len), up.observer);
        let Some((owner, entry)) = self.entry_for(dst) else {
            // The uplink already took the datagram: an unknown host is dropped after it.
            match fate {
                Fate::Drop(why) => self.drop_pkt(t, pkt, why),
                Fate::Sent { .. } => self.drop_pkt(t, pkt, DropReason::NoRoute),
            }
            return;
        };
        if matches!(fate, Fate::Sent { .. }) && self.partitioned(t, l as u32, self.lan_of(owner)) {
            self.drop_pkt(t, pkt, DropReason::Partition);
            return;
        }
        let rd = self.lan_of(owner).map_or(0, |dl| {
            self.region_delay
                .get(&(self.lans[l].cfg.region, self.lans[dl as usize].cfg.region))
                .copied()
                .unwrap_or(0)
        });
        self.finish_hop(t, pkt, entry, fate, obs, rd);
    }

    fn partitioned(&self, t: Time, from: u32, to: Option<u32>) -> bool {
        let Some(to) = to else { return false };
        self.lan_parts.iter().any(|p| {
            (p.from..p.to).contains(&t)
                && ((p.x.contains(&from) && p.y.contains(&to)) || (p.both && p.y.contains(&from) && p.x.contains(&to)))
        })
    }

    /// Leaves the destination LAN's downlink toward the owner of the destination address.
    fn lan_down(&mut self, t: Time, l: usize, pkt: u32) {
        let Some(p) = self.pkts[pkt as usize].as_ref() else {
            return;
        };
        let (len, dst) = (p.data.len(), p.dst.ip());
        let down = &mut self.lans[l].down;
        let (fate, obs) = (down.send(t, len), down.observer);
        let Some(owner) = self.addr_map.get(&dst).copied() else {
            self.drop_pkt(t, pkt, DropReason::NoRoute);
            return;
        };
        self.finish_hop(t, pkt, owner, fate, obs, 0);
    }

    pub(crate) fn on_arrive(&mut self, t: Time, site: u32, pkt: u32) {
        match self.sites[site as usize] {
            SiteKind::Iface { node, idx } => self.deliver(t, node as usize, idx as usize, pkt),
            SiteKind::Nat(n) => self.nat_step(t, n as usize, pkt),
            SiteKind::LanDown(l) => self.lan_down(t, l as usize, pkt),
            SiteKind::Host(h) => {
                self.hosts[h as usize].received += 1;
                if let Some(p) = self.pkts[pkt as usize].take() {
                    self.recycle(pkt, p);
                }
            }
        }
    }

    /// Translates at a NAT: inbound if addressed to its public address, otherwise outbound from a private host.
    fn nat_step(&mut self, t: Time, n: usize, pkt: u32) {
        let Some(p) = self.pkts[pkt as usize].as_ref() else {
            return;
        };
        let (src, dst) = (p.src, p.dst);
        if dst.ip() == self.nats[n].nat.cfg.ext_ip {
            let public_src = self
                .addr_map
                .get(&src.ip())
                .is_some_and(|s| match self.sites[*s as usize] {
                    SiteKind::Iface { node, idx } => self.nodes[node as usize].ifaces[idx as usize].via.is_none(),
                    SiteKind::Host(_) => true,
                    _ => false,
                });
            let Some(int) = self.nats[n].nat.inbound(t, dst.port(), src, public_src) else {
                self.drop_pkt(t, pkt, DropReason::NatFilter);
                return;
            };
            if let Some(p) = self.pkts[pkt as usize].as_mut() {
                p.dst = int;
            }
            match self.nats[n].lan_map.get(&int.ip()).copied() {
                Some(s) => self.on_arrive(t, s, pkt),
                None => self.drop_pkt(t, pkt, DropReason::NoRoute),
            }
        } else {
            let ext = self.nats[n].nat.outbound(t, src, dst);
            if let Some(p) = self.pkts[pkt as usize].as_mut() {
                p.src = ext;
            }
            let site = self.nats[n].site;
            self.route_from(t, site, pkt);
        }
    }

    fn deliver(&mut self, t: Time, n: usize, idx: usize, pkt: u32) {
        let Some(p) = self.pkts[pkt as usize].as_ref() else {
            return;
        };
        let slot = &self.nodes[n];
        let iface = &slot.ifaces[idx];
        let lan = iface.lan.map(|l| &self.lans[l as usize]);
        let firewalled = lan.is_some_and(|l| {
            l.cfg.v6_firewall && p.dst.is_ipv6() && !l.fw.get(&p.dst.ip()).is_some_and(|s| s.contains(&p.src))
        });
        let why = match slot.state {
            NodeState::Crashed => Some(DropReason::NodeDown),
            NodeState::Suspended => Some(DropReason::NodeAsleep),
            NodeState::Up if !iface.up || iface.addr != p.dst.ip() => Some(DropReason::NoIface),
            NodeState::Up if firewalled => Some(DropReason::NatFilter),
            NodeState::Up if slot.portal_until > t || lan.is_some_and(|l| l.cfg.udp_block) => {
                Some(DropReason::Middlebox)
            }
            NodeState::Up => p
                .origin
                .filter(|o| self.nodes[*o as usize].group != slot.group)
                .map(|_| DropReason::Partition),
        };
        if let Some(why) = why {
            self.drop_pkt(t, pkt, why);
            return;
        }
        let Some(mut p) = self.pkts[pkt as usize].take() else {
            return;
        };
        let len = p.data.len();
        let keep = self.cfg.latency_samples;
        let m = &mut self.metrics.nodes[n];
        m.recv_packets += 1;
        m.recv_bytes += len as u64;
        m.latency.record(t - p.sent_at, keep);
        if self.cfg.trace_packets {
            self.trace_line(format_args!("{{\"t\":{t},\"k\":\"rx\",\"n\":{n},\"len\":{len}}}"));
        }
        self.nodes[n].node.handle_datagram(t, p.dst, p.src, &mut p.data);
        self.recycle(pkt, p);
        let send_at = self.finish_call(n, t, Call::Datagram, len);
        self.drive(n, t, send_at, false);
    }

    /// Injects a datagram from an adversary host, with any source address it likes.
    pub(crate) fn inject(&mut self, t: Time, host: u32, src: SocketAddr, dst: SocketAddr, data: &[u8]) {
        self.metrics.injected += 1;
        let pkt = self.alloc_pkt(src, dst, data, None, t);
        let site = self.hosts[host as usize].site;
        self.route_from(t, site, pkt);
    }
}
