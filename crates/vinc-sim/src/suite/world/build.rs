//! The shared builder of the reference generators: sites, NATs, interfaces and the three standard node classes.
//!
//! Invariant: the builder draws from the world's generator in exactly the order the reference `Builder` does
//! (NAT class, NAT timeout, IPv6 flags, then the site's delay, loss and burst), and the numeric ids it hands out
//! (sites, NATs, public addresses) count up in the same order.

use std::collections::BTreeMap;

use super::WorldError;
use super::model::{Addr, IfaceSpec, Intent, IntentKind, Must, NatSpec, NodeSpec, Param, Params, Site, World};
use super::params::ParamsExt;
use crate::reference::PyRandom;

pub(super) const NS: u64 = 1_000_000_000;
pub(super) const MS: u64 = 1_000_000;
pub(super) const KIB: u64 = 1024;
pub(super) const MIB: u64 = 1024 * KIB;

/// The one-way delay between the three regions, nanoseconds.
pub(super) fn region_delay() -> Vec<Vec<u64>> {
    vec![
        vec![2 * MS, 40 * MS, 90 * MS],
        vec![40 * MS, 2 * MS, 60 * MS],
        vec![90 * MS, 60 * MS, 2 * MS],
    ]
}

/// `int(x * unit)`: the float product truncated toward zero.
pub(super) fn scaled(x: f64, unit: u64) -> u64 {
    (x * unit as f64) as u64
}

/// A UDP mapping timeout drawn from the measured distribution (`nat_timeout`).
pub(super) fn nat_timeout(rng: &mut PyRandom, cellular: bool) -> u64 {
    let u = rng.random();
    let (lo, hi) = if cellular {
        if u < 0.48 {
            (20.0, 60.0)
        } else if u < 0.5 {
            (60.0, 65.0)
        } else {
            (65.0, 200.0)
        }
    } else if u < 0.5 {
        (10.0, 35.0)
    } else if u < 0.98 {
        (35.0, 60.0)
    } else {
        (60.0, 200.0)
    };
    scaled(rng.uniform(lo, hi), NS)
}

/// The NAT class of a home router (`home_nat`).
pub(super) fn home_nat(rng: &mut PyRandom) -> (&'static str, &'static str) {
    let u = rng.random();
    if u < 0.02 {
        ("edm", "apdf")
    } else if u < 0.30 {
        ("eim", "eif")
    } else if u < 0.55 {
        ("eim", "adf")
    } else {
        ("eim", "apdf")
    }
}

/// The NAT class of a carrier (`carrier_nat`).
pub(super) fn carrier_nat(rng: &mut PyRandom) -> (&'static str, &'static str) {
    let u = rng.random();
    if u < 0.40 {
        ("edm", "apdf")
    } else if u < 0.60 {
        ("eim", "eif")
    } else {
        ("eim", "apdf")
    }
}

/// `choice(seq)`.
pub(super) fn choice<T: Copy>(rng: &mut PyRandom, xs: &[T], what: &'static str) -> Result<T, WorldError> {
    rng.choice_index(xs.len()).map(|i| xs[i]).ok_or(WorldError::Empty(what))
}

/// `sample(xs, k)`.
pub(super) fn sample<T: Clone>(
    rng: &mut PyRandom,
    xs: &[T],
    k: usize,
    what: &'static str,
) -> Result<Vec<T>, WorldError> {
    let idx = rng.sample_indices(xs.len(), k).ok_or(WorldError::Empty(what))?;
    Ok(idx.into_iter().map(|i| xs[i].clone()).collect())
}

/// `randrange(n)` for a length, which the reference raises on when empty.
pub(super) fn below(rng: &mut PyRandom, n: usize, what: &'static str) -> Result<usize, WorldError> {
    rng.choice_index(n).ok_or(WorldError::Empty(what))
}

/// The arguments of [`Builder::site`].
pub(super) struct SiteArgs {
    pub region: usize,
    pub up_bps: u64,
    pub down_bps: u64,
    pub delay_ns: u64,
    pub loss: f64,
    pub burst_ns: u64,
    pub nats: Vec<NatSpec>,
    pub v6_open: bool,
    pub queue: Option<u64>,
}

/// The reference `Builder`: the generator, the parameters and the id counters.
pub(super) struct Builder {
    /// The parameters of the run.
    pub p: Params,
    /// The scenario generator.
    pub rng: PyRandom,
    next_nat: usize,
    next_ip: u64,
}

impl Builder {
    pub(super) fn new(p: Params, seed: u64) -> Self {
        Self {
            p,
            rng: PyRandom::from_seed(u128::from(seed)),
            next_nat: 0,
            next_ip: 1_000_000,
        }
    }

    /// `_pick(rng, p[key])`: a uniform draw from the pair `p[key]`.
    pub(super) fn pick(&mut self, key: &str) -> Result<f64, WorldError> {
        let (lo, hi) = self.p.pair(key)?;
        Ok(self.rng.uniform(lo, hi))
    }

    /// Adds a site to the world and returns its number.
    pub(super) fn site(&mut self, w: &mut World, a: SiteArgs) -> Result<usize, WorldError> {
        let sid = w.sites.len();
        let queue_bytes = a
            .queue
            .filter(|q| *q != 0)
            .unwrap_or_else(|| (64 * KIB).max((a.down_bps as f64 / 8.0 * 0.25) as u64));
        w.sites.push(Site {
            sid,
            region: a.region,
            up_bps: a.up_bps,
            down_bps: a.down_bps,
            up_delay_ns: a.delay_ns,
            down_delay_ns: a.delay_ns,
            loss: a.loss,
            burst_ns: a.burst_ns,
            queue_bytes,
            nats: a.nats,
            v6_open: a.v6_open,
            mtu: u32::try_from(self.p.int_or("mtu", 1500)?).unwrap_or(1500),
            middlebox: None,
        });
        Ok(sid)
    }

    /// A NAT with the next number.
    pub(super) fn nat(&mut self, mapping: &str, filtering: &str, timeout_ns: u64) -> Result<NatSpec, WorldError> {
        self.next_nat += 1;
        Ok(NatSpec {
            nid: self.next_nat,
            ext_ip: 2_000_000 + self.next_nat as u64,
            mapping: mapping.to_string(),
            filtering: filtering.to_string(),
            timeout_ns,
            no_punch: self.p.flag_or("no_punch", false)?,
            tcp_timeout_ns: None,
        })
    }

    /// The interfaces of a node: four public ones, or the private ones of a site's host.
    pub(super) fn ifaces(&mut self, sid: usize, idx: usize, v6: bool, public: bool) -> Vec<IfaceSpec> {
        let mtu = 1500 - 28;
        let mk = |name: &str, kind: &str, a: &str, host: u64, port: u16, mtu: u64| IfaceSpec {
            name: name.to_string(),
            kind: kind.to_string(),
            addr: Addr {
                kind: a.to_string(),
                host,
                port,
            },
            mtu,
            public: false,
            v6: false,
        };
        if public {
            let ip = self.next_ip;
            self.next_ip += 1;
            return vec![
                IfaceSpec {
                    public: true,
                    ..mk("u4", "udp4", "udp4", ip, 4433, mtu)
                },
                IfaceSpec {
                    public: true,
                    ..mk("u6", "udp6", "udp6", 5_000_000 + idx as u64, 4433, 1500 - 48)
                },
                IfaceSpec {
                    public: true,
                    ..mk("t", "tcp", "tcp4", ip, 443, 1 << 20)
                },
                IfaceSpec {
                    public: true,
                    ..mk("w", "ws", "tcp4", ip, 8443, 1 << 20)
                },
            ];
        }
        let host = 3_000_000 + sid as u64 * 256 + (idx as u64 % 250);
        let mut out = vec![mk("u4", "udp4", "udp4", host, 4433, mtu)];
        if v6 {
            out.push(IfaceSpec {
                v6: true,
                ..mk("u6", "udp6", "udp6", 6_000_000 + idx as u64 * 1000, 4433, 1500 - 48)
            });
        }
        out.push(mk("t", "tcp", "tcp4", host, 50000, 1 << 20));
        out.push(mk("w", "ws", "tcp4", host, 50001, 1 << 20));
        out
    }

    fn node(device: &str, kind: &str, site: usize, region: usize, ifaces: Vec<IfaceSpec>) -> NodeSpec {
        NodeSpec {
            device: device.to_string(),
            site,
            kind: kind.to_string(),
            region,
            ifaces,
            topics: Vec::new(),
            sites: Vec::new(),
            clock: None,
            cpu_factor: None,
        }
    }

    /// A cloud node on a 10 Gbit/s site.
    pub(super) fn add_cloud(&mut self, w: &mut World, region: usize) -> Result<usize, WorldError> {
        let sid = self.site(
            w,
            SiteArgs {
                region,
                up_bps: 10_000_000_000,
                down_bps: 10_000_000_000,
                delay_ns: 100_000,
                loss: 0.0,
                burst_ns: MS,
                nats: Vec::new(),
                v6_open: false,
                queue: Some(8 * MIB),
            },
        )?;
        let idx = w.nodes.len();
        let ifaces = self.ifaces(sid, idx, true, true);
        w.nodes.push(Self::node("cloud", "cloud", sid, region, ifaces));
        Ok(idx)
    }

    /// A home node behind a home NAT.
    pub(super) fn add_home(
        &mut self,
        w: &mut World,
        region: usize,
        down: Option<u64>,
        up: Option<u64>,
    ) -> Result<usize, WorldError> {
        let (m, f) = home_nat(&mut self.rng);
        let timeout = nat_timeout(&mut self.rng, false);
        let nat = self.nat(m, f, timeout)?;
        let v6 = self.rng.random() < self.p.num("v6_share")?;
        let v6_open = v6 && self.rng.random() < self.p.num("v6_open_share")?;
        let delay_ns = scaled(self.rng.uniform(3.0, 12.0), MS);
        let loss = self.p.num("home_loss")?;
        let burst_ns = scaled(self.pick("burst_ms")?, MS);
        let sid = self.site(
            w,
            SiteArgs {
                region,
                up_bps: up.filter(|x| *x != 0).unwrap_or(10_000_000),
                down_bps: down.filter(|x| *x != 0).unwrap_or(50_000_000),
                delay_ns,
                loss,
                burst_ns,
                nats: vec![nat],
                v6_open,
                queue: None,
            },
        )?;
        let idx = w.nodes.len();
        let ifaces = self.ifaces(sid, idx, v6, false);
        w.nodes.push(Self::node("desktop", "home", sid, region, ifaces));
        Ok(idx)
    }

    /// A mobile node behind a carrier NAT, with a home Wi-Fi site when the scenario hands over.
    pub(super) fn add_mobile(&mut self, w: &mut World, region: usize) -> Result<usize, WorldError> {
        let (m, f) = carrier_nat(&mut self.rng);
        let timeout = nat_timeout(&mut self.rng, true);
        let nat = self.nat(m, f, timeout)?;
        let loss = match self.p.get("mobile_loss") {
            Some(Param::Range { .. }) => self.pick("mobile_loss")?,
            _ => self.p.num("mobile_loss")?,
        };
        let delay_ns = scaled(self.pick("mobile_delay_ms")?, MS);
        let v6 = self.rng.random() < self.p.num("v6_share")?;
        let burst_ns = scaled(self.pick("burst_ms")?, MS);
        let sid = self.site(
            w,
            SiteArgs {
                region,
                up_bps: 3_000_000,
                down_bps: 10_920_000,
                delay_ns,
                loss,
                burst_ns,
                nats: vec![nat],
                v6_open: false,
                queue: None,
            },
        )?;
        let idx = w.nodes.len();
        let ifaces = self.ifaces(sid, idx, v6, false);
        let mut node = Self::node("phone", "mobile", sid, region, ifaces);
        node.sites.push(sid);
        if self.p.truthy("handover_every_s") {
            let (hm, hf) = home_nat(&mut self.rng);
            let htimeout = nat_timeout(&mut self.rng, false);
            let hn = self.nat(hm, hf, htimeout)?;
            let delay_ns = scaled(self.rng.uniform(4.0, 15.0), MS);
            let loss = self.p.num("home_loss")?;
            let burst_ns = scaled(self.pick("burst_ms")?, MS);
            let wid = self.site(
                w,
                SiteArgs {
                    region,
                    up_bps: 10_000_000,
                    down_bps: 50_000_000,
                    delay_ns,
                    loss,
                    burst_ns,
                    nats: vec![hn],
                    v6_open: false,
                    queue: None,
                },
            )?;
            node.sites.push(wid);
        }
        w.nodes.push(node);
        Ok(idx)
    }
}

/// A world with the fields every scenario starts from (`_base`, and the head of the slice `generate`).
pub(super) fn blank_world(id: &str, p: &Params, seed: u64) -> Result<World, WorldError> {
    let secs = |key: &str| -> Result<(u64, u64), WorldError> {
        let (lo, hi) = p.int_pair(key)?;
        Ok((lo as u64 * NS, hi as u64 * NS))
    };
    Ok(World {
        id: id.to_string(),
        seed,
        params: p.clone(),
        sites: Vec::new(),
        nodes: Vec::new(),
        region_delay_ns: region_delay(),
        bootstrap: Vec::new(),
        duration_ns: p.int("duration_s")? as u64 * NS,
        idle_window: secs("idle_s")?,
        env: Vec::new(),
        intents: Vec::new(),
        values: BTreeMap::default(),
        provides: BTreeMap::default(),
        changes: Vec::new(),
        denied: Vec::new(),
        revoked: Vec::new(),
        connect_deadline_ns: 30 * NS,
        acp_latency_ns: 100_000,
        acp_validity_ns: 60 * NS,
        revocation_bound_cap_ns: 5 * NS,
        awareness_bound_cap_ns: 150 * NS,
        false_suspicion_cap: 1.0,
        score_c3: id == "S3",
        clouds: Vec::new(),
        homes: Vec::new(),
        mobiles: Vec::new(),
        hostile: Vec::new(),
        browsers: Vec::new(),
        liars: Vec::new(),
        soak: false,
        partitions: Vec::new(),
        adversary: None,
        adversary_env: Vec::new(),
        compromise: Vec::new(),
        compromise_node: None,
        eclipse_victim: None,
        sets: BTreeMap::default(),
        set_profiles: BTreeMap::default(),
        load_used: BTreeMap::default(),
    })
}

/// `_finish`: sets the node classes and the bootstrap nodes.
pub(super) fn finish(w: &mut World, clouds: Vec<usize>, homes: Vec<usize>, mobiles: Vec<usize>) {
    w.bootstrap = clouds.iter().take(3).copied().collect();
    w.clouds = clouds;
    w.homes = homes;
    w.mobiles = mobiles;
}

/// The final stable sorts of every generator: environment by `(time, name)`, intents by `(time, node)`.
pub(super) fn sort_world(w: &mut World) {
    w.env.sort_by_key(|e| (e.t, e.kind));
    w.intents.sort_by_key(|d| (d.t, d.node));
}

impl Intent {
    /// An intent with only the fields every intent has; the generator sets the rest.
    pub(super) fn new(t: u64, node: usize, kind: IntentKind, deadline_ns: u64, must: Must) -> Self {
        Self {
            t,
            node,
            kind,
            to: None,
            topic: None,
            size: None,
            req: None,
            resp: None,
            deadline_ns,
            receivers: Vec::new(),
            must,
            value: None,
            providers: Vec::new(),
            ranges: Vec::new(),
            stream_rate: None,
            probe: false,
            under_bulk: false,
            set_ref: None,
        }
    }
}
