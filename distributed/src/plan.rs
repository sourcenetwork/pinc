//! The network plan of a scenario: every address, interface, route, translation rule, shaper and CPU set, computed
//! before anything is created, as plain data and command lines.
//!
//! The layout (backend a; backend b reuses the shaping part):
//! - Site `i` has the LAN `10.<i+1>.0.0/24`. Its router holds a bridge `lan` with `10.<i+1>.0.1`; node `j` of the
//!   site has `10.<i+1>.0.<j+2>` on its `eth0`, joined to the bridge through the router's port `p<j>`.
//! - Link `k` between two routers is a /30 from `100.64.0.0/10`: `w<k>` on both routers.
//! - Every router routes every routed LAN and every link subnet over the path of fewest links (least delay between
//!   equals). A site behind address
//!   translation is not routed: its router masquerades the LAN out of its links.
//! - Shaping happens only in routers, on packets that are already MTU-sized: a node's `eth0` segments every
//!   offloaded batch before it leaves the node (`gso_max_segs 1`), so a shaper never loses a whole batch at once.
//!   The node-to-router direction of an access link is shaped on the ingress of the router's port, redirected
//!   through an `ifb` device `u<j>`; the router-to-node direction on the port's egress; each direction of a link
//!   between routers on the sending router's `w<k>`.
//!
//! Invariants: names fit the kernel's 15 bytes; every address is unique; every node's CPU set is the same for every
//! stack of a run; the plan is a pure function of the scenario, the run id and the host's CPUs.

use std::collections::BTreeMap;
use std::net::Ipv4Addr;

use crate::scenario::{Nat, Role, Scenario, Shape};

/// The interface MTU everywhere.
pub const MTU: u32 = 1500;
/// The label every container of a run carries, with the run id as its value.
pub const LABEL: &str = "vinc.distributed";
/// What a router container gets.
pub const ROUTER_MEMORY_MIB: u32 = 128;

/// A network namespace of the plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Ns {
    /// The router of site `i`.
    Router(usize),
    /// Node `i`.
    Node(usize),
}

/// A tool a plan command runs as root in a namespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tool {
    /// `ip`.
    Ip,
    /// `tc`.
    Tc,
    /// `iptables`.
    Iptables,
    /// `sysctl`.
    Sysctl,
}

impl Tool {
    /// The program's name.
    pub fn program(self) -> &'static str {
        match self {
            Self::Ip => "ip",
            Self::Tc => "tc",
            Self::Iptables => "iptables",
            Self::Sysctl => "sysctl",
        }
    }
}

/// One command line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cmd {
    /// The program.
    pub tool: Tool,
    /// Its arguments.
    pub args: Vec<String>,
}

impl Cmd {
    fn new(tool: Tool, args: &[&str]) -> Self {
        Self {
            tool,
            args: args.iter().map(|s| (*s).to_owned()).collect(),
        }
    }

    /// The command as one line, for logs and the infrastructure record.
    pub fn line(&self) -> String {
        format!("{} {}", self.tool.program(), self.args.join(" "))
    }
}

/// A container to start.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Container {
    /// The container's name.
    pub name: String,
    /// The CPUs it may use (`--cpuset-cpus`).
    pub cpus: String,
    /// Its memory limit.
    pub memory_mib: u32,
}

/// A site.
#[derive(Debug, Clone, PartialEq)]
pub struct SitePlan {
    /// The site's name.
    pub name: String,
    /// Its translation.
    pub nat: Nat,
    /// The LAN's network address (a /24).
    pub lan: Ipv4Addr,
    /// The router's address on the LAN.
    pub gateway: Ipv4Addr,
    /// The router's container.
    pub router: Container,
}

/// A node.
#[derive(Debug, Clone, PartialEq)]
pub struct NodePlan {
    /// The node's name.
    pub name: String,
    /// Index of its site.
    pub site: usize,
    /// Its role.
    pub role: Role,
    /// Its address.
    pub ip: Ipv4Addr,
    /// The router's port facing it.
    pub port: String,
    /// The `ifb` device that shapes what it sends.
    pub ifb: String,
    /// Its access link (both directions).
    pub link: Shape,
    /// Its container.
    pub container: Container,
}

/// A link between two routers.
#[derive(Debug, Clone, PartialEq)]
pub struct LinkPlan {
    /// Site of the first end.
    pub a: usize,
    /// Site of the second end.
    pub b: usize,
    /// The interface on both routers.
    pub dev: String,
    /// The first end's address.
    pub ip_a: Ipv4Addr,
    /// The second end's address.
    pub ip_b: Ipv4Addr,
    /// The a-to-b direction.
    pub forward: Shape,
    /// The b-to-a direction.
    pub reverse: Shape,
}

/// A veth pair: one end in each namespace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Veth {
    /// The first end.
    pub a: (Ns, String),
    /// The second end.
    pub b: (Ns, String),
}

/// Where one direction of a link is shaped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShapePoint {
    /// The namespace.
    pub ns: Ns,
    /// The device whose egress is shaped.
    pub dev: String,
}

/// The whole plan.
#[derive(Debug, Clone, PartialEq)]
pub struct Plan {
    /// The run id: every container name and label carries it.
    pub run: String,
    /// The sites.
    pub sites: Vec<SitePlan>,
    /// The nodes.
    pub nodes: Vec<NodePlan>,
    /// The links between routers.
    pub links: Vec<LinkPlan>,
    /// The veth pairs.
    pub veths: Vec<Veth>,
    /// What runs in each namespace once its interfaces exist, in order.
    pub setup: Vec<(Ns, Vec<Cmd>)>,
    /// Whether nodes share CPUs because the host has fewer than the scenario asks.
    pub shared_cpus: bool,
}

fn site_lan(i: usize) -> Ipv4Addr {
    Ipv4Addr::new(10, u8::try_from(i + 1).unwrap_or(u8::MAX), 0, 0)
}

fn host_in(lan: Ipv4Addr, host: usize) -> Ipv4Addr {
    let o = lan.octets();
    Ipv4Addr::new(o[0], o[1], o[2], u8::try_from(host).unwrap_or(u8::MAX))
}

/// The /30 of link `k`: its network address and the two ends.
fn link_net(k: usize) -> (Ipv4Addr, Ipv4Addr, Ipv4Addr) {
    let base = u32::from(Ipv4Addr::new(100, 64, 0, 0)) + u32::try_from(k * 4).unwrap_or(u32::MAX);
    (Ipv4Addr::from(base), Ipv4Addr::from(base + 1), Ipv4Addr::from(base + 2))
}

/// CPU sets for `nodes` nodes of `per` CPUs each, from the CPUs `1..cpus` (CPU 0 is left to the routers and the
/// orchestrator); nodes wrap around and share when there are too few. Returns the sets and whether any are shared.
pub fn cpu_sets(nodes: usize, per: u32, cpus: usize) -> (Vec<String>, bool) {
    let pool: Vec<usize> = if cpus > 1 { (1..cpus).collect() } else { vec![0] };
    let per = (per as usize).clamp(1, pool.len());
    let shared = nodes * per > pool.len();
    let sets = (0..nodes)
        .map(|i| {
            let mut set: Vec<usize> = (0..per).filter_map(|k| pool.get((i * per + k) % pool.len()).copied()).collect();
            set.sort_unstable();
            set.dedup();
            set.iter().map(ToString::to_string).collect::<Vec<_>>().join(",")
        })
        .collect();
    (sets, shared)
}

/// The packets a shaper may hold: what is in flight over the delay and jitter at the rate, plus the buffer.
pub fn queue_limit(s: &Shape) -> u64 {
    let Some(rate) = s.rate_mbit else { return 10_000 };
    let secs = (s.delay_ms + 3.0 * s.jitter_ms + s.queue_ms.unwrap_or(50.0)) / 1000.0;
    let packets = rate * 1e6 / 8.0 * secs / f64::from(MTU);
    // A float of at most a few million packets: the cast cannot truncate meaningfully.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let n = packets.ceil() as u64;
    n.max(64) + 16
}

/// The `netem` arguments of a shape (after `tc qdisc add|change dev X root`).
pub fn netem_args(s: &Shape) -> Vec<String> {
    // Microseconds and kbit/s as integers: tc parses them exactly, and a float would print in exponent form.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let us = |ms: f64| ((ms * 1000.0).round().max(0.0)) as u64;
    let mut a = vec!["netem".to_owned(), "delay".to_owned(), format!("{}us", us(s.delay_ms))];
    if s.jitter_ms > 0.0 {
        a.extend([format!("{}us", us(s.jitter_ms)), "distribution".into(), "normal".into()]);
    }
    if s.loss_pct > 0.0 {
        a.extend(["loss".into(), format!("{}%", trim(s.loss_pct))]);
    }
    if let Some(r) = s.rate_mbit {
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let kbit = (r * 1000.0).round().max(1.0) as u64;
        a.extend(["rate".into(), format!("{kbit}kbit")]);
    }
    a.extend(["limit".into(), queue_limit(s).to_string()]);
    a
}

fn trim(v: f64) -> String {
    let s = format!("{v:.4}");
    s.trim_end_matches('0').trim_end_matches('.').to_owned()
}

/// The command that gives `dev` the shape `s`; `change` replaces a shaper that is already there.
pub fn shape_cmd(dev: &str, s: &Shape, change: bool) -> Cmd {
    let mut args = vec![
        "qdisc".to_owned(),
        if change { "change" } else { "add" }.to_owned(),
        "dev".to_owned(),
        dev.to_owned(),
        "root".to_owned(),
    ];
    args.extend(netem_args(s));
    Cmd { tool: Tool::Tc, args }
}

/// The shape of a cut link: every packet lost.
pub fn cut() -> Shape {
    Shape {
        loss_pct: 100.0,
        ..Shape::default()
    }
}

/// Next hops: for each site, the link to take towards every other reachable site (fewest links, then least delay).
fn next_hops(sites: usize, links: &[LinkPlan]) -> Vec<BTreeMap<usize, usize>> {
    let mut hops = vec![BTreeMap::new(); sites];
    for (src, hop) in hops.iter_mut().enumerate() {
        // Dijkstra over at most a few hundred sites: a linear scan for the minimum is enough.
        let mut dist = vec![f64::INFINITY; sites];
        let mut first: Vec<Option<usize>> = vec![None; sites];
        let mut done = vec![false; sites];
        if let Some(d) = dist.get_mut(src) {
            *d = 0.0;
        }
        loop {
            let Some((u, du)) = dist
                .iter()
                .enumerate()
                .filter(|(i, d)| !done.get(*i).copied().unwrap_or(true) && d.is_finite())
                .min_by(|x, y| x.1.total_cmp(y.1))
                .map(|(i, d)| (i, *d))
            else {
                break;
            };
            if let Some(d) = done.get_mut(u) {
                *d = true;
            }
            for (k, l) in links.iter().enumerate() {
                let (v, w) = if l.a == u {
                    (l.b, l.forward.delay_ms)
                } else if l.b == u {
                    (l.a, l.reverse.delay_ms)
                } else {
                    continue;
                };
                // Fewest links first, as routing between sites does; the delay only breaks ties, so a direct link is
                // used even when a detour has less delay.
                let nd = du + 1e6 + w;
                if dist.get(v).is_some_and(|dv| nd < *dv) {
                    if let Some(dv) = dist.get_mut(v) {
                        *dv = nd;
                    }
                    let via = if u == src { Some(k) } else { first.get(u).copied().flatten() };
                    if let Some(f) = first.get_mut(v) {
                        *f = via;
                    }
                }
            }
        }
        for (dst, f) in first.iter().enumerate() {
            if let Some(k) = f {
                hop.insert(dst, *k);
            }
        }
    }
    hops
}

impl Plan {
    /// Plan `sc` for run `run` on a host with `cpus` CPUs. The scenario must validate.
    pub fn new(sc: &Scenario, run: &str, cpus: usize) -> Self {
        let site_idx: BTreeMap<&str, usize> = sc.sites.iter().enumerate().map(|(i, s)| (s.name.as_str(), i)).collect();
        let sites: Vec<SitePlan> = sc
            .sites
            .iter()
            .enumerate()
            .map(|(i, s)| SitePlan {
                name: s.name.clone(),
                nat: s.nat,
                lan: site_lan(i),
                gateway: host_in(site_lan(i), 1),
                router: Container {
                    name: format!("vd-{run}-r-{}", s.name),
                    cpus: "0".into(),
                    memory_mib: ROUTER_MEMORY_MIB,
                },
            })
            .collect();
        let specs = sc.expand();
        let (sets, shared_cpus) = cpu_sets(specs.len(), sc.resources.cpus, cpus);
        let mut in_site = vec![0usize; sites.len()];
        let nodes: Vec<NodePlan> = specs
            .iter()
            .zip(sets)
            .map(|(n, cpus)| {
                let j = in_site.get(n.site).copied().unwrap_or(0);
                if let Some(c) = in_site.get_mut(n.site) {
                    *c += 1;
                }
                NodePlan {
                    name: n.name.clone(),
                    site: n.site,
                    role: n.role,
                    ip: host_in(site_lan(n.site), j + 2),
                    port: format!("p{j}"),
                    ifb: format!("u{j}"),
                    link: n.link,
                    container: Container {
                        name: format!("vd-{run}-{}", n.name),
                        cpus,
                        memory_mib: sc.resources.memory_mib,
                    },
                }
            })
            .collect();
        let links: Vec<LinkPlan> = sc
            .links
            .iter()
            .enumerate()
            .filter_map(|(k, l)| {
                let (_, ip_a, ip_b) = link_net(k);
                Some(LinkPlan {
                    a: *site_idx.get(l.a.as_str())?,
                    b: *site_idx.get(l.b.as_str())?,
                    dev: format!("w{k}"),
                    ip_a,
                    ip_b,
                    forward: l.shape,
                    reverse: l.reverse_shape(),
                })
            })
            .collect();
        let mut plan = Self {
            run: run.to_owned(),
            sites,
            nodes,
            links,
            veths: Vec::new(),
            setup: Vec::new(),
            shared_cpus,
        };
        plan.wire();
        plan
    }

    fn wire(&mut self) {
        for (i, n) in self.nodes.iter().enumerate() {
            self.veths.push(Veth {
                a: (Ns::Node(i), "eth0".into()),
                b: (Ns::Router(n.site), n.port.clone()),
            });
        }
        for l in &self.links {
            self.veths.push(Veth {
                a: (Ns::Router(l.a), l.dev.clone()),
                b: (Ns::Router(l.b), l.dev.clone()),
            });
        }
        let hops = next_hops(self.sites.len(), &self.links);
        for (s, site) in self.sites.iter().enumerate() {
            self.setup.push((Ns::Router(s), self.router_cmds(s, site, hops.get(s))));
        }
        for (i, n) in self.nodes.iter().enumerate() {
            let gw = self.sites.get(n.site).map_or(Ipv4Addr::UNSPECIFIED, |s| s.gateway);
            let ip = format!("{}/24", n.ip);
            let gw = gw.to_string();
            let mtu = MTU.to_string();
            let cmds = vec![
                Cmd::new(Tool::Ip, &["link", "set", "lo", "up"]),
                // Segment offloaded batches here, so every shaper downstream sees MTU-sized packets.
                Cmd::new(Tool::Ip, &["link", "set", "eth0", "mtu", &mtu, "gso_max_segs", "1"]),
                Cmd::new(Tool::Ip, &["addr", "add", &ip, "dev", "eth0"]),
                Cmd::new(Tool::Ip, &["link", "set", "eth0", "up"]),
                Cmd::new(Tool::Ip, &["route", "add", "default", "via", &gw]),
            ];
            self.setup.push((Ns::Node(i), cmds));
        }
    }

    fn router_cmds(&self, s: usize, site: &SitePlan, hops: Option<&BTreeMap<usize, usize>>) -> Vec<Cmd> {
        let mtu = MTU.to_string();
        let gw = format!("{}/24", site.gateway);
        let mut c = vec![
            Cmd::new(Tool::Ip, &["link", "set", "lo", "up"]),
            Cmd::new(Tool::Sysctl, &["-q", "-w", "net.ipv4.ip_forward=1"]),
            Cmd::new(Tool::Ip, &["link", "add", "lan", "type", "bridge"]),
            Cmd::new(Tool::Ip, &["link", "set", "lan", "mtu", &mtu]),
            Cmd::new(Tool::Ip, &["addr", "add", &gw, "dev", "lan"]),
            Cmd::new(Tool::Ip, &["link", "set", "lan", "up"]),
        ];
        for n in self.nodes.iter().filter(|n| n.site == s) {
            c.push(Cmd::new(Tool::Ip, &["link", "set", &n.port, "mtu", &mtu, "master", "lan", "up"]));
            c.push(shape_cmd(&n.port, &n.link, false));
            c.push(Cmd::new(Tool::Ip, &["link", "add", &n.ifb, "type", "ifb"]));
            c.push(Cmd::new(Tool::Ip, &["link", "set", &n.ifb, "mtu", &mtu, "up"]));
            c.push(shape_cmd(&n.ifb, &n.link, false));
            c.push(Cmd::new(Tool::Tc, &["qdisc", "add", "dev", &n.port, "handle", "ffff:", "ingress"]));
            // The u32 classifier with an empty match takes every packet; a distribution kernel may not ship the
            // match-all classifier (Amazon Linux 2023 does not).
            c.push(Cmd::new(
                Tool::Tc,
                &[
                    "filter", "add", "dev", &n.port, "parent", "ffff:", "protocol", "all", "u32", "match", "u32", "0", "0",
                    "action", "mirred", "egress", "redirect", "dev", &n.ifb,
                ],
            ));
        }
        let lan = format!("{}/24", site.lan);
        for l in self.links.iter().filter(|l| l.a == s || l.b == s) {
            let (mine, shape) = if l.a == s { (l.ip_a, l.forward) } else { (l.ip_b, l.reverse) };
            let addr = format!("{mine}/30");
            c.push(Cmd::new(Tool::Ip, &["addr", "add", &addr, "dev", &l.dev]));
            c.push(Cmd::new(Tool::Ip, &["link", "set", &l.dev, "mtu", &mtu, "up"]));
            c.push(shape_cmd(&l.dev, &shape, false));
            if site.nat != Nat::None {
                let mut args = vec!["-t", "nat", "-A", "POSTROUTING", "-s", lan.as_str(), "-o", l.dev.as_str(), "-j", "MASQUERADE"];
                if site.nat == Nat::Symmetric {
                    args.push("--random-fully");
                }
                c.push(Cmd::new(Tool::Iptables, &args));
            }
        }
        let Some(hops) = hops else { return c };
        let mut routes = Vec::new();
        for (dst, d) in self.sites.iter().enumerate() {
            if dst != s && d.nat == Nat::None {
                routes.push((format!("{}/24", d.lan), hops.get(&dst)));
            }
        }
        for (k, l) in self.links.iter().enumerate() {
            if l.a != s && l.b != s {
                // Towards the nearer end's site: either end routes the /30 it is on.
                let (net, _, _) = link_net(k);
                routes.push((format!("{net}/30"), hops.get(&l.a).or_else(|| hops.get(&l.b))));
            }
        }
        for (prefix, hop) in routes {
            let Some(k) = hop else { continue };
            let Some(l) = self.links.get(*k) else { continue };
            let via = if l.a == s { l.ip_b } else { l.ip_a }.to_string();
            c.push(Cmd::new(Tool::Ip, &["route", "add", &prefix, "via", &via, "dev", &l.dev]));
        }
        c
    }

    /// The node with this name.
    pub fn node(&self, name: &str) -> Option<usize> {
        self.nodes.iter().position(|n| n.name == name)
    }

    /// The site with this name.
    pub fn site(&self, name: &str) -> Option<usize> {
        self.sites.iter().position(|s| s.name == name)
    }

    /// The two directions of the link between `a` and `b` (two sites, or a node and its site): where each is shaped
    /// and the scenario's shape for it.
    pub fn link_points(&self, a: &str, b: &str) -> Option<[(ShapePoint, Shape); 2]> {
        let access = |node: &str, site: &str| {
            let n = self.nodes.get(self.node(node)?)?;
            (Some(n.site) == self.site(site)).then(|| {
                [
                    (ShapePoint { ns: Ns::Router(n.site), dev: n.port.clone() }, n.link),
                    (ShapePoint { ns: Ns::Router(n.site), dev: n.ifb.clone() }, n.link),
                ]
            })
        };
        if let Some(p) = access(a, b).or_else(|| access(b, a)) {
            return Some(p);
        }
        let (sa, sb) = (self.site(a)?, self.site(b)?);
        self.links.iter().find(|l| (l.a == sa && l.b == sb) || (l.a == sb && l.b == sa)).map(|l| {
            [
                (ShapePoint { ns: Ns::Router(l.a), dev: l.dev.clone() }, l.forward),
                (ShapePoint { ns: Ns::Router(l.b), dev: l.dev.clone() }, l.reverse),
            ]
        })
    }

    /// Every link of a site to other sites, by the other site's name.
    pub fn site_links(&self, site: usize) -> Vec<String> {
        self.links
            .iter()
            .filter_map(|l| {
                let other = if l.a == site {
                    l.b
                } else if l.b == site {
                    l.a
                } else {
                    return None;
                };
                self.sites.get(other).map(|s| s.name.clone())
            })
            .collect()
    }
}
