//! Backend (b): real machines over SSH. A node is a program in a transient systemd scope on a machine of the fleet, so
//! the kernel's accounting of its CPU time and peak memory is the same kind as for a container; the network is the
//! machines' own, with `tc netem` added on their egress for the traffic between sites where the scenario gives a link
//! a shape (delay, loss, rate), per destination machine.
//!
//! What differs from containers, said in the results: the machines are not the harness's to quiet (the quiet-host
//! check is not run), the interface counters are read only for a machine that runs one node (traffic between nodes
//! of one machine does not cross its interface), the peak memory is the scope's peak since its program started, a node's access link is not shaped, and a
//! fault on a link applies to the links that join two sites directly.
//!
//! Invariants: nothing outside the run's scopes and its own `tc` objects is touched; a machine that already has scopes
//! of the harness is refused; teardown removes every scope and every `tc` object this run made and checks that nothing is
//! left; every word that reaches a remote shell passed the `plain` check of the fleet module.

use std::collections::{BTreeMap, BTreeSet};
use std::net::Ipv4Addr;
use std::process::Stdio;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

use tokio::process::Command;

use crate::backend::fleet::{Fleet, Placement, plain};
use crate::backend::proc::Proc;
use crate::error::{Error, Result};
use crate::metrics::{self, Qdisc, Reading};
use crate::plan::{Ns, Plan, ShapePoint, cpu_sets, netem_args};
use crate::scenario::{Scenario, Shape};

/// Destinations one machine can shape separately (the classes of its `prio` queue, less the unshaped one).
const BANDS: usize = 14;

/// One link between two sites as the scenario has it.
#[derive(Debug, Clone)]
struct Link {
    a: usize,
    b: usize,
    dev: String,
    forward: Shape,
    reverse: Shape,
}

/// The backend of one run.
#[derive(Debug)]
pub struct Ssh {
    fleet: Fleet,
    place: Vec<Placement>,
    names: Vec<String>,
    ips: Vec<std::net::Ipv4Addr>,
    ifaces: Vec<String>,
    cpus: Vec<String>,
    /// How many nodes each machine runs: its interface counters mean something only for one.
    on_host: Vec<usize>,
    memory_mib: u32,
    run: String,
    units: Mutex<Vec<String>>,
    spawned: AtomicU64,
    links: Vec<Link>,
    /// Hosts that run nodes of each site.
    site_hosts: Vec<BTreeSet<usize>>,
    /// Per host: the machine it sends to, and the class that shapes it.
    bands: Vec<BTreeMap<usize, usize>>,
    shaped: Mutex<BTreeSet<usize>>,
}

async fn remote(h: &crate::backend::fleet::Host, cmd: &str) -> Result<String> {
    let out = Command::new("ssh")
        .args(h.ssh(cmd))
        .stdin(Stdio::null())
        .output()
        .await
        .map_err(|e| Error::Host(format!("ssh did not start ({e}); install an OpenSSH client")))?;
    if out.status.success() {
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    } else {
        Err(Error::Command {
            cmd: format!("ssh {}@{} {cmd}", h.user, h.address),
            stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        })
    }
}

/// The interface of `text` (`ip -o -4 addr show`) that carries `ip`.
pub fn iface_of(text: &str, ip: Ipv4Addr) -> Option<String> {
    text.lines().find_map(|l| {
        let f: Vec<&str> = l.split_whitespace().collect();
        let at = f.iter().position(|x| *x == "inet")?;
        let addr = f.get(at + 1)?.split('/').next()?;
        (addr.parse::<Ipv4Addr>().ok()? == ip).then(|| f.get(1).map(|n| n.trim_end_matches(':').to_owned()))?
    })
}

/// The commands that give `iface` a `prio` queue with one class per destination machine and a `netem` on each, then a
/// filter that sends the traffic for each destination to its class. `dests` are (class, address, shape).
pub fn shaping_commands(iface: &str, dests: &[(usize, Ipv4Addr, Shape)]) -> Vec<String> {
    let zeros = ["0"; 16].join(" ");
    let mut v = vec![format!(
        "tc qdisc add dev {iface} root handle 1: prio bands 16 priomap {zeros}"
    )];
    for (class, ip, shape) in dests {
        let c = class + 2;
        v.push(format!(
            "tc qdisc add dev {iface} parent 1:{c} handle {c}0: {}",
            netem_args(shape).join(" ")
        ));
        v.push(format!(
            "tc filter add dev {iface} protocol ip parent 1: prio 1 u32 match ip dst {ip}/32 flowid 1:{c}"
        ));
    }
    v
}

/// The command that gives class `class` of `iface` another shape.
pub fn reshape_command(iface: &str, class: usize, shape: &Shape) -> String {
    let c = class + 2;
    format!(
        "tc qdisc change dev {iface} parent 1:{c} handle {c}0: {}",
        netem_args(shape).join(" ")
    )
}

/// A shape for a path of several links: delays add, losses combine, the rate is the smallest, jitters add in square.
pub fn compose(path: &[Shape]) -> Shape {
    let mut out = Shape::default();
    let mut keep = 1.0;
    let mut var = 0.0;
    for s in path {
        out.delay_ms += s.delay_ms;
        keep *= 1.0 - s.loss_pct / 100.0;
        var += s.jitter_ms * s.jitter_ms;
        out.rate_mbit = match (out.rate_mbit, s.rate_mbit) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
        out.queue_ms = s.queue_ms.or(out.queue_ms);
    }
    out.loss_pct = (1.0 - keep) * 100.0;
    out.jitter_ms = var.sqrt();
    out
}

/// Make one machine ready: reachable with keys, free of scopes of the harness, the binary in place; returns its
/// interface and CPU count.
async fn prepare(h: &crate::backend::fleet::Host, exe: &std::path::Path) -> Result<(String, usize)> {
    remote(h, "true").await.map_err(|e| {
        Error::Host(format!(
            "machine {} cannot be reached over SSH with keys only: {e}",
            h.name
        ))
    })?;
    let left = remote(h, "systemctl list-units --all --plain --no-legend 'vd-*.scope'").await?;
    if !left.trim().is_empty() {
        return Err(Error::Leftovers(
            left.lines()
                .filter_map(|l| l.split_whitespace().next())
                .map(|u| format!("{} on {}", u, h.name))
                .collect(),
        ));
    }
    let dir = h.bin.rsplit_once('/').map_or(".", |(d, _)| d);
    remote(h, &format!("mkdir -p {dir}")).await?;
    let put = Command::new("ssh")
        .args(h.ssh(&format!(
            "cat > {bin}.new && chmod +x {bin}.new && mv {bin}.new {bin}",
            bin = h.bin
        )))
        .stdin(Stdio::from(std::fs::File::open(exe)?))
        .output()
        .await?;
    if !put.status.success() {
        return Err(Error::Command {
            cmd: format!("copy the binary to {}", h.name),
            stderr: String::from_utf8_lossy(&put.stderr).into_owned(),
        });
    }
    let ip = h
        .ip()
        .ok_or_else(|| Error::Host(format!("{} has no IPv4 address", h.name)))?;
    let iface = match &h.interface {
        Some(i) => i.clone(),
        None => iface_of(&remote(h, "ip -o -4 addr show").await?, ip).ok_or_else(|| {
            Error::Host(format!(
                "no interface of {} carries {ip}; name it as `interface` in the fleet file",
                h.name
            ))
        })?,
    };
    let cpus = remote(h, "nproc").await?.trim().parse::<usize>().unwrap_or(1);
    Ok((iface, cpus))
}

impl Ssh {
    /// Check the fleet, put the binary on every machine, and shape the traffic between sites. On any failure removes what
    /// it made.
    ///
    /// # Errors
    /// The fleet or the scenario cannot be placed, a machine cannot be reached or already has scopes of the harness,
    /// or a command failed.
    pub async fn up(sc: &Scenario, plan: &Plan, fleet: Fleet, run: &str) -> Result<Self> {
        let problems = fleet.validate();
        if !problems.is_empty() {
            return Err(Error::Scenario(problems));
        }
        let specs = sc.expand();
        let place = fleet.place(&specs, &sc.sites).map_err(Error::Host)?;
        let mut per_host = vec![0usize; fleet.hosts.len()];
        for p in &place {
            if let Some(c) = per_host.get_mut(p.host) {
                *c += 1;
            }
        }
        let exe = std::env::current_exe()?;
        let mut ifaces = Vec::new();
        let mut host_cpus = Vec::new();
        for h in &fleet.hosts {
            let (iface, cpu_count) = prepare(h, &exe).await?;
            ifaces.push(iface);
            host_cpus.push(cpu_count);
        }
        // Each machine's nodes get CPU sets of their own from the machine's CPUs, CPU 0 left to the system.
        let mut cpus = vec![String::new(); specs.len()];
        for (hi, cpu_count) in host_cpus.iter().enumerate() {
            let mine: Vec<usize> = place
                .iter()
                .enumerate()
                .filter(|(_, p)| p.host == hi)
                .map(|(i, _)| i)
                .collect();
            let (sets, _) = cpu_sets(mine.len(), sc.resources.cpus, *cpu_count);
            for (i, set) in mine.iter().zip(sets) {
                if let Some(c) = cpus.get_mut(*i) {
                    *c = set;
                }
            }
        }
        let mut site_hosts = vec![BTreeSet::new(); sc.sites.len()];
        for (n, p) in specs.iter().zip(&place) {
            if let Some(s) = site_hosts.get_mut(n.site) {
                s.insert(p.host);
            }
        }
        let me = Self {
            names: specs.iter().map(|n| n.name.clone()).collect(),
            ips: place
                .iter()
                .map(|p| {
                    fleet
                        .hosts
                        .get(p.host)
                        .and_then(crate::backend::fleet::Host::ip)
                        .unwrap_or(Ipv4Addr::UNSPECIFIED)
                })
                .collect(),
            units: Mutex::new(vec![String::new(); specs.len()]),
            links: plan
                .links
                .iter()
                .map(|l| Link {
                    a: l.a,
                    b: l.b,
                    dev: l.dev.clone(),
                    forward: l.forward,
                    reverse: l.reverse,
                })
                .collect(),
            bands: vec![BTreeMap::new(); fleet.hosts.len()],
            shaped: Mutex::new(BTreeSet::new()),
            fleet,
            place,
            ifaces,
            cpus,
            on_host: per_host,
            memory_mib: sc.resources.memory_mib,
            run: run.to_owned(),
            spawned: AtomicU64::new(0),
            site_hosts,
        };
        let mut me = me;
        if let Err(e) = me.shape_sites(sc).await {
            let _ = me.down().await;
            return Err(e);
        }
        Ok(me)
    }

    /// The shape of the traffic from site `a` to site `b` over the scenario's links: the direct link's, or the
    /// composition along the path with the fewest links.
    fn path_shape(&self, from_site: usize, to_site: usize) -> Option<Shape> {
        if from_site == to_site {
            return None;
        }
        // Breadth first over sites: fewest links.
        let count = self.site_hosts.len();
        let mut from: Vec<Option<(usize, Shape)>> = vec![None; count];
        let mut seen = vec![false; count];
        let mut queue = std::collections::VecDeque::from([from_site]);
        if let Some(s) = seen.get_mut(from_site) {
            *s = true;
        }
        while let Some(u) = queue.pop_front() {
            for l in &self.links {
                let (v, s) = if l.a == u {
                    (l.b, l.forward)
                } else if l.b == u {
                    (l.a, l.reverse)
                } else {
                    continue;
                };
                if seen.get(v).copied().unwrap_or(true) {
                    continue;
                }
                if let Some(x) = seen.get_mut(v) {
                    *x = true;
                }
                if let Some(f) = from.get_mut(v) {
                    *f = Some((u, s));
                }
                queue.push_back(v);
            }
        }
        let mut path = Vec::new();
        let mut at = to_site;
        while at != from_site {
            let (prev, s) = from.get(at).copied().flatten()?;
            path.push(s);
            at = prev;
        }
        path.reverse();
        Some(compose(&path))
    }

    async fn shape_sites(&mut self, sc: &Scenario) -> Result<()> {
        let hosts = self.fleet.hosts.len();
        // A machine that runs nodes of two sites cannot have its traffic to the others shaped per site.
        let mixed: Vec<bool> = (0..hosts)
            .map(|h| self.site_hosts.iter().filter(|s| s.contains(&h)).count() > 1)
            .collect();
        let mut plan_cmds: Vec<(usize, Vec<String>)> = Vec::new();
        for h in 0..hosts {
            let mut dests = Vec::new();
            let my_sites: Vec<usize> = (0..self.site_hosts.len())
                .filter(|s| self.site_hosts.get(*s).is_some_and(|x| x.contains(&h)))
                .collect();
            for d in (0..hosts).filter(|d| *d != h) {
                let their: Vec<usize> = (0..self.site_hosts.len())
                    .filter(|s| self.site_hosts.get(*s).is_some_and(|x| x.contains(&d)))
                    .collect();
                let (Some(&sa), Some(&sb)) = (my_sites.first(), their.first()) else {
                    continue;
                };
                let Some(shape) = self.path_shape(sa, sb) else { continue };
                if mixed.get(h).copied().unwrap_or(false) || mixed.get(d).copied().unwrap_or(false) {
                    return Err(Error::Host(format!(
                        "machine {} or {} runs nodes of more than one site, so the traffic between sites cannot be shaped per site; give every machine one `site` in the fleet file or use as many machines as sites",
                        self.fleet.hosts.get(h).map_or("?", |x| x.name.as_str()),
                        self.fleet.hosts.get(d).map_or("?", |x| x.name.as_str()),
                    )));
                }
                if dests.len() >= BANDS {
                    return Err(Error::Host(format!(
                        "a machine would shape its traffic to more than {BANDS} machines; use fewer machines or sites"
                    )));
                }
                let ip = self
                    .fleet
                    .hosts
                    .get(d)
                    .and_then(crate::backend::fleet::Host::ip)
                    .unwrap_or(Ipv4Addr::UNSPECIFIED);
                if let Some(b) = self.bands.get_mut(h) {
                    b.insert(d, dests.len());
                }
                dests.push((dests.len(), ip, shape));
            }
            if !dests.is_empty() {
                let iface = self.ifaces.get(h).cloned().unwrap_or_default();
                plan_cmds.push((h, shaping_commands(&iface, &dests)));
            }
        }
        let _ = sc;
        for (h, cmds) in plan_cmds {
            let host = self
                .fleet
                .hosts
                .get(h)
                .ok_or_else(|| Error::Host("no such machine".into()))?;
            if let Ok(mut s) = self.shaped.lock() {
                s.insert(h);
            }
            for c in cmds {
                remote(host, &host.root(&c)).await?;
            }
        }
        Ok(())
    }

    fn host_of(&self, node: usize) -> Result<&crate::backend::fleet::Host> {
        self.place
            .get(node)
            .and_then(|p| self.fleet.hosts.get(p.host))
            .ok_or_else(|| Error::Node(format!("there is no node {node}")))
    }

    fn unit(&self, node: usize) -> String {
        self.units
            .lock()
            .ok()
            .and_then(|u| u.get(node).cloned())
            .unwrap_or_default()
    }

    /// The address of node `i`, the slot among the nodes of its machine, and the address other sites reach it at.
    pub fn address(&self, i: usize) -> (Ipv4Addr, u16) {
        (
            self.ips.get(i).copied().unwrap_or(Ipv4Addr::UNSPECIFIED),
            self.place.get(i).map_or(0, |p| u16::try_from(p.slot).unwrap_or(0)),
        )
    }

    /// Start the node binary in node `i` with `args` and `env`, in a scope with the node's CPUs and memory.
    ///
    /// # Errors
    /// The node does not exist, or a word is not safe to send to a shell.
    pub fn spawn(&self, i: usize, args: &[String], env: &[(String, String)]) -> Result<Proc> {
        let h = self.host_of(i)?;
        let n = self.spawned.fetch_add(1, Ordering::Relaxed);
        let unit = format!(
            "vd-{}-{}-{n}",
            self.run.to_ascii_lowercase(),
            self.names.get(i).map_or("n", String::as_str)
        );
        let mut words: Vec<String> = vec![
            "systemd-run".into(),
            "--scope".into(),
            "--quiet".into(),
            "--collect".into(),
            format!("--unit={unit}"),
            "-p".into(),
            format!("AllowedCPUs={}", self.cpus.get(i).map_or("", String::as_str)),
            "-p".into(),
            format!("MemoryMax={}M", self.memory_mib),
            "-p".into(),
            "MemorySwapMax=0".into(),
        ];
        for (k, v) in env {
            words.push(format!("--setenv={k}={v}"));
        }
        words.push(h.bin.clone());
        words.extend(args.iter().cloned());
        if let Some(bad) = words.iter().find(|w| {
            !w.bytes()
                .all(|b| b.is_ascii_alphanumeric() || b"-_./:@=,+".contains(&b))
        }) {
            return Err(Error::Node(format!(
                "`{bad}` cannot be sent to a remote shell as one word"
            )));
        }
        if let Ok(mut u) = self.units.lock()
            && let Some(slot) = u.get_mut(i)
        {
            slot.clone_from(&unit);
        }
        let mut cmd = Command::new("ssh");
        cmd.args(h.ssh(&h.root(&words.join(" "))));
        Proc::spawn(
            cmd,
            format!("the node program on {}", self.names.get(i).map_or("?", String::as_str)),
        )
    }

    /// Kill every process of node `i`'s scope.
    ///
    /// # Errors
    /// The command failed.
    pub async fn stop(&self, i: usize) -> Result<()> {
        let h = self.host_of(i)?;
        let unit = self.unit(i);
        if unit.is_empty() {
            return Ok(());
        }
        remote(
            h,
            &h.root(&format!("systemctl kill --kill-whom=all -s KILL {unit}.scope; true")),
        )
        .await?;
        Ok(())
    }

    /// Freeze or thaw node `i`.
    ///
    /// # Errors
    /// The command failed.
    pub async fn pause(&self, i: usize, pause: bool) -> Result<()> {
        let h = self.host_of(i)?;
        let unit = self.unit(i);
        let sig = if pause { "SIGSTOP" } else { "SIGCONT" };
        remote(
            h,
            &h.root(&format!("systemctl kill --kill-whom=all -s {sig} {unit}.scope")),
        )
        .await?;
        Ok(())
    }

    /// Node `i`'s CPU time from its scope and its machine's interface counters.
    ///
    /// # Errors
    /// The command failed.
    pub async fn reading(&self, i: usize) -> Result<Reading> {
        let h = self.host_of(i)?;
        let unit = self.unit(i);
        let host_i = self.place.get(i).map_or(0, |p| p.host);
        let iface = self.ifaces.get(host_i).cloned().unwrap_or_default();
        let out = remote(
            h,
            &format!("cat /sys/fs/cgroup/system.slice/{unit}.scope/cpu.stat 2>/dev/null; echo ---; cat /proc/net/dev"),
        )
        .await?;
        let (cpu, net) = out.split_once("---").unwrap_or((out.as_str(), ""));
        Ok(Reading {
            cpu_usec: metrics::parse_cpu_usec(cpu),
            // Traffic between two nodes of one machine does not cross its interface: the counters count only what
            // leaves a machine that runs one node.
            eth0: (self.on_host.get(host_i).copied() == Some(1))
                .then(|| metrics::parse_net_dev(net).get(&iface).copied())
                .flatten(),
        })
    }

    /// Node `i`'s peak memory in bytes since its program started (a scope's peak cannot be reset from outside).
    ///
    /// # Errors
    /// The command failed.
    pub async fn peak_read(&self, i: usize) -> Result<Option<u64>> {
        let h = self.host_of(i)?;
        let unit = self.unit(i);
        let out = remote(
            h,
            &format!("cat /sys/fs/cgroup/system.slice/{unit}.scope/memory.peak 2>/dev/null; true"),
        )
        .await?;
        Ok(out.trim().parse().ok())
    }

    /// The `netem` counters of the machines that run site `s`'s nodes.
    ///
    /// # Errors
    /// The command failed.
    pub async fn shapers(&self, s: usize) -> Result<Vec<Qdisc>> {
        let mut out = Vec::new();
        for h in self.site_hosts.get(s).into_iter().flatten() {
            if !self.shaped.lock().is_ok_and(|x| x.contains(h)) {
                continue;
            }
            let (Some(host), Some(iface)) = (self.fleet.hosts.get(*h), self.ifaces.get(*h)) else {
                continue;
            };
            let text = remote(host, &host.root(&format!("tc -s -j qdisc show dev {iface}"))).await?;
            out.extend(metrics::parse_tc(&text));
        }
        Ok(out)
    }

    /// Give one direction of a link between two sites another shape, now: the traffic of the machines of one site to the
    /// machines of the other. Only the router-side links of the plan (the links between sites) exist here.
    ///
    /// # Errors
    /// The point is not a link between sites, or a command failed.
    pub async fn reshape(&self, at: &ShapePoint, shape: &Shape) -> Result<()> {
        let Ns::Router(site) = at.ns else {
            return Err(Error::Host(
                "only links between sites can be changed on real machines".into(),
            ));
        };
        let Some(l) = self
            .links
            .iter()
            .find(|l| l.dev == at.dev && (l.a == site || l.b == site))
        else {
            return Err(Error::Host(
                "a node's own access link cannot be changed on real machines; change a link between sites".into(),
            ));
        };
        let other = if l.a == site { l.b } else { l.a };
        for h in self.site_hosts.get(site).into_iter().flatten() {
            for d in self.site_hosts.get(other).into_iter().flatten() {
                let Some(class) = self.bands.get(*h).and_then(|b| b.get(d)) else {
                    continue;
                };
                let (Some(host), Some(iface)) = (self.fleet.hosts.get(*h), self.ifaces.get(*h)) else {
                    continue;
                };
                remote(host, &host.root(&reshape_command(iface, *class, shape))).await?;
            }
        }
        Ok(())
    }

    /// The scopes' names, for the quiet-host check (none: the machines are not checked).
    pub fn scopes(&self) -> Vec<String> {
        Vec::new()
    }

    /// Remove every scope and `tc` object of this run, then check that nothing is left; returns what is.
    ///
    /// # Errors
    /// A machine could not be reached.
    pub async fn down(&mut self) -> Result<Vec<String>> {
        let mut left = Vec::new();
        for (hi, h) in self.fleet.hosts.iter().enumerate() {
            remote(h, &h.root("systemctl kill --kill-whom=all -s KILL 'vd-*.scope'; true")).await?;
            if self.shaped.lock().is_ok_and(|s| s.contains(&hi)) {
                let iface = self.ifaces.get(hi).cloned().unwrap_or_default();
                remote(h, &h.root(&format!("tc qdisc del dev {iface} root; true"))).await?;
            }
            let units = remote(h, "systemctl list-units --all --plain --no-legend 'vd-*.scope'").await?;
            left.extend(
                units
                    .lines()
                    .filter_map(|l| l.split_whitespace().next())
                    .map(|u| format!("{u} on {}", h.name)),
            );
            if let Some(iface) = self.ifaces.get(hi) {
                let q = remote(h, &h.root(&format!("tc qdisc show dev {iface}"))).await?;
                if self.shaped.lock().is_ok_and(|s| s.contains(&hi)) && q.contains("prio") {
                    left.push(format!("shaping on {iface} of {}", h.name));
                }
            }
        }
        Ok(left)
    }
}

/// Remove what a run left on the machines of `fleet`: its scopes and the `prio` queue it put on each interface.
///
/// # Errors
/// A machine could not be reached.
pub async fn clean(fleet: &Fleet) -> Result<Vec<String>> {
    let mut removed = Vec::new();
    for h in &fleet.hosts {
        let units = remote(h, "systemctl list-units --all --plain --no-legend 'vd-*.scope'").await?;
        for u in units.lines().filter_map(|l| l.split_whitespace().next()) {
            removed.push(format!("{u} on {}", h.name));
        }
        remote(h, &h.root("systemctl kill --kill-whom=all -s KILL 'vd-*.scope'; true")).await?;
        if let Some(ip) = h.ip() {
            let iface = match &h.interface {
                Some(i) => i.clone(),
                None => iface_of(&remote(h, "ip -o -4 addr show").await?, ip).unwrap_or_default(),
            };
            if plain(&iface) {
                let q = remote(h, &h.root(&format!("tc qdisc show dev {iface}"))).await?;
                if q.contains("qdisc prio 1:") {
                    remote(h, &h.root(&format!("tc qdisc del dev {iface} root; true"))).await?;
                    removed.push(format!("shaping on {iface} of {}", h.name));
                }
            }
        }
    }
    Ok(removed)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]
mod tests {
    use super::*;

    #[test]
    fn the_interface_of_an_address_is_found_in_the_machines_listing() {
        let text = "1: lo    inet 127.0.0.1/8 scope host lo\\       valid_lft forever\n2: ens5    inet 10.0.1.10/24 brd 10.0.1.255 scope global dynamic ens5\\       valid_lft 3000sec\n";
        assert_eq!(iface_of(text, "10.0.1.10".parse().unwrap()).as_deref(), Some("ens5"));
        assert_eq!(iface_of(text, "127.0.0.1".parse().unwrap()).as_deref(), Some("lo"));
        assert_eq!(iface_of(text, "10.9.9.9".parse().unwrap()), None);
    }

    #[test]
    fn shaping_gives_each_destination_a_class_a_netem_and_a_filter() {
        let s = Shape {
            delay_ms: 25.0,
            loss_pct: 1.0,
            rate_mbit: Some(100.0),
            ..Shape::default()
        };
        let cmds = shaping_commands(
            "ens5",
            &[
                (0, "10.0.2.20".parse().unwrap(), s),
                (1, "10.0.3.30".parse().unwrap(), s),
            ],
        );
        assert_eq!(cmds.len(), 5);
        assert!(cmds[0].starts_with("tc qdisc add dev ens5 root handle 1: prio bands 16 priomap 0 0"));
        assert!(cmds[1].starts_with(
            "tc qdisc add dev ens5 parent 1:2 handle 20: netem delay 25000us loss 1% rate 100000kbit limit"
        ));
        assert!(cmds[2].contains("match ip dst 10.0.2.20/32 flowid 1:2"));
        assert!(cmds[3].contains("parent 1:3 handle 30: netem"));
        assert!(cmds[4].contains("match ip dst 10.0.3.30/32 flowid 1:3"));
        assert!(
            reshape_command("ens5", 1, &s)
                .starts_with("tc qdisc change dev ens5 parent 1:3 handle 30: netem delay 25000us")
        );
    }

    #[test]
    fn a_path_composes_delays_losses_rates_and_jitters() {
        let a = Shape {
            delay_ms: 10.0,
            loss_pct: 10.0,
            jitter_ms: 3.0,
            rate_mbit: Some(200.0),
            ..Shape::default()
        };
        let b = Shape {
            delay_ms: 40.0,
            loss_pct: 10.0,
            jitter_ms: 4.0,
            rate_mbit: Some(50.0),
            ..Shape::default()
        };
        let c = compose(&[a, b]);
        assert!((c.delay_ms - 50.0).abs() < 1e-9);
        assert!((c.loss_pct - 19.0).abs() < 1e-9);
        assert!((c.jitter_ms - 5.0).abs() < 1e-9);
        assert_eq!(c.rate_mbit, Some(50.0));
        assert_eq!(compose(&[]), Shape::default());
    }
}
