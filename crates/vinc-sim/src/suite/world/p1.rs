//! The phase-1 scenarios: S1 (datacenter), S4 (hostile networks), S10 (browsers), S12 (adversarial members), S13
//! (churn and partitions) and S15 (soak), plus the dispatch that also reaches S6 (`scenarios_p1`).
//!
//! Invariant: each scenario builds its nodes, calls the shared workload (`mixed`) and then applies its own ground
//! truth corrections, with the draws in the reference order; the final sort is applied once at the end.

use super::WorldError;
use super::build::{
    Builder, MIB, MS, NS, SiteArgs, below, blank_world, carrier_nat, choice, finish, home_nat, nat_timeout, sample,
    scaled, sort_world,
};
use super::mixed::{mixed, window};
use super::model::{
    Addr, ClockSpec, Cut, EnvArg, EnvKind, IfaceSpec, Intent, IntentKind, MiddleboxSpec, Must, NodeSpec, Params, World,
};
use super::p1_capacity::s6;
use super::params::ParamsExt;

/// One fabric: 20 microseconds one way through the spine.
const DC_REGION_NS: u64 = 20_000;

/// Generates a phase-1 scenario from the merged parameters.
pub(super) fn generate(id: &str, p: Params, seed: u64) -> Result<World, WorldError> {
    let mut w = blank_world(id, &p, seed)?;
    let mut b = Builder::new(p, seed);
    match id {
        "S1" => s1(&mut w, &mut b)?,
        "S4" => s4(&mut w, &mut b)?,
        "S6" => s6(&mut w, &mut b)?,
        "S10" => s10(&mut w, &mut b)?,
        "S12" => s12(&mut w, &mut b)?,
        "S13" => s13(&mut w, &mut b)?,
        _ => s15(&mut w, &mut b)?,
    }
    sort_world(&mut w);
    Ok(w)
}

/// The standard cloud, home, mobile node triple of S4, S12, S13 and S15 (and S10 with homes only).
/// The clouds, homes and mobiles of a scenario.
type Classes = (Vec<usize>, Vec<usize>, Vec<usize>);

fn standard_nodes(w: &mut World, b: &mut Builder) -> Result<Classes, WorldError> {
    let mut clouds = Vec::new();
    for r in 0..b.p.count("n_cloud")? {
        clouds.push(b.add_cloud(w, r % 3)?);
    }
    let mut homes = Vec::new();
    for _ in 0..b.p.count("n_home")? {
        let region = below(&mut b.rng, 3, "regions")?;
        homes.push(b.add_home(w, region, None, None)?);
    }
    let mut mobiles = Vec::new();
    for _ in 0..b.p.count("n_mobile")? {
        let region = below(&mut b.rng, 3, "regions")?;
        mobiles.push(b.add_mobile(w, region)?);
    }
    Ok((clouds, homes, mobiles))
}

fn standard(w: &mut World, b: &mut Builder) -> Result<(), WorldError> {
    let (clouds, homes, mobiles) = standard_nodes(w, b)?;
    finish(w, clouds, homes, mobiles);
    mixed(w, b)
}

// ------------------------------------------------------------------ S1

fn dc_server(w: &mut World, b: &mut Builder) -> Result<usize, WorldError> {
    let pick = choice(&mut b.rng, &[10u64, 25, 40, 100], "link speeds")? * 1_000_000_000;
    let (lo, hi) = b.p.int_pair("server_bps")?;
    let bps = pick.max(lo as u64).min(hi as u64);
    let delay_ns = scaled(b.pick("server_delay_us")?, 1000);
    let sid = b.site(
        w,
        SiteArgs {
            region: 0,
            up_bps: bps,
            down_bps: bps,
            delay_ns,
            loss: 0.0,
            burst_ns: MS,
            nats: Vec::new(),
            v6_open: false,
            queue: Some(4 * MIB),
        },
    )?;
    let idx = w.nodes.len();
    let mut ifaces = b.ifaces(sid, idx, false, true);
    let mtu = b.p.int("mtu")? as u64;
    for d in &mut ifaces {
        if d.kind == "udp4" {
            d.mtu = mtu - 28;
        } else if d.kind == "udp6" {
            d.mtu = mtu - 48;
        }
    }
    w.nodes.push(NodeSpec {
        device: "cloud".to_string(),
        site: sid,
        kind: "cloud".to_string(),
        region: 0,
        ifaces,
        topics: Vec::new(),
        sites: Vec::new(),
        clock: None,
        cpu_factor: None,
    });
    Ok(idx)
}

fn s1(w: &mut World, b: &mut Builder) -> Result<(), WorldError> {
    let (n_cloud, n_server) = (b.p.count("n_cloud")?, b.p.count("n_server")?);
    let mut nodes = Vec::new();
    for _ in 0..n_cloud + n_server {
        nodes.push(dc_server(w, b)?);
    }
    finish(w, nodes[..n_cloud].to_vec(), nodes[n_cloud..].to_vec(), Vec::new());
    w.region_delay_ns = vec![vec![DC_REGION_NS]];
    mixed(w, b)?;
    let t = 20 * NS;
    let sizes = b.p.int_list("bulk_sizes")?.to_vec();
    for (j, size) in sizes.iter().enumerate() {
        let name = format!("bulk{j}");
        let prov = choice(&mut b.rng, &nodes, "servers")?;
        let c: Vec<usize> = nodes.iter().copied().filter(|x| *x != prov).collect();
        let dst = choice(&mut b.rng, &c, "servers")?;
        w.values.insert(name.clone(), *size as u64);
        w.provides.entry(prov).or_default().push(name.clone());
        w.intents
            .push(fetch(t + j as u64 * 15 * NS, dst, &name, vec![prov], 120 * NS));
    }
    if b.p.truthy("multi_size") {
        let provs = sample(&mut b.rng, &nodes, 3, "servers")?;
        let c: Vec<usize> = nodes.iter().copied().filter(|x| !provs.contains(x)).collect();
        let dst = choice(&mut b.rng, &c, "servers")?;
        w.values.insert("multi".to_string(), b.p.int("multi_size")? as u64);
        for pv in &provs {
            w.provides.entry(*pv).or_default().push("multi".to_string());
        }
        w.intents.push(fetch(t + 45 * NS, dst, "multi", provs, 120 * NS));
    }
    Ok(())
}

fn fetch(t: u64, node: usize, name: &str, providers: Vec<usize>, deadline: u64) -> Intent {
    let mut d = Intent::new(t, node, IntentKind::Fetch, deadline, Must::Flag(true));
    d.value = Some(name.to_string());
    d.providers = providers;
    d
}

// ------------------------------------------------------------------ S4

fn s4(w: &mut World, b: &mut Builder) -> Result<(), WorldError> {
    let (clouds, homes, mobiles) = standard_nodes(w, b)?;
    let mut hostile = Vec::new();
    let share = b.p.num("hostile_share")?;
    for &i in homes.iter().chain(mobiles.iter()) {
        if b.rng.random() < share {
            hostile.push(i);
        }
    }
    for &i in &hostile {
        let sid = w.nodes[i].site;
        let mut mb = MiddleboxSpec {
            udp_block: true,
            tcp_ports: b.p.int_list("tcp_ports")?.iter().map(|x| *x as u16).collect(),
            tls_only: b.p.flag("tls_only")?,
            fw_reject: b.p.flag("fw_reject")?,
            portal_ns: None,
        };
        if b.rng.random() < b.p.num("portal_share")? {
            mb.portal_ns = Some(scaled(b.pick("portal_s")?, NS));
        }
        w.sites[sid].middlebox = Some(mb);
        for k in 0..w.sites[sid].nats.len() {
            w.sites[sid].nats[k].tcp_timeout_ns = Some(scaled(b.pick("tcp_idle_s")?, NS));
        }
    }
    finish(w, clouds, homes, mobiles);
    w.hostile.clone_from(&hostile);
    mixed(w, b)?;
    let portal = |w: &World, x: usize| -> u64 {
        if !hostile.contains(&x) {
            return 0;
        }
        w.sites[w.nodes[x].site]
            .middlebox
            .as_ref()
            .and_then(|m| m.portal_ns)
            .unwrap_or(0)
    };
    let mut starts: std::collections::BTreeMap<usize, Vec<u64>> = std::collections::BTreeMap::new();
    for e in &w.env {
        if matches!(e.kind, EnvKind::Start | EnvKind::Restart) {
            starts.entry(e.node).or_default().push(e.t);
        }
    }
    let portals: std::collections::BTreeMap<usize, u64> = (0..w.nodes.len()).map(|x| (x, portal(w, x))).collect();
    let behind = |x: usize, d: &Intent| -> bool {
        let pt = portals.get(&x).copied().unwrap_or(0);
        pt != 0
            && starts
                .get(&x)
                .is_some_and(|ss| ss.iter().any(|s| *s <= d.t + d.deadline_ns && d.t < *s + pt + 5 * NS))
    };
    for d in &mut w.intents {
        let mut ends = vec![d.node];
        ends.extend(d.to);
        ends.extend(d.providers.iter().copied());
        if ends.iter().any(|x| behind(*x, d)) {
            d.must = if d.kind == IntentKind::Publish {
                Must::Set(Vec::new())
            } else {
                Must::Flag(false)
            };
        } else if let (IntentKind::Publish, Must::Set(m)) = (d.kind, &d.must) {
            let kept: Vec<usize> = m.iter().copied().filter(|r| !behind(*r, d)).collect();
            d.must = Must::Set(kept);
        }
    }
    Ok(())
}

// ------------------------------------------------------------------ S10

fn browser(w: &mut World, b: &mut Builder, region: usize, mobile: bool) -> Result<usize, WorldError> {
    let (m, f) = if mobile {
        carrier_nat(&mut b.rng)
    } else {
        home_nat(&mut b.rng)
    };
    let timeout = nat_timeout(&mut b.rng, mobile);
    let nat = b.nat(m, f, timeout)?;
    let sid = if mobile {
        let delay_ns = scaled(b.pick("mobile_delay_ms")?, MS);
        let loss = b.p.num("mobile_loss")?;
        let burst_ns = scaled(b.pick("burst_ms")?, MS);
        b.site(
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
        )?
    } else {
        let delay_ns = scaled(b.rng.uniform(3.0, 12.0), MS);
        let loss = b.p.num("home_loss")?;
        let burst_ns = scaled(b.pick("burst_ms")?, MS);
        b.site(
            w,
            SiteArgs {
                region,
                up_bps: 10_000_000,
                down_bps: 50_000_000,
                delay_ns,
                loss,
                burst_ns,
                nats: vec![nat],
                v6_open: false,
                queue: None,
            },
        )?
    };
    let idx = w.nodes.len();
    let host = 3_000_000 + sid as u64 * 256 + (idx as u64 % 250);
    let ifaces = vec![IfaceSpec {
        name: "w".to_string(),
        kind: "ws".to_string(),
        addr: Addr {
            kind: "tcp4".to_string(),
            host,
            port: 50001,
        },
        mtu: 1 << 20,
        public: false,
        v6: false,
    }];
    w.nodes.push(NodeSpec {
        device: "browser".to_string(),
        site: sid,
        kind: "browser".to_string(),
        region,
        ifaces,
        topics: Vec::new(),
        sites: Vec::new(),
        clock: None,
        cpu_factor: None,
    });
    Ok(idx)
}

fn s10(w: &mut World, b: &mut Builder) -> Result<(), WorldError> {
    let mut clouds = Vec::new();
    for r in 0..b.p.count("n_cloud")? {
        clouds.push(b.add_cloud(w, r % 3)?);
    }
    let mut homes = Vec::new();
    for _ in 0..b.p.count("n_home")? {
        let region = below(&mut b.rng, 3, "regions")?;
        homes.push(b.add_home(w, region, None, None)?);
    }
    let share = b.p.num("browser_mobile_share")?;
    let mut browsers = Vec::new();
    for _ in 0..b.p.count("n_browser")? {
        let region = below(&mut b.rng, 3, "regions")?;
        let mobile = b.rng.random() < share;
        browsers.push(browser(w, b, region, mobile)?);
    }
    finish(w, clouds, homes, browsers.clone());
    mixed(w, b)?;
    w.browsers = browsers;
    Ok(())
}

// ------------------------------------------------------------------ S12

fn s12(w: &mut World, b: &mut Builder) -> Result<(), WorldError> {
    standard(w, b)?;
    let n = w.nodes.len();
    let sybils = w.denied.clone();
    let (t0, t1, t0s, t1s) = window(b)?;
    let honest: Vec<usize> = (0..n).filter(|i| !sybils.contains(i)).collect();
    let mut topics: Vec<Vec<u8>> = honest.iter().flat_map(|i| w.nodes[*i].topics.clone()).collect();
    topics.sort();
    topics.dedup();
    let every = b.p.num("sybil_publish_every_s")?;
    let clouds = w.clouds.clone();
    for &i in &sybils {
        w.nodes[i].topics.clone_from(&topics);
        let mut t = t0 + scaled(b.rng.uniform(5.0, 15.0), NS);
        while t < t1 {
            let tp = topics[below(&mut b.rng, topics.len(), "topics")?].clone();
            let rec: Vec<usize> = honest
                .iter()
                .copied()
                .filter(|j| w.nodes[*j].topics.contains(&tp))
                .collect();
            let mut d = Intent::new(t, i, IntentKind::Publish, 60 * NS, Must::Set(Vec::new()));
            d.topic = Some(tp);
            d.size = Some(200);
            d.receivers = rec;
            w.intents.push(d);
            t += scaled(b.rng.expovariate(1.0 / every), NS);
        }
        for _ in 0..3 {
            let z = choice(&mut b.rng, &clouds, "clouds")?;
            let tp = scaled(b.rng.uniform(t0s + 5.0, t1s), NS);
            let mut d = Intent::new(tp, i, IntentKind::Push, 60 * NS, Must::Flag(false));
            d.to = Some(z);
            d.size = Some(2048);
            w.intents.push(d);
            let td = scaled(b.rng.uniform(t0s + 5.0, t1s), NS);
            let to = choice(&mut b.rng, &honest, "honest nodes")?;
            let mut d = Intent::new(td, i, IntentKind::Docsync, 60 * NS, Must::Flag(false));
            d.to = Some(to);
            d.req = Some(120);
            d.resp = Some(4096);
            w.intents.push(d);
        }
    }
    let cands: Vec<usize> = w.homes.iter().copied().filter(|x| !sybils.contains(x)).collect();
    let liars = sample(&mut b.rng, &cands, 2, "liars")?;
    w.liars.clone_from(&liars);
    let revoked_nodes: Vec<usize> = w.revoked.iter().map(|(r, _)| *r).collect();
    for j in 0..b.p.count("n_liar_fetch")? {
        let (llo, lhi) = b.p.pair("liar_sizes")?;
        let size = b.rng.uniform(llo, lhi) as u64;
        let name = format!("lv{j}");
        let liar = liars[j % liars.len()];
        let good = choice(&mut b.rng, &clouds, "clouds")?;
        w.values.insert(name.clone(), size);
        for pv in [liar, good] {
            w.provides.entry(pv).or_default().push(name.clone());
        }
        let c: Vec<usize> = honest
            .iter()
            .copied()
            .filter(|x| *x != liar && *x != good && !revoked_nodes.contains(x))
            .collect();
        let f = choice(&mut b.rng, &c, "fetchers")?;
        let t = scaled(b.rng.uniform(t0s + 20.0, t1s - 120.0), NS);
        w.intents.push(fetch(t, f, &name, vec![liar, good], 120 * NS));
    }
    if let Some(&(x, tv)) = w.revoked.first() {
        let lead = scaled(b.rng.uniform(20.0, 60.0), NS);
        let t = tv.checked_sub(lead).ok_or(WorldError::Empty("compromise time"))?;
        w.compromise_node = Some((t, x));
    }
    w.eclipse_victim = Some(choice(&mut b.rng, &w.homes.clone(), "homes")?);
    Ok(())
}

// ------------------------------------------------------------------ S13

/// `cut_between`: is any packet between sites `sa` and `sb`, either way, cut during `[t0, t1]`?
pub(super) fn cut_between(cuts: &[Cut], t0: u64, t1: u64, sa: usize, sb: usize) -> bool {
    cuts.iter().any(|c| {
        c.from <= t1
            && c.to >= t0
            && ((c.x.contains(&sa) && c.y.contains(&sb)) || (c.x.contains(&sb) && c.y.contains(&sa)))
    })
}

fn s13(w: &mut World, b: &mut Builder) -> Result<(), WorldError> {
    standard(w, b)?;
    let n = w.nodes.len();
    let share = b.p.num("stateless_share")?;
    for e in &mut w.env {
        if e.kind == EnvKind::Restart && b.rng.random() < share {
            e.arg = EnvArg::Flag(false);
        }
    }
    let clouds = w.clouds.clone();
    let mut others: Vec<usize> = (0..n).filter(|i| !clouds.contains(i)).collect();
    b.rng.shuffle(&mut others);
    let (w0, w1) = b.p.int_pair("cut_window_s")?;
    let modes = b.p.str_list("partitions")?.to_vec();
    let span = (w1 - w0) as f64 / modes.len().max(1) as f64;
    let site = |w: &World, xs: &[usize]| -> Vec<usize> { xs.iter().map(|x| w.nodes[*x].site).collect() };
    let mut cuts = Vec::new();
    for (k, mode) in modes.iter().enumerate() {
        let a = scaled(w0 as f64 + k as f64 * span + b.rng.uniform(0.0, span / 3.0), NS);
        let z = a + scaled(b.pick("cut_s")?, NS);
        let grp: Vec<usize> = others.iter().skip(k * 3).take(3).copied().collect();
        let rest: Vec<usize> = (0..n).filter(|i| !grp.contains(i)).collect();
        let (y, both) = match mode.as_str() {
            "complete" => (site(w, &rest), true),
            "partial" => {
                let nc: Vec<usize> = rest.iter().copied().filter(|i| !clouds.contains(i)).collect();
                let half: Vec<usize> = nc.into_iter().take(rest.len() / 2).collect();
                (site(w, &half), true)
            }
            _ => (site(w, &rest), false),
        };
        cuts.push(Cut {
            from: a,
            to: z,
            x: site(w, &grp),
            y,
            both,
        });
    }
    unmust_cut(w, &cuts);
    w.partitions = cuts;
    for &i in &others {
        let offset_ns = (b.pick("skew_s")? * NS as f64) as i64;
        let drift_ppm = b.pick("drift_ppm")? as i64;
        w.nodes[i].clock = Some(ClockSpec {
            offset_ns,
            drift_ppm,
            jumps: Vec::new(),
        });
    }
    let n_jump = b.p.count("n_jump")?.min(others.len());
    for i in sample(&mut b.rng, &others, n_jump, "jumping clocks")? {
        let at = scaled(b.rng.uniform(60.0, 400.0), NS);
        let jump = scaled(b.pick("jump_s")?, NS);
        if let Some(c) = w.nodes[i].clock.as_mut() {
            c.jumps = vec![(at, jump)];
        }
    }
    let n_slow = b.p.count("n_slow")?.min(others.len());
    for i in sample(&mut b.rng, &others, n_slow, "slow nodes")? {
        w.nodes[i].cpu_factor = Some(b.pick("slow_factor")? as u32);
    }
    Ok(())
}

/// `_unmust_cut`: an intent whose path is cut during its deadline has no must.
fn unmust_cut(w: &mut World, cuts: &[Cut]) {
    let site: Vec<usize> = w.nodes.iter().map(|nd| nd.site).collect();
    for d in &mut w.intents {
        let (a, dl) = (d.node, d.deadline_ns);
        if d.kind == IntentKind::Publish {
            if let Must::Set(m) = &d.must {
                let kept = m
                    .iter()
                    .copied()
                    .filter(|r| !cut_between(cuts, d.t, d.t + dl, site[a], site[*r]))
                    .collect();
                d.must = Must::Set(kept);
            }
            continue;
        }
        let peers: Vec<usize> = d.to.map_or_else(|| d.providers.clone(), |z| vec![z]);
        if peers
            .iter()
            .any(|z| cut_between(cuts, d.t, d.t + dl, site[a], site[*z]))
        {
            d.must = Must::Flag(false);
        }
    }
}

// ------------------------------------------------------------------ S15

fn s15(w: &mut World, b: &mut Builder) -> Result<(), WorldError> {
    standard(w, b)?;
    w.soak = true;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cut(from: u64, to: u64, x: &[usize], y: &[usize]) -> Cut {
        Cut {
            from,
            to,
            x: x.to_vec(),
            y: y.to_vec(),
            both: true,
        }
    }

    #[test]
    fn cut_between_is_symmetric_and_windowed() {
        let cuts = [cut(100, 200, &[1], &[2, 3])];
        assert!(cut_between(&cuts, 150, 160, 1, 2));
        assert!(cut_between(&cuts, 150, 160, 3, 1));
        assert!(cut_between(&cuts, 50, 100, 1, 2), "touching the start counts");
        assert!(cut_between(&cuts, 200, 300, 1, 2), "touching the end counts");
        assert!(!cut_between(&cuts, 0, 99, 1, 2));
        assert!(!cut_between(&cuts, 201, 300, 1, 2));
        assert!(!cut_between(&cuts, 150, 160, 2, 3), "both on the same side");
        assert!(!cut_between(&cuts, 150, 160, 1, 9), "a site outside the cut");
    }
}
