//! S6 (low bandwidth): thin access links and the capacity-feasible plan (`_thin`, `_capacity_load`,
//! `_capacity_deadlines`).
//!
//! Invariant: float arithmetic follows the reference expression by expression (the order of the products and
//! quotients decides the last bit), and `round(x, 3)` is the correctly rounded decimal value, as Python's is.

use std::collections::BTreeMap;

use super::WorldError;
use super::build::{Builder, KIB, MS, NS, SiteArgs, below, carrier_nat, finish, home_nat, nat_timeout, scaled};
use super::mixed::mixed;
use super::model::{EnvKind, IntentKind, Must, NodeSpec, World};
use super::params::ParamsExt;

/// The bytes of a hybrid post-quantum handshake with certificates, both ways (an upper bound).
const HANDSHAKE_B: u128 = 8 * KIB as u128;

fn thin(
    w: &mut World,
    b: &mut Builder,
    region: usize,
    bps: &str,
    delay: &str,
    cellular: bool,
) -> Result<usize, WorldError> {
    let (m, f) = if cellular {
        carrier_nat(&mut b.rng)
    } else {
        home_nat(&mut b.rng)
    };
    let timeout = nat_timeout(&mut b.rng, cellular);
    let nat = b.nat(m, f, timeout)?;
    let down = b.pick(bps)? as u64;
    let up = (down as f64 * b.rng.uniform(0.4, 1.0)) as u64;
    let v6 = b.rng.random() < b.p.num("v6_share")?;
    let delay_ns = scaled(b.pick(delay)?, MS);
    let loss = b.pick("loss")?;
    let burst_ns = scaled(b.pick("burst_ms")?, MS);
    let v6_open = v6 && b.rng.random() < b.p.num("v6_open_share")?;
    let sid = b.site(
        w,
        SiteArgs {
            region,
            up_bps: up,
            down_bps: down,
            delay_ns,
            loss,
            burst_ns,
            nats: vec![nat],
            v6_open,
            queue: Some((8 * KIB).max(down / 8 * 2)),
        },
    )?;
    let idx = w.nodes.len();
    let ifaces = b.ifaces(sid, idx, v6, false);
    let (device, kind) = if cellular {
        ("phone", "mobile")
    } else {
        ("desktop", "home")
    };
    w.nodes.push(NodeSpec {
        device: device.to_string(),
        site: sid,
        kind: kind.to_string(),
        region,
        ifaces,
        topics: Vec::new(),
        sites: Vec::new(),
        clock: None,
        cpu_factor: None,
    });
    Ok(idx)
}

/// S6.
pub(super) fn s6(w: &mut World, b: &mut Builder) -> Result<(), WorldError> {
    let mut clouds = Vec::new();
    for r in 0..b.p.count("n_cloud")? {
        clouds.push(b.add_cloud(w, r % 3)?);
    }
    let mut homes = Vec::new();
    for _ in 0..b.p.count("n_geo")? {
        let region = below(&mut b.rng, 3, "regions")?;
        homes.push(thin(w, b, region, "geo_bps", "geo_delay_ms", false)?);
    }
    let mut mobiles = Vec::new();
    for _ in 0..b.p.count("n_rural")? {
        let region = below(&mut b.rng, 3, "regions")?;
        mobiles.push(thin(w, b, region, "rural_bps", "rural_delay_ms", true)?);
    }
    for _ in 0..b.p.count("n_2g")? {
        let region = below(&mut b.rng, 3, "regions")?;
        mobiles.push(thin(w, b, region, "g2_bps", "g2_delay_ms", true)?);
    }
    finish(w, clouds, homes, mobiles);
    mixed(w, b)?;
    let cap = if b.p.contains_key("load_cap") {
        b.p.num("load_cap")?
    } else {
        0.25
    };
    capacity_load(w, b, cap)?;
    capacity_deadlines(w);
    Ok(())
}

/// Python's `round(x, 3)`: the nearest decimal with three digits, ties to even, read back as a float.
fn round3(x: f64) -> f64 {
    format!("{x:.3}").parse().unwrap_or(x)
}

/// Keeps intents (in list order) only while every node's application bytes stay within `cap` of its uplink and
/// downlink capacity over the active window.
fn capacity_load(w: &mut World, b: &Builder, cap: f64) -> Result<(), WorldError> {
    let (lo, hi) = b.p.int_pair("active_s")?;
    let span = (hi - lo) as u64 * NS;
    let budget: Vec<[f64; 2]> = w
        .nodes
        .iter()
        .map(|nd| {
            let s = &w.sites[nd.site];
            [
                cap * s.up_bps as f64 / 8.0 * span as f64 / NS as f64,
                cap * s.down_bps as f64 / 8.0 * span as f64 / NS as f64,
            ]
        })
        .collect();
    let mut used = vec![[0u64; 2]; budget.len()];
    let mut kept = Vec::new();
    for d in std::mem::take(&mut w.intents) {
        let a = d.node;
        let ch: Vec<(usize, usize, u64)> = match d.kind {
            IntentKind::Publish => {
                let size = d.size.unwrap_or(0);
                let mut ch = vec![(a, 0, size * (d.receivers.len().clamp(1, 3) as u64))];
                ch.extend(d.receivers.iter().map(|r| (*r, 1, size)));
                ch
            }
            IntentKind::Push => {
                let size = d.size.unwrap_or(0);
                vec![(a, 0, size), (d.to.unwrap_or(0), 1, size)]
            }
            IntentKind::Docsync => {
                let (req, resp, to) = (d.req.unwrap_or(0), d.resp.unwrap_or(0), d.to.unwrap_or(0));
                vec![(a, 0, req), (to, 1, req), (to, 0, resp), (a, 1, resp)]
            }
            IntentKind::Fetch => {
                let n = d.value.as_ref().and_then(|v| w.values.get(v)).copied().unwrap_or(0);
                let share = n / (d.providers.len().max(1) as u64);
                let mut ch: Vec<(usize, usize, u64)> = d.providers.iter().map(|pv| (*pv, 0, share)).collect();
                ch.push((a, 1, n));
                ch
            }
            _ => Vec::new(),
        };
        if ch.iter().any(|(i, wd, n)| (used[*i][*wd] + n) as f64 > budget[*i][*wd]) {
            continue;
        }
        for (i, wd, n) in ch {
            used[i][wd] += n;
        }
        kept.push(d);
    }
    w.intents = kept;
    let load: BTreeMap<usize, (f64, f64)> = used
        .iter()
        .enumerate()
        .filter(|(i, _)| budget[*i][0] != 0.0)
        .map(|(i, u)| {
            (
                i,
                (
                    round3(u[0] as f64 / budget[i][0] * cap),
                    round3(u[1] as f64 / budget[i][1] * cap),
                ),
            )
        })
        .collect();
    w.load_used = load;
    Ok(())
}

/// Capacity-feasible time to move `nbytes` from node `a` to node `z`: a handshake of four round trips plus the
/// serialisation at the bottleneck, inflated for loss.
fn path_time(w: &World, a: usize, z: usize, nbytes: u64) -> u64 {
    let (sa, sz) = (&w.sites[w.nodes[a].site], &w.sites[w.nodes[z].site]);
    let bps = u128::from(sa.up_bps.min(sz.down_bps));
    let rtt = 2
        * (u128::from(sa.up_delay_ns)
            + u128::from(w.region_delay_ns[sa.region][sz.region])
            + u128::from(sz.down_delay_ns));
    let loss = 1.0 - (1.0 - sa.loss) * (1.0 - sz.loss);
    let ser = (u128::from(nbytes) + HANDSHAKE_B) * 8 * u128::from(NS) / bps;
    let keep = std::hint::black_box(1.0 - loss).powf(std::hint::black_box(2.0));
    ((4 * rtt + ser) as f64 / keep) as u64
}

/// Every must deadline is at least three times the capacity-feasible time on its path; an intent whose longer window
/// meets a departure or the end of the run is not must.
fn capacity_deadlines(w: &mut World) {
    const SLACK: u64 = 3;
    let mut down: BTreeMap<usize, Vec<u64>> = BTreeMap::new();
    for e in &w.env {
        if matches!(e.kind, EnvKind::Leave | EnvKind::Crash | EnvKind::Upgrade) {
            down.entry(e.node).or_default().push(e.t);
        }
    }
    let end = w.idle_window.0;
    let up = |i: usize, t0: u64, t1: u64| !down.get(&i).is_some_and(|ds| ds.iter().any(|x| t0 <= *x && *x <= t1));
    let mut intents = std::mem::take(&mut w.intents);
    for d in &mut intents {
        let (a, t) = (d.node, d.t);
        let flows: Vec<(usize, usize, u64)> = match d.kind {
            IntentKind::Publish => {
                let size = d.size.unwrap_or(0) * (d.receivers.len().clamp(1, 3) as u64);
                d.receivers.iter().map(|r| (a, *r, size)).collect()
            }
            IntentKind::Fetch => {
                let n = d.value.as_ref().and_then(|v| w.values.get(v)).copied().unwrap_or(0);
                d.providers.iter().map(|pv| (*pv, a, n)).collect()
            }
            IntentKind::Docsync => {
                let to = d.to.unwrap_or(0);
                vec![(a, to, d.req.unwrap_or(120)), (to, a, d.resp.unwrap_or(2048))]
            }
            IntentKind::Push | IntentKind::Manage => vec![(a, d.to.unwrap_or(0), d.size.unwrap_or(2048))],
            _ => vec![(a, d.to.unwrap_or(0), 0)],
        };
        if flows.is_empty() {
            continue;
        }
        let need = flows
            .iter()
            .map(|(x, y, n)| path_time(w, *x, *y, *n))
            .max()
            .unwrap_or(0)
            * SLACK;
        let dl = d.deadline_ns.max(need);
        d.deadline_ns = dl;
        if d.kind == IntentKind::Publish {
            if let Must::Set(m) = &d.must {
                let kept = m
                    .iter()
                    .copied()
                    .filter(|r| t + dl < end && up(*r, t, t + dl) && up(a, t, t + dl))
                    .collect();
                d.must = Must::Set(kept);
            }
        } else if d.must == Must::Flag(true) {
            let mut ends = vec![a];
            match d.to {
                Some(z) => ends.push(z),
                None => ends.extend(d.providers.iter().copied()),
            }
            d.must = Must::Flag(t + dl < end && ends.iter().all(|x| up(*x, t, t + dl)));
        }
    }
    w.intents = intents;
}

#[cfg(test)]
mod tests {
    use super::round3;

    #[test]
    fn round3_is_python_round() {
        // values checked against CPython 3.14: round(0.0625, 3) == 0.062, round(0.0635, 3) == 0.064 (the double is
        // above the tie), round(2.675, 2)-style ties follow the exact binary value.
        assert_eq!(round3(0.0625), 0.062);
        assert_eq!(round3(0.0635), 0.064);
        assert_eq!(round3(0.1245), 0.124);
        assert_eq!(round3(0.5), 0.5);
    }
}
