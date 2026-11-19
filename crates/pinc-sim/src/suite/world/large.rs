//! S11: values from 1 MiB to 1 TiB, multi-provider fetches, a streaming consumer, disconnections and restarts, with
//! small control traffic running under the bulk transfers (`_large_values`).
//!
//! Invariant: draws in the reference order; the nodes that restart are visited in ascending node order, which is
//! the iteration order of the reference's small-integer set.

use std::collections::BTreeSet;

use super::WorldError;
use super::build::{Builder, MIB, NS, choice, sample, scaled};
use super::model::{Change, ChangeKind, EnvAction, EnvArg, EnvKind, Intent, IntentKind, Must, World};
use super::params::ParamsExt;

fn fetch(t: u64, node: usize, name: &str, providers: Vec<usize>, deadline: u64) -> Intent {
    let mut d = Intent::new(t, node, IntentKind::Fetch, deadline, Must::Flag(true));
    d.value = Some(name.to_string());
    d.providers = providers;
    d
}

/// Adds `name` of `size` bytes provided by `prov`.
fn provide(w: &mut World, name: &str, size: u64, prov: usize) {
    w.values.insert(name.to_string(), size);
    w.provides.entry(prov).or_default().push(name.to_string());
}

/// The workload of S11 on the nodes built so far.
pub(super) fn large_values(w: &mut World, b: &mut Builder) -> Result<(), WorldError> {
    let n = w.nodes.len();
    let (clouds, homes, mobiles) = (w.clouds.clone(), w.homes.clone(), w.mobiles.clone());
    for i in 0..n {
        let t = if w.bootstrap.contains(&i) {
            0
        } else {
            scaled(b.rng.uniform(0.5, 3.0), NS)
        };
        w.env.push(EnvAction {
            t,
            kind: EnvKind::Start,
            node: i,
            arg: EnvArg::None,
        });
        w.nodes[i].topics = vec![b"/col/0".to_vec()];
    }
    let mut providers = clouds.clone();
    providers.extend(homes.iter().take(2));
    let mut fetchers: Vec<usize> = homes.iter().skip(2).copied().collect();
    fetchers.extend(&mobiles);
    if providers.is_empty() || fetchers.is_empty() {
        return Err(WorldError::Empty("providers or fetchers"));
    }
    let t = 15 * NS;
    let dl = 240 * NS;
    let n_restart = b.p.count("n_restart")?.min(fetchers.len());
    // vertexia: ascending order equals the reference's set order only for one restart or small ids without hash
    // collisions (the reference iterates a Python set); emulate the set's slot order if a variant restarts several.
    let restarts: BTreeSet<usize> = sample(&mut b.rng, &fetchers, n_restart, "restarting nodes")?
        .into_iter()
        .collect();
    let rest: Vec<usize> = fetchers.iter().copied().filter(|x| !restarts.contains(x)).collect();
    let n_disc = b.p.count("n_disconnect")?.min(fetchers.len());
    let disconn = sample(&mut b.rng, &rest, n_disc, "disconnecting nodes")?;
    let mut k = 0usize;
    let next = |k: &mut usize| {
        let f = fetchers[*k % fetchers.len()];
        *k += 1;
        f
    };
    for (j, size) in b.p.int_list("full_sizes")?.iter().enumerate() {
        let name = format!("full{j}");
        let prov = providers[j % providers.len()];
        provide(w, &name, *size as u64, prov);
        let f = next(&mut k);
        w.intents.push(fetch(t + j as u64 * 8 * NS, f, &name, vec![prov], dl));
    }
    let multi = b.p.int("multi_size")? as u64;
    let provs: Vec<usize> = providers[..b.p.count("n_multi_prov")?.min(providers.len())].to_vec();
    provide_all(w, "multi", multi, &provs);
    let f = next(&mut k);
    w.intents.push(fetch(t + 30 * NS, f, "multi", provs, dl));
    for (j, size) in b.p.int_list("range_sizes")?.iter().enumerate() {
        let size = *size as u64;
        let name = format!("huge{j}");
        let prov = providers[(j + 1) % providers.len()];
        provide(w, &name, size, prov);
        let f = next(&mut k);
        let mut d = fetch(t + (40 + 5 * j as u64) * NS, f, &name, vec![prov], dl);
        d.ranges = vec![(0, 2 * MIB), (size / 2 + 12345, MIB), (size.saturating_sub(MIB), MIB)];
        w.intents.push(d);
    }
    let stream_size = b.p.int("stream_size")? as u64;
    let prov = providers[providers.len() - 1];
    provide(w, "stream", stream_size, prov);
    let f = next(&mut k);
    let mut d = fetch(t + 60 * NS, f, "stream", vec![prov], dl);
    d.stream_rate = Some(b.p.int("stream_rate_bps")? as u64);
    w.intents.push(d);
    let bulk_nodes: Vec<usize> = w
        .intents
        .iter()
        .map(|d| d.node)
        .chain(providers.iter().copied())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    for &x in &disconn {
        let Some(first) = w.intents.iter().find(|d| d.node == x).map(|d| d.t) else {
            continue;
        };
        let a = first + scaled(b.rng.uniform(2.0, 6.0), NS);
        let o = scaled(b.rng.uniform(2.0, 8.0), NS);
        w.env.push(EnvAction {
            t: a,
            kind: EnvKind::Outage,
            node: x,
            arg: EnvArg::Num(o),
        });
    }
    for &x in &restarts {
        let Some(first) = w.intents.iter().find(|d| d.node == x).map(|d| d.t) else {
            continue;
        };
        let a = first + scaled(b.rng.uniform(2.0, 5.0), NS);
        w.env.push(EnvAction {
            t: a,
            kind: EnvKind::Crash,
            node: x,
            arg: EnvArg::None,
        });
        w.env.push(EnvAction {
            t: a + 5 * NS,
            kind: EnvKind::Restart,
            node: x,
            arg: EnvArg::Flag(true),
        });
        w.changes.push(Change {
            t: a,
            kind: ChangeKind::Crash,
            node: x,
            version: None,
        });
        w.changes.push(Change {
            t: a + 5 * NS,
            kind: ChangeKind::Join,
            node: x,
            version: None,
        });
    }
    for _ in 0..6 {
        let c: Vec<usize> = bulk_nodes.iter().copied().filter(|x| !clouds.contains(x)).collect();
        let o = choice(&mut b.rng, &c, "bulk nodes")?;
        let r = choice(&mut b.rng, &clouds, "clouds")?;
        let mut tt = t + 20 * NS;
        while tt < 200 * NS {
            let mut d = Intent::new(tt, o, IntentKind::Push, 60 * NS, Must::Flag(!restarts.contains(&o)));
            d.to = Some(r);
            d.size = Some(512 + b.rng.randbelow(1024));
            d.under_bulk = true;
            w.intents.push(d);
            tt += scaled(b.rng.uniform(2.0, 6.0), NS);
        }
    }
    for i in 0..n {
        if clouds.contains(&i) {
            continue;
        }
        let mut tt = t + scaled(b.rng.uniform(0.0, 20.0), NS);
        while tt < 200 * NS {
            let rec: Vec<usize> = (0..n).filter(|j| *j != i && !restarts.contains(j)).collect();
            let must = if restarts.contains(&i) { Vec::new() } else { rec.clone() };
            let mut d = Intent::new(tt, i, IntentKind::Publish, 60 * NS, Must::Set(must));
            d.topic = Some(b"/col/0".to_vec());
            d.size = Some(200);
            d.receivers = rec;
            d.under_bulk = true;
            w.intents.push(d);
            tt += scaled(b.rng.uniform(15.0, 30.0), NS);
        }
    }
    for _ in 0..10 {
        let live: Vec<usize> = (0..n).filter(|x| !restarts.contains(x)).collect();
        let a = choice(&mut b.rng, &live, "echo origins")?;
        let c: Vec<usize> = live.iter().copied().filter(|x| *x != a).collect();
        let z = choice(&mut b.rng, &c, "echo peers")?;
        let tt = scaled(b.rng.uniform(20.0, 200.0), NS);
        let mut d = Intent::new(tt, a, IntentKind::Echo, 30 * NS, Must::Flag(true));
        d.to = Some(z);
        w.intents.push(d);
    }
    w.revoked.clear();
    Ok(())
}

fn provide_all(w: &mut World, name: &str, size: u64, provs: &[usize]) {
    w.values.insert(name.to_string(), size);
    for pv in provs {
        w.provides.entry(*pv).or_default().push(name.to_string());
    }
}
