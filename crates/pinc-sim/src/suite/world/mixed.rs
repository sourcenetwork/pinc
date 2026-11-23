//! The internet-mix workload of S2, S3, S5 and the phase-1 scenarios built on it (`_mixed`): churn, mobile
//! shakiness, publications, ordered pushes, request flows, probes and value fetches, with the ground truth of what
//! must complete worked out from the plan of who is up and when.
//!
//! Invariant: every draw happens in the reference order, including the draws whose result is then discarded (an
//! intent is dropped after its time was drawn); the environment and intent lists are left unsorted for the caller.

use std::collections::BTreeMap;

use super::WorldError;
use super::build::{Builder, MS, NS, below, choice, sample, scaled};
use super::model::{Change, ChangeKind, EnvAction, EnvArg, EnvKind, Intent, IntentKind, Must, World};
use super::params::ParamsExt;

/// Who is up, down, suspended or revoked, as the generator planned it.
pub(super) struct Plan {
    starts: Vec<u64>,
    down: BTreeMap<usize, Vec<(u64, Option<u64>)>>,
    susp: BTreeMap<usize, Vec<(u64, u64)>>,
    revoked: Vec<(usize, u64)>,
    denied: Vec<usize>,
}

impl Plan {
    /// `up_through(i, a, z)`: node `i` is up and not revoked or denied for all of `[a, z]`.
    fn up(&self, i: usize, a: u64, z: u64) -> bool {
        if a < self.starts[i] + 2 * NS {
            return false;
        }
        if self
            .down
            .get(&i)
            .is_some_and(|ds| ds.iter().any(|(d0, d1)| *d0 <= z && d1.is_none_or(|d1| d1 >= a)))
        {
            return false;
        }
        if self.revoked.iter().any(|(r, tv)| *r == i && *tv <= z) {
            return false;
        }
        !self.denied.contains(&i)
    }

    /// `not_suspended(i, a, z)`.
    fn awake(&self, i: usize, a: u64, z: u64) -> bool {
        !self
            .susp
            .get(&i)
            .is_some_and(|ss| ss.iter().any(|(s0, s1)| *s0 <= z && *s1 >= a))
    }

    fn both(&self, i: usize, a: u64, z: u64) -> bool {
        self.up(i, a, z) && self.awake(i, a, z)
    }
}

fn env(w: &mut World, t: u64, kind: EnvKind, node: usize, arg: EnvArg) {
    w.env.push(EnvAction { t, kind, node, arg });
}

fn change(w: &mut World, t: u64, kind: ChangeKind, node: usize, version: Option<u64>) {
    w.changes.push(Change { t, kind, node, version });
}

/// The active window `(t0, t1)` in nanoseconds and in seconds.
pub(super) fn window(b: &Builder) -> Result<(u64, u64, f64, f64), WorldError> {
    let (lo, hi) = b.p.int_pair("active_s")?;
    Ok((lo as u64 * NS, hi as u64 * NS, lo as f64, hi as f64))
}

/// `_mixed(sc, b, p, rng)`: S2, S3, S5 and the base workload of S1, S4, S6, S10, S12, S13 and S15.
pub(super) fn mixed(w: &mut World, b: &mut Builder) -> Result<(), WorldError> {
    let n = w.nodes.len();
    let (clouds, homes, mobiles) = (w.clouds.clone(), w.homes.clone(), w.mobiles.clone());
    let (t0, t1, t0s, t1s) = window(b)?;
    let topics: Vec<Vec<u8>> = (0..4).map(|i| format!("/col/{i}").into_bytes()).collect();
    for node in &mut w.nodes {
        if node.kind == "cloud" {
            node.topics.clone_from(&topics);
        } else {
            let k = 1 + usize::from(b.rng.random() < 0.4);
            let mut picked = sample(&mut b.rng, &topics, k, "topics")?
                .into_iter()
                .collect::<Vec<_>>();
            picked.sort();
            node.topics = picked;
        }
    }
    let mut starts = vec![0u64; n];
    for (i, s) in starts.iter_mut().enumerate() {
        *s = if w.bootstrap.contains(&i) {
            0
        } else {
            scaled(b.rng.uniform(0.5, 4.0), NS)
        };
    }
    let others: Vec<usize> = (0..n).filter(|i| !clouds.contains(i)).collect();
    let mut denied = Vec::new();
    if b.p.truthy("n_denied") {
        let k = b.p.count("n_denied")?;
        denied = sample(&mut b.rng, &others, k, "denied nodes")?;
        w.denied.clone_from(&denied);
    }
    let mut churnable: Vec<usize> = others.iter().copied().filter(|i| !denied.contains(i)).collect();
    b.rng.shuffle(&mut churnable);
    let mut k = 0usize;
    let take = |k: &mut usize| -> Result<usize, WorldError> {
        let i = churnable.get(*k).copied().ok_or(WorldError::Empty("churnable nodes"))?;
        *k += 1;
        Ok(i)
    };
    for _ in 0..b.p.int_or("n_late_join", 0)?.max(0) {
        let i = take(&mut k)?;
        starts[i] = scaled(b.rng.uniform(60.0, 200.0), NS);
        change(w, starts[i], ChangeKind::Join, i, None);
    }
    for (i, s) in starts.iter().enumerate() {
        env(w, *s, EnvKind::Start, i, EnvArg::None);
    }
    let mut down: BTreeMap<usize, Vec<(u64, Option<u64>)>> = BTreeMap::new();
    let crash_frac = if b.p.contains_key("crash_frac") {
        b.p.num("crash_frac")?
    } else {
        0.0
    };
    let ncrash = (crash_frac * others.len() as f64).round_ties_even() as i64;
    for _ in 0..ncrash.max(0) {
        if k >= churnable.len() {
            break;
        }
        let i = take(&mut k)?;
        let tc = scaled(b.rng.uniform(60.0, 300.0), NS);
        let tr = tc + scaled(b.rng.uniform(20.0, 90.0), NS);
        env(w, tc, EnvKind::Crash, i, EnvArg::None);
        change(w, tc, ChangeKind::Crash, i, None);
        env(w, tr, EnvKind::Restart, i, EnvArg::Flag(true));
        change(w, tr, ChangeKind::Join, i, None);
        down.entry(i).or_default().push((tc, Some(tr)));
    }
    for _ in 0..b.p.int_or("n_leave", 0)?.max(0) {
        if k >= churnable.len() {
            break;
        }
        let i = take(&mut k)?;
        let tl = scaled(b.rng.uniform(150.0, 330.0), NS);
        env(w, tl, EnvKind::Leave, i, EnvArg::None);
        change(w, tl, ChangeKind::Leave, i, None);
        down.entry(i).or_default().push((tl, None));
    }
    for _ in 0..b.p.int_or("n_upgrade", 0)?.max(0) {
        if k >= churnable.len() {
            break;
        }
        let i = take(&mut k)?;
        let tu = scaled(b.rng.uniform(100.0, 300.0), NS);
        env(w, tu, EnvKind::Upgrade, i, EnvArg::Num(2));
        change(w, tu, ChangeKind::Stack, i, Some(2));
        down.entry(i).or_default().push((tu, Some(tu + 2 * NS)));
    }
    let mut revoked = Vec::new();
    for _ in 0..b.p.int_or("n_revoke", 0)?.max(0) {
        if k >= churnable.len() {
            break;
        }
        let i = take(&mut k)?;
        let tv = scaled(b.rng.uniform(150.0, 300.0), NS);
        env(w, tv, EnvKind::Revoke, i, EnvArg::None);
        change(w, tv, ChangeKind::Revoke, i, None);
        revoked.push((i, tv));
    }
    let mut susp: BTreeMap<usize, Vec<(u64, u64)>> = BTreeMap::new();
    if b.p.truthy("handover_every_s") {
        for &i in &mobiles {
            let mut t = scaled(b.pick("handover_every_s")?, NS) / 2;
            let mut which = 1usize;
            while t < t1 {
                let sites = w.nodes[i].sites.clone();
                let out = scaled(b.pick("handover_outage_ms")?, MS);
                let site = *sites
                    .get(which % sites.len().max(1))
                    .ok_or(WorldError::Empty("mobile sites"))?;
                env(w, t, EnvKind::Handover, i, EnvArg::SiteGap(site, out));
                change(w, t + out, ChangeKind::Addr, i, None);
                which += 1;
                t += scaled(b.pick("handover_every_s")?, NS);
            }
            let mut t = scaled(b.pick("suspend_every_s")?, NS);
            while t < t1 {
                let d = scaled(b.pick("suspend_s")?, NS);
                env(w, t, EnvKind::Suspend, i, EnvArg::Num(d));
                susp.entry(i).or_default().push((t, t + d));
                t += scaled(b.pick("suspend_every_s")?, NS);
            }
        }
        for &i in &mobiles {
            let nat_ids: Vec<usize> = w.nodes[i]
                .sites
                .iter()
                .flat_map(|s| w.sites[*s].nats.iter().map(|nn| nn.nid))
                .collect();
            let mut t = scaled(b.pick("rebind_every_s")?, NS);
            while t < t1 {
                let nat = *nat_ids.first().ok_or(WorldError::Empty("mobile NATs"))?;
                env(w, t, EnvKind::Rebind, nat, EnvArg::None);
                t += scaled(b.pick("rebind_every_s")?, NS);
            }
        }
    }
    w.revoked.clone_from(&revoked);
    let plan = Plan {
        starts,
        down,
        susp,
        revoked,
        denied,
    };
    let dl = 60 * NS;
    let every = b.p.num("publish_every_s")?;
    let subs: Vec<Vec<usize>> = topics
        .iter()
        .map(|tp| (0..n).filter(|i| w.nodes[*i].topics.contains(tp)).collect())
        .collect();
    for i in 0..n {
        if clouds.contains(&i) {
            continue;
        }
        let mut t = t0 + scaled(b.rng.expovariate(1.0 / every), NS);
        while t < t1 {
            let mine = w.nodes[i].topics.clone();
            let tp = mine[below(&mut b.rng, mine.len(), "node topics")?].clone();
            let tix = topics.iter().position(|x| *x == tp).unwrap_or(0);
            let rec: Vec<usize> = subs[tix]
                .iter()
                .copied()
                .filter(|j| *j != i && plan.up(*j, t, t + dl))
                .collect();
            let must_ok = plan.up(i, t, t + 15 * NS);
            let recv: Vec<usize> = if must_ok {
                rec.iter().copied().filter(|j| plan.awake(*j, t, t + dl)).collect()
            } else {
                Vec::new()
            };
            if must_ok && plan.awake(i, t, t + 15 * NS) {
                let mut d = Intent::new(t, i, IntentKind::Publish, dl, Must::Set(recv));
                d.topic = Some(tp);
                d.size = Some(150 + b.rng.randbelow(250));
                d.receivers = rec;
                w.intents.push(d);
            }
            t += scaled(b.rng.expovariate(1.0 / every), NS);
        }
    }
    let mut reps = clouds.clone();
    reps.extend(homes.iter().take(2));
    let push_every = b.p.num("push_every_s")?;
    for _ in 0..b.p.count("n_push_pairs")? {
        let cands: Vec<usize> = (0..n)
            .filter(|i| !clouds.contains(i) && !plan.denied.contains(i))
            .collect();
        let o = choice(&mut b.rng, &cands, "push origins")?;
        let rcands: Vec<usize> = reps.iter().copied().filter(|x| *x != o).collect();
        let r = choice(&mut b.rng, &rcands, "push replicators")?;
        let mut t = t0 + scaled(b.rng.uniform(0.0, 10.0), NS);
        while t < t1 {
            let ok = plan.up(o, t, t + dl) && plan.up(r, t, t + dl);
            let must = ok && plan.awake(o, t, t + dl) && plan.awake(r, t, t + dl);
            if plan.both(o, t, t + NS) {
                let mut d = Intent::new(t, o, IntentKind::Push, dl, Must::Flag(must));
                d.to = Some(r);
                d.size = Some(1024 + b.rng.randbelow(3072));
                w.intents.push(d);
            }
            t += scaled(b.rng.expovariate(1.0 / push_every), NS);
        }
    }
    let pool: Vec<usize> = (0..n).filter(|i| !plan.denied.contains(i)).collect();
    for (kind, cnt) in [
        (IntentKind::Docsync, b.p.count("n_docsync")?),
        (IntentKind::Manage, b.p.count("n_manage")?),
        (IntentKind::Echo, b.p.count("n_echo")?),
    ] {
        for _ in 0..cnt {
            let a = choice(&mut b.rng, &pool, "request origins")?;
            let z = if kind == IntentKind::Manage {
                choice(&mut b.rng, &clouds, "clouds")?
            } else {
                let c: Vec<usize> = pool.iter().copied().filter(|x| *x != a).collect();
                choice(&mut b.rng, &c, "request peers")?
            };
            if a == z {
                continue;
            }
            let t = scaled(b.rng.uniform(t0s + 5.0, t1s), NS);
            if !plan.both(a, t, t + NS) {
                continue;
            }
            let dln = if kind == IntentKind::Echo { 30 * NS } else { dl };
            let must = plan.up(a, t, t + dln)
                && plan.up(z, t, t + dln)
                && plan.awake(a, t, t + dln)
                && plan.awake(z, t, t + dln);
            let mut d = Intent::new(t, a, kind, dln, Must::Flag(must));
            d.to = Some(z);
            if kind == IntentKind::Docsync {
                d.req = Some(120);
                d.resp = Some(512 + b.rng.randbelow(8192));
            }
            w.intents.push(d);
        }
    }
    let pushes: Vec<usize> = (0..w.intents.len())
        .filter(|i| w.intents[*i].kind == IntentKind::Push)
        .collect();
    for ix in sample(&mut b.rng, &pushes, pushes.len().min(4), "probe pushes")? {
        let (node, to, at) = (
            w.intents[ix].node,
            w.intents[ix].to.unwrap_or(0),
            w.intents[ix].t + 3 * NS,
        );
        if plan.both(node, at, at + 30 * NS) && plan.both(to, at, at + 30 * NS) {
            let mut d = Intent::new(at, node, IntentKind::Echo, 30 * NS, Must::Flag(true));
            d.to = Some(to);
            d.probe = true;
            w.intents.push(d);
        }
    }
    let (flo, fhi) = b.p.pair("fetch_sizes")?;
    let provs: Vec<usize> = clouds.iter().chain(homes.iter()).copied().collect();
    for j in 0..b.p.count("n_fetch")? {
        let size = b.rng.uniform(flo, fhi) as u64;
        let prov = choice(&mut b.rng, &provs, "providers")?;
        let name = format!("v{j}");
        w.values.insert(name.clone(), size);
        w.provides.entry(prov).or_default().push(name.clone());
        let c: Vec<usize> = pool.iter().copied().filter(|x| *x != prov).collect();
        let f = choice(&mut b.rng, &c, "fetchers")?;
        let t = scaled(b.rng.uniform(t0s + 10.0, t1s - 60.0), NS);
        let dlf = 120 * NS;
        if !plan.up(f, t, t + NS) {
            continue;
        }
        let must = plan.up(f, t, t + dlf) && plan.up(prov, t, t + dlf);
        let mut d = Intent::new(t, f, IntentKind::Fetch, dlf, Must::Flag(must));
        d.value = Some(name);
        d.providers = vec![prov];
        w.intents.push(d);
    }
    Ok(())
}
