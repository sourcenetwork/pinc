//! S14 (set reconciliation): per node and collection, a set of 40 byte items (an 8 byte document id then the 32 byte
//! `BLAKE2b` of the document's version) in one of five profiles relative to a base set, and the sessions between nodes
//! (`generate_s14`; the application side of the session is not part of the world).
//!
//! Invariant: an item is `doc.to_be_bytes() ++ blake2b-256(repr((seed, collection, doc, version)))`, so a set sorted
//! by bytes is sorted by document id; the sets are built once per collection and node from the base, never per
//! session.

use std::collections::BTreeMap;

use super::WorldError;
use super::build::{Builder, NS, below, blank_world, choice, finish, region_delay, sample, scaled, sort_world};
use super::model::{EnvAction, EnvArg, EnvKind, Intent, IntentKind, Must, Params, World};
use super::params::ParamsExt;
use crate::reference::{Py, PyRandom, digest32};

const SET_REFS: [&[u8]; 2] = [b"/col/0", b"/col/1"];

type Item = [u8; 40];

/// `_item(seed, ref, doc, ver)`.
fn item(seed: u64, set_ref: &[u8], doc: u64, ver: u64) -> Item {
    let d = digest32(&[
        Py::Int(i128::from(seed)),
        Py::Bytes(set_ref),
        Py::Int(i128::from(doc)),
        Py::Int(i128::from(ver)),
    ]);
    let mut out = [0u8; 40];
    out[..8].copy_from_slice(&doc.to_be_bytes());
    out[8..].copy_from_slice(&d);
    out
}

fn doc_of(x: &Item) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&x[..8]);
    u64::from_be_bytes(b)
}

/// `_profile_set(rng, p, seed, ref, base, kind)`.
fn profile_set(
    rng: &mut PyRandom,
    p: &Params,
    seed: u64,
    set_ref: &[u8],
    base: &[Item],
    kind: &str,
) -> Result<Vec<Item>, WorldError> {
    let n = base.len() as u64;
    if kind == "base" {
        return Ok(base.to_vec());
    }
    if kind == "cold" {
        let (lo, hi) = p.pair("cold_frac")?;
        let keep = (n as f64 * rng.uniform(lo, hi)) as usize;
        let mut out = sample(rng, base, keep, "cold replica")?;
        out.sort_unstable();
        return Ok(out);
    }
    let mut out: BTreeMap<u64, Item> = base.iter().map(|x| (doc_of(x), *x)).collect();
    if kind == "branch" {
        let (lo, hi) = p.int_pair("branch_items")?;
        let k = rng.randint(lo, hi);
        for j in 0..k.max(0) as u64 {
            let doc = n + 1_000_000 + j;
            out.insert(doc, item(seed, set_ref, doc, 1));
        }
        return Ok(out.into_values().collect());
    }
    let k = if kind == "small" {
        let (lo, hi) = p.int_pair("small_diff")?;
        rng.randint(lo, hi).max(0) as usize
    } else {
        let (lo, hi) = p.pair("large_frac")?;
        (n as f64 * rng.uniform(lo, hi)) as usize
    };
    let keys: Vec<u64> = out.keys().copied().collect();
    let docs = sample(rng, &keys, k.min(base.len()), "differing documents")?;
    for doc in docs {
        let r = rng.random();
        if r < 0.4 {
            out.insert(doc, item(seed, set_ref, doc, 2 + rng.randbelow(1000)));
        } else if r < 0.7 {
            out.remove(&doc);
        } else {
            let nd = n + 2_000_000 + doc;
            out.insert(nd, item(seed, set_ref, nd, 1));
        }
    }
    Ok(out.into_values().collect())
}

/// Generates S14 from the merged parameters.
pub(super) fn generate(p: Params, seed: u64) -> Result<World, WorldError> {
    let mut w = blank_world("S14", &p, seed)?;
    let mut b = Builder::new(p, seed);
    let mut clouds = Vec::new();
    for r in 0..b.p.count("n_cloud")? {
        clouds.push(b.add_cloud(&mut w, r % 3)?);
    }
    let mut homes = Vec::new();
    for _ in 0..b.p.count("n_home")? {
        let region = below(&mut b.rng, 3, "regions")?;
        homes.push(b.add_home(&mut w, region, None, None)?);
    }
    let mut mobiles = Vec::new();
    for _ in 0..b.p.count("n_mobile")? {
        let region = below(&mut b.rng, 3, "regions")?;
        mobiles.push(b.add_mobile(&mut w, region)?);
    }
    let n = w.nodes.len();
    w.region_delay_ns = region_delay();
    finish(&mut w, clouds.clone(), homes.clone(), mobiles.clone());
    for i in 0..n {
        w.nodes[i].topics = vec![b"/col/0".to_vec()];
        let t = if clouds.contains(&i) {
            0
        } else {
            scaled(b.rng.uniform(0.5, 4.0), NS)
        };
        w.env.push(EnvAction {
            t,
            kind: EnvKind::Start,
            node: i,
            arg: EnvArg::None,
        });
    }
    let profiles = b.p.str_list("profiles")?.to_vec();
    let n_items = b.p.int("n_items")?.max(0) as u64;
    for set_ref in SET_REFS {
        let base: Vec<Item> = (0..n_items).map(|d| item(seed, set_ref, d, 1)).collect();
        for i in 0..n {
            let kind = if clouds.contains(&i) {
                "base".to_string()
            } else {
                profiles[below(&mut b.rng, profiles.len(), "profiles")?].clone()
            };
            let set = profile_set(&mut b.rng, &b.p, seed, set_ref, &base, &kind)?;
            w.set_profiles.insert((i, set_ref.to_vec()), kind);
            w.sets.insert((i, set_ref.to_vec()), set);
        }
    }
    let (lo, hi) = b.p.int_pair("active_s")?;
    let (t0s, t1s) = (lo as f64, hi as f64);
    let dl = b.p.int("deadline_s")? as u64 * NS;
    let idle0 = b.p.int_pair("idle_s")?.0 as u64 * NS;
    let mut free: BTreeMap<(usize, usize), u64> = BTreeMap::new();
    let others: Vec<usize> = homes.iter().chain(mobiles.iter()).copied().collect();
    for _ in 0..b.p.count("n_sessions")? {
        let a = choice(&mut b.rng, &others, "session origins")?;
        let r = below(&mut b.rng, SET_REFS.len(), "collections")?;
        let z = if b.rng.random() < 0.6 {
            choice(&mut b.rng, &clouds, "clouds")?
        } else {
            let c: Vec<usize> = others.iter().copied().filter(|x| *x != a).collect();
            choice(&mut b.rng, &c, "session peers")?
        };
        let t = scaled(b.rng.uniform(t0s + 5.0, t1s), NS).max(free.get(&(a, r)).copied().unwrap_or(0));
        let set_ref = SET_REFS[r].to_vec();
        if t + dl > idle0 || w.sets.get(&(a, set_ref.clone())) == w.sets.get(&(z, set_ref.clone())) {
            continue;
        }
        free.insert((a, r), t + dl + 5 * NS);
        let mut d = Intent::new(t, a, IntentKind::Reconcile, dl, Must::Flag(true));
        d.to = Some(z);
        d.set_ref = Some(set_ref);
        w.intents.push(d);
    }
    for _ in 0..b.p.count("n_echo")? {
        let a = below(&mut b.rng, n, "nodes")?;
        let c: Vec<usize> = (0..n).filter(|x| *x != a).collect();
        let z = choice(&mut b.rng, &c, "echo peers")?;
        let t = scaled(b.rng.uniform(t0s + 5.0, t1s), NS);
        let mut d = Intent::new(t, a, IntentKind::Echo, 30 * NS, Must::Flag(true));
        d.to = Some(z);
        w.intents.push(d);
    }
    sort_world(&mut w);
    Ok(w)
}
