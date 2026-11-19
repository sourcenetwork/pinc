//! Trace generation for the connection id tables: seeded random runs of a real table (`pinc-transport`, built with
//! the `trace` feature) driven by the calls a connection makes, recorded as ndjson (`cid.ndjson`) for the TLA+ trace
//! check (`TraceCid.tla`) and the Lean replay (`Pinc/TraceCid.lean`).
//!
//! A run learns the peer's first id and installs the secret at random moments, authenticates packets addressed to
//! the ids of indices near the highest seen (skipping some, repeating some, outside the lookahead, below the
//! highest, index 0), takes ids for new paths and confirms some of the ids it took. After every call the table shows
//! its slots (index, tick of last use, whether a packet used it), the highest index, the counters and the epoch.
//!
//! Derived ids may collide. The runs with ids of four bytes have none; the runs with ids of one byte have many, with
//! each other and with the first id; two scripted runs at the code's sizes have the single collisions of the model's
//! witnesses of #398 (index 9 with the id of index 1, index 8 with the id of index 1, the secret searched for as the
//! unit tests of `conn/cid.rs` do). The first event of every run records, for each index the run reaches, the least
//! index whose id is the same (0 for the first id), so the models derive what the code derives.
//!
//! The test asserts what it can itself (the ids of the indices from one below the highest seen to two above it are
//! accepted once the secret is installed; in a run with no collision the two indices after the highest are held and a
//! retired index is never held again; the sender takes a fresh index only within the lookahead of the highest
//! confirmed one, otherwise an index of that window) so it is meaningful without the proof tools.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::many_single_char_names,
    clippy::cast_possible_truncation,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::panic,
    unreachable_pub
)]

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use pinc_crypto::extract;
use pinc_tests::SplitMix64;
use pinc_transport::conn::{CidTable, CidView};

fn b(x: bool) -> &'static str {
    if x { "true" } else { "false" }
}

fn view_json(v: &CidView) -> String {
    let ents: Vec<String> = v
        .entries
        .iter()
        .map(|e| match e {
            Some((i, u, s)) => format!("[{i},{u},{}]", b(*s)),
            None => "[-1,0,false]".to_string(),
        })
        .collect();
    format!(
        r#"{{"ent":[{}],"hi":{},"tick":{},"ns":{},"cf":{},"sec":{},"fr":{},"epoch":{}}}"#,
        ents.join(","),
        v.highest,
        v.tick,
        v.next_send,
        v.confirmed,
        b(v.secret),
        b(v.first_remote),
        v.epoch
    )
}

/// The id the code derives for `index` of a receiver whose role is `client` (`conn/cid.rs` `derive`). The models get
/// their ids from this; one that differs from the code's on an index a run reaches shows as a step the models do not
/// take, never as a pass.
fn derive(secret: &[u8; 32], client: bool, index: u64, len: usize) -> Vec<u8> {
    let mut input = [0u8; 9];
    input[0] = u8::from(client);
    input[1..].copy_from_slice(&index.to_be_bytes());
    extract(secret, &input)[..len].to_vec()
}

/// For each index from 0 to `upto`, the least index whose id is the same: 0 for an index with the first id.
fn classes(secret: &[u8; 32], client: bool, first: &[u8], upto: u64) -> Vec<u64> {
    let mut least: BTreeMap<Vec<u8>, u64> = BTreeMap::new();
    least.insert(first.to_vec(), 0);
    (0..=upto)
        .map(|j| {
            if j == 0 {
                0
            } else {
                *least.entry(derive(secret, client, j, first.len())).or_insert(j)
            }
        })
        .collect()
}

/// The first event of a run: the table as made, and the id of each index up to the highest the run reached plus six
/// (past every index a call of the run can touch: a refill reaches the highest seen plus four, a packet or a probe the
/// highest seen plus five).
fn init_line(id: u32, client: bool, v0: &CidView, ids: &[u64], highest: u64) -> String {
    let ids: Vec<String> = ids[..=usize::try_from(highest + 6).unwrap()]
        .iter()
        .map(u64::to_string)
        .collect();
    format!(
        r#"{{"t":"txcid","run":{id},"op":"init","client":{},"ids":[{}],"v":{}}}"#,
        b(client),
        ids.join(","),
        view_json(v0)
    )
}

/// The checks the models state, after every call: no index is held twice; once the secret is installed, the ids of the
/// indices from one below the highest seen to two above it are accepted (`Lookahead`, `WindowAccepted`); with no
/// collision the two indices after the highest are held themselves and an index the table forgot is never held again
/// and is not above the highest seen.
fn check(t: &CidTable, collide: bool, held: &mut BTreeSet<u64>, retired: &mut BTreeSet<u64>) {
    let v = t.view();
    let now: BTreeSet<u64> = v.entries.iter().flatten().map(|e| e.0).collect();
    assert_eq!(now.len(), v.entries.iter().flatten().count(), "an index is held twice");
    if v.secret {
        for j in v.highest.saturating_sub(1).max(1)..=v.highest + 2 {
            assert!(
                t.is_local(j),
                "the id of index {j} is not accepted (highest {})",
                v.highest
            );
        }
    }
    if collide {
        return;
    }
    if v.secret {
        for j in v.highest + 1..=v.highest + 2 {
            assert!(
                now.contains(&j),
                "the lookahead index {j} is not held (highest {})",
                v.highest
            );
        }
    }
    retired.extend(held.difference(&now).copied());
    for r in &*retired {
        assert!(!now.contains(r), "the retired index {r} is held again");
        assert!(*r <= v.highest, "an index above the highest seen was retired");
    }
    *held = now;
}

/// A query: `is_local` of `probes`, `remote_usable` of `usable`.
fn query(t: &CidTable, probes: &[u64], usable: &[u64]) -> (String, Vec<bool>) {
    let has: Vec<String> = probes.iter().map(|p| format!("[{p},{}]", b(t.is_local(*p)))).collect();
    let answers: Vec<bool> = usable.iter().map(|p| t.remote_usable(*p)).collect();
    let usable: Vec<String> = usable
        .iter()
        .zip(&answers)
        .map(|(p, r)| format!("[{p},{}]", b(*r)))
        .collect();
    (
        format!(
            r#""op":"query","lc":{},"has":[{}],"usable":[{}]"#,
            t.local_count(),
            has.join(","),
            usable.join(",")
        ),
        answers,
    )
}

/// A seeded random run. `first` is the table's first id; its length is that of every derived id, so one byte makes
/// collisions frequent.
fn run(seed: u64, out: &mut String, id: u32, steps: u32, skipper: bool, first: &[u8], seen: &mut [bool; 2]) -> bool {
    let mut rng = SplitMix64::traced(seed);
    let client = id.is_multiple_of(2);
    let mut t = CidTable::new(client, first).unwrap();
    let mut secret_bytes = [0u8; 32];
    rng.fill(&mut secret_bytes);
    // a call moves the highest index seen by at most four (to an entry a refill reached), so no run passes this
    let ids = classes(&secret_bytes, client, first, 4 * u64::from(steps) + 6);
    let collide = ids.iter().zip(0u64..).any(|(c, j)| *c != j);
    let v0 = t.view();
    let mut body = String::new();
    let log = |t: &CidTable, body: &mut String, op: &str| {
        let _ = writeln!(body, r#"{{"t":"txcid","run":{id},{op},"v":{}}}"#, view_json(&t.view()));
    };
    let mut retired: BTreeSet<u64> = BTreeSet::new();
    let mut held: BTreeSet<u64> = BTreeSet::new();
    let mut claimed: Vec<u64> = Vec::new();
    for _ in 0..steps {
        let v = t.view();
        match rng.next_u64() % 100 {
            0..=3 if !v.first_remote => {
                t.set_first_remote(&[5, 6, 7, 8]);
                log(&t, &mut body, r#""op":"frem""#);
            }
            4..=8 if !v.secret => {
                t.install(&secret_bytes);
                log(&t, &mut body, r#""op":"install""#);
            }
            9..=64 => {
                let hi = v.highest;
                let index = if skipper {
                    hi + 2
                } else {
                    match rng.next_u64() % 10 {
                        0..=3 => hi + 1,
                        4 | 5 => hi + 2,
                        6 => hi + 3,
                        7 => hi.saturating_sub(rng.next_u64() % 4),
                        8 => 0,
                        _ => rng.next_u64() % (hi + 6),
                    }
                };
                t.on_authenticated(index);
                log(&t, &mut body, &format!(r#""op":"auth","k":{index}"#));
            }
            65..=80 => {
                let (before, confirmed) = (v.next_send, v.confirmed);
                let r = t.claim_remote().map(|(k, derived)| {
                    assert!(derived, "the id claimed is not the one derived for its index");
                    k
                });
                if let Some(k) = r {
                    if k == before {
                        assert!(
                            k <= confirmed + 2,
                            "a fresh index {k} is past the window of confirmed {confirmed}"
                        );
                        assert_eq!(t.view().next_send, before + 1);
                    } else {
                        assert!(
                            k > confirmed && k <= confirmed + 2,
                            "the index {k} taken again is outside the window of confirmed {confirmed}"
                        );
                        assert_eq!(t.view().next_send, before);
                    }
                    claimed.push(k);
                } else {
                    assert_eq!(t.view().next_send, before);
                }
                log(
                    &t,
                    &mut body,
                    &format!(r#""op":"claim","k":{}"#, r.map_or(-1, |k| i64::try_from(k).unwrap())),
                );
            }
            81..=84 if !claimed.is_empty() => {
                let k = claimed[usize::try_from(rng.next_u64()).unwrap() % claimed.len()];
                t.confirm_remote(k);
                assert_eq!(t.view().confirmed, v.confirmed.max(k));
                log(&t, &mut body, &format!(r#""op":"conf","k":{k}"#));
            }
            _ => {
                let hi = v.highest;
                let probes: Vec<u64> = (0..6).map(|_| rng.next_u64() % (hi + 6)).collect();
                let usable: Vec<u64> = [0, v.confirmed, v.confirmed + 1, v.next_send]
                    .into_iter()
                    .chain((0..2).map(|_| rng.next_u64() % (v.next_send + 6)))
                    .collect();
                let (op, answers) = query(&t, &probes, &usable);
                for (p, r) in usable.iter().zip(answers) {
                    if *p != 0 {
                        seen[usize::from(r)] = true;
                    }
                }
                log(&t, &mut body, &op);
            }
        }
        check(&t, collide, &mut held, &mut retired);
    }
    let _ = writeln!(out, "{}", init_line(id, client, &v0, &ids, t.view().highest));
    out.push_str(&body);
    collide
}

/// A scripted run at the code's sizes with one collision: the secret is searched so that index `pair.0` derives the id
/// of index `pair.1` (ids of one byte) and no other two of the indices 1..=14, nor the first id, share one; then the
/// secret is installed and packets are authenticated to the ids of `indices`, each followed by a query of the window.
fn scripted(out: &mut String, id: u32, pair: (u64, u64), indices: &[u64]) {
    let client = false;
    let first = [0xffu8];
    let secret = (0..=u32::MAX)
        .map(|n| {
            let mut s = [0u8; 32];
            s[..4].copy_from_slice(&n.to_be_bytes());
            s
        })
        .find(|s| {
            let ids = classes(s, client, &first, 14);
            (1..=14u64).all(|j| ids[j as usize] == if j == pair.0 { pair.1 } else { j })
        })
        .unwrap_or_else(|| panic!("no secret found for the collision {pair:?}"));
    let ids = classes(&secret, client, &first, 40);
    let mut t = CidTable::new(client, &first).unwrap();
    let v0 = t.view();
    let mut body = String::new();
    let log = |t: &CidTable, body: &mut String, op: &str| {
        let _ = writeln!(body, r#"{{"t":"txcid","run":{id},{op},"v":{}}}"#, view_json(&t.view()));
    };
    t.install(&secret);
    log(&t, &mut body, r#""op":"install""#);
    let (mut held, mut retired) = (BTreeSet::new(), BTreeSet::new());
    check(&t, true, &mut held, &mut retired);
    for &k in indices {
        t.on_authenticated(k);
        log(&t, &mut body, &format!(r#""op":"auth","k":{k}"#));
        check(&t, true, &mut held, &mut retired);
        let hi = t.view().highest;
        let probes: Vec<u64> = (hi.saturating_sub(1)..=hi + 2).chain([pair.0, pair.1]).collect();
        let (op, _) = query(&t, &probes, &[0, 1]);
        log(&t, &mut body, &op);
    }
    let _ = writeln!(out, "{}", init_line(id, client, &v0, &ids, t.view().highest));
    out.push_str(&body);
}

#[test]
fn connection_id_runs_match_the_models() {
    let mut out = String::new();
    let mut seen = [false; 2];
    let mut collided = 0;
    for id in 1..=60u32 {
        // runs 41 to 60 take ids of one byte: their derived ids collide with each other and with the first id
        let first: &[u8] = if id <= 40 { &[1, 2, 3, 4] } else { &[0x5a] };
        let collide = run(
            0x4349_4400 + u64::from(id),
            &mut out,
            id,
            300,
            id.is_multiple_of(5),
            first,
            &mut seen,
        );
        assert!(collide || id <= 40, "run {id}: ids of one byte did not collide");
        collided += usize::from(collide);
    }
    // the witnesses of the model at the code's sizes: index 9 with the id of index 1 (a packet at the highest index 7
    // and then 8: the entry of index 1 must stand for index 9), index 8 with the id of index 1 (the highest index 9)
    scripted(&mut out, 61, (9, 1), &[1, 3, 5, 7, 8]);
    scripted(&mut out, 62, (8, 1), &[1, 3, 5, 7, 9]);
    assert!(collided >= 20, "only {collided} runs had a collision");
    assert!(seen[0], "no probe of a non-zero index was refused as remote_usable");
    assert!(seen[1], "no probe of a non-zero index was accepted as remote_usable");
    for needle in [
        r#""op":"frem""#,
        r#""op":"install""#,
        r#""op":"auth""#,
        r#""op":"claim""#,
        r#""op":"conf""#,
        r#""op":"query""#,
    ] {
        assert!(
            pinc_tests::soaking() || out.contains(needle),
            "the runs never reach {needle}"
        );
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("cid.ndjson"), &out).unwrap();
    }
}
