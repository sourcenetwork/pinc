//! Trace generation for the connection id tables: seeded random runs of a real table (`vinc-transport`, built with
//! the `trace` feature) driven by the calls a connection makes, recorded as ndjson (`cid.ndjson`) for the TLA+ trace
//! check (`TraceCid.tla`) and the Lean replay (`Vinc/TraceCid.lean`).
//!
//! A run learns the peer's first id and installs the secret at random moments, authenticates packets addressed to
//! the ids of indices near the highest seen (skipping some, repeating some, outside the lookahead, below the
//! highest, index 0), takes ids for new paths and confirms some of the ids it took. After every call the table shows its slots (index, tick of last
//! use, whether a packet used it), the highest index, the counters and the epoch.
//!
//! The test asserts what it can itself (the lookahead is always held once the secret is installed, a retired id is
//! never accepted again, the sender takes a fresh index only within the lookahead of the highest confirmed one, otherwise an index of that window) so it is meaningful without the proof tools.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::many_single_char_names,
    clippy::cast_possible_truncation,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    unreachable_pub
)]

use std::collections::BTreeSet;
use std::fmt::Write as _;

use vinc_tests::SplitMix64;
use vinc_transport::conn::{CidTable, CidView};

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

fn run(seed: u64, out: &mut String, id: u32, steps: u32, skipper: bool, seen: &mut [bool; 2]) {
    let mut rng = SplitMix64::new(seed);
    let client = id.is_multiple_of(2);
    let mut t = CidTable::new(client, &[1, 2, 3, 4]).unwrap();
    let mut secret_bytes = [0u8; 32];
    rng.fill(&mut secret_bytes);
    let log = |t: &CidTable, out: &mut String, body: &str| {
        let _ = writeln!(out, r#"{{"t":"txcid","run":{id},{body},"v":{}}}"#, view_json(&t.view()));
    };
    let _ = writeln!(
        out,
        r#"{{"t":"txcid","run":{id},"op":"init","client":{},"v":{}}}"#,
        b(client),
        view_json(&t.view())
    );
    let mut retired: BTreeSet<u64> = BTreeSet::new();
    let mut held: BTreeSet<u64> = BTreeSet::new();
    let mut claimed: Vec<u64> = Vec::new();
    for _ in 0..steps {
        let v = t.view();
        match rng.next_u64() % 100 {
            0..=3 if !v.first_remote => {
                t.set_first_remote(&[5, 6, 7, 8]);
                log(&t, out, r#""op":"frem""#);
            }
            4..=8 if !v.secret => {
                t.install(&secret_bytes);
                log(&t, out, r#""op":"install""#);
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
                log(&t, out, &format!(r#""op":"auth","k":{index}"#));
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
                    out,
                    &format!(r#""op":"claim","k":{}"#, r.map_or(-1, |k| i64::try_from(k).unwrap())),
                );
            }
            81..=84 if !claimed.is_empty() => {
                let k = claimed[usize::try_from(rng.next_u64()).unwrap() % claimed.len()];
                t.confirm_remote(k);
                assert_eq!(t.view().confirmed, v.confirmed.max(k));
                log(&t, out, &format!(r#""op":"conf","k":{k}"#));
            }
            _ => {
                let hi = v.highest;
                let probes: Vec<u64> = (0..6).map(|_| rng.next_u64() % (hi + 6)).collect();
                let has: Vec<String> = probes.iter().map(|p| format!("[{p},{}]", b(t.is_local(*p)))).collect();
                let usable: Vec<String> = [0, v.confirmed, v.confirmed + 1, v.next_send]
                    .into_iter()
                    .chain((0..2).map(|_| rng.next_u64() % (v.next_send + 6)))
                    .map(|p| {
                        let r = t.remote_usable(p);
                        if p != 0 {
                            seen[usize::from(r)] = true;
                        }
                        format!("[{p},{}]", b(r))
                    })
                    .collect();
                log(
                    &t,
                    out,
                    &format!(
                        r#""op":"query","lc":{},"has":[{}],"usable":[{}]"#,
                        t.local_count(),
                        has.join(","),
                        usable.join(",")
                    ),
                );
            }
        }
        // the checks the models state
        let v = t.view();
        let now: BTreeSet<u64> = v.entries.iter().flatten().map(|e| e.0).collect();
        assert_eq!(now.len(), v.entries.iter().flatten().count(), "an index is held twice");
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
        for r in &retired {
            assert!(!now.contains(r), "the retired index {r} is held again");
            assert!(*r <= v.highest, "an index above the highest seen was retired");
        }
        held = now;
    }
}

#[test]
fn connection_id_runs_match_the_models() {
    let mut out = String::new();
    let mut seen = [false; 2];
    for id in 1..=40u32 {
        run(
            0x4349_4400 + u64::from(id),
            &mut out,
            id,
            300,
            id.is_multiple_of(5),
            &mut seen,
        );
    }
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
        assert!(out.contains(needle), "the runs never reach {needle}");
    }
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("cid.ndjson"), &out).unwrap();
    }
}
