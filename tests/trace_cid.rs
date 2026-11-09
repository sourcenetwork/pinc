//! Trace generation for the connection id tables: seeded random runs of a real table (`vinc-transport`, built with
//! the `trace` feature) driven by the calls a connection makes, recorded as ndjson (`cid.ndjson`) for the TLA+ trace
//! check (`TraceCid.tla`) and the Lean replay (`Vinc/TraceCid.lean`).
//!
//! A run learns the peer's first id and installs the secret at random moments, authenticates packets addressed to
//! the ids of indices near the highest seen (skipping some, repeating some, outside the lookahead, below the
//! highest, index 0), and takes ids for new paths. After every call the table shows its slots (index, tick of last
//! use, whether a packet used it), the highest index, the counters and the epoch.
//!
//! The test asserts what it can itself (the lookahead is always held once the secret is installed, a retired id is
//! never accepted again, the sender takes each index once) so it is meaningful without the proof tools.
#![allow(clippy::unwrap_used, clippy::too_many_lines, unreachable_pub)]

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
        r#"{{"ent":[{}],"hi":{},"tick":{},"ns":{},"sec":{},"fr":{},"epoch":{}}}"#,
        ents.join(","),
        v.highest,
        v.tick,
        v.next_send,
        b(v.secret),
        b(v.first_remote),
        v.epoch
    )
}

fn run(seed: u64, out: &mut String, id: u32, steps: u32, skipper: bool) {
    let mut rng = SplitMix64::new(seed);
    let client = id % 2 == 0;
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
    let mut next_claim = 0u64;
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
            65..=84 => {
                let before = t.view().next_send;
                let r = t.claim_remote().map(|(k, derived)| {
                    assert!(derived, "the id claimed is not the one derived for its index");
                    k
                });
                if let Some(k) = r {
                    assert_eq!(k, before, "the sender took an index out of order");
                    assert_eq!(k, next_claim, "the sender reused or skipped an index");
                    next_claim += 1;
                } else {
                    assert_eq!(t.view().next_send, before);
                }
                log(
                    &t,
                    out,
                    &format!(r#""op":"claim","k":{}"#, r.map_or(-1, |k| i64::try_from(k).unwrap())),
                );
            }
            _ => {
                let hi = v.highest;
                let probes: Vec<u64> = (0..6).map(|_| rng.next_u64() % (hi + 6)).collect();
                let has: Vec<String> = probes.iter().map(|p| format!("[{p},{}]", b(t.is_local(*p)))).collect();
                log(
                    &t,
                    out,
                    &format!(r#""op":"query","lc":{},"has":[{}]"#, t.local_count(), has.join(",")),
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
    for id in 1..=40u32 {
        run(0x4349_4400 + u64::from(id), &mut out, id, 300, id % 5 == 0);
    }
    for needle in [
        r#""op":"frem""#,
        r#""op":"install""#,
        r#""op":"auth""#,
        r#""op":"claim""#,
        r#""op":"query""#,
    ] {
        assert!(out.contains(needle), "the runs never reach {needle}");
    }
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("cid.ndjson"), &out).unwrap();
    }
}
