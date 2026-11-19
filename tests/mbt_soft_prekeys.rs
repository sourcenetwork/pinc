//! Model-based tests of the software prekey store: a real `SoftPrekeys` of `pinc-security` driven along every edge of the
//! state graph of `proofs/tla/MbtSoftPrekeys.tla` (the rule is `SoftAcquire` of `PrekeyRotation.tla`).
//!
//! TLC enumerates every state the acquire of the store reaches within the bounds of a config and writes the graph;
//! `scripts/mbt.py` turns it into paths from the new store that take every edge, which `scripts/proofs.sh` writes to
//! the directory `PINC_MBT_DIR`: `softprekeys.ndjson` from `MbtSoftPrekeys.cfg` (lifetime 2 ns, 2 uses) and
//! `softprekeys_zero.ndjson` from `MbtSoftPrekeys_zero.cfg` (lifetime 0, 0 uses). This test runs each path on a fresh
//! store, twice: model time `t` is `origin + t` ns, with the origin 0 and the origin `u64::MAX - tmax`, the largest
//! time of the model, so the clock ends at the top of `u64`. A `CallAcquire` acquires at that time and must return the
//! handle the model names; a `CallDecap` decapsulates a ciphertext made for the prekey of that handle (when it was
//! returned) and must be answered with the encapsulated secret or refused as the model says. After every call the
//! store's handle and use count must be the model's (the creation time is not observable: the acquires that rotate or
//! not check it). It stops at the first difference and names the file, the case, the step, the origin and the calls that
//! led there. Without `PINC_MBT_DIR` the walk checks nothing, while `rule_without_model` always runs: seeded random
//! calls under 25 policies against a reference written from the doc of `SoftPrekeys`.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    unreachable_pub,
    clippy::similar_names,
    clippy::trivially_copy_pass_by_ref
)]

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;

use pinc_crypto::provider::KEM_CIPHERTEXT_LEN;
use pinc_crypto::{CryptoError, Drbg, Provider, Secret, Software};
use pinc_security::keys::SoftPrekeys;
use pinc_security::{Env, KeyHandle, PrekeyInfo, PrekeyPolicy};
use pinc_tests::{Json, MbtCase, SplitMix64, mbt_cases};

fn num(v: &Json) -> u64 {
    v.u64().unwrap()
}

/// The calls of `case` up to step `upto`, for a failure message.
fn calls(case: &MbtCase, upto: usize) -> String {
    let mut s = String::new();
    for (i, st) in case.steps.iter().take(upto + 1).enumerate() {
        let _ = write!(s, "\n  {i}: {st}");
    }
    s
}

/// A ciphertext for the prekey `info` of handle `h`, with the secret it encapsulates; zeros and no secret when the
/// handle has no returned info.
fn ciphertext(p: &Software, info: Option<&PrekeyInfo>, h: u64) -> ([u8; KEM_CIPHERTEXT_LEN], Option<Secret<32>>) {
    match info {
        Some(info) => {
            let ek = p.kem_encaps_key(info.encaps_key()).unwrap();
            let m = [(h as u8) ^ 0x5a; 32];
            let (ct, secret) = p.kem_encapsulate(&ek, &m).unwrap();
            (p.kem_ciphertext_bytes(&ct), Some(secret))
        }
        None => ([0u8; KEM_CIPHERTEXT_LEN], None),
    }
}

/// Runs one case of `file` on a fresh store at `origin`; returns the number of calls.
fn run(file: &str, case: &MbtCase, life: u64, uses: u64, origin: u64) -> usize {
    let p = Software;
    let mut drbg = Drbg::new(&[(case.id % 251) as u8; 32]);
    let policy = PrekeyPolicy {
        lifetime_ns: life,
        max_uses: u32::try_from(uses).unwrap(),
    };
    let mut s = SoftPrekeys::new(
        &mut Env {
            provider: &p,
            now: origin,
            drbg: &mut drbg,
        },
        policy,
    )
    .unwrap();
    let mut infos: HashMap<u64, PrekeyInfo> = HashMap::new();
    for (i, st) in case.steps.iter().enumerate() {
        let at = || {
            format!(
                "{file} case {} step {i} origin {origin}; calls:{}",
                case.id,
                calls(case, i)
            )
        };
        match (st.call.as_str(), st.args.as_slice()) {
            ("CallAcquire", [t, h]) => {
                let info = s
                    .acquire(&mut Env {
                        provider: &p,
                        now: origin + num(t),
                        drbg: &mut drbg,
                    })
                    .unwrap();
                assert_eq!(info.handle(), KeyHandle(num(h)), "{}: the handle acquired", at());
                infos.insert(num(h), info);
            }
            ("CallDecap", [h, ok]) => {
                let h = num(h);
                let (ctb, secret) = ciphertext(&p, infos.get(&h), h);
                let r = s.decapsulate(&p, KeyHandle(h), &ctb);
                if ok.bool().unwrap() {
                    let got = r.unwrap_or_else(|e| panic!("{}: the model answers, the store refuses: {e:?}", at()));
                    if let Some(secret) = secret {
                        assert_eq!(got.expose(), secret.expose(), "{}: the secret answered", at());
                    }
                } else {
                    assert!(
                        matches!(r, Err(CryptoError::InvalidSecretKey)),
                        "{}: the model refuses and the store does not",
                        at()
                    );
                }
            }
            _ => panic!("{file} case {}: a call the test does not know: {st}", case.id),
        }
        let state = st.state.get("st").unwrap();
        let held = state.get("held").and_then(Json::arr).unwrap();
        assert_eq!(
            s.handle(),
            KeyHandle(num(&held[0])),
            "{}: the handle held differs from the model's",
            at()
        );
        assert_eq!(
            u64::from(s.uses()),
            num(state.get("uses").unwrap()),
            "{}: the use count differs from the model's",
            at()
        );
    }
    case.steps.len()
}

/// Walks every case of `file` at both origins; false when `PINC_MBT_DIR` is unset.
fn walk(file: &str) -> bool {
    let Some(cases) = mbt_cases(file) else {
        return false;
    };
    let mut cases = cases.unwrap();
    let head = cases.head.clone();
    let c = head.get("constants").unwrap();
    let k = |n: &str| num(c.get(n).unwrap_or_else(|| panic!("{file}: the constants have no {n}")));
    let (life, uses, gens, gmax) = (k("LIFE"), k("USES"), k("GENS"), k("GMAX"));
    assert!(gens >= gmax + 2, "{file}: a handle wraps inside the graph");
    let tmax = c.get("TS").and_then(Json::arr).unwrap().iter().map(num).max().unwrap();
    let init = head.get("init").unwrap();
    let st = init.get("st").unwrap();
    let held = st.get("held").and_then(Json::arr).unwrap();
    assert!(
        matches!(init, Json::Obj(f) if f.len() == 1)
            && matches!(st, Json::Obj(f) if f.len() == 3)
            && held.len() == 1
            && num(&held[0]) == 0
            && num(st.get("created").unwrap()) == 0
            && num(st.get("uses").unwrap()) == 0,
        "{file}: the model's first state is not a store at generation 0 with no use"
    );
    let (mut n, mut steps) = (0u64, 0usize);
    for case in &mut cases {
        let case = case.unwrap();
        for origin in [0, u64::MAX - tmax] {
            steps += run(file, &case, life, uses, origin);
        }
        n += 1;
    }
    let count = |f: &str| num(head.get(f).unwrap());
    assert_eq!(
        (n, steps as u64),
        (count("cases"), 2 * count("steps")),
        "{file}: the file ends early"
    );
    eprintln!(
        "mbt_soft_prekeys: {file}: {n} cases, {steps} calls at two origins, every one of the {} edges between the {} states of the graph",
        count("edges"),
        count("states")
    );
    true
}

#[test]
fn walk_graph() {
    // MbtSoftPrekeys.cfg and MbtSoftPrekeys_zero.cfg
    let walked = ["softprekeys.ndjson", "softprekeys_zero.ndjson"].map(walk);
    if walked == [false; 2] {
        eprintln!("mbt_soft_prekeys: PINC_MBT_DIR is not set, nothing checked (scripts/proofs.sh generates the cases)");
    }
}

#[test]
fn rule_without_model() {
    let lifetimes = [0, 1, 2, 600_000_000_000, u64::MAX];
    let max_uses = [0, 1, 2, 64, u32::MAX];
    let p = Software;
    for seed in 1..=8u64 {
        let mut rng = SplitMix64::traced(seed);
        let mut drbg = Drbg::new(&[seed as u8; 32]);
        let now0 = if seed % 2 == 1 { 0 } else { u64::MAX - 2_000_000_000_000 };
        for lifetime_ns in lifetimes {
            for max in max_uses {
                let policy = PrekeyPolicy {
                    lifetime_ns,
                    max_uses: max,
                };
                let at = |op: usize| format!("seed {seed} lifetime {lifetime_ns} uses {max} operation {op}");
                let mut s = SoftPrekeys::new(
                    &mut Env {
                        provider: &p,
                        now: now0,
                        drbg: &mut drbg,
                    },
                    policy,
                )
                .unwrap();
                // the reference: the generation, the creation time and the count of uses
                let (mut generation, mut created, mut uses) = (0u64, now0, 0u32);
                let mut now = now0;
                let mut infos: BTreeMap<u64, PrekeyInfo> = BTreeMap::new();
                let mut most = 0;
                for op in 0..300 {
                    if rng.next_u64() % 4 < 3 {
                        now = match rng.next_u64() % 4 {
                            0 if now > now0 => now - 1,
                            0 | 1 => now,
                            2 => now.saturating_add(1),
                            _ => now.saturating_add(rng.next_u64() % 1_000_000_000_000),
                        };
                        let due = uses >= max || now.saturating_sub(created) >= lifetime_ns;
                        if due {
                            generation += 1;
                            created = now;
                            uses = 0;
                        }
                        uses = uses.saturating_add(1);
                        let info = s
                            .acquire(&mut Env {
                                provider: &p,
                                now,
                                drbg: &mut drbg,
                            })
                            .unwrap();
                        assert_eq!(info.handle(), KeyHandle(generation), "{}: the handle acquired", at(op));
                        assert_eq!(s.handle(), KeyHandle(generation), "{}: the handle held", at(op));
                        assert_eq!(s.uses(), uses, "{}: the use count", at(op));
                        infos.insert(generation, info);
                        most = most.max(uses);
                        assert!(most <= max.max(1), "{}: a prekey served {most} handshakes", at(op));
                    } else {
                        let keys: Vec<u64> = infos.keys().copied().chain([generation + 1]).collect();
                        let h = keys[(rng.next_u64() % keys.len() as u64) as usize];
                        let (ctb, secret) = ciphertext(&p, infos.get(&h), h);
                        let r = s.decapsulate(&p, KeyHandle(h), &ctb);
                        if h == generation {
                            let got = r.unwrap_or_else(|e| panic!("{}: the current prekey refuses: {e:?}", at(op)));
                            if let Some(secret) = secret {
                                assert_eq!(got.expose(), secret.expose(), "{}: the secret answered", at(op));
                            }
                        } else {
                            assert!(
                                matches!(r, Err(CryptoError::InvalidSecretKey)),
                                "{}: handle {h} is not the current {generation} and is not refused",
                                at(op)
                            );
                        }
                    }
                }
            }
        }
    }
}
