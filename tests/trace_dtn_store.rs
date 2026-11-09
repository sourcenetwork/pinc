//! Trace generation for the charged store: seeded random runs of the real `Ledger` through its public API (`admit`,
//! `expire`, `release`, `reclass`, `iter`, `used`), recorded as ndjson for the TLA+ trace check (`TraceDtnStore.tla`)
//! and the Lean replay (`Vinc/TraceDtnStore.lean`).
//!
//! The world is small so that every branch is met: ledgers of one to four slots, a budget of ten bytes, two spaces
//! (bundles and mailbox items) with five ids each, sizes of 0 to 12 bytes, both classes, lifetimes and clocks of 0 to
//! 6 (a clock may go back between calls, and an item expires exactly when `expires <= now`). A run mixes admissions
//! (also of a key already kept), expiries, releases and reclasses in a seeded order.
//!
//! What is recorded is what an observer sees: the call, what it returned (the error, the evicted entries in the order
//! the callback saw them, the entry released), and after every call the kept entries in slot order (`snap`) and the
//! bytes charged (`used`). The admission number of an entry is not observable; the model has to reproduce it for the
//! eviction order to match.
//!
//! The test asserts everything itself against `dtn_ledger_oracle`, a reference written from the documented rules that
//! shares no code with the ledger (accepted exactly when the custody items leave room in 128-bit sums, expired first,
//! then transit oldest admission first, only as many as needed), and that every error and every kind of eviction was
//! met, so it is meaningful without the proof tools. The main world goes to `dtn_store.ndjson` and is checked by both
//! TLA+ and Lean; `dtn_store_edge.ndjson` holds budgets and sizes around `u64::MAX` (the saturating sums) and is
//! replayed by Lean only, because the TLA+ check uses a small saturation maximum. The trace is written to the
//! directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::needless_pass_by_value,
    clippy::type_complexity,
    unreachable_pub
)]

mod dtn_ledger_oracle;

use dtn_ledger_oracle::{Ent, Oracle, Refusal, ents_json};
use vinc_dtn::store::{Class, Entry, Key, Ledger, Space, StoreError};
use vinc_tests::SplitMix64;

const SPACES: [u8; 2] = [1, 2];

fn key(space: u8, id: u8) -> Key {
    Key {
        space: Space(space),
        id: [id; 32],
    }
}

fn ent_of(e: &Entry) -> (u8, u8, u64, bool, u64) {
    (
        e.key.space.0,
        e.key.id[0],
        e.bytes,
        e.class == Class::Custody,
        e.expires,
    )
}

fn view(e: &Ent) -> (u8, u8, u64, bool, u64) {
    (e.space, e.id, e.bytes, e.custody, e.exp)
}

#[derive(Default)]
struct Seen {
    dup: u32,
    custody_refused: u32,
    full: u32,
    ok: u32,
    expired_evicted: u32,
    transit_evicted: u32,
    boundary: u32,
    released: u32,
    release_none: u32,
    reclass_ok: u32,
    reclass_unknown: u32,
    cross_space: u32,
}

/// One run on a ledger of `N` slots; the events go to `out`.
fn run<const N: usize>(
    seed: u64,
    budget: u64,
    sizes: &[u64],
    times: &[u64],
    ops: usize,
    out: &mut Vec<String>,
    seen: &mut Seen,
) {
    let mut rng = SplitMix64::new(seed);
    let mut pick = |v: &[u64]| v[(rng.next_u64() % v.len() as u64) as usize];
    let mut real = Ledger::<N>::new(budget);
    let mut model = Oracle::new(N, budget);
    out.push(format!(r#"{{"t":"dl_new","n":{N},"budget":{budget}}}"#));
    let after = |real: &Ledger<N>, model: &Oracle| {
        let snap: Vec<_> = real.iter().map(ent_of).collect();
        let expected: Vec<_> = model.ents().iter().map(view).collect();
        assert_eq!(snap, expected, "kept entries");
        assert_eq!(u128::from(real.used()), model.used(), "bytes charged");
        assert!(real.used() <= real.budget());
        let es: Vec<Ent> = model.ents();
        format!(r#""snap":{},"used":{}"#, ents_json(&es), real.used())
    };
    for _ in 0..ops {
        let kind = pick(&[0, 0, 0, 0, 0, 0, 1, 2, 3, 3, 4]);
        let space = SPACES[(pick(&[0, 1]) as usize) % 2];
        let id = pick(&[1, 2, 3, 4, 5]) as u8;
        let now = pick(times);
        match kind {
            0 => {
                let bytes = pick(sizes);
                let custody = pick(&[0, 1]) == 0;
                let exp = pick(times);
                let mut gone = vec![];
                let r = real.admit(
                    key(space, id),
                    bytes,
                    if custody { Class::Custody } else { Class::Transit },
                    exp,
                    now,
                    |e| gone.push(*e),
                );
                let (mr, mev) = model.admit(space, id, bytes, custody, exp, now);
                let err = match (&r, mr) {
                    (Ok(()), Ok(())) => "ok",
                    (Err(StoreError::Duplicate), Err(Refusal::Dup)) => "dup",
                    (Err(StoreError::CustodyRefused), Err(Refusal::Custody)) => "cust",
                    (Err(StoreError::Full), Err(Refusal::Full)) => "full",
                    other => panic!("admit differs from the reference: {other:?}"),
                };
                assert_eq!(
                    gone.iter().map(ent_of).collect::<Vec<_>>(),
                    mev.iter().map(view).collect::<Vec<_>>(),
                    "evictions"
                );
                match err {
                    "ok" => seen.ok += 1,
                    "dup" => seen.dup += 1,
                    "cust" => seen.custody_refused += 1,
                    _ => seen.full += 1,
                }
                seen.expired_evicted += u32::try_from(mev.iter().filter(|e| e.exp <= now).count()).unwrap();
                seen.transit_evicted += u32::try_from(mev.iter().filter(|e| e.exp > now).count()).unwrap();
                seen.boundary += u32::from(mev.iter().any(|e| e.exp == now));
                seen.cross_space += u32::from(mev.iter().any(|e| e.exp > now && e.space != space));
                let ev = ents_json(&mev);
                out.push(format!(
                    r#"{{"t":"dl_adm","s":{space},"i":{id},"b":{bytes},"c":{},"x":{exp},"now":{now},"err":"{err}","ev":{ev},{}}}"#,
                    u8::from(!custody),
                    after(&real, &model)
                ));
            }
            1 => {
                let mut gone = vec![];
                let n = real.expire(now, |e| gone.push(*e));
                let mev = model.expire(now);
                assert_eq!(n, mev.len());
                assert_eq!(
                    gone.iter().map(ent_of).collect::<Vec<_>>(),
                    mev.iter().map(view).collect::<Vec<_>>()
                );
                seen.boundary += u32::from(mev.iter().any(|e| e.exp == now));
                out.push(format!(
                    r#"{{"t":"dl_exp","now":{now},"ev":{},{}}}"#,
                    ents_json(&mev),
                    after(&real, &model)
                ));
            }
            2 => {
                let got = real.release(&key(space, id));
                let mgot = model.release(space, id);
                assert_eq!(got.as_ref().map(ent_of), mgot.as_ref().map(view));
                if got.is_some() {
                    seen.released += 1;
                } else {
                    seen.release_none += 1;
                }
                let e = mgot.as_ref().map_or_else(
                    || r#"{"s":0,"i":0,"b":0,"c":0,"x":0}"#.to_string(),
                    dtn_ledger_oracle::ent_json,
                );
                out.push(format!(
                    r#"{{"t":"dl_rel","s":{space},"i":{id},"got":{},"e":{e},{}}}"#,
                    got.is_some(),
                    after(&real, &model)
                ));
            }
            _ => {
                let custody = pick(&[0, 1]) == 0;
                let r = real.reclass(&key(space, id), if custody { Class::Custody } else { Class::Transit });
                let mr = model.reclass(space, id, custody);
                assert_eq!(r.is_ok(), mr);
                if mr {
                    seen.reclass_ok += 1;
                } else {
                    assert_eq!(r.err(), Some(StoreError::Unknown));
                    seen.reclass_unknown += 1;
                }
                out.push(format!(
                    r#"{{"t":"dl_rec","s":{space},"i":{id},"c":{},"ok":{mr},{}}}"#,
                    u8::from(!custody),
                    after(&real, &model)
                ));
            }
        }
    }
}

fn write(name: &str, lines: &[String]) {
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        let mut text = lines.join("\n");
        text.push('\n');
        std::fs::write(std::path::Path::new(&dir).join(name), text).unwrap();
    }
}

#[test]
fn ledger_runs_match_the_reference_and_are_recorded() {
    let mut out = vec![];
    let mut seen = Seen::default();
    let sizes = [0, 1, 2, 3, 4, 5, 6, 8, 10, 12];
    let times = [0, 1, 2, 3, 4, 5, 6];
    for seed in 0..40 {
        run::<1>(seed, 10, &sizes, &times, 60, &mut out, &mut seen);
        run::<2>(seed + 100, 10, &sizes, &times, 60, &mut out, &mut seen);
        run::<3>(seed + 200, 10, &sizes, &times, 60, &mut out, &mut seen);
        run::<4>(seed + 300, 10, &sizes, &times, 60, &mut out, &mut seen);
    }
    for (name, n) in [
        ("duplicates", seen.dup),
        ("custody refusals", seen.custody_refused),
        ("transit refusals", seen.full),
        ("accepted", seen.ok),
        ("expired evictions", seen.expired_evicted),
        ("transit evictions", seen.transit_evicted),
        ("expiry boundary", seen.boundary),
        ("releases", seen.released),
        ("releases of nothing", seen.release_none),
        ("reclasses", seen.reclass_ok),
        ("reclasses of nothing", seen.reclass_unknown),
        ("cross-space evictions", seen.cross_space),
    ] {
        assert!(n > 0, "the world never met: {name}");
    }
    write("dtn_store.ndjson", &out);

    // Budgets and sizes around u64::MAX: the saturating sums of the fit test and the 128-bit reference agree.
    let mut edge = vec![];
    let mut seen = Seen::default();
    let big = u64::MAX;
    let sizes = [0, 1, big / 4, big / 3, big / 2, big / 2 + 1, big - 1, big];
    let times = [0, 1, 2, big - 1, big];
    for seed in 0..60 {
        run::<2>(seed, big, &sizes, &times, 40, &mut edge, &mut seen);
        run::<3>(seed + 100, big - 1, &sizes, &times, 40, &mut edge, &mut seen);
        run::<4>(seed + 200, big / 2 + 1, &sizes, &times, 40, &mut edge, &mut seen);
    }
    assert!(seen.ok > 0 && seen.transit_evicted > 0 && seen.custody_refused > 0 && seen.full > 0);
    write("dtn_store_edge.ndjson", &edge);
}
