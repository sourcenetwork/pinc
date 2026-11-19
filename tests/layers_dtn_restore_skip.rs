//! A record that cannot be read is dropped during `dtn_restore` and changes nothing else: the record after it is
//! still visited, and a partial record with a bad run evicts no bundle before it is refused.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

mod layers_common;

use layers_common::{LWorld, big, secs};
use pinc_dtn::head::BundleId;
use pinc_node::{DtnPlan, Enabled};
use pinc_tests::{LayerApps, NCmd, SplitMix64};

fn dtn_on(tag: u8) -> LayerApps {
    let mut apps = LayerApps::new(
        tag,
        Enabled {
            dtn: true,
            ..Enabled::NONE
        },
    );
    apps.dtn.policy.max_sends = 60;
    apps
}

#[test]
fn an_unreadable_record_does_not_hide_the_next_one() {
    big(|| {
        let seed = 431u64;
        let mut w = LWorld::build_with(seed, 2, 3, 1_000_000, true, dtn_on);
        let (a, c) = (w.members[0], w.members[2]);
        // A record under the smallest id, which sorts before every real one, that is not a record.
        w.apps(a).dtn.records.insert(BundleId([0; 32]), vec![0xff, 0xff, 0xff]);
        let keys = w.apps(c).dtn.keys();
        let mut body = vec![0u8; 400 << 10];
        SplitMix64::new(seed).fill(&mut body);
        w.sim.command(
            secs(30),
            a,
            NCmd::DtnSend {
                to: Box::new(keys),
                payload: body,
                plan: DtnPlan {
                    lifetime_ms: 600_000,
                    copies: 4,
                    k: 4,
                    m: 2,
                    slice_log: 2,
                },
            },
        );
        w.sim.crash(secs(33), a);
        w.sim.restart(secs(35), a);
        w.run(secs(40));
        let r = w.sim.node(a).restored;
        eprintln!("{r:?}");
        assert_eq!(r.dropped, 1, "{r:?}");
        assert_eq!(r.held, 1, "the held bundle's record was visited: {r:?}");
    });
}

/// A held record's head, past its version, kind, copies, custody, previous holder and bytes.
const HELD_HEAD: usize = 2 + 2 + 1 + 33 + 8;

#[test]
fn a_partial_record_with_a_bad_run_evicts_nothing() {
    big(|| {
        let seed = 432u64;
        let mut w = LWorld::build_with(seed, 2, 3, 1_000_000, true, dtn_on);
        let (a, c) = (w.members[0], w.members[2]);
        // No contact: the holder keeps both bundles and their records as they are.
        w.apps(a).dtn.windows = Some(vec![]);
        let keys = w.apps(c).dtn.keys();
        for (s, at) in [(seed, 30), (seed + 1, 31)] {
            let mut body = vec![0u8; 3000];
            SplitMix64::new(s).fill(&mut body);
            w.sim.command(
                secs(at),
                a,
                NCmd::DtnSend {
                    to: Box::new(keys),
                    payload: body,
                    plan: DtnPlan {
                        lifetime_ms: 600_000,
                        copies: 4,
                        k: 4,
                        m: 2,
                        slice_log: 2,
                    },
                },
            );
        }
        w.run(secs(40));
        let records = &mut w.apps(a).dtn.records;
        assert_eq!(records.len(), 2, "both bundles are held");
        // The first record visited stays a held bundle, carried in transit so it may be evicted; the second becomes
        // a partial record of the same size with a run that ends where it starts.
        let (held, bad) = (*records.keys().next().unwrap(), *records.keys().nth(1).unwrap());
        records.get_mut(&held).unwrap()[4] = 0;
        let mut partial = vec![2, 1];
        partial.extend_from_slice(&records[&bad][HELD_HEAD..]);
        partial.extend_from_slice(&[0; 16]);
        let bytes = u64::from_be_bytes(records[&held][HELD_HEAD - 8..HELD_HEAD].try_into().unwrap());
        records.insert(bad, partial);
        // Room for one bundle and a half: the partial's charge fits only by evicting the held bundle.
        w.apps(a).dtn.budget = bytes * 3 / 2;
        w.sim.crash(secs(41), a);
        w.sim.restart(secs(42), a);
        w.run(secs(43));
        let r = w.sim.node(a).restored;
        eprintln!("{r:?}");
        assert_eq!((r.held, r.partial, r.dropped), (1, 0, 1), "{r:?}");
        assert_eq!(w.sim.node(a).node.dtn_held(), 1, "the held bundle is still held");
        let dtn = &w.apps(a).dtn;
        assert!(dtn.records.contains_key(&held), "its record is kept");
        assert!(dtn.bundles.contains_key(&held), "its bundle is kept");
        assert!(!dtn.records.contains_key(&bad), "the bad record is dropped");
    });
}

/// A held record has one encoding: a custody byte other than 0 or 1, or a byte after the head, drops it.
#[test]
fn a_held_record_with_a_bad_custody_byte_or_a_byte_after_it_is_dropped() {
    big(|| {
        for (seed, corrupt) in [(433u64, 0), (434, 1)] {
            let mut w = LWorld::build_with(seed, 2, 3, 1_000_000, true, dtn_on);
            let (a, c) = (w.members[0], w.members[2]);
            w.apps(a).dtn.windows = Some(vec![]);
            let keys = w.apps(c).dtn.keys();
            w.sim.command(
                secs(30),
                a,
                NCmd::DtnSend {
                    to: Box::new(keys),
                    payload: vec![7; 3000],
                    plan: DtnPlan {
                        lifetime_ms: 600_000,
                        copies: 4,
                        k: 4,
                        m: 2,
                        slice_log: 2,
                    },
                },
            );
            w.run(secs(40));
            let rec = w.apps(a).dtn.records.values_mut().next().unwrap();
            if corrupt == 0 {
                rec[4] = 2;
            } else {
                rec.push(0);
            }
            w.sim.crash(secs(41), a);
            w.sim.restart(secs(42), a);
            w.run(secs(43));
            let r = w.sim.node(a).restored;
            assert_eq!((r.held, r.dropped), (0, 1), "corruption {corrupt}: {r:?}");
        }
    });
}
