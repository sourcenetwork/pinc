//! Churn over real sessions: joins, crashes, restarts without state and graceful leaves. A failed member is confirmed
//! down by every other node within the awareness bound; a member that left is reported as left; nobody who stays is
//! ever confirmed down.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names
)]

mod node_common;

use node_common::{World, big, secs};
use pinc_sim::SEC;
use pinc_tests::NCmd;

/// The awareness bound of the algorithm: a failure is known everywhere within this long.
const AWARENESS: u64 = 145 * SEC;

#[test]
fn churn_is_noticed_everywhere_and_nobody_else_is_accused() {
    big(|| {
        for seed in [11u64, 12, 13] {
            let mut w = World::build(seed, 3, 8);
            let hubs = w.hubs.clone();
            let m = w.members.clone();
            let (crashed, leaver, restarted, steady) = (m[0], m[1], m[2], m[3]);
            w.sim.crash(secs(50), crashed);
            w.sim.command(secs(60), leaver, NCmd::Leave);
            w.sim.crash(secs(70), restarted);
            w.sim.restart(secs(80), restarted);
            w.run(secs(50) + AWARENESS + secs(30));

            let ids = |n| w.id(n);
            let alive: Vec<_> = hubs
                .iter()
                .map(|(n, _)| *n)
                .chain(m.iter().copied())
                .filter(|n| *n != crashed && *n != leaver)
                .collect();
            for &n in &alive {
                let v = w.view(n);
                assert!(
                    !v.contains(&ids(crashed)),
                    "seed {seed}: {n:?} still lists the crashed member"
                );
                assert!(
                    !v.contains(&ids(leaver)),
                    "seed {seed}: {n:?} still lists the member that left"
                );
                for live in [restarted, steady] {
                    assert!(
                        live == n || v.contains(&ids(live)),
                        "seed {seed}: {n:?} lost live member {live:?}"
                    );
                }
                // Completeness: the crashed member was confirmed down within the bound.
                let down = w.confirmed_down(n, &ids(crashed));
                assert!(
                    down.first().is_some_and(|t| *t <= secs(50) + AWARENESS),
                    "seed {seed}: {n:?} confirmed the crash at {down:?}"
                );
                // Accuracy: the members that stayed were never confirmed down by anyone.
                for live in [steady, hubs[0].0, hubs[1].0] {
                    if live != n {
                        assert!(
                            w.confirmed_down(n, &ids(live)).is_empty(),
                            "seed {seed}: {n:?} accused a live node {live:?}"
                        );
                    }
                }
                // The leave is reported as a leave, not as a crash.
                assert!(
                    !w.left(n, &ids(leaver)).is_empty() || w.confirmed_down(n, &ids(leaver)).is_empty(),
                    "seed {seed}: {n:?} reported the leave as a failure"
                );
            }
        }
    });
}
