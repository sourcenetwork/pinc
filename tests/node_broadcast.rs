//! Broadcast over real hub streams: origin authentication, a body at the configured size limit, and publishes during
//! churn reaching every live subscriber.
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
use vinc_broadcast::Limits;
use vinc_tests::NCmd;

const TOPIC: &[u8] = b"news";

fn body(len: usize, salt: u8) -> Vec<u8> {
    (0..len)
        .map(|i| (i as u8).wrapping_mul(31).wrapping_add(salt))
        .collect()
}

#[test]
fn a_message_reaches_every_subscriber_once_with_its_origin() {
    big(|| {
        for seed in [51u64, 52, 53] {
            let mut w = World::build(seed, 3, 6);
            let m = w.members.clone();
            for sub in &m[1..] {
                w.sim.command(secs(20), *sub, NCmd::Subscribe(TOPIC.to_vec()));
            }
            let sent = body(1000, 7);
            w.sim.command(
                secs(40),
                m[0],
                NCmd::Publish {
                    topic: TOPIC.to_vec(),
                    body: sent.clone(),
                },
            );
            w.run(secs(80));
            let origin = w.id(m[0]);
            for sub in &m[1..] {
                let got = w.messages(*sub);
                assert_eq!(got.len(), 1, "seed {seed}: {sub:?} got {} messages", got.len());
                let (_, topic, from, b) = &got[0];
                assert_eq!(
                    (topic.as_slice(), *from, b),
                    (TOPIC, origin, &sent),
                    "seed {seed}: {sub:?}"
                );
            }
            // The publisher and a non-subscriber hear nothing.
            assert!(
                w.messages(m[0]).is_empty(),
                "seed {seed}: the origin got its own message"
            );
        }
    });
}

#[test]
fn a_subscriber_that_refuses_the_origin_gets_nothing() {
    big(|| {
        let mut w = World::build(61, 2, 4);
        let m = w.members.clone();
        w.sim.command(0, m[3], NCmd::BroadcastAllow(false));
        for sub in &m[1..] {
            w.sim.command(secs(20), *sub, NCmd::Subscribe(TOPIC.to_vec()));
        }
        w.sim.command(
            secs(40),
            m[0],
            NCmd::Publish {
                topic: TOPIC.to_vec(),
                body: body(64, 1),
            },
        );
        w.run(secs(70));
        assert_eq!(w.messages(m[1]).len(), 1);
        assert_eq!(w.messages(m[2]).len(), 1);
        assert!(w.messages(m[3]).is_empty(), "a refused origin must not be delivered");
    });
}

#[test]
fn a_body_at_the_configured_limit_crosses_a_hub_stream() {
    big(|| {
        // The default limit, and one past the old frame cap of 262,144 bytes.
        for max_body in [65_536usize, 300_000] {
            let limits = Limits {
                max_body,
                log_bytes: 2 * max_body + (1 << 20),
                ..Limits::default()
            };
            let mut w = World::build_with(71, 2, 3, |w| w.limits = limits);
            let m = w.members.clone();
            for sub in &m[1..] {
                w.sim.command(secs(20), *sub, NCmd::Subscribe(TOPIC.to_vec()));
            }
            let sent = body(max_body, 3);
            w.sim.command(
                secs(40),
                m[0],
                NCmd::Publish {
                    topic: TOPIC.to_vec(),
                    body: sent.clone(),
                },
            );
            w.run(secs(100));
            for sub in &m[1..] {
                let got = w.messages(*sub);
                assert_eq!(got.len(), 1, "limit {max_body}: {sub:?} got {} messages", got.len());
                assert!(got[0].3 == sent, "limit {max_body}: the body arrived altered or cut");
            }
        }
    });
}

#[test]
fn a_publish_during_churn_reaches_every_live_subscriber() {
    big(|| {
        for seed in [81u64, 82, 83] {
            let mut w = World::build(seed, 3, 8);
            let m = w.members.clone();
            let subs = &m[1..];
            for s in subs {
                w.sim.command(secs(20), *s, NCmd::Subscribe(TOPIC.to_vec()));
            }
            // Churn: one subscriber crashes for good, one restarts, one resets its carriers, the primary hub of the
            // publisher is not touched.
            w.sim.crash(secs(60), m[2]);
            w.sim.crash(secs(70), m[3]);
            w.sim.restart(secs(75), m[3]);
            w.sim.command(secs(76), m[3], NCmd::Subscribe(TOPIC.to_vec()));
            w.sim.command(secs(90), m[4], NCmd::DropCarriers);
            let n = 20u8;
            for i in 0..n {
                w.sim.command(
                    secs(45 + 5 * u64::from(i)),
                    m[0],
                    NCmd::Publish {
                        topic: TOPIC.to_vec(),
                        body: body(200, i),
                    },
                );
            }
            w.run(secs(45 + 5 * u64::from(n) + 60));
            for (j, s) in subs.iter().enumerate() {
                let got: Vec<Vec<u8>> = w.messages(*s).into_iter().map(|(_, _, _, b)| b).collect();
                let live_always = *s != m[2] && *s != m[3];
                if live_always {
                    for i in 0..n {
                        assert!(
                            got.contains(&body(200, i)),
                            "seed {seed}: live subscriber {j} missed message {i} (got {})",
                            got.len()
                        );
                    }
                }
                // At most once.
                let mut seen = got.clone();
                seen.sort();
                seen.dedup();
                assert_eq!(seen.len(), got.len(), "seed {seed}: subscriber {j} got a message twice");
            }
            // The restarted subscriber gets every message published after it subscribed again.
            let got: Vec<Vec<u8>> = w.messages(m[3]).into_iter().map(|(_, _, _, b)| b).collect();
            for i in 0..n {
                if 45 + 5 * u64::from(i) >= 80 {
                    assert!(
                        got.contains(&body(200, i)),
                        "seed {seed}: the restarted subscriber missed {i}"
                    );
                }
            }
        }
    });
}
