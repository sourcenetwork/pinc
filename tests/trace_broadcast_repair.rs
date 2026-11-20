//! Trace generation for the repair of a gap in a topic at a subscriber: the real `Topics` machines of two hubs, a
//! subscriber that talks only to the first and a publisher, driven through the broadcast harness with the probe of the
//! `trace` feature of `pinc-broadcast` that says whether a hub's log holds a message. One run of 105 seconds publishes
//! eight messages, loses some on the way to the subscriber, cuts and heals the subscriber's link to its hub and the
//! link between the hubs, and lets the timers run (the hubs' anti-entropy every 5 s, the subscriber's gap check every
//! 20 s). Every event is a line of `bcast/repair.ndjson` for the TLA+ trace check (`TraceBroadcastRepair.tla`): the
//! actions of the model (`publish`, `tohub`, `flip`) and its timers (`tick`, `ae`, `gap`); the last event of each call
//! carries the links, each hub's log and what the subscriber delivered.
//!
//! The test asserts the facts it relies on itself: the timer constants the schedule relies on, a lost message
//! reaches the subscriber by the first gap check after it, the resubscription repairs what the cut link missed, the
//! second hub gets a message from the first only by its anti-entropy, and the subscriber delivers all eight messages
//! once. `publish_reaches_both_hubs` checks the fan-out of a publish to both hubs, which the trace leaves out. The trace
//! is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    unreachable_pub,
    clippy::manual_is_multiple_of,
    clippy::similar_names
)]

#[path = "broadcast_common.rs"]
mod common;

use std::cell::Cell;
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::rc::Rc;

use common::{Net, SEC, ty};
use pinc_broadcast::consts::{GAP_EVERY, HUB_AE};
use pinc_crypto::IdentityAlg;
use pinc_tests::SplitMix64;

const T: &[u8] = b"repair";
/// The last second of the run: under the model's `MaxTime` and the log window, so nothing expires.
const END: u64 = 105;

#[derive(Clone, Copy)]
enum Act {
    /// Publish the next message; whether the subscriber's copy is lost on the way.
    Publish { lose: bool },
    /// The subscriber's link to its hub goes down or up.
    S1(bool),
    /// The link between the hubs goes down or up.
    H(bool),
}

struct World {
    net: Net,
    mids: Vec<[u8; 8]>,
    s1: bool,
    h: bool,
    out: String,
}

fn nums(v: &[u32]) -> String {
    let s: Vec<String> = v.iter().map(u32::to_string).collect();
    format!("[{}]", s.join(","))
}

impl World {
    /// The messages (numbers, ascending) hub `hub` logs.
    fn held(&self, hub: usize) -> Vec<u32> {
        let t = &self.net.nodes[hub].t;
        (1..=u32::try_from(self.mids.len()).unwrap())
            .filter(|k| t.log_holds(T, &self.mids[usize::try_from(*k).unwrap() - 1]))
            .collect()
    }

    fn delivered(&self) -> Vec<u32> {
        let got = self.net.delivered(2);
        let mut v: Vec<u32> = (1..=u32::try_from(self.mids.len()).unwrap())
            .filter(|k| got.contains(&self.mids[usize::try_from(*k).unwrap() - 1]))
            .collect();
        v.sort_unstable();
        v
    }

    /// Record the events of one call; the last carries the state after it.
    fn emit(&mut self, now: u64, evs: &[(&str, String)]) {
        for (i, (op, keys)) in evs.iter().enumerate() {
            let mut line = format!(r#"{{"t":"rep","op":"{op}","now":{now}{keys}"#);
            if i + 1 == evs.len() {
                let _ = write!(
                    line,
                    r#","lnk":{{"S1":{},"P1":true,"P2":true,"H":{},"PS":true}},"hl1":{},"hl2":{},"dlv":{}"#,
                    self.s1,
                    self.h,
                    nums(&self.held(0)),
                    nums(&self.held(1)),
                    nums(&self.delivered())
                );
            }
            line.push_str("}\n");
            self.out.push_str(&line);
        }
    }

    fn publish(&mut self, now: u64, lose: bool) {
        let m = u32::try_from(self.mids.len()).unwrap() + 1;
        let line = format!(r#"{{"t":"rep","op":"publish","now":{now},"m":{m}}}"#);
        self.out.push_str(&line);
        self.out.push('\n');
        let drop_first = Rc::new(Cell::new(lose));
        let d = drop_first.clone();
        self.net.filter = Some(Box::new(move |from, to, b: &mut Vec<u8>| {
            if d.get() && from == 0 && to == 2 && b.get(4) == Some(&ty::MSG) {
                d.set(false);
                return false;
            }
            true
        }));
        let mid = self.net.publish(3, T, &[m as u8; 16]);
        self.net.filter = None;
        self.mids.push(mid);
        self.emit(now, &[("tohub", format!(r#","m":{m},"lose":{lose}"#))]);
    }

    /// A link goes down or up: the subscriber's (`s1`) or the hubs'. When the subscriber's comes up the subscriber
    /// asks its hub again at once.
    fn flip(&mut self, now: u64, s1: bool, up: bool) {
        if s1 {
            self.s1 = up;
            self.net.link(2, 0, up);
            if up {
                let (t, hub) = (self.net.now, self.net.id(0));
                let n2 = &mut self.net.nodes[2];
                n2.h.tick(t);
                n2.t.resubscribe(&mut n2.h, t, &hub);
                self.net.pump();
            }
        } else {
            self.h = up;
            self.net.link(0, 1, up);
        }
        let l = if s1 { "S1" } else { "H" };
        self.emit(now, &[("flip", format!(r#","l":"{l}""#))]);
    }

    fn has(&self, k: usize) -> bool {
        self.net.delivered(2).contains(&self.mids[k - 1])
    }
}

#[test]
fn repair_trace() {
    assert_eq!(GAP_EVERY, 20 * SEC);
    assert_eq!(HUB_AE, 5 * SEC);
    let mut rng = SplitMix64::traced(0x5747_0006);
    let lose = |rng: &mut SplitMix64| Act::Publish {
        lose: rng.next_u64() % 2 == 0,
    };
    let plain = Act::Publish { lose: false };
    let lost = Act::Publish { lose: true };
    let script: Vec<(u64, Act)> = vec![
        (0, plain),
        (2, lost),
        (22, Act::S1(false)),
        (22, plain),
        (24, Act::H(false)),
        (24, plain),
        (26, Act::S1(true)),
        (28, Act::H(true)),
        (33, lost),
        (41, Act::S1(false)),
        (41, lose(&mut rng)),
        (43, lose(&mut rng)),
        (50, Act::S1(true)),
        (55, lose(&mut rng)),
    ];

    let mut w = World {
        net: Net::new(IdentityAlg::Ed25519, 2, 2, 0),
        mids: Vec::new(),
        s1: true,
        h: true,
        out: String::new(),
    };
    w.net.link(2, 1, false);
    // P hands a publish to every hub it reaches (FAN) when all are up; the model's P writes to hub 1 only, so it never
    // reaches hub 2 and the publish is mirrored between the hubs (PUB), which the hub link carries.
    w.net.link(3, 1, false);
    w.net.subscribe(2, T);
    w.net.run_until(0);
    w.emit(0, &[("ae", r#","h":1"#.to_owned()), ("ae", r#","h":2"#.to_owned())]);

    let (mut now, mut next_gap, mut idx) = (0u64, 20u64, 0usize);
    loop {
        while idx < script.len() && script[idx].0 == now {
            let act = script[idx].1;
            match act {
                Act::Publish { lose } => w.publish(now, lose),
                Act::S1(up) => w.flip(now, true, up),
                Act::H(up) => w.flip(now, false, up),
            }
            idx += 1;
            match (now, act) {
                (26, Act::S1(true)) => assert!(w.has(3) && w.has(4), "the resubscription did not repair 3 and 4"),
                (28, Act::H(true)) => assert!(!w.held(1).contains(&4), "hub 2 held message 4 before its AE"),
                _ => {}
            }
        }
        if now >= END {
            break;
        }
        let next = [script.get(idx).map(|a| a.0), Some((now / 5 + 1) * 5), Some(next_gap)]
            .into_iter()
            .flatten()
            .min()
            .unwrap();
        now = next;
        w.net.run_until(now * SEC);
        let mut evs: Vec<(&str, String)> = vec![("tick", String::new())];
        if now % 5 == 0 {
            evs.push(("ae", r#","h":1"#.to_owned()));
            evs.push(("ae", r#","h":2"#.to_owned()));
        }
        if now == next_gap {
            evs.push(("gap", String::new()));
            next_gap += 20;
        }
        w.emit(now, &evs);
        match now {
            15 => assert!(!w.has(2), "message 2 was delivered before the gap check"),
            20 => assert!(w.has(2), "the gap check at 20 s did not repair message 2"),
            30 => assert!(
                w.held(1).contains(&4),
                "the anti-entropy at 30 s did not give message 4 to hub 2"
            ),
            40 => assert!(w.has(5), "the gap check at 40 s did not repair message 5"),
            _ => {}
        }
    }
    let got = w.net.delivered(2);
    assert_eq!(got.len(), 8, "the subscriber did not deliver eight messages");
    assert_eq!(
        got.iter().collect::<BTreeSet<_>>().len(),
        8,
        "the subscriber delivered a message twice"
    );
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        let dir = std::path::Path::new(&dir).join("bcast");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("repair.ndjson"), &w.out).unwrap();
    }
}

/// A publish fans out to every hub the publisher reaches: with the link between the hubs down, hub 2 can only hold the
/// message if the publisher handed it over itself, which `repair_trace` (the model's publisher writes to hub 1 only)
/// leaves out.
#[test]
fn publish_reaches_both_hubs() {
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 2, 0);
    net.link(2, 1, false);
    net.link(0, 1, false);
    net.subscribe(2, T);
    net.run_until(0);
    let mid = net.publish(3, T, &[1u8; 16]);
    net.run_until(SEC);
    for hub in 0..2 {
        assert!(
            net.nodes[hub].t.log_holds(T, &mid),
            "hub {} did not get the publish from the publisher",
            hub + 1
        );
    }
    assert!(
        net.delivered(2).contains(&mid),
        "the subscriber did not get the message through hub 1"
    );
}
