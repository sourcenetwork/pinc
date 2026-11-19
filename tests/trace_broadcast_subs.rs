//! Trace generation for a hub's subscription table: the real `Topics` machines of a hub, three members that
//! subscribe to two topics and a publisher, driven through the broadcast harness with the probe of the `trace` feature
//! of `pinc-broadcast` that reads a member's subscription at the hub (live, held or none). The actions are the model's:
//! a member subscribes and unsubscribes (`sub`, `unsub`), membership holds a member's subscriptions while its session
//! is down, gives them back (`restore`, the hub tells the member which topics are live again) or drops them for good
//! (`release`), and the publisher pushes (`push`, the hub hands the message to every live subscription). Every event is
//! a line of `bcast/subs.ndjson` for the TLA+ trace check (`TraceBroadcastSubs.tla`): the action and the whole table
//! after it; a restore also carries the topics the hub told, a push the members it reached.
//!
//! The scripted run makes each case the model names; a seeded run of 300 actions follows on the same hub. The test
//! asserts the facts it relies on itself: a held subscription gets no push, a push reaches exactly the live ones, a
//! restore tells exactly the topics that were held, and a release leaves nothing. The trace is written to the
//! directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    unreachable_pub
)]

#[path = "broadcast_common.rs"]
mod common;

use std::collections::BTreeSet;
use std::fmt::Write as _;

use common::{Net, SEC, ty};
use pinc_crypto::IdentityAlg;
use pinc_tests::SplitMix64;

/// The topic named `t` (1 or 2) in the model.
fn topic(t: u8) -> &'static [u8] {
    if t == 1 { b"t1" } else { b"t2" }
}

fn nums(v: &[usize]) -> String {
    let s: Vec<String> = v.iter().map(usize::to_string).collect();
    format!("[{}]", s.join(","))
}

struct World {
    net: Net,
    /// The subscriptions each member holds on its own side, as `(member, topic)`.
    mine: BTreeSet<(usize, u8)>,
    out: String,
}

impl World {
    fn state(&self, t: u8, m: usize) -> Option<bool> {
        self.net.nodes[0].t.sub_state(topic(t), &self.net.id(m))
    }

    fn event(&mut self, op: &str, keys: &str) {
        let row = |t: u8| {
            let cells: Vec<String> = (1..=3)
                .map(|m| match self.state(t, m) {
                    None => "\"none\"".to_owned(),
                    Some(true) => "\"live\"".to_owned(),
                    Some(false) => "\"held\"".to_owned(),
                })
                .collect();
            format!("[{}]", cells.join(","))
        };
        let subs = format!("[{},{}]", row(1), row(2));
        let _ = writeln!(self.out, r#"{{"t":"subs","op":"{op}"{keys},"subs":{subs}}}"#);
    }

    fn sub(&mut self, m: usize, t: u8) {
        assert!(self.mine.insert((m, t)), "member {m} already holds topic {t}");
        self.net.subscribe(m, topic(t));
        self.event("sub", &format!(r#","m":{m},"topic":{t}"#));
    }

    fn unsub(&mut self, m: usize, t: u8) {
        assert!(self.mine.remove(&(m, t)), "member {m} does not hold topic {t}");
        self.net.unsubscribe(m, topic(t));
        self.event("unsub", &format!(r#","m":{m},"topic":{t}"#));
    }

    fn hold(&mut self, m: usize) {
        let id = self.net.id(m);
        let n0 = &mut self.net.nodes[0];
        n0.t.hold(&mut n0.h, &id);
        self.net.pump();
        self.event("hold", &format!(r#","m":{m}"#));
    }

    fn release(&mut self, m: usize) {
        let id = self.net.id(m);
        let n0 = &mut self.net.nodes[0];
        n0.t.release(&mut n0.h, &id);
        self.net.pump();
        for t in 1..=2 {
            assert_eq!(self.state(t, m), None, "member {m} keeps topic {t} after a release");
        }
        self.event("release", &format!(r#","m":{m}"#));
    }

    fn restore(&mut self, m: usize) {
        let id = self.net.id(m);
        let held: Vec<u8> = (1..=2).filter(|t| self.state(*t, m) == Some(false)).collect();
        let n0 = &mut self.net.nodes[0];
        n0.h.out.clear();
        n0.t.restore(&mut n0.h, &id);
        let told: Vec<u8> =
            n0.h.out
                .iter()
                .filter(|o| o.to == id && o.bytes[4] == ty::RESTORED)
                .map(|o| {
                    let name = &o.bytes[6..6 + usize::from(o.bytes[5])];
                    if name == topic(1) { 1 } else { 2 }
                })
                .collect();
        let mut sorted = told.clone();
        sorted.sort_unstable();
        assert_eq!(
            sorted, held,
            "a restore of member {m} did not tell exactly the held topics"
        );
        self.net.pump();
        let list: Vec<String> = told.iter().map(u8::to_string).collect();
        self.event("restore", &format!(r#","m":{m},"told":[{}]"#, list.join(",")));
    }

    fn push(&mut self, t: u8) {
        let live: Vec<usize> = (1..=3).filter(|m| self.state(t, *m) == Some(true)).collect();
        let held: Vec<usize> = (1..=3).filter(|m| self.state(t, *m) == Some(false)).collect();
        let before = self.net.log.len();
        self.net.publish(4, topic(t), b"p");
        let pushed: BTreeSet<usize> = self.net.log[before..]
            .iter()
            .filter(|(_, from, to, fty, _)| *from == 0 && (1..=3).contains(to) && *fty == ty::MSG)
            .map(|(_, _, to, _, _)| *to)
            .collect();
        let pushed: Vec<usize> = pushed.into_iter().collect();
        assert!(
            held.iter().all(|m| !pushed.contains(m)),
            "a held member was pushed a message"
        );
        assert_eq!(pushed, live, "a push did not reach exactly the live subscriptions");
        self.event("push", &format!(r#","topic":{t},"pushed":{}"#, nums(&pushed)));
    }
}

fn scripted(w: &mut World) {
    w.sub(1, 1);
    w.sub(2, 1);
    w.sub(3, 1);
    w.sub(1, 2);
    w.push(1);
    w.push(2);
    w.hold(1);
    w.push(1);
    w.push(2);
    w.restore(1);
    w.restore(1);
    w.hold(2);
    w.unsub(2, 1);
    w.restore(2);
    w.push(1);
    w.release(3);
    w.push(1);
    w.restore(3);
    w.hold(3);
    w.unsub(3, 1);
    w.sub(3, 1);
    w.hold(1);
    w.release(1);
    w.restore(1);
    w.unsub(1, 1);
    w.unsub(1, 2);
    w.sub(1, 2);
    w.push(1);
    w.push(2);
}

fn seeded(w: &mut World) {
    let mut rng = SplitMix64::traced(0x5747_0007);
    for _ in 0..300 {
        let kind = rng.next_u64() % 6;
        let m = usize::try_from(1 + rng.next_u64() % 3).unwrap();
        match kind {
            0 => {
                let free: Vec<(usize, u8)> = (1..=3)
                    .flat_map(|m| [(m, 1u8), (m, 2u8)])
                    .filter(|p| !w.mine.contains(p))
                    .collect();
                if !free.is_empty() {
                    let (m, t) = free[usize::try_from(rng.next_u64()).unwrap() % free.len()];
                    w.sub(m, t);
                }
            }
            1 => {
                let held: Vec<(usize, u8)> = w.mine.iter().copied().collect();
                if !held.is_empty() {
                    let (m, t) = held[usize::try_from(rng.next_u64()).unwrap() % held.len()];
                    w.unsub(m, t);
                }
            }
            2 => w.hold(m),
            3 => w.restore(m),
            4 => w.release(m),
            _ => w.push(u8::try_from(1 + rng.next_u64() % 2).unwrap()),
        }
    }
}

#[test]
fn subs_trace() {
    let mut w = World {
        net: Net::new(IdentityAlg::Ed25519, 1, 4, SEC),
        mine: BTreeSet::new(),
        out: String::new(),
    };
    scripted(&mut w);
    seeded(&mut w);
    assert!(w.out.lines().count() > 200);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        let dir = std::path::Path::new(&dir).join("bcast");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("subs.ndjson"), &w.out).unwrap();
    }
}
