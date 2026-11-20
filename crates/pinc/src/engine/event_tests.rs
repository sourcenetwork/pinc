//! The topic event queue of the core, recorded for the trace check `TraceFacadeEvents`: pushes past the queue's size,
//! node losses, a stop, and seeded random calls, each with the queue after it.

#![allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]

use alloc::collections::VecDeque;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::fmt::Write as _;

use pinc_node::NodeEvent;

use super::EVENTS;
use crate::engine::Try;
use crate::engine::adjacent_tests::{C, core};
use crate::error::Error;
use crate::event::Event;
use crate::trace_util::{below, mix, write_trace};

/// One core with the shadow the test checks the answers against.
struct Run {
    c: C,
    next_id: u32,
    queued: VecDeque<u32>,
    owed: u64,
    last_polled: u32,
    stopped: bool,
    lines: Vec<String>,
}

fn limbs(v: u32) -> String {
    format!("[{},{}]", v & 0xffff, v >> 16)
}

impl Run {
    fn new(out: &[String]) -> Self {
        let mut r = Self {
            c: core(),
            next_id: 1,
            queued: VecDeque::new(),
            owed: 0,
            last_polled: 0,
            stopped: false,
            lines: Vec::new(),
        };
        assert!(matches!(r.c.poll_event(), Try::Wait(_)));
        r.line("init", "", out);
        r
    }

    fn id_of(e: &Event) -> u32 {
        match e {
            Event::Message { payload, .. } => u32::from_be_bytes(payload[..4].try_into().unwrap()),
            other => unreachable!("{other:?}"),
        }
    }

    fn queue_ids(&self) -> String {
        let ids: Vec<String> = self.c.events.iter().map(|e| Self::id_of(e).to_string()).collect();
        format!("[{}]", ids.join(","))
    }

    /// One line, without its closing brace: the queue after the call. Every 50th line of the file carries the queue.
    fn line(&mut self, op: &str, extra: &str, out: &[String]) {
        let first = self.c.events.front().map_or(0, Self::id_of);
        let last = self.c.events.back().map_or(0, Self::id_of);
        let mut l = format!(
            r#"{{"t":"events","op":"{op}",{extra}"qn":{},"first":{first},"last":{last},"lost":{},"stopped":{}"#,
            self.c.events.len(),
            limbs(self.c.lost),
            self.c.stopped.is_some()
        );
        if (out.len() + self.lines.len() + 1).is_multiple_of(50) {
            let _ = write!(l, r#","q":{}"#, self.queue_ids());
        }
        self.lines.push(l);
    }

    fn push(&mut self, out: &[String]) {
        let k = self.next_id;
        self.next_id += 1;
        self.c.on_node_event(
            1,
            NodeEvent::Message {
                topic: b"t".to_vec(),
                origin: [1; 32],
                hop: [1; 32],
                mid: [0; 8],
                body: k.to_be_bytes().to_vec(),
            },
        );
        if self.queued.len() < EVENTS {
            self.queued.push_back(k);
        } else {
            self.owed += 1;
        }
        self.line("push", &format!(r#""id":{k},"#), out);
    }

    fn node_lost(&mut self, n: u32, out: &[String]) {
        self.c.on_node_event(1, NodeEvent::Lost { count: n });
        self.owed += u64::from(n);
        self.line("nodelost", &format!(r#""c":{},"#, limbs(n)), out);
    }

    fn stop(&mut self, out: &[String]) {
        self.c.stopped = Some(Error::shutdown());
        self.stopped = true;
        self.line("stop", "", out);
    }

    /// Poll, check the answer against the shadow, and return its kind.
    fn poll(&mut self, out: &[String]) -> &'static str {
        let (r, n, e) = match self.c.poll_event() {
            Try::Done(Some(Event::Lost { count })) => {
                assert_eq!(u64::from(count), self.owed.min(u64::from(u32::MAX)));
                self.owed = 0;
                ("lost", count, 0)
            }
            Try::Done(Some(ev @ Event::Message { .. })) => {
                assert_eq!(self.owed, 0, "an event came before the count");
                let id = Self::id_of(&ev);
                assert_eq!(Some(id), self.queued.pop_front());
                assert!(id > self.last_polled, "ids rise");
                self.last_polled = id;
                ("event", 0, id)
            }
            Try::Done(None) => {
                assert!(self.stopped && self.owed == 0 && self.queued.is_empty());
                ("none", 0, 0)
            }
            Try::Done(Some(other)) => unreachable!("{other:?}"),
            Try::Taken(_) => unreachable!("an event returns through Done"),
            Try::Wait(_) => {
                assert!(!self.stopped && self.owed == 0 && self.queued.is_empty());
                ("wait", 0, 0)
            }
        };
        assert!(self.c.events.len() <= EVENTS);
        self.line("poll", &format!(r#""r":"{r}","n":{},"e":{e},"#, limbs(n)), out);
        r
    }

    fn poll_until(&mut self, kind: &str, out: &[String]) {
        while self.poll(out) != kind {}
    }

    /// The core is done: the last line carries the whole queue, and the lines join the file.
    fn finish(mut self, out: &mut Vec<String>) {
        if self.lines.last().is_some_and(|l| !l.contains(r#","q":"#)) {
            let q = self.queue_ids();
            if let Some(l) = self.lines.last_mut() {
                let _ = write!(l, r#","q":{q}"#);
            }
        }
        out.append(&mut self.lines);
    }
}

#[test]
fn trace_events() {
    let mut out: Vec<String> = Vec::new();

    let mut r = Run::new(&out);
    for _ in 0..1030 {
        r.push(&out);
    }
    assert_eq!(r.poll(&out), "lost");
    r.poll_until("wait", &out);
    r.finish(&mut out);

    let mut r = Run::new(&out);
    for _ in 0..10 {
        r.push(&out);
    }
    r.node_lost(3, &out);
    assert_eq!(r.poll(&out), "lost");
    r.push(&out);
    r.poll_until("wait", &out);
    r.finish(&mut out);

    let mut r = Run::new(&out);
    r.node_lost(u32::MAX - 1, &out);
    for _ in 0..1027 {
        r.push(&out);
    }
    assert_eq!(r.c.lost, u32::MAX);
    assert_eq!(r.poll(&out), "lost");
    assert_eq!(r.poll(&out), "event");
    r.finish(&mut out);

    let mut r = Run::new(&out);
    for _ in 0..5 {
        r.push(&out);
    }
    r.node_lost(2, &out);
    r.stop(&out);
    r.poll_until("none", &out);
    assert_eq!(r.poll(&out), "none");
    r.push(&out);
    assert_eq!(r.poll(&out), "event");
    assert_eq!(r.poll(&out), "none");
    r.finish(&mut out);

    for seed in 1..=4u64 {
        let mut rng = seed;
        let mut r = Run::new(&out);
        let mut bursts = 0;
        for _ in 0..3000 {
            match below(&mut rng, 100) {
                0..60 => r.push(&out),
                90..95 => {
                    let n = if mix(&mut rng).is_multiple_of(50) {
                        u32::MAX - 1
                    } else {
                        1 + u32::try_from(mix(&mut rng) % 3).unwrap()
                    };
                    r.node_lost(n, &out);
                }
                95 if !r.stopped => r.stop(&out),
                96..100 if bursts < 2 => {
                    bursts += 1;
                    for _ in 0..1100 {
                        r.push(&out);
                    }
                }
                _ => {
                    r.poll(&out);
                }
            }
        }
        r.finish(&mut out);
    }

    let mut text = String::new();
    for l in out {
        text.push_str(&l);
        text.push_str("}\n");
    }
    write_trace("facade_events.ndjson", &text);
}

/// A hub-full notice is told for a topic this endpoint joined, and for no other.
#[test]
fn a_hub_full_notice_is_told_for_a_joined_topic_only() {
    let mut c = core();
    let topic = b"full".to_vec();
    c.on_node_event(
        1,
        NodeEvent::HubFull {
            hub: [1; 32],
            topic: topic.clone(),
        },
    );
    assert!(c.events.is_empty());
    c.topics.insert(topic.clone(), Vec::new());
    c.on_node_event(
        1,
        NodeEvent::HubFull {
            hub: [1; 32],
            topic: topic.clone(),
        },
    );
    let hub = c.node.full_id(&[1; 32]);
    assert_eq!(
        c.events.pop_front(),
        Some(Event::HubFull {
            topic,
            hub,
            message: None
        })
    );
    let mid = [7; 8];
    c.on_node_event(
        1,
        NodeEvent::PublishFull {
            hub: [1; 32],
            topic: b"other".to_vec(),
            mid,
        },
    );
    let hub = c.node.full_id(&[1; 32]);
    assert_eq!(
        c.events.pop_front(),
        Some(Event::HubFull {
            topic: b"other".to_vec(),
            hub,
            message: Some(mid)
        }),
        "a refused publish is told with no joined-topic guard"
    );
    assert!(c.events.is_empty());
}
