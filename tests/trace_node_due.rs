//! Trace generation for the node's deadline cache: a node over the scripted endpoint of `node_script.rs` and, after
//! every call and once more at once, the probe `trace_due`, which reads the cache, answers `due()` as the host would
//! and works the answer out fresh. Recorded as ndjson (`node_due.ndjson`) for the TLA+ trace check
//! (`TraceNodeDue.tla`), one line per ask: `{call, kind, due, ep, layers, layers_at, fresh, fresh_layers}`. A time is
//! `[t / 2^30, t % 2^30]` (TLC's integers are 32 bits), none is `[]`.
//!
//! The runs are a node with no relay and one with a relay, over a script that says exactly what waits and one that
//! cannot tell, driven by a timeout, data commands that move the endpoint's deadline, asks for a datagram (one that
//! waits and is routed to the connectivity layer, one that does not), a command, a poll and another call, 3 s apart.
//!
//! The test asserts, without the model: the answer is the earlier of the endpoint's deadline and the layers' part, a
//! cached layers' part is the layers' deadline worked out again at the clock it was taken at (a fresh one at the clock
//! now), the answer is never later than a fresh one, and a command, a routed packet, a timeout and a poll leave the
//! cache stale. The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    missing_docs,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

mod node_script;

use std::fmt::Write as _;

use node_script::{ScriptNode, id_of, node_with};
use pinc_core::{Command, SessionId, Transmit};
use pinc_node::{DueProbe, HUB_ALPN, NoApps};

const SEC: u64 = 1_000_000_000;

fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

fn time(t: Option<u64>) -> String {
    t.map_or_else(
        || "[]".to_string(),
        |t| format!("[{},{}]", t >> 30, t & ((1 << 30) - 1)),
    )
}

/// None is later than every time.
fn le(a: Option<u64>, b: Option<u64>) -> bool {
    b.is_none() || a.is_some_and(|a| a <= b.unwrap())
}

fn min(a: Option<u64>, b: Option<u64>) -> Option<u64> {
    if le(a, b) { a } else { b }
}

fn ask(n: &ScriptNode<NoApps>, call: &str, out: &mut String) {
    let p: DueProbe = n.trace_due();
    let kind = ["stale", "ep", "known"][usize::from(p.kind)];
    assert_eq!(
        p.due,
        min(p.ep, p.layers),
        "{call}: the answer is the endpoint's and the layers' part"
    );
    if p.kind == 0 {
        assert_eq!(
            p.layers, p.fresh_layers,
            "{call}: a stale cache works the layers out now"
        );
    } else {
        assert_eq!(
            p.layers, p.layers_at,
            "{call}: a cached layers' part is the layers' at its clock"
        );
    }
    assert!(
        le(p.due, p.fresh),
        "{call}: the answer {:?} is later than a fresh {:?}",
        p.due,
        p.fresh
    );
    if matches!(call, "command" | "routed" | "timeout" | "poll") {
        assert_eq!(kind, "stale", "{call} left the cache stale");
    }
    let _ = writeln!(
        out,
        "{{\"call\":\"{call}\",\"kind\":\"{kind}\",\"due\":{},\"ep\":{},\"layers\":{},\"layers_at\":{},\"fresh\":{},\"fresh_layers\":{}}}",
        time(p.due),
        time(p.ep),
        time(p.layers),
        time(p.layers_at),
        time(p.fresh),
        time(p.fresh_layers)
    );
}

fn datagram() -> Command<'static, pinc_transport::stream::NoSource> {
    Command::SendDatagram {
        session: SessionId(1),
        data: b"x",
    }
}

const STEPS: [&str; 14] = [
    "timeout", "data", "data", "transmit", "data", "routed", "data", "data", "command", "data", "poll", "data",
    "timeout", "other",
];

fn run(exact: bool, relay: bool, out: &mut String) {
    let hubs = if relay { vec![id_of(0x41)] } else { Vec::new() };
    let mut n = node_with(false, &hubs, HUB_ALPN, NoApps::default()).unwrap();
    n.endpoint_mut().exact = exact;
    ask(&n, "other", out);
    ask(&n, "other", out);
    let mut buf = [0u8; 2048];
    for (i, step) in STEPS.iter().enumerate() {
        let t = (i as u64 + 1) * 3 * SEC;
        // Every second command arms the endpoint's own timer, so its deadline moves under the cache.
        if i % 2 == 0 {
            let ep = n.endpoint_mut();
            ep.rearm = true;
            ep.next_due = Some(t + 5 * SEC);
        }
        match *step {
            "timeout" => n.handle_timeout(t),
            "data" => {
                n.data_command(t, datagram()).unwrap();
            }
            "transmit" => assert!(n.poll_transmit(t, &mut buf).is_none()),
            "routed" => {
                n.endpoint_mut().transmits.push_back(Transmit {
                    local: "203.0.113.10:4433".parse().unwrap(),
                    remote: pinc_core::relay_addr(false, 0, 1),
                    len: 1,
                    segment_size: 1,
                });
                assert!(
                    n.poll_transmit(t, &mut buf).is_none(),
                    "a routed packet is not the host's"
                );
            }
            "command" => {
                n.command(t, datagram()).unwrap();
            }
            "poll" => n.poll(t),
            "other" => assert!(n.set_hints(t, b"h")),
            _ => unreachable!(),
        }
        ask(&n, step, out);
        ask(&n, "other", out);
    }
}

#[test]
fn the_deadline_cache_answers_the_layers_and_endpoint_and_is_never_late() {
    let out = big(|| {
        let mut out = String::new();
        for exact in [true, false] {
            for relay in [false, true] {
                run(exact, relay, &mut out);
            }
        }
        out
    });
    assert!(
        out.contains("\"kind\":\"ep\""),
        "a data command leaves the layers' part cached"
    );
    assert!(out.contains("\"call\":\"routed\""));
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("node_due.ndjson"), out).unwrap();
    }
}
