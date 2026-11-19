//! The node programs of the real workloads, on loopback addresses, with no root and no Docker: each test starts the
//! binary in node mode as one process per node (127.x.y.z addresses, one test per second octet so they can run side by
//! side), speaks the control protocol to them and checks what the programs report.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

use std::io::{BufRead, BufReader, Write};
use std::net::Ipv4Addr;
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{Receiver, channel};
use std::time::{Duration, Instant};

use std::collections::BTreeMap;

use pinc_distributed::dtn::{Check, Sent, evaluate};
use pinc_distributed::node::pinc::node_id;
use pinc_distributed::node::proto::{Cmd, DtnInit, DtnReport, DtnWhat, Init, PeerSpec, PubSubReport, Reply, Request};
use pinc_distributed::scenario::{Role, Stack};
use serde_json::{Value, json};

struct Prog {
    child: Child,
    stdin: ChildStdin,
    out: Receiver<String>,
    next: u64,
}

impl Prog {
    fn start(init: &Init) -> Self {
        let mut child = Command::new(env!("CARGO_BIN_EXE_pinc-distributed"))
            .args(["node", "app"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap();
        let mut stdin = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();
        let (tx, out) = channel();
        std::thread::spawn(move || {
            for l in BufReader::new(stdout).lines().map_while(Result::ok) {
                if tx.send(l).is_err() {
                    break;
                }
            }
        });
        writeln!(stdin, "{}", serde_json::to_string(init).unwrap()).unwrap();
        let mut me = Self {
            child,
            stdin,
            out,
            next: 1,
        };
        let ready = me.line(Duration::from_secs(60));
        assert!(ready.starts_with("READY "), "{} did not start: {ready}", init.name);
        me
    }

    fn line(&mut self, wait: Duration) -> String {
        self.out
            .recv_timeout(wait)
            .unwrap_or_else(|e| panic!("the program said nothing for {wait:?}: {e}"))
    }

    fn send(&mut self, cmd: Cmd) -> u64 {
        let id = self.next;
        self.next += 1;
        writeln!(self.stdin, "{}", serde_json::to_string(&Request { id, cmd }).unwrap()).unwrap();
        id
    }

    fn wait(&mut self, id: u64, wait: Duration) -> Reply {
        let end = Instant::now() + wait;
        loop {
            let left = end.saturating_duration_since(Instant::now());
            let l = self.line(left);
            let r: Reply = serde_json::from_str(&l).unwrap();
            if r.re == id {
                return r;
            }
        }
    }

    fn call(&mut self, cmd: Cmd, secs: u64) -> Reply {
        let id = self.send(cmd);
        self.wait(id, Duration::from_secs(secs))
    }

    fn ok(&mut self, cmd: Cmd, secs: u64) -> Value {
        let r = self.call(cmd, secs);
        assert!(r.ok, "{:?}", r.error);
        r.data
    }
}

impl Drop for Prog {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// A group of `peers` peers and one hub on 127.`net`.0.x.
fn group(stack: Stack, net: u8, peers: u16) -> Vec<(Init, Role)> {
    let mut specs = vec![PeerSpec {
        name: "hub".into(),
        index: 0,
        ip: Ipv4Addr::new(127, net, 0, 1),
        public_ip: Ipv4Addr::new(127, net, 0, 1),
        role: Role::Hub,
        slot: 0,
    }];
    for i in 1..=peers {
        specs.push(PeerSpec {
            name: format!("p-{i}"),
            index: i,
            ip: Ipv4Addr::new(127, net, 0, u8::try_from(i + 1).unwrap()),
            public_ip: Ipv4Addr::new(127, net, 0, u8::try_from(i + 1).unwrap()),
            role: Role::Peer,
            slot: 0,
        });
    }
    specs
        .iter()
        .map(|s| {
            (
                Init {
                    stack,
                    name: s.name.clone(),
                    peers: specs.clone(),
                    mtu: 1500,
                    sessions: 16,
                    iroh_gossip_max: None,
                    dtn: None,
                    trace: false,
                    portmap: false,
                },
                s.role,
            )
        })
        .collect()
}

fn report(p: &mut Prog) -> PubSubReport {
    let v = p.ok(Cmd::Report, 30);
    serde_json::from_value(v["pubsub"].clone()).unwrap()
}

/// Everything published reaches every subscriber exactly once, with a latency measured.
fn pubsub_on(stack: Stack, net: u8) {
    let mut progs: Vec<Prog> = group(stack, net, 3).iter().map(|(i, _)| Prog::start(i)).collect();
    for p in &mut progs {
        p.ok(
            Cmd::Join {
                topic: "t".into(),
                wait_ms: 40_000,
            },
            60,
        );
    }
    std::thread::sleep(Duration::from_secs(4));
    let published = progs[1].ok(
        Cmd::Publish {
            topic: "t".into(),
            count: 60,
            size: 100,
            interval_us: 10_000,
            start_ns: 0,
        },
        60,
    );
    assert_eq!(published["published"], json!(60));
    // A deadline and a bounded backoff, not a fixed wait.
    let end = Instant::now() + Duration::from_secs(30);
    let mut backoff = Duration::from_millis(50);
    let rep = loop {
        let r = report(&mut progs[2]);
        if r.delivered >= 60 || Instant::now() >= end {
            break r;
        }
        std::thread::sleep(backoff);
        backoff = (backoff * 2).min(Duration::from_secs(1));
    };
    assert_eq!(rep.delivered, 60, "{rep:?}");
    assert_eq!(rep.duplicates, 0);
    assert_eq!(rep.per_origin.get(&1), Some(&60));
    let p99 = rep.latency_us.quantile(0.99).unwrap();
    assert!(p99 > 0.0 && p99 < 5_000_000.0, "{p99}");
    // The publisher is not owed its own messages.
    assert_eq!(report(&mut progs[1]).delivered, 0);
}

#[test]
fn pinc_delivers_every_message_once() {
    pubsub_on(Stack::Pinc, 101);
}

#[test]
fn iroh_delivers_every_message_once() {
    pubsub_on(Stack::Iroh, 102);
}

#[test]
fn libp2p_delivers_every_message_once() {
    pubsub_on(Stack::Libp2p, 103);
}

/// A value held by `providers` providers reaches another node whole.
fn sync_on(stack: Stack, net: u8, providers: u16, size: u64) {
    let mut progs: Vec<Prog> = group(stack, net, providers + 1)
        .iter()
        .map(|(i, _)| Prog::start(i))
        .collect();
    for p in &mut progs {
        p.ok(
            Cmd::Join {
                topic: "sync".into(),
                wait_ms: 40_000,
            },
            60,
        );
    }
    let mut value = Value::Null;
    for p in progs.iter_mut().skip(1).take(usize::from(providers)) {
        value = p.ok(Cmd::Provide { size, seed: 9 }, 120);
    }
    let names: Vec<String> = (1..=providers).map(|i| format!("p-{i}")).collect();
    let got = progs[usize::from(providers) + 1].ok(
        Cmd::Fetch {
            value,
            providers: names,
            timeout_ms: 60_000,
        },
        90,
    );
    assert_eq!(got["bytes"], json!(size));
    assert!(got["ms"].as_f64().unwrap() > 0.0);
}

#[test]
fn pinc_fetches_a_value_from_two_providers() {
    sync_on(Stack::Pinc, 104, 2, 3 * (1 << 20) + 17);
}

#[test]
fn iroh_fetches_a_value_from_two_providers() {
    sync_on(Stack::Iroh, 105, 2, 3 * (1 << 20) + 17);
}

#[test]
fn libp2p_fetches_a_value_from_two_providers() {
    sync_on(Stack::Libp2p, 106, 2, 3 * (1 << 20) + 17);
}

#[test]
fn pinc_fetches_a_small_value_from_three_providers() {
    sync_on(Stack::Pinc, 110, 3, 3 << 20);
}

/// A value of 48 MiB held by two providers reaches the consumer over real sockets on loopback. It once did not finish
/// in a minute: a provider's session that began on the relay never moved to the direct path, and the relay's quota ran
/// out.
#[test]
fn pinc_fetches_a_large_value_from_two_providers() {
    sync_on(Stack::Pinc, 111, 2, 48 << 20);
}

#[test]
fn pinc_fetches_a_large_value_from_one_provider() {
    sync_on(Stack::Pinc, 112, 1, 48 << 20);
}

/// Two sets that differ in a few items on each side reconcile to exactly that difference.
#[test]
fn pinc_reconciles_two_sets_to_their_exact_difference() {
    let mut progs: Vec<Prog> = group(Stack::Pinc, 107, 2).iter().map(|(i, _)| Prog::start(i)).collect();
    for p in &mut progs {
        p.ok(
            Cmd::Join {
                topic: "sets".into(),
                wait_ms: 40_000,
            },
            60,
        );
    }
    for (i, other) in [(1usize, 1u64), (2, 2)] {
        progs[i].ok(
            Cmd::HoldSet {
                set: "s".into(),
                items: 600,
                seed: 5,
                different: 7,
                other_seed: other,
            },
            60,
        );
    }
    let got = progs[2].ok(
        Cmd::Reconcile {
            peer: "p-1".into(),
            set: "s".into(),
            timeout_ms: 30_000,
        },
        60,
    );
    assert_eq!(got["missing_here"], json!(7));
    assert_eq!(got["missing_there"], json!(7));
}

fn dtn_log(p: &mut Prog) -> DtnReport {
    let v = p.ok(Cmd::Report, 30);
    serde_json::from_value(v["dtn"].clone()).unwrap()
}

/// Store and forward through pinc-node's own layer: the source sends to a node that has not started, hands a copy to
/// the carrier and ends; the destination starts later and gets the bundle, intact and once, from the carrier. The
/// logs pass the custody and copy rules.
#[test]
fn pinc_carries_a_bundle_to_a_node_that_comes_online_after_its_source_left() {
    let mut inits = group(Stack::Pinc, 113, 3);
    for (init, role) in &mut inits {
        if *role == Role::Peer {
            init.dtn = Some(DtnInit {
                budget: 64 << 20,
                retry_ms: 2_000,
                max_sends: 8,
                dir: None,
                tamper_slices: false,
                tamper_one_slice: false,
                tamper_heads: false,
            });
        }
    }
    let (src, carrier, dst) = ("p-1", "p-2", "p-3");
    let mut progs: Vec<Prog> = inits.iter().take(3).map(|(i, _)| Prog::start(i)).collect();
    for p in &mut progs {
        p.ok(
            Cmd::Join {
                topic: "dtn".into(),
                wait_ms: 40_000,
            },
            60,
        );
    }
    std::thread::sleep(Duration::from_secs(3));
    let size = 200_000;
    let sent_at = u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_millis(),
    )
    .unwrap();
    let v = progs[1].ok(
        Cmd::DtnSend {
            to: dst.into(),
            size,
            seed: 9,
            copies: 2,
            lifetime_ms: 300_000,
            k: 4,
            m: 2,
            slice_log: 2,
        },
        30,
    );
    let bundle = v["bundle"].as_str().unwrap().to_owned();
    // The carrier takes its copy (deadline and bounded backoff, not a fixed wait).
    let end = Instant::now() + Duration::from_secs(60);
    let mut backoff = Duration::from_millis(100);
    while dtn_log(&mut progs[2]).held == 0 {
        assert!(Instant::now() < end, "the carrier never took the bundle");
        std::thread::sleep(backoff);
        backoff = (backoff * 2).min(Duration::from_secs(1));
    }
    let src_log = dtn_log(&mut progs[1]);
    drop(progs.remove(1));
    let mut late = Prog::start(&inits[3].0);
    late.ok(
        Cmd::Join {
            topic: "dtn".into(),
            wait_ms: 40_000,
        },
        60,
    );
    let end = Instant::now() + Duration::from_secs(90);
    let got = loop {
        let l = dtn_log(&mut late);
        if l.log.iter().any(|e| matches!(e.what, DtnWhat::Received { .. })) || Instant::now() >= end {
            break l;
        }
        std::thread::sleep(Duration::from_millis(500));
    };
    let mut logs = BTreeMap::new();
    logs.insert(src.to_owned(), vec![src_log]);
    logs.insert(carrier.to_owned(), vec![dtn_log(&mut progs[1])]);
    logs.insert(dst.to_owned(), vec![got]);
    let sent = [Sent {
        bundle,
        from: src.into(),
        to: dst.into(),
        copies: 2,
        at_ms: sent_at,
        lifetime_ms: 300_000,
    }];
    let checks = [
        Check::Delivered {
            to: dst.into(),
            via: Some(carrier.into()),
            after_s: None,
        },
        Check::Custody { moves: vec![] },
        Check::Copies,
        Check::NoRefetch { at: dst.into() },
    ];
    let o = evaluate(&checks, &sent, &logs, sent_at, |n| node_id(n).ok().map(|i| i.bytes));
    assert_eq!(o.failures, Vec::<String>::new(), "{logs:#?}");
    assert_eq!(o.passed, 4);
}

/// Set reconciliation is asked of a stack that has no protocol for it: the answer says so, and the program goes on.
#[test]
fn a_stack_without_set_reconciliation_says_so() {
    let mut progs: Vec<Prog> = group(Stack::Libp2p, 108, 1)
        .iter()
        .map(|(i, _)| Prog::start(i))
        .collect();
    let r = progs[1].call(
        Cmd::HoldSet {
            set: "s".into(),
            items: 10,
            seed: 1,
            different: 1,
            other_seed: 2,
        },
        30,
    );
    assert!(!r.ok);
    assert!(r.error.unwrap().contains("not available"));
    // Still answering.
    assert!(progs[1].call(Cmd::Report, 30).ok);
}

/// A line that is not a request is answered with an error and does not end the program.
#[test]
fn a_request_that_is_not_understood_is_answered_and_the_program_goes_on() {
    let mut progs: Vec<Prog> = group(Stack::Libp2p, 109, 1)
        .iter()
        .map(|(i, _)| Prog::start(i))
        .collect();
    writeln!(progs[1].stdin, "this is not json").unwrap();
    let l = progs[1].line(Duration::from_secs(10));
    let r: Reply = serde_json::from_str(&l).unwrap();
    assert!(!r.ok);
    assert!(progs[1].call(Cmd::Report, 30).ok);
}

/// With tracing asked for, a PINC node reports its trace and packet log; without, the report has no trace.
#[test]
fn a_traced_pinc_node_reports_its_packet_log_and_an_untraced_one_does_not() {
    let mut inits = group(Stack::Pinc, 140, 2);
    for (init, _) in &mut inits {
        init.trace = init.name == "p-2";
    }
    let mut progs: Vec<Prog> = inits.iter().map(|(i, _)| Prog::start(i)).collect();
    for p in &mut progs {
        p.ok(
            Cmd::Join {
                topic: "sync".into(),
                wait_ms: 40_000,
            },
            60,
        );
    }
    let value = progs[1].ok(Cmd::Provide { size: 4096, seed: 9 }, 60);
    progs[2].ok(
        Cmd::Fetch {
            value,
            providers: vec!["p-1".into()],
            timeout_ms: 60_000,
        },
        90,
    );
    let plain = progs[1].ok(Cmd::Report, 30);
    assert!(plain.get("trace").is_none(), "{plain}");
    let traced = progs[2].ok(Cmd::Report, 30);
    let entries = traced["trace"]["entries"].as_array().unwrap();
    assert_eq!(traced["trace"]["dropped"], json!(0));
    for kind in ["trace", "udp_rx", "udp_tx"] {
        assert!(entries.iter().any(|e| e[1] == kind), "no {kind} entry");
    }
    assert!(entries.iter().all(|e| e[0].is_u64() && e[2].is_string()));
}
