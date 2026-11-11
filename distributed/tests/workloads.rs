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

use serde_json::{Value, json};
use vinc_distributed::node::proto::{Cmd, Init, PeerSpec, PubSubReport, Reply, Request};
use vinc_distributed::scenario::{Role, Stack};

struct Prog {
    child: Child,
    stdin: ChildStdin,
    out: Receiver<String>,
    next: u64,
}

impl Prog {
    fn start(init: &Init) -> Self {
        let mut child = Command::new(env!("CARGO_BIN_EXE_vinc-distributed"))
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
    }];
    for i in 1..=peers {
        specs.push(PeerSpec {
            name: format!("p-{i}"),
            index: i,
            ip: Ipv4Addr::new(127, net, 0, u8::try_from(i + 1).unwrap()),
            public_ip: Ipv4Addr::new(127, net, 0, u8::try_from(i + 1).unwrap()),
            role: Role::Peer,
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
fn vinc_delivers_every_message_once() {
    pubsub_on(Stack::Vinc, 101);
}

#[test]
fn iroh_delivers_every_message_once() {
    pubsub_on(Stack::Iroh, 102);
}

#[test]
fn libp2p_delivers_every_message_once() {
    pubsub_on(Stack::Libp2p, 103);
}

/// A value held by two providers reaches a third node whole.
fn sync_on(stack: Stack, net: u8) {
    let mut progs: Vec<Prog> = group(stack, net, 3).iter().map(|(i, _)| Prog::start(i)).collect();
    for p in &mut progs {
        p.ok(
            Cmd::Join {
                topic: "sync".into(),
                wait_ms: 40_000,
            },
            60,
        );
    }
    let size = 3 * (1 << 20) + 17;
    let mut value = Value::Null;
    for i in [1, 2] {
        value = progs[i].ok(Cmd::Provide { size, seed: 9 }, 120);
    }
    let got = progs[3].ok(
        Cmd::Fetch {
            value,
            providers: vec!["p-1".into(), "p-2".into()],
            timeout_ms: 60_000,
        },
        90,
    );
    assert_eq!(got["bytes"], json!(size));
    assert!(got["ms"].as_f64().unwrap() > 0.0);
}

#[test]
fn vinc_fetches_a_value_from_two_providers() {
    sync_on(Stack::Vinc, 104);
}

#[test]
fn iroh_fetches_a_value_from_two_providers() {
    sync_on(Stack::Iroh, 105);
}

#[test]
fn libp2p_fetches_a_value_from_two_providers() {
    sync_on(Stack::Libp2p, 106);
}

/// Two sets that differ in a few items on each side reconcile to exactly that difference.
#[test]
fn vinc_reconciles_two_sets_to_their_exact_difference() {
    let mut progs: Vec<Prog> = group(Stack::Vinc, 107, 2).iter().map(|(i, _)| Prog::start(i)).collect();
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
