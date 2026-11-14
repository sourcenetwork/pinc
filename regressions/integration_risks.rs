//! Scratch reproductions of suspected gaps between a comment's promise and the code (not for merge). Each test asserts
//! the promise as written, so a failure is the reproduction; the printed lines record what was observed.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::large_stack_arrays,
    clippy::semicolon_if_nothing_returned,
    clippy::items_after_statements,
    clippy::print_stdout
)]

mod node_common;
mod vinc_common;

use std::net::{SocketAddr, UdpSocket};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

use node_common::{World, big, secs};
use vinc::NodeAddr;
use vinc_core::{Answer, Command, CommandError, Event, Query, Role, SessionStats, Value};
use vinc_node::trace::tag;
use vinc_node::{Body, HUB_ALPN, NodeEvent, NodeTrace};
use vinc_tests::{ALPN_A, ALPN_B, CoreNet, MS_NS, NCmd, NEv, SEC_NS, big_stack};

/// Every live session of an endpoint, as its counters.
macro_rules! stats_list {
    ($ep:expr) => {{
        let mut v: Vec<SessionStats> = Vec::new();
        for i in 0..256 {
            match $ep.query(Query::SessionAt(i)) {
                Answer::Stats(s) => v.push(s),
                _ => break,
            }
        }
        v
    }};
}

fn is_hub_with(s: &SessionStats, peer: &[u8; 32]) -> bool {
    s.node.is_some_and(|n| n.bytes == *peer) && s.alpn.is_some_and(|a| a.as_bytes() == HUB_ALPN)
}

// ------------------------------------------------------------------------------------------------ claim 1

/// `vinc-node/src/events.rs:8`: "a hub-protocol session produces no stream event for the application".
#[test]
fn c1_a_stopped_hub_stream_reaches_the_application() {
    big(|| {
        let mut w = World::build_with(11, 1, 1, |w| w.trace = true);
        w.run(secs(20));
        let (hub, m) = (w.hubs[0].0, w.members[0]);
        let (mid, hid) = (w.id(m), w.id(hub));
        let sid = stats_list!(w.sim.node(hub).node.endpoint())
            .into_iter()
            .find(|s| is_hub_with(s, &mid))
            .expect("the hub holds a hub session with the member")
            .session;
        let t = secs(20);
        // The hub asks the member to stop sending on stream 0, the write stream the member opened when it dialed.
        let r = w.sim.node_mut(hub).node.command(
            t,
            Command::StopSending {
                session: sid,
                stream: 0,
                error: 7,
            },
        );
        println!("c1: StopSending(stream 0) at the hub: {r:?}");
        w.sim.command(t, hub, NCmd::Tick);
        w.run(secs(25));
        let stopped: Vec<_> = w
            .sim
            .events(m)
            .iter()
            .filter(|(at, e)| {
                *at >= t && matches!(e, NEv::Node(NodeEvent::Endpoint(Event::StreamStopped { .. })))
            })
            .cloned()
            .collect();
        println!("c1: member application events of kind StreamStopped: {stopped:?}");
        // The member's node keeps the stopped stream as its write stream: a write to it now.
        let msid = stats_list!(w.sim.node(m).node.endpoint())
            .into_iter()
            .find(|s| is_hub_with(s, &hid))
            .expect("the member holds a hub session")
            .session;
        let probe = w.sim.node_mut(m).node.command(
            secs(25),
            Command::Write {
                session: msid,
                stream: 0,
                data: b"x",
            },
        );
        println!("c1: a write to the member's hub write stream after the stop: {probe:?}");
        // What the member's hub direction does afterwards (its write stream is reset under it).
        w.run(secs(200));
        let ht = tag(&hid);
        let downs: Vec<_> = w
            .sim
            .node(m)
            .traces
            .iter()
            .filter(|(at, it)| {
                *at >= t
                    && matches!(it.body, Body::Node(NodeTrace::SessionDown { peer, .. } | NodeTrace::BacklogClosed { peer } | NodeTrace::StreamRepaired { peer }) if peer == ht)
            })
            .map(|(at, it)| (*at / SEC_NS, format!("{:?}", it.body)))
            .collect();
        println!("c1: member traces about the hub after the stop: {downs:?}");
        println!(
            "c1: the hub's view holds the member at 200 s: {}",
            w.view(hub).contains(&mid)
        );
        assert!(
            stopped.is_empty(),
            "a hub-protocol session raised a stream event for the application: {stopped:?}"
        );
    });
}

/// What the stopped write stream costs: the node keeps it as the member's hub write stream, so what the member
/// publishes afterwards does not reach the other member.
#[test]
fn c1b_after_the_stop_a_members_publish_is_lost() {
    big(|| {
        let mut w = World::build_with(12, 1, 2, |w| w.trace = true);
        let (hub, m0, m1) = (w.hubs[0].0, w.members[0], w.members[1]);
        for m in [m0, m1] {
            w.sim.command(secs(1), m, NCmd::Subscribe(b"t".to_vec()));
        }
        w.run(secs(20));
        w.sim.command(
            secs(20),
            m0,
            NCmd::Publish {
                topic: b"t".to_vec(),
                body: b"before".to_vec(),
            },
        );
        w.run(secs(30));
        let mid = w.id(m0);
        let sid = stats_list!(w.sim.node(hub).node.endpoint())
            .into_iter()
            .find(|s| is_hub_with(s, &mid))
            .unwrap()
            .session;
        let t = secs(30);
        let _ = w.sim.node_mut(hub).node.command(
            t,
            Command::StopSending {
                session: sid,
                stream: 0,
                error: 7,
            },
        );
        w.sim.command(t, hub, NCmd::Tick);
        w.run(secs(35));
        w.sim.command(
            secs(35),
            m0,
            NCmd::Publish {
                topic: b"t".to_vec(),
                body: b"after".to_vec(),
            },
        );
        w.run(secs(120));
        let got: Vec<_> = w.messages(m1).into_iter().map(|(at, _, _, body)| (at / SEC_NS, body)).collect();
        let gave_up = w
            .sim
            .events(m0)
            .iter()
            .filter(|(_, e)| matches!(e, NEv::Node(NodeEvent::PublishGaveUp { .. })))
            .count();
        println!("c1b: messages member 1 received (s, body): {got:?}; member 0 PublishGaveUp events: {gave_up}");
        assert!(got.iter().any(|(_, b)| b == b"after"), "the publish after the stop never arrived");
    });
}

// ------------------------------------------------------------------------------------------------ claim 2

/// A UDP relay to `to` that drops every datagram until `open` is set.
fn gate_proxy(to: SocketAddr, open: Arc<AtomicBool>, stop: Arc<AtomicBool>) -> SocketAddr {
    let s = UdpSocket::bind("127.0.0.1:0").unwrap();
    s.set_read_timeout(Some(Duration::from_millis(20))).unwrap();
    let addr = s.local_addr().unwrap();
    std::thread::spawn(move || {
        let mut client: Option<SocketAddr> = None;
        let mut buf = vec![0u8; 65_536];
        while !stop.load(Ordering::Relaxed) {
            let Ok((n, from)) = s.recv_from(&mut buf) else {
                continue;
            };
            if from != to {
                client = Some(from);
            }
            if !open.load(Ordering::Relaxed) {
                continue;
            }
            if from == to {
                if let Some(c) = client {
                    let _ = s.send_to(&buf[..n], c);
                }
            } else {
                let _ = s.send_to(&buf[..n], to);
            }
        }
    });
    addr
}

/// `vinc/src/engine.rs:546`: a dial is found by `(node, alpn)` and `ConnectFailed` names no session, so the failure of
/// one dial ends whichever dial to the same peer and protocol started last.
#[nuclei::test]
async fn c2_one_dials_failure_ends_another_dial_to_the_same_peer() {
    vinc_common::within(150, async {
        let server = vinc_common::node().await;
        let s_addr = server.addr();
        let s_udp = s_addr.direct[0];
        let client = vinc_common::bind(
            vinc_common::builder()
                .alpn(vinc_common::ECHO)
                .connect_timeout(Duration::from_secs(40)),
        )
        .await;
        // Dial 1 goes to an address that never answers: its handshake gives up after 30 s (ConnectFailed{Timeout}).
        let hole = UdpSocket::bind("127.0.0.1:0").unwrap();
        let (open, stop) = (Arc::new(AtomicBool::new(false)), Arc::new(AtomicBool::new(false)));
        // Dial 2 goes through a relay that lets nothing through until just after dial 1 gave up, then works.
        let proxy = gate_proxy(s_udp, Arc::clone(&open), Arc::clone(&stop));
        let t0 = Instant::now();
        let (c1, n1) = (
            client.clone(),
            NodeAddr {
                node: s_addr.node,
                direct: vec![hole.local_addr().unwrap()],
                relays: vec![],
            },
        );
        let d1 = nuclei::spawn_local(async move {
            let r = c1.connect(n1, vinc_common::ECHO).await;
            (t0.elapsed(), r.map(|_| ()).map_err(|e| format!("{:?}: {}", e.kind(), e.message())))
        });
        nuclei::time::sleep(Duration::from_secs(27)).await;
        let (c2, n2) = (
            client.clone(),
            NodeAddr {
                node: s_addr.node,
                direct: vec![proxy],
                relays: vec![],
            },
        );
        let d2 = nuclei::spawn_local(async move {
            let r = c2.connect(n2, vinc_common::ECHO).await;
            let at = t0.elapsed();
            let out = match r {
                Ok(conn) => {
                    let (mut tx, mut rx) = conn.open_bi().await.unwrap();
                    tx.write_all(b"alive").await.unwrap();
                    tx.finish().await.unwrap();
                    Ok(rx.read_to_end(100).await.unwrap())
                }
                Err(e) => Err(format!("{:?}: {}", e.kind(), e.message())),
            };
            (at, out)
        });
        nuclei::time::sleep_until(t0 + Duration::from_millis(30_500)).await;
        open.store(true, Ordering::Relaxed);
        let r2 = d2.await;
        let r1 = d1.await;
        stop.store(true, Ordering::Relaxed);
        println!("c2: dial 1 (to a dead address, started at 0 s) ended at {:?}: {:?}", r1.0, r1.1);
        println!("c2: dial 2 (through the relay, started at 27 s, relay opens at 30.5 s) ended at {:?}: {:?}", r2.0, r2.1);
        assert!(r2.1.is_ok(), "dial 2 was ended by dial 1's failure: {r2:?}");
    })
    .await;
}

/// Control for c2: the relay path alone, opened 3.5 s after the dial, gives a working session.
#[nuclei::test]
async fn c2_control_the_relay_path_alone_connects() {
    vinc_common::within(60, async {
        let server = vinc_common::node().await;
        let s_addr = server.addr();
        let client = vinc_common::bind(
            vinc_common::builder()
                .alpn(vinc_common::ECHO)
                .connect_timeout(Duration::from_secs(40)),
        )
        .await;
        let (open, stop) = (Arc::new(AtomicBool::new(false)), Arc::new(AtomicBool::new(false)));
        let proxy = gate_proxy(s_addr.direct[0], Arc::clone(&open), Arc::clone(&stop));
        let t0 = Instant::now();
        let c2 = client.clone();
        let n2 = NodeAddr {
            node: s_addr.node,
            direct: vec![proxy],
            relays: vec![],
        };
        let d2 = nuclei::spawn_local(async move {
            let r = c2.connect(n2, vinc_common::ECHO).await;
            (t0.elapsed(), r.is_ok())
        });
        nuclei::time::sleep(Duration::from_millis(3_500)).await;
        open.store(true, Ordering::Relaxed);
        let r2 = d2.await;
        stop.store(true, Ordering::Relaxed);
        println!("c2 control: the relay dial alone ended at {:?}, ok = {}", r2.0, r2.1);
        assert!(r2.1);
    })
    .await;
}

// ------------------------------------------------------------------------------------------------ claim 3

/// `vinc-core/src/queue.rs:8`: an event the application cannot recover is not lost (the core holds work back
/// instead). The node empties the core's queue into its own bounded one every round, so the core never holds back.
#[test]
fn c3_the_node_queue_drops_an_unrecoverable_event_the_core_kept() {
    big(|| {
        let mut w = World::build(13, 1, 1);
        w.run(secs(20));
        let (hub, m) = (w.hubs[0].0, w.members[0]);
        let hid = w.id(hub);
        let sid = stats_list!(w.sim.node(m).node.endpoint())
            .into_iter()
            .find(|s| is_hub_with(s, &hid))
            .expect("the member holds a hub session")
            .session;
        let me = w.sim.node(m).me;
        let t = secs(20);
        let node = &mut w.sim.node_mut(m).node;
        // A host that reads no event for a while issues commands: each dial of itself queues one ConnectFailed.
        let mut refused = 0;
        for _ in 0..8_300 {
            let r = node.command(
                t,
                Command::Connect {
                    node: me,
                    alpn: b"t/app",
                    addrs: &[],
                    role: Role::Other,
                },
            );
            refused += u32::from(r == Err(CommandError::Refused));
        }
        // Then the hub session ends.
        let close = node.command(t, Command::Close { session: sid, error: 0 });
        for k in 1..=100u64 {
            node.handle_timeout(t + k * 100 * MS_NS);
        }
        let core = node.endpoint().node_stats();
        let (mut lost, mut failed, mut closed) = (0u32, 0u32, 0u32);
        while let Some(e) = node.poll_event() {
            match e {
                NodeEvent::Lost { count } => lost += count,
                NodeEvent::Endpoint(Event::ConnectFailed { .. }) => failed += 1,
                NodeEvent::Endpoint(Event::Closed { session, .. }) if session == sid => closed += 1,
                _ => {}
            }
        }
        let still = stats_list!(node.endpoint()).iter().any(|s| s.session == sid);
        println!(
            "c3: dials refused {refused}, close {close:?}, session still live {still}; node queue gave ConnectFailed \
             {failed}, Closed(hub session) {closed}, Lost {lost}; core events_dropped {} events_lost {}",
            core.events_dropped, core.events_lost
        );
        assert_eq!((core.events_dropped, core.events_lost), (0, 0));
        assert_eq!(closed, 1, "the Closed of the session was dropped by the node's queue (Lost {lost})");
    });
}

// ------------------------------------------------------------------------------------------------ claim 4

/// Fill the table of node `n` with dials to a peer that never answers; returns their sessions.
fn fill(net: &mut CoreNet, n: usize, peer: usize) -> Vec<vinc_core::SessionId> {
    let (node, nowhere) = (net.nodes[peer].node, SocketAddr::from(([10, 0, 0, 99], 4433)));
    let mut out = Vec::new();
    loop {
        let now = net.now;
        match net.nodes[n].connect(now, node, ALPN_A, nowhere, Role::Other) {
            Ok(r) => out.push(net.nodes[n].session(&r)),
            Err(e) => {
                assert_eq!(e, CommandError::Full);
                return out;
            }
        }
    }
}

/// `vinc-core/src/commands.rs:4`: "A command that fails changes nothing".
#[test]
fn c4_a_dial_refused_for_a_full_table_spends_the_ticket() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b, c) = (net.add(1), net.add(2), net.add(3));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(SEC_NS);
        assert!(net.nodes[a].saw(|e| matches!(e, Event::TicketsReceived { .. })));
        let now = net.now;
        net.nodes[a].cmd(now, Command::Close { session: sa, error: 0 }).unwrap();
        net.run_for(2 * SEC_NS);
        let fillers = fill(&mut net, a, c);
        let before = net.nodes[a].ep.tickets().len();
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let r = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).map(|r| r.value);
        let after = net.nodes[a].ep.tickets().len();
        // A slot comes free and the application dials again.
        let now = net.now;
        net.nodes[a]
            .cmd(now, Command::Close { session: fillers[0], error: 0 })
            .unwrap();
        net.run_for(2 * SEC_NS);
        let mark = net.nodes[a].events.len();
        let now = net.now;
        let again = net.nodes[a].connect(now, peer, ALPN_A, to, Role::Other).map(|r| r.value);
        net.run(net.now + 5 * SEC_NS, |n| {
            n.nodes[a].events[mark..].iter().any(|(_, e)| matches!(e, Event::Connected { .. }))
        });
        let resumed = net.nodes[a].events[mark..].iter().find_map(|(_, e)| match e {
            Event::Connected { resumed, .. } => Some(*resumed),
            _ => None,
        });
        println!(
            "c4: {} fillers; tickets before the refused dial {before}, refused dial {r:?}, tickets after {after}; \
             next dial {again:?} connected with resumed = {resumed:?}",
            fillers.len()
        );
        assert_eq!(r, Err(CommandError::Full));
        assert_eq!(after, before, "the dial refused with Full spent the ticket");
    });
}

// ------------------------------------------------------------------------------------------------ claim 6

/// An established pair where the server (ML-DSA identity) holds a ticket for the client; the client's second dial is
/// captured on the wire without reaching the server (as in `core_defense.rs`).
fn spoofable_resume() -> (CoreNet, usize, Vec<u8>) {
    let mut net = CoreNet::new(5 * MS_NS);
    let (s, c) = (net.add_with_alg(1, vinc_crypto::IdentityAlg::MlDsa65), net.add(2));
    let (sa, _) = net.connect_pair(c, s, ALPN_A, Role::Other);
    net.run_for(SEC_NS);
    let now = net.now;
    net.nodes[c].cmd(now, Command::Close { session: sa, error: 0 }).unwrap();
    net.run_for(SEC_NS);
    net.capture = true;
    let (peer, to, now) = (net.nodes[s].node, net.nodes[s].addr, net.now);
    net.loss = Some(Box::new(|_, _, _| true));
    net.nodes[c].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
    net.run_for(100 * MS_NS);
    net.loss = None;
    let hello = net.captured.first().cloned().unwrap().2;
    (net, s, hello)
}

fn ledger(net: &CoreNet, s: usize, x: SocketAddr) -> vinc_core::LedgerEntry {
    match net.nodes[s].ep.query(Query::Ledger(x)) {
        Answer::Ledger(e) => e,
        _ => panic!("no ledger entry"),
    }
}

/// `vinc-core/src/ledger.rs:3-4,9-10`: an address that wrote first is held to three times what it sent "until it
/// answers something we sent it", so "a spoofed source gets at most three times what it sent".
#[test]
fn c6a_one_junk_byte_from_a_spoofed_source_lifts_its_amplification_limit() {
    big_stack(|| {
        let (mut net, s, hello) = spoofable_resume();
        let x: SocketAddr = "10.9.9.9:1000".parse().unwrap();
        let to = net.nodes[s].addr;
        let rx = hello.len() as u64;
        net.inject(x, to, hello, 0);
        net.run_for(50 * MS_NS);
        let e1 = ledger(&net, s, x);
        // One byte from the same spoofed source: it parses as nothing and answers nothing.
        net.inject(x, to, vec![0u8; 1], 0);
        net.run_for(35 * SEC_NS);
        let e2 = ledger(&net, s, x);
        let sent: u64 = net.tapped.iter().filter(|t| t.2 == x).map(|t| t.3 as u64 + 28).sum();
        let n = net.tapped.iter().filter(|t| t.2 == x).count();
        println!(
            "c6a: after the Hello {e1:?}; after one junk byte and 35 s {e2:?}; {n} datagrams, {sent} bytes (with \
             headers) sent to the spoofed source for {} bytes received (3x = {})",
            rx + 1,
            3 * (rx + 1)
        );
        assert!(!e2.validated, "a junk byte validated the spoofed source");
        assert!(sent <= 3 * (rx + 1), "the spoofed source got {sent} bytes for {}", rx + 1);
    });
}

/// Mitigation check for c6a: with a full first Initial (the attacker's own dial from a spoofed source) the junk byte
/// validates the ledger entry too, but the connection's own amplification budget keeps the bytes within 3x.
#[test]
fn c6c_mitigation_after_a_full_initial_the_connection_budget_still_holds() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (s, c) = (net.add_with_alg(1, vinc_crypto::IdentityAlg::MlDsa65), net.add(2));
        net.capture = true;
        let (peer, to) = (net.nodes[s].node, net.nodes[s].addr);
        let caddr = net.nodes[c].addr;
        // Two first flights of the attacker's own dials, captured and never delivered.
        let mut flights = Vec::new();
        for _ in 0..2 {
            let mark = net.captured.len();
            net.loss = Some(Box::new(|_, _, _| true));
            let now = net.now;
            net.nodes[c].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
            net.pump_all();
            let flight: Vec<Vec<u8>> = net.captured[mark..]
                .iter()
                .filter(|(f, t, _)| *f == caddr && *t == to)
                .map(|(_, _, d)| d.clone())
                .collect();
            flights.push(flight);
            net.run_for(10 * MS_NS);
        }
        net.loss = None;
        let (x, y): (SocketAddr, SocketAddr) = ("10.9.9.8:1000".parse().unwrap(), "10.9.9.7:1000".parse().unwrap());
        let rx: u64 = flights[0].iter().map(|d| d.len() as u64).sum();
        for d in &flights[0] {
            net.inject(x, to, d.clone(), 0);
        }
        for d in &flights[1] {
            net.inject(y, to, d.clone(), 0);
        }
        // Wait for the server's first answer to x, then one junk byte from x.
        net.run(net.now + 3 * SEC_NS, |n| n.tapped.iter().any(|t| t.2 == x));
        let e1 = ledger(&net, s, x);
        net.inject(x, to, vec![0u8; 1], 0);
        net.run_for(35 * SEC_NS);
        let e2 = ledger(&net, s, x);
        let e3 = ledger(&net, s, y);
        let sent: u64 = net.tapped.iter().filter(|t| t.2 == x).map(|t| t.3 as u64 + 28).sum();
        let sent_y: u64 = net.tapped.iter().filter(|t| t.2 == y).map(|t| t.3 as u64 + 28).sum();
        println!(
            "c6c: first flight of {} datagrams, {rx} bytes; with junk: after the first answer {e1:?}, at the end {e2:?}, \
             sent {sent} bytes (3x of {} = {}); control without junk: {e3:?}, sent {sent_y} bytes",
            flights[0].len(),
            rx + 1,
            3 * (rx + 1)
        );
        // The ledger entry is validated by the junk byte here too, but the connection's own budget keeps the bytes.
        assert!(e2.validated && !e3.validated);
        assert!(sent <= 3 * (rx + 1), "the spoofed source got {sent} bytes for {}", rx + 1);
    });
}

/// `NodeStats::datagrams_out` is "Datagrams sent"; `tx.rs:80` counts a datagram before the ledger refuses it.
#[test]
fn c6b_datagrams_out_counts_what_the_ledger_held() {
    big_stack(|| {
        let (mut net, s, hello) = spoofable_resume();
        let x: SocketAddr = "10.9.9.9:1000".parse().unwrap();
        let to = net.nodes[s].addr;
        let st0 = net.nodes[s].ep.node_stats();
        let left0 = net.tapped.iter().filter(|t| t.1 == to).count() as u64;
        net.inject(x, to, hello, 0);
        net.run_for(5 * SEC_NS);
        let st1 = net.nodes[s].ep.node_stats();
        let left = net.tapped.iter().filter(|t| t.1 == to).count() as u64 - left0;
        let counted = st1.datagrams_out - st0.datagrams_out;
        let held = st1.held_by_ledger - st0.held_by_ledger;
        println!("c6b: datagrams that left {left}, datagrams_out grew by {counted}, held_by_ledger grew by {held}");
        assert!(held >= 1);
        assert_eq!(counted, left, "datagrams_out counted datagrams the ledger held back");
    });
}

// ------------------------------------------------------------------------------------------------ claim 8

/// `vinc-core/src/sub.rs:21-22`: an open "that finds no free slot is dropped without effect".
#[test]
fn c8_a_sub_open_refused_for_a_full_table_is_ignored_when_repeated() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b, c) = (net.add(1), net.add(2), net.add(3));
        let _ = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(SEC_NS);
        let fillers = fill(&mut net, b, c);
        let (aaddr, baddr, bnode) = (net.nodes[a].addr, net.nodes[b].addr, net.nodes[b].node);
        // Nothing from b reaches a: the packet that carried the open is never acknowledged, so a sends it again.
        net.loss = Some(Box::new(move |from, to, _| from == baddr && to == aaddr));
        let now = net.now;
        let rep = net.nodes[a].connect(now, bnode, ALPN_B, baddr, Role::Other).unwrap();
        let child = net.nodes[a].session(&rep);
        let Value::Stream(id) = net.nodes[a]
            .cmd(now, Command::OpenStream { session: child, bidi: false })
            .unwrap()
            .value
        else {
            panic!()
        };
        net.nodes[a]
            .cmd(now, Command::Write { session: child, stream: id, data: b"sub" })
            .unwrap();
        net.run_for(300 * MS_NS);
        let early = net.nodes[b].saw(|e| matches!(e, Event::Incoming { alpn, .. } if alpn.as_bytes() == ALPN_B));
        // A slot of b comes free while a still repeats the open.
        let now = net.now;
        net.nodes[b]
            .cmd(now, Command::Close { session: fillers[0], error: 0 })
            .unwrap();
        net.run_for(200 * MS_NS);
        let freed = net.nodes[b].ep.node_stats().sessions;
        let t_free = net.now;
        net.run_for(1500 * MS_NS);
        let repeats = net.tapped.iter().filter(|t| t.0 >= t_free && t.1 == aaddr && t.2 == baddr).count();
        net.loss = None;
        net.run_for(3 * SEC_NS);
        let late = net.nodes[b].saw(|e| matches!(e, Event::Incoming { alpn, .. } if alpn.as_bytes() == ALPN_B));
        println!(
            "c8: {} fillers; Incoming(ALPN_B) at b while full: {early}; b sessions after one closed: {freed}; a->b \
             datagrams after the slot came free: {repeats}; Incoming(ALPN_B) at b in the end: {late}",
            fillers.len()
        );
        assert!(late, "the repeated open was ignored: the refused open was remembered as seen");
    });
}

/// Control for c8: an open refused because its protocol is not registered (a refusal that marks nothing) is accepted
/// when a repeat arrives after the protocol was registered, so repeats do reach the acceptor in this setup.
#[test]
fn c8_control_a_repeat_is_accepted_when_the_first_refusal_marked_nothing() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let _ = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.run_for(SEC_NS);
        net.nodes[b].ep.unregister_alpn(ALPN_B);
        let (aaddr, baddr, bnode) = (net.nodes[a].addr, net.nodes[b].addr, net.nodes[b].node);
        net.loss = Some(Box::new(move |from, to, _| from == baddr && to == aaddr));
        let now = net.now;
        let rep = net.nodes[a].connect(now, bnode, ALPN_B, baddr, Role::Other).unwrap();
        let child = net.nodes[a].session(&rep);
        let Value::Stream(id) = net.nodes[a]
            .cmd(now, Command::OpenStream { session: child, bidi: false })
            .unwrap()
            .value
        else {
            panic!()
        };
        net.nodes[a]
            .cmd(now, Command::Write { session: child, stream: id, data: b"sub" })
            .unwrap();
        net.run_for(300 * MS_NS);
        let early = net.nodes[b].saw(|e| matches!(e, Event::Incoming { alpn, .. } if alpn.as_bytes() == ALPN_B));
        assert!(net.nodes[b].ep.register_alpn(ALPN_B));
        net.run_for(1700 * MS_NS);
        net.loss = None;
        net.run_for(3 * SEC_NS);
        let late = net.nodes[b].saw(|e| matches!(e, Event::Incoming { alpn, .. } if alpn.as_bytes() == ALPN_B));
        println!("c8 control: Incoming(ALPN_B) while unregistered: {early}; in the end: {late}");
        assert!(!early && late);
    });
}
