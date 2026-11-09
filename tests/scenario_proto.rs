//! The application and the harness protocols in the scenario suite: framing, PUSHLOG, DOCSYNC, MANAGE and ECHO over an
//! in-memory byte pipe with arbitrary chunking and backpressure, the origin and integrity checks, the durable log
//! across lost connections and restarts, the tally of intents that wait for an absent layer, and the application's
//! accounting of broadcast, fetch and reconcile through a fake on-top layer.
#![allow(
    clippy::indexing_slicing,
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::decimal_bitwise_operands,
    clippy::assert_is_empty,
    clippy::collapsible_if,
    clippy::manual_range_contains,
    clippy::needless_pass_by_value,
    clippy::unreadable_literal,
    unreachable_pub,
    dead_code
)]

#[path = "scenario_proto/lone.rs"]
mod lone;
#[path = "scenario_proto/net.rs"]
mod net;
#[path = "scenario_proto/ontop.rs"]
mod ontop;

use std::collections::BTreeSet;

use net::{Net, allow, base_intent};
use vinc_sim::suite::crypto::PayloadKind;
use vinc_sim::suite::proto::body::render;
use vinc_sim::suite::proto::frame::{Frame, FrameError, Framer, T_ACK, T_ECHO, T_PUSH, hdr};
use vinc_sim::suite::proto::host::Layers;
use vinc_sim::suite::proto::{ALPN_DOCSYNC, ALPN_ECHO, ALPN_MANAGE, ALPN_PUSHLOG};
use vinc_sim::suite::rec::NS;
use vinc_sim::suite::world::model::IntentKind;

/// The chunkings every transfer test runs under: byte by byte, one large write, and two backpressured pipes.
const CONFIGS: [(usize, usize); 4] = [(1, usize::MAX), (4096, usize::MAX), (3, 20), (64, 100)];

fn violations(net: &Net) -> Vec<(String, String)> {
    net.rec
        .borrow()
        .violations
        .iter()
        .map(|v| (v.gate.clone(), v.msg.clone()))
        .collect()
}

fn push(net: &mut Net, from: usize, to: usize, size: u64) -> u32 {
    let mut d = base_intent(from, IntentKind::Push);
    d.to = Some(to);
    d.size = Some(size);
    net.intent(from, &d);
    net.rec.borrow().next_iid - 1
}

fn order(net: &Net, origin: usize, rep: usize) -> Vec<u64> {
    net.rec
        .borrow()
        .pushlog_order
        .get(&(origin, rep))
        .cloned()
        .unwrap_or_default()
}

fn unacked(net: &Net, node: usize, rep: usize) -> usize {
    net.nodes[node]
        .durable
        .borrow()
        .pl_out
        .get(&rep)
        .map_or(0, |o| o.unacked.len())
}

// ---------------------------------------------------------------------------------------------- framing

#[test]
fn framer_reassembles_frames_cut_anywhere() {
    let mut wire = Vec::new();
    wire.extend_from_slice(&hdr(T_PUSH, 5, 7));
    wire.extend_from_slice(b"hello");
    wire.extend_from_slice(&hdr(T_ACK, 0, 9));
    wire.extend_from_slice(&hdr(T_ECHO, 3, u64::MAX));
    wire.extend_from_slice(b"abc");
    let expect = vec![
        Frame {
            ty: T_PUSH,
            id: 7,
            body: Some(b"hello".to_vec()),
        },
        Frame {
            ty: T_ACK,
            id: 9,
            body: None,
        },
        Frame {
            ty: T_ECHO,
            id: u64::MAX,
            body: Some(b"abc".to_vec()),
        },
    ];
    for cut in 0..=wire.len() {
        let mut f = Framer::new();
        let mut out = Vec::new();
        f.feed(&wire[..cut], &mut out).unwrap();
        f.feed(&wire[cut..], &mut out).unwrap();
        assert_eq!(out, expect, "cut at {cut}");
    }
    let mut f = Framer::new();
    let mut out = Vec::new();
    for b in &wire {
        f.feed(std::slice::from_ref(b), &mut out).unwrap();
    }
    assert_eq!(out, expect);
}

#[test]
fn framer_refuses_bad_headers_and_keeps_earlier_frames() {
    let mut f = Framer::new();
    let mut out = Vec::new();
    let mut wire = hdr(T_ACK, 0, 1).to_vec();
    wire.extend_from_slice(&hdr(9, 0, 2));
    assert_eq!(f.feed(&wire, &mut out), Err(FrameError::UnknownType));
    assert_eq!(out.len(), 1);
    let mut out = Vec::new();
    assert_eq!(
        Framer::new().feed(&hdr(T_PUSH, 1 << 25, 0), &mut out),
        Err(FrameError::TooLarge)
    );
    let mut f = Framer::new();
    assert_eq!(f.feed(&hdr(T_ACK, 4, 0), &mut out), Err(FrameError::AckBody));
}

#[test]
fn framer_does_not_allocate_for_a_forged_length() {
    // a header that announces 16 MiB followed by 10 bytes holds 10 bytes, not 16 MiB
    let mut f = Framer::new();
    let mut out = Vec::new();
    let mut wire = hdr(T_PUSH, 1 << 24, 1).to_vec();
    wire.extend_from_slice(&[7u8; 10]);
    f.feed(&wire, &mut out).unwrap();
    assert!(out.is_empty());
    assert!(format!("{f:?}").len() < 600, "{f:?}");
}

// ---------------------------------------------------------------------------------------------- PUSHLOG

#[test]
fn push_is_delivered_once_in_order_across_drops_and_restarts() {
    for (chunk, cap) in CONFIGS {
        let mut net = Net::new(2, chunk, cap);
        allow(&net.rec, 1, 0);
        net.boot();

        let a = push(&mut net, 0, 1, 1000);
        net.run();
        assert_eq!(order(&net, 0, 1), [1], "{chunk}/{cap}");
        assert_eq!(unacked(&net, 0, 1), 0);

        // the connection is lost between two pushes
        net.kill_sessions();
        let b = push(&mut net, 0, 1, 1500);
        net.run();
        assert_eq!(order(&net, 0, 1), [1, 2]);

        // a push is written, then the connection dies before a byte of it arrives
        let c = push(&mut net, 0, 1, 2000);
        net.kill_sessions();
        assert_eq!(unacked(&net, 0, 1), 1);
        let t0 = net.now;
        assert_eq!(
            net.nodes[0].stack.poll_timeout(),
            Some(t0 + NS),
            "first retry after the 1 s backoff"
        );
        net.run();
        assert_eq!(order(&net, 0, 1), [1, 2, 3]);
        assert_eq!(unacked(&net, 0, 1), 0);

        // the node restarts with the push unacknowledged: the durable log survives, the retry is 100 ms after start
        let d = push(&mut net, 0, 1, 700);
        net.kill_sessions();
        net.restart(0);
        assert_eq!(net.nodes[0].stack.poll_timeout(), Some(net.now + 100_000_000));
        net.run();
        assert_eq!(order(&net, 0, 1), [1, 2, 3, 4]);

        // the replicator got a push but its acknowledgement was lost: the resend is acknowledged, not delivered again
        net.lose.insert(1);
        let e = push(&mut net, 0, 1, 900);
        net.run();
        assert_eq!(order(&net, 0, 1), [1, 2, 3, 4, 5]);
        assert_eq!(unacked(&net, 0, 1), 1);
        net.lose.clear();
        net.kill_sessions();
        net.run();
        assert_eq!(order(&net, 0, 1), [1, 2, 3, 4, 5], "no duplicate delivery");
        assert_eq!(unacked(&net, 0, 1), 0);
        assert_eq!(net.nodes[1].durable.borrow().pl_in[&0], 6);

        let rec = net.rec.borrow();
        for (iid, size) in [(a, 1000), (b, 1500), (c, 2000), (d, 700), (e, 900)] {
            let it = &rec.intents[&iid];
            assert_eq!(it.delivered.keys().copied().collect::<Vec<_>>(), [1], "intent {iid}");
            assert_eq!(it.size, size);
            assert_eq!(it.receivers, BTreeSet::from([1]));
        }
        assert_eq!(rec.app_bytes, 1000 + 1500 + 2000 + 700 + 900);
        drop(rec);
        assert_eq!(violations(&net), []);
        assert!(!net.nodes[0].stack.has_open_intents(net.now));
    }
}

#[test]
fn push_log_survives_a_restart_before_any_connection() {
    let mut net = Net::new(2, 1024, usize::MAX);
    allow(&net.rec, 1, 0);
    net.boot();
    let a = push(&mut net, 0, 1, 500);
    assert!(
        net.nodes[0].stack.has_open_intents(net.now),
        "an undelivered push is open"
    );
    net.restart(0);
    net.run();
    assert_eq!(order(&net, 0, 1), [1]);
    assert_eq!(net.rec.borrow().intents[&a].delivered.len(), 1);
}

#[test]
fn push_reconnect_backs_off_one_two_four_eight_seconds() {
    let mut net = Net::new(2, 1024, usize::MAX);
    net.boot();
    // node 5 does not exist: every dial fails, so every retry doubles the wait up to 8 s
    let mut d = base_intent(0, IntentKind::Push);
    d.to = Some(5);
    d.size = Some(100);
    net.intent(0, &d);
    net.advance(40 * NS);
    let times: Vec<u64> = net.dials.iter().map(|d| d.1).collect();
    let gaps: Vec<u64> = times.windows(2).map(|w| w[1] - w[0]).collect();
    // a dial is carried out one round (1 ms) after its timer fires
    let ms = 1_000_000;
    assert_eq!(gaps[..5], [NS + ms, 2 * NS + ms, 4 * NS + ms, 8 * NS + ms, 8 * NS + ms]);
    assert_eq!(
        unacked(&net, 0, 5),
        1,
        "the push stays in the log while the replicator is unreachable"
    );
}

// ---------------------------------------------------------------------------------------------- DOCSYNC / MANAGE

fn request(net: &mut Net, kind: IntentKind, from: usize, to: usize, req: Option<u64>, resp: Option<u64>) -> u32 {
    let mut d = base_intent(from, kind);
    d.to = Some(to);
    d.req = req;
    d.resp = resp;
    net.intent(from, &d);
    net.rec.borrow().next_iid - 1
}

#[test]
fn docsync_and_manage_round_trips_have_the_right_sizes() {
    for (chunk, cap) in CONFIGS {
        let mut net = Net::new(2, chunk, cap);
        allow(&net.rec, 0, 1);
        net.boot();

        // docsync: 120 B request, 2048 B response by default
        let a = request(&mut net, IntentKind::Docsync, 0, 1, None, None);
        net.run();
        assert_eq!(
            (net.nodes[0].host.written, net.nodes[1].host.written),
            (13 + 120, 13 + 2048),
            "{chunk}/{cap}"
        );
        {
            let rec = net.rec.borrow();
            let it = &rec.intents[&a];
            assert_eq!(it.size, 2048);
            assert_eq!(it.receivers, BTreeSet::from([1]));
            assert_eq!(
                it.delivered.keys().copied().collect::<Vec<_>>(),
                [1],
                "reported for the peer"
            );
            assert_eq!(rec.app_bytes, 2048 + 120);
        }

        // manage: 1024 B request by default; a second docsync reuses the cached connection
        let m = request(&mut net, IntentKind::Manage, 0, 1, None, None);
        net.run();
        assert_eq!(
            (net.nodes[0].host.written, net.nodes[1].host.written),
            (133 + 13 + 1024, 2061 + 13 + 2048)
        );
        let b = request(&mut net, IntentKind::Docsync, 0, 1, Some(50), Some(700));
        net.run();
        assert_eq!(
            (net.nodes[0].host.written, net.nodes[1].host.written),
            (133 + 1037 + 13 + 50, 2061 + 2061 + 13 + 700)
        );
        let docsync_dials = net.nodes[0]
            .host
            .connects
            .iter()
            .filter(|c| c.1 == ALPN_DOCSYNC)
            .count();
        assert_eq!(docsync_dials, 1, "the connection is cached per peer");
        {
            let rec = net.rec.borrow();
            for iid in [a, m, b] {
                assert_eq!(rec.intents[&iid].delivered.len(), 1);
            }
            assert_eq!(rec.intents[&b].size, 700);
        }
        assert_eq!(violations(&net), []);
    }
}

#[test]
fn a_request_whose_connection_dies_is_asked_again() {
    let mut net = Net::new(2, 16, usize::MAX);
    allow(&net.rec, 0, 1);
    net.boot();
    let a = request(&mut net, IntentKind::Docsync, 0, 1, None, None);
    net.rounds(40);
    assert!(
        net.rec.borrow().intents[&a].delivered.is_empty(),
        "the answer is still on its way"
    );
    net.kill_sessions();
    net.run();
    let rec = net.rec.borrow();
    assert_eq!(rec.intents[&a].delivered.len(), 1);
    assert_eq!(rec.app_bytes, 2048 + 120, "delivered once");
    drop(rec);
    assert_eq!(violations(&net), []);
}

#[test]
fn a_request_with_no_time_left_is_not_asked_again() {
    let mut net = Net::new(2, 16, usize::MAX);
    allow(&net.rec, 0, 1);
    net.boot();
    let mut d = base_intent(0, IntentKind::Docsync);
    d.to = Some(1);
    d.deadline_ns = 1_000_000;
    net.intent(0, &d);
    net.rounds(40);
    net.now += 10 * NS;
    net.kill_sessions();
    net.run();
    assert!(net.rec.borrow().intents[&1].delivered.is_empty());
    assert_eq!(net.nodes[0].host.connects.len(), 1);
}

#[test]
fn a_refused_dial_drops_the_waiting_requests() {
    let mut net = Net::new(2, 16, usize::MAX);
    net.boot();
    // node 9 does not exist: the dial fails, the request ends undelivered
    let a = request(&mut net, IntentKind::Docsync, 0, 9, None, None);
    net.run();
    assert!(net.rec.borrow().intents[&a].delivered.is_empty());
    assert!(net.nodes[0].stack.poll_timeout().is_none());
}

// ---------------------------------------------------------------------------------------------- ECHO

#[test]
fn echo_records_its_timeline_and_delivers_to_the_origin() {
    for (chunk, cap) in CONFIGS {
        let mut net = Net::new(2, chunk, cap);
        allow(&net.rec, 0, 1);
        net.boot();
        let mut d = base_intent(0, IntentKind::Echo);
        d.to = Some(1);
        d.probe = true;
        net.intent(0, &d);
        net.run();
        let rec = net.rec.borrow();
        let it = &rec.intents[&1];
        assert_eq!(it.size, 32);
        assert!(it.receivers.is_empty());
        assert!(it.meta.probe);
        assert_eq!(it.meta.to, Some(1));
        assert_eq!(it.delivered.keys().copied().collect::<Vec<_>>(), [0], "{chunk}/{cap}");
        let e = rec.echo[&1];
        let (c, w, s, done) = (
            e.connected.unwrap(),
            e.written.unwrap(),
            e.served.unwrap(),
            e.done.unwrap(),
        );
        assert!(c <= w && w < s && s < done, "{e:?}");
        assert_eq!(rec.app_bytes, 32);
        drop(rec);
        assert_eq!(violations(&net), []);
        // 13 B header + 32 B body each way, and the connection is closed by the client afterwards
        assert_eq!((net.nodes[0].host.written, net.nodes[1].host.written), (45, 45));
        assert!(net.nodes[0].host.peers.is_empty());
    }
}

#[test]
fn concurrent_echoes_to_one_peer_all_complete() {
    let mut net = Net::new(2, 5, 40);
    allow(&net.rec, 0, 1);
    net.boot();
    for _ in 0..3 {
        let mut d = base_intent(0, IntentKind::Echo);
        d.to = Some(1);
        net.intent(0, &d);
    }
    net.run();
    let rec = net.rec.borrow();
    for iid in 1..=3 {
        let e = rec.echo[&iid];
        assert!(e.connected.is_some() && e.written.is_some() && e.served.is_some() && e.done.is_some());
        assert_eq!(rec.intents[&iid].delivered.len(), 1);
    }
}

// ---------------------------------------------------------------------------------------------- misc

#[test]
fn the_four_harness_protocols_are_registered() {
    let net = Net::new(1, 1, 1);
    let a = net.nodes[0].stack.alpns();
    for p in [ALPN_PUSHLOG, ALPN_DOCSYNC, ALPN_MANAGE, ALPN_ECHO] {
        assert!(a.contains(&p));
    }
    assert_eq!(ALPN_PUSHLOG, b"/defra/pushlog/1");
    assert_eq!(ALPN_DOCSYNC, b"/defra/docsync/1");
    assert_eq!(ALPN_MANAGE, b"/defra/manage/1");
    assert_eq!(ALPN_ECHO, b"/echo/1");
    assert_eq!(a.len(), 4);
}

#[test]
fn open_intents_follow_topics_pushes_and_fetches() {
    let mut w = net::new_world(2);
    w.nodes[1].topics = vec![b"/col/0".to_vec()];
    let mut net = Net::with_world(w, 64, usize::MAX);
    allow(&net.rec, 1, 0);
    net.boot();
    assert!(!net.nodes[0].stack.has_open_intents(0));
    assert!(
        net.nodes[1].stack.has_open_intents(0),
        "a subscribed node wants a resume record"
    );
    push(&mut net, 0, 1, 300);
    assert!(net.nodes[0].stack.has_open_intents(0));
    net.run();
    assert!(!net.nodes[0].stack.has_open_intents(0));
}

#[test]
fn intents_for_absent_layers_are_tallied_not_dropped_and_not_recorded() {
    let mut net = Net::new(2, 64, usize::MAX);
    net.boot();
    let mut p = base_intent(0, IntentKind::Publish);
    p.topic = Some(b"/col/0".to_vec());
    p.size = Some(200);
    let mut f = base_intent(0, IntentKind::Fetch);
    f.value = Some("v".to_owned());
    f.providers = vec![1];
    let mut r = base_intent(0, IntentKind::Reconcile);
    r.to = Some(1);
    r.set_ref = Some(b"/col/0".to_vec());
    net.intent(0, &p);
    net.intent(0, &p);
    net.intent(0, &f);
    net.intent(0, &r);
    let w = &net.nodes[0].stack.waiting;
    assert_eq!(w.get("publish"), Some(&2));
    assert_eq!(w.get("fetch"), Some(&1));
    assert_eq!(w.get("reconcile"), Some(&1));
    assert_eq!(w.len(), 3);
    assert!(
        net.rec.borrow().intents.is_empty(),
        "nothing recorded for work that cannot run"
    );
    assert!(net.nodes[0].host.connects.is_empty());
    // a kind that does not wait is recorded
    push(&mut net, 0, 1, 100);
    assert_eq!(net.rec.borrow().intents.len(), 1);
    assert_eq!(net.nodes[0].stack.waiting.len(), 3);
}

// ---------------------------------------------------------------------------------------------- the helpers' own check

#[test]
fn a_message_names_its_creator() {
    let net = Net::new(3, 1, 1);
    let m = net.reg.new_msg(2, PayloadKind::Msg, 100);
    let bytes = render(net.reg, m, 100);
    assert_eq!(vinc_sim::suite::proto::body::message_id(&bytes), Some(m));
    assert_eq!(net.reg.creator_of(m), Some(2));
}
