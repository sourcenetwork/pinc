//! Trace generation for which frames go in which kind of packet: real connections of `pinc-transport` (built with
//! the `trace` and `inject` features), recorded as ndjson (`packet_kind.ndjson`) for the TLA+ trace check
//! (`TracePacketKind.tla`).
//!
//! Four kinds of event, each the frame kinds of one real packet in order. `early`: a 0-RTT packet sealed by a real
//! resuming dialing side with crafted frames in front of its own (`inject_frames`), handed to the resumed responder,
//! which refuses it whole (`Drop::EarlyFrame`, counted in `early_refused`) or applies it. `short`: the same frames in
//! a 1-RTT packet handed to an established responder, which never refuses it for its frames. `move`: a 1-RTT packet,
//! the highest numbered, on a validated direct path while the active path is a relayed one (through a node that
//! carries the relay role), and whether the active path moved to the packet's. `sent`: every packet a real dialing
//! side sealed in resumed sessions with early data and after it, with its kind.
//!
//! The test asserts by itself that a refusal is counted exactly when it happens, that a 1-RTT packet is never refused
//! for its frames, and that a 0-RTT packet a dialing side sealed holds none of the frames a receiver refuses there.
//! The trace is written to `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::items_after_statements,
    unreachable_pub
)]

use std::fmt::Write as _;

use pinc_crypto::IdentityAlg;
use pinc_security::{Rekey, TicketBatch, TicketEntry};
use pinc_tests::*;
use pinc_transport::conn::{Drop as RxDrop, PackKind, PathId, PathInfo};
use pinc_transport::frame::{Frame, FrameIter, write_ack};
use pinc_transport::packet::{LongHeader, LongType};
use pinc_transport::recovery::PathKind;
use pinc_wire::Writer;

/// The name of a frame in the model, an exhaustive match so that a new variant breaks the build until the model has it.
fn name(f: &Frame<'_>) -> &'static str {
    match f {
        Frame::Padding { .. } => "PADDING",
        Frame::Ping => "PING",
        Frame::Ack(_) => "ACK",
        Frame::ResetStream { .. } => "RESET_STREAM",
        Frame::StopSending { .. } => "STOP_SENDING",
        Frame::Stream { .. } => "STREAM",
        Frame::MaxStreamData { .. } => "MAX_STREAM_DATA",
        Frame::MaxStreams { .. } => "MAX_STREAMS",
        Frame::PathChallenge(_) => "PATH_CHALLENGE",
        Frame::PathResponse(_) => "PATH_RESPONSE",
        Frame::Close { .. } => "CLOSE",
        Frame::Datagram { .. } => "DATAGRAM",
        Frame::MtuProbeEcho { .. } => "MTU_ECHO",
        Frame::Sleep => "SLEEP",
        Frame::Wake => "WAKE",
        Frame::Rekey(_) => "REKEY",
        Frame::Ready => "READY",
        Frame::NewTickets(_) => "NEW_TICKETS",
        Frame::Extension { .. } => "EXTENSION",
    }
}

/// The names of the frames of `bytes`, in order.
fn kinds(bytes: &[u8]) -> Vec<&'static str> {
    FrameIter::new(bytes).map(|f| name(&f.unwrap())).collect()
}

fn names_json(names: &[&str]) -> String {
    let quoted: Vec<String> = names.iter().map(|n| format!("\"{n}\"")).collect();
    format!("[{}]", quoted.join(","))
}

fn encoded(frames: &[Frame<'_>]) -> Vec<u8> {
    let mut buf = vec![0u8; 1400];
    let mut w = Writer::new(&mut buf);
    for f in frames {
        f.write(&mut w).unwrap();
    }
    let n = w.written().len();
    buf.truncate(n);
    buf
}

/// The 19 frame names of the model, in the order of the specification.
const ALL: [&str; 19] = [
    "PADDING",
    "PING",
    "ACK",
    "RESET_STREAM",
    "STOP_SENDING",
    "STREAM",
    "MAX_STREAM_DATA",
    "MAX_STREAMS",
    "PATH_CHALLENGE",
    "PATH_RESPONSE",
    "CLOSE",
    "DATAGRAM",
    "MTU_ECHO",
    "SLEEP",
    "WAKE",
    "REKEY",
    "READY",
    "NEW_TICKETS",
    "EXTENSION",
];

/// The frames only an established session sends.
const EST: [&str; 5] = ["ACK", "CLOSE", "REKEY", "NEW_TICKETS", "PATH_RESPONSE"];

/// One frame of the kind `n`, encoded.
fn sample(n: &str) -> Vec<u8> {
    match n {
        "PADDING" => encoded(&[Frame::Padding { len: 3 }]),
        "PING" => encoded(&[Frame::Ping]),
        "ACK" => {
            let mut ack = vec![0u8; 16];
            let mut w = Writer::new(&mut ack);
            write_ack(&mut w, std::iter::once(0..=0)).unwrap();
            let len = w.written().len();
            ack.truncate(len);
            ack
        }
        "RESET_STREAM" => encoded(&[Frame::ResetStream {
            id: 8,
            error: 1,
            final_size: 0,
        }]),
        "STOP_SENDING" => encoded(&[Frame::StopSending { id: 12, error: 1 }]),
        "STREAM" => encoded(&[Frame::Stream {
            id: 4,
            offset: 0,
            fin: false,
            data: b"kind",
            implicit_len: false,
        }]),
        "MAX_STREAM_DATA" => encoded(&[Frame::MaxStreamData { id: 4, max: 1 << 20 }]),
        "MAX_STREAMS" => encoded(&[Frame::MaxStreams { limit: 100 }]),
        "PATH_CHALLENGE" => encoded(&[Frame::PathChallenge([7; 8])]),
        "PATH_RESPONSE" => encoded(&[Frame::PathResponse([1; 8])]),
        "CLOSE" => encoded(&[Frame::Close { error: 0 }]),
        "DATAGRAM" => encoded(&[Frame::Datagram {
            data: b"dgram",
            implicit_len: false,
        }]),
        "MTU_ECHO" => encoded(&[Frame::MtuProbeEcho { mtu: 1200 }]),
        "SLEEP" => encoded(&[Frame::Sleep]),
        "WAKE" => encoded(&[Frame::Wake]),
        "REKEY" => encoded(&[Frame::Rekey(Rekey {
            answer: false,
            share: [1; 32],
            echo: [0; pinc_security::keyroll::ECHO_LEN],
            switch_pn: 0,
        })]),
        "READY" => encoded(&[Frame::Ready]),
        "NEW_TICKETS" => {
            let mut tickets = TicketBatch::new();
            tickets.push(TicketEntry {
                tid: [3; 16],
                lifetime_s: 60,
            });
            encoded(&[Frame::NewTickets(tickets)])
        }
        "EXTENSION" => encoded(&[Frame::Extension { ty: 0x40, body: b"x" }]),
        other => panic!("no sample for {other}"),
    }
}

fn pair(a: &str, b: &str) -> Vec<u8> {
    let mut v = sample(a);
    v.extend(sample(b));
    v
}

/// A resumed dialing side and a resumed responder on a link, handed to `f`.
fn with_resumed<R>(seed: u64, f: impl FnOnce(&mut Net<'_, '_>) -> R) -> R {
    let mut world = World::new(IdentityAlg::Ed25519);
    let mut tickets = first_session(&mut world);
    let ticket = tickets.take(&world.rp.id.node_id(), ALPN, T0).unwrap();
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let dialer = world.client(&mut sa, Some(ticket), pinc_security::ClientTickets::new());
    let resumed = world.server(&mut sb);
    let mut net = Net::new(
        dialer,
        resumed,
        Link::new(seed, Params::new(10 * MS)),
        &mut world.stores,
    );
    f(&mut net)
}

/// Hand the responder of `net` one datagram.
fn give(net: &mut Net<'_, '_>, mut d: Vec<u8>) -> Result<(), RxDrop> {
    let now = net.now;
    let stores = &mut *net.stores;
    net.b
        .with_env(now, |c, env| c.handle_datagram_with(env, stores, PathId(2), &mut d))
}

/// A result as text for the `res` field, which the model ignores (no quote or backslash to escape).
fn res(result: &Result<(), RxDrop>) -> String {
    format!("{result:?}").replace(['"', '\\'], "'")
}

fn outcome(result: &Result<(), RxDrop>) -> &'static str {
    if matches!(result, Err(RxDrop::EarlyFrame)) {
        "refused"
    } else {
        "applied"
    }
}

/// The frames of the specification's frame sets that a refusal of the packet may come from for another reason.
fn has_own_handling(raw_names: &[&str]) -> bool {
    const OWN: [&str; 6] = [
        "CLOSE",
        "RESET_STREAM",
        "STOP_SENDING",
        "MAX_STREAM_DATA",
        "NEW_TICKETS",
        "REKEY",
    ];
    raw_names.iter().any(|n| OWN.contains(n))
}

/// A real 0-RTT packet of a resuming dialing side with the encoded frames `raw` in front of its own, handed to the
/// resumed responder after the Hello that raises its early keys.
fn early_event(out: &mut String, run: u32, raw: &[u8]) {
    let raw_names = kinds(raw);
    with_resumed(u64::from(run) + 700, |net| {
        net.a.conn.trace_pack_enable();
        net.a.conn.inject_frames(raw);
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, b"early bytes").unwrap();
        net.a.conn.finish(id).unwrap();
        let now = net.now;
        let mut buf = vec![0u8; 65_536];
        let len = net
            .a
            .with_env(now, |conn, env| conn.poll_transmit(env, &mut buf))
            .unwrap()
            .len;
        let dgram = &buf[..len];
        let (hs, hs_len) = LongHeader::parse(dgram).unwrap();
        assert_eq!(hs.ty, LongType::Handshake, "{raw_names:?}");
        let cut = hs_len + hs.body_len;
        let (zh, zh_len) = LongHeader::parse(&dgram[cut..]).unwrap();
        assert_eq!(zh.ty, LongType::ZeroRtt, "{raw_names:?}");
        assert_eq!(
            cut + zh_len + zh.body_len,
            len,
            "{raw_names:?}: the datagram is the Hello and one 0-RTT packet"
        );
        let (hello, zero) = (dgram[..cut].to_vec(), dgram[cut..].to_vec());
        let records = net.a.conn.trace_pack_take();
        let rec = records.iter().find(|r| r.kind == PackKind::ZeroRtt).unwrap();
        let frames = kinds(&rec.frames);
        assert_eq!(
            &frames[..raw_names.len()],
            &raw_names[..],
            "the injected frames come first"
        );
        give(net, hello).unwrap();
        let before = net.b.conn.stats().early_refused;
        let result = give(net, zero);
        let r = outcome(&result);
        let counted = net.b.conn.stats().early_refused - before;
        assert_eq!(counted, u64::from(r == "refused"), "{raw_names:?}: {result:?}");
        if !has_own_handling(&raw_names) {
            assert!(result.is_ok() || r == "refused", "{raw_names:?}: {result:?}");
        }
        let _ = writeln!(
            out,
            r#"{{"t":"pk","op":"early","frames":{},"r":"{r}","res":"{}"}}"#,
            names_json(&frames),
            res(&result)
        );
    });
}

/// The same frames in a 1-RTT packet handed to an established responder.
fn short_event(out: &mut String, k: u32, payload: &[u8]) {
    let mut w = World::new(IdentityAlg::Ed25519);
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(
        &mut w,
        &mut sa,
        &mut sb,
        Link::new(800 + u64::from(k), Params::new(10 * MS)),
    );
    assert!(net.connect(net.now + 10 * SEC));
    let id = net.b.conn.active_path().unwrap();
    let now = net.now;
    let result = net
        .b
        .with_env(now, |c, env| c.inject_payload(env, id, now, 1_000_000, payload));
    assert!(
        !matches!(result, Err(RxDrop::EarlyFrame)),
        "a 1-RTT packet was refused for its frames"
    );
    assert_eq!(net.b.conn.stats().early_refused, 0);
    let _ = writeln!(
        out,
        r#"{{"t":"pk","op":"short","frames":{},"r":"{}","res":"{}"}}"#,
        names_json(&kinds(payload)),
        outcome(&result),
        res(&result)
    );
}

/// 72 packets on a validated direct path while the active path is a relayed one.
fn move_events(out: &mut String) {
    const KINDS: [&str; 8] = [
        "PADDING",
        "PING",
        "MAX_STREAMS",
        "PATH_CHALLENGE",
        "PATH_RESPONSE",
        "STREAM",
        "DATAGRAM",
        "WAKE",
    ];
    let mut w = World::new(IdentityAlg::Ed25519);
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(900, Params::new(10 * MS)));
    assert!(net.connect(net.now + 10 * SEC));
    let d = net.b.conn.active_path().unwrap();
    let now = net.now;
    net.b
        .with_env(now, |c, env| {
            c.add_path(
                env,
                PathId(77),
                PathInfo {
                    kind: PathKind::Relay,
                    ..PathInfo::default()
                },
            )
        })
        .unwrap();
    let mut inputs: Vec<Vec<&str>> = KINDS.iter().map(|a| vec![*a]).collect();
    for a in KINDS {
        for b in KINDS {
            inputs.push(vec![a, b]);
        }
    }
    assert_eq!(inputs.len(), 72);
    let mut offset = 0u64;
    for (k, input) in inputs.iter().enumerate() {
        let mut payload = Vec::new();
        for n in input {
            if *n == "STREAM" {
                payload.extend(encoded(&[Frame::Stream {
                    id: 4,
                    offset,
                    fin: false,
                    data: b"kind",
                    implicit_len: false,
                }]));
                offset += 4;
            } else {
                payload.extend(sample(n));
            }
        }
        net.b.conn.set_active(PathId(77)).unwrap();
        let result = net.b.with_env(now, |c, env| {
            c.inject_payload(env, d, now, 1_000_000 + k as u64, &payload)
        });
        assert_eq!(result, Ok(()), "{input:?}");
        net.b.service(now);
        let moved = net.b.conn.active_path() == Some(d);
        let _ = writeln!(
            out,
            r#"{{"t":"pk","op":"move","frames":{},"moved":{moved}}}"#,
            names_json(&kinds(&payload))
        );
    }
}

/// Every packet a resumed dialing side sealed, with its kind.
fn sent_run(out: &mut String, k: u32) {
    with_resumed(1000 + u64::from(k), |net| {
        net.a.conn.trace_pack_enable();
        let id = net.a.conn.open_bi().unwrap();
        let data = pattern(100 * (k as usize + 1), u64::from(k));
        net.a.conn.write(id, &data).unwrap();
        net.a.conn.finish(id).unwrap();
        net.run(net.now + 3 * SEC, |_| false);
        assert!(net.a.conn.is_connected(), "run {k}: the session is not established");
        if k % 2 == 1 {
            let id = net.a.conn.open_bi().unwrap();
            net.a.conn.write(id, &pattern(2000, 77)).unwrap();
            net.a.conn.finish(id).unwrap();
            net.run(net.now + 2 * SEC, |_| false);
        }
        let (mut zrtt, mut short) = (0, 0);
        for rec in net.a.conn.trace_pack_take() {
            let frames = kinds(&rec.frames);
            let kind = match rec.kind {
                PackKind::ZeroRtt => {
                    zrtt += 1;
                    assert!(
                        !frames.iter().any(|n| EST.contains(n)),
                        "run {k}: a 0-RTT packet holds a frame the receiver refuses: {frames:?}"
                    );
                    "zrtt"
                }
                PackKind::Short => {
                    short += 1;
                    "short"
                }
            };
            let _ = writeln!(
                out,
                r#"{{"t":"pk","op":"sent","kind":"{kind}","frames":{}}}"#,
                names_json(&frames)
            );
        }
        assert!(
            zrtt >= 1 && short >= 1,
            "run {k}: {zrtt} 0-RTT and {short} 1-RTT packets"
        );
    });
}

#[test]
fn packet_kinds_match_the_model() {
    big_stack(|| {
        let mut out = String::new();
        let mut run = 0u32;
        let mut early_inputs: Vec<Vec<u8>> = ALL.iter().map(|n| sample(n)).collect();
        for e in EST {
            early_inputs.push(pair(e, "PING"));
            early_inputs.push(pair("PING", e));
        }
        assert_eq!(early_inputs.len(), 29);
        for raw in &early_inputs {
            early_event(&mut out, run, raw);
            run += 1;
        }
        let mut short_inputs: Vec<Vec<u8>> = ALL.iter().map(|n| sample(n)).collect();
        for e in EST {
            for x in [
                "PING",
                "STREAM",
                "DATAGRAM",
                "WAKE",
                "MAX_STREAMS",
                "PATH_CHALLENGE",
                "EXTENSION",
            ] {
                short_inputs.push(pair(e, x));
            }
        }
        assert_eq!(short_inputs.len(), 54);
        for (k, payload) in short_inputs.iter().enumerate() {
            short_event(&mut out, k as u32, payload);
        }
        move_events(&mut out);
        for k in 0..12u32 {
            sent_run(&mut out, k);
        }
        assert!(out.contains(r#""r":"refused""#) && out.contains(r#""r":"applied""#));
        assert!(out.contains(r#""moved":true"#) && out.contains(r#""moved":false"#));
        assert!(out.contains(r#""kind":"zrtt""#) && out.contains(r#""kind":"short""#));
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("packet_kind.ndjson"), &out).unwrap();
        }
    });
}
