//! Trace generation for the size of the datagrams the connection builds: every call of `build_datagram` on either side
//! of a real exchange (through `trace_dgram_enable` and `trace_dgram_take`), recorded as ndjson (`dgram_size.ndjson`)
//! for the TLA+ trace check (`TraceDgramSize.tla`).
//!
//! A record carries the inputs of the call (the path's datagram size, the interface MTU and family, the caller's
//! buffer, the amplification room, the probe size, the size of a whole flight, the padding the handshake owed) and
//! what it wrote (the handshake fragment, the application packet, the padding and the length returned). Runs: a
//! resumed dial with early data behind a whole flight, a fresh dial for every interface MTU and family with the
//! flight split on and off and path MTU probes on, and seeded random runs.
//!
//! The test asserts, without the model: every exchange completes; a datagram is its parts; none exceeds the buffer or
//! the amplification room; without a probe a datagram with application data fits the path's size; and the runs show
//! data behind a whole flight, a probe above the path's size, a whole flight above it, a padding-only datagram and a
//! call that wrote nothing. The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise
//! nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::struct_excessive_bools
)]

use std::fmt::Write as _;

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::{DgramRecord, PathId, PathInfo};

/// One exchange: the client dials (resumed when `resumed`) and writes `len` bytes before the dial, the responder
/// answers with `len` bytes once the request is whole. Returns every call of `build_datagram` on both sides.
fn exchange(w: &mut World, resumed: bool, len: usize, delay: u64, info: (u16, bool), seed: u64) -> Vec<DgramRecord> {
    let ticket = resumed.then(|| {
        let mut tickets = first_session(w);
        tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap()
    });
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let a = w.client(&mut sa, ticket, pinc_security::ClientTickets::new());
    let b = w.server(&mut sb);
    let mut net = Net::new(a, b, Link::new(seed, Params::new(delay)), &mut w.stores);
    net.a.conn.set_path_info(
        PathId(1),
        PathInfo {
            interface_mtu: info.0,
            v6: info.1,
            ..PathInfo::default()
        },
    );
    net.a.conn.trace_dgram_enable();
    net.b.conn.trace_dgram_enable();
    // A full handshake knows the peer's stream limit only once the first flight is answered: open as soon as it is.
    let id = if let Ok(id) = net.a.conn.open_bi() {
        id
    } else {
        let mut opened = None;
        assert!(
            net.run(net.now + 10 * SEC, |n| {
                opened = n.a.conn.open_bi().ok();
                opened.is_some()
            }),
            "the client could not open a stream"
        );
        opened.unwrap()
    };
    if len > 0 {
        net.a.conn.write(id, &vec![1; len]).unwrap();
    }
    net.a.conn.finish(id).unwrap();
    let mut answered = false;
    let done = net.run(net.now + 20 * SEC, |n| {
        if !answered && n.b.fin.contains(&id) {
            if len > 0 {
                n.b.conn.write(id, &vec![2; len]).unwrap();
            }
            n.b.conn.finish(id).unwrap();
            answered = true;
        }
        n.a.fin.contains(&id)
    });
    assert!(done, "no answer: {:?}", net.rx_drops);
    let got = |n: &Node<'_>| n.read.get(&id).map_or(0, Vec::len);
    assert_eq!((got(&net.a), got(&net.b)), (len, len));
    let mut recs = net.a.conn.trace_dgram_take();
    recs.extend(net.b.conn.trace_dgram_take());
    recs
}

fn line(out: &mut String, r: &DgramRecord) {
    assert!(r.out <= 1 << 20, "a buffer above 2^20 bytes");
    writeln!(
        out,
        r#"{{"t":"dgram","p":{},"f":{},"v6":{},"o":{},"a":{},"q":{},"fl":{},"pad":{},"hs":{},"app":{},"pd":{},"len":{}}}"#,
        r.path_mtu,
        r.interface_mtu,
        u8::from(r.v6),
        r.out,
        r.amp,
        r.probe,
        r.flight,
        r.pad_owed,
        r.hs,
        r.app,
        r.pad,
        r.len
    )
    .unwrap();
}

#[derive(Default)]
struct Seen {
    behind: bool,
    probe_big: bool,
    whole_big: bool,
    pad_only: bool,
    empty: bool,
}

fn check(r: &DgramRecord, seen: &mut Seen) {
    let p = usize::from(r.path_mtu);
    assert!(
        r.len == 0 || r.len == r.hs + r.app + r.pad,
        "a datagram is not its parts: {r:?}"
    );
    assert!(
        r.len <= r.out.min(r.amp),
        "a datagram past its buffer or the amplification room: {r:?}"
    );
    assert!(
        r.probe > 0 || r.app == 0 || r.hs + r.app <= p,
        "an application packet past the path's size: {r:?}"
    );
    seen.behind |= r.flight > 0 && r.hs > 0 && r.app > 0;
    seen.probe_big |= r.probe > 0 && r.len > p;
    seen.whole_big |= r.len > p && r.probe == 0;
    seen.pad_only |= r.hs == 0 && r.app == 0 && r.pad > 0;
    seen.empty |= r.len == 0;
}

#[test]
fn dgram_size_traces() {
    let out = big_stack(|| {
        let mut out = String::new();
        let mut seen = Seen::default();
        let mut run = |recs: Vec<DgramRecord>, out: &mut String| {
            for r in &recs {
                check(r, &mut seen);
                line(out, r);
            }
        };
        for (i, len) in [0usize, 100, 1200, 4000].into_iter().enumerate() {
            let mut w = World::new(IdentityAlg::Ed25519);
            w.cfg.flight_split = true;
            w.cfg.probe_mtu = false;
            run(
                exchange(&mut w, true, len, 10 * MS, (1500, false), 7 + i as u64),
                &mut out,
            );
        }
        for (i, (mtu, v6, split)) in [1200u16, 1280, 1420, 1500, 9000]
            .into_iter()
            .flat_map(|m| {
                [false, true]
                    .into_iter()
                    .flat_map(move |v| [true, false].map(move |s| (m, v, s)))
            })
            .enumerate()
        {
            let mut w = World::new(IdentityAlg::Ed25519);
            w.cfg.flight_split = split;
            w.cfg.probe_mtu = true;
            run(
                exchange(&mut w, false, 4000, 10 * MS, (mtu, v6), 100 + i as u64),
                &mut out,
            );
        }
        for s in 0..32u64 {
            let mut rng = SplitMix64::new(s);
            let mtu = [1200u16, 1280, 1420, 1500, 9000][(rng.next_u64() % 5) as usize];
            let v6 = rng.next_u64() % 2 == 1;
            let mut w = World::new(IdentityAlg::Ed25519);
            w.cfg.flight_split = rng.next_u64() % 2 == 1;
            w.cfg.probe_mtu = rng.next_u64() % 2 == 1;
            let len = [0usize, 1, 30, 1088, 1303, 9000][(rng.next_u64() % 6) as usize];
            let delay = (1 + rng.next_u64() % 50) * MS;
            let resumed = rng.next_u64() % 2 == 1;
            run(exchange(&mut w, resumed, len, delay, (mtu, v6), 200 + s), &mut out);
        }
        assert!(seen.behind, "no data behind a whole flight");
        assert!(seen.probe_big, "no probe above the path's size");
        assert!(seen.whole_big, "no whole flight above the path's size");
        assert!(seen.pad_only, "no padding-only datagram");
        assert!(seen.empty, "no call that wrote nothing");
        out
    });
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("dgram_size.ndjson"), out).unwrap();
    }
}
