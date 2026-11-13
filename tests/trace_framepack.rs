//! Trace generation for the VINCER packet builder (`vinc-transport` `conn/send.rs`): the frames real connections
//! put into the packets they seal, and the two byte functions of the builder, recorded as ndjson for the TLA+ trace
//! check (`TraceFramePack.tla`) and the Lean replay (`Vinc/TraceFramePack.lean`).
//!
//! Pairs of real connections run on a simulated link: bulk transfers over several streams at several urgencies
//! with and without loss and with GSO (packets padded to the full size), datagrams and extension frames between
//! the stream data, request streams answered by the peer (the credit a stream gives back rides behind its data),
//! resets and stop requests, a second path (challenge, response and path PING), sleep and wake, a keepalive, key
//! rolls, the tickets and READY of a full handshake, a resumption whose client sends stream data in 0-RTT packets,
//! a lost tail (the probe timeout's packets), path MTU probes and the CLOSE packet. Each connection records, through
//! the `trace` view of the builder, every packet it seals: its header (short or 0-RTT), what it was built for, the
//! frames the fill wrote, the place of the last STREAM frame the fill kept, the least payload, and the payload as
//! sealed. `implicit_stream_len` and `put_stream_header` are also called directly, on the frames of real fills
//! and on seeded inputs: a frame that ends the payload, one followed by more bytes, one cut short, a place that is
//! not a frame, lengths at the varint edges, and buffers of the exact size, one byte off and empty.
//!
//! Two files are written: `framepack.ndjson` holds the events whose numbers stay below 2^28 (the TLA+ checker has
//! 32-bit integers), `framepack_wide.ndjson` every event, with stream ids, offsets and lengths up to `2^64 - 1`.
//!
//! The test checks every packet against a naive reading of the code, so it is meaningful without the proof tools:
//! the fill's frames parse with the real `FrameIter` with no error, none is PADDING or CLOSE (CLOSE only in the CLOSE
//! packet) and none leaves its length out; their kinds come in the builder's order; the place kept is the last
//! frame, a STREAM frame of a normal fill whose data runs to the end; the payload sealed is the frames padded to the
//! least payload, or the frames with the length of that STREAM frame dropped; and it parses into the frames written,
//! the last one without its length, then one PADDING frame for the padding.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::missing_panics_doc,
    clippy::fn_params_excessive_bools,
    unreachable_pub
)]

use std::collections::BTreeMap;

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::{CreditRecord, PackKind, PackMode, PackProbe, PackRecord, PathId, PathInfo};
use vinc_transport::frame::{Frame, FrameIter, MAX_STREAM_END, ext, stream_overhead};
use vinc_wire::{Reader, Writer, varint};

vinc_tests::install_counting_allocator!();

/// Numbers below this fit the TLA+ checker with room for its arithmetic.
const NARROW: u64 = 1 << 28;
const SENTINEL: u8 = 0xaa;

/// The place of the last STREAM frame a fill keeps, and the size of its header before the length.
type Hint = Option<(usize, usize)>;

#[derive(Default)]
struct Out {
    narrow: String,
    wide: String,
    events: usize,
    narrow_events: usize,
    /// How often each mode, header, finish and frame kind was seen.
    seen: BTreeMap<String, usize>,
    /// The fills of real packets, for the direct calls of `implicit_stream_len`.
    fills: Vec<(Vec<u8>, Hint)>,
}

impl Out {
    fn push(&mut self, narrow: bool, line: &str) {
        self.wide.push_str(line);
        self.wide.push('\n');
        self.events += 1;
        if narrow {
            self.narrow.push_str(line);
            self.narrow.push('\n');
            self.narrow_events += 1;
        }
    }

    fn see(&mut self, what: &str) {
        *self.seen.entry(what.to_string()).or_default() += 1;
    }
}

fn arr(b: &[u8]) -> String {
    let v: Vec<String> = b.iter().map(u8::to_string).collect();
    format!("[{}]", v.join(","))
}

/// The name the models give the kind of a frame.
fn kind(f: &Frame<'_>) -> &'static str {
    match f {
        Frame::Padding { .. } => "Padding",
        Frame::Ping => "Ping",
        Frame::Ack(_) => "Ack",
        Frame::ResetStream { .. } => "ResetStream",
        Frame::StopSending { .. } => "StopSending",
        Frame::Stream { .. } => "Stream",
        Frame::MaxStreamData { .. } => "MaxStreamData",
        Frame::MaxStreams { .. } => "MaxStreams",
        Frame::PathChallenge(_) => "PathChallenge",
        Frame::PathResponse(_) => "PathResponse",
        Frame::Close { .. } => "Close",
        Frame::Datagram { .. } => "Datagram",
        Frame::MtuProbeEcho { .. } => "MtuProbeEcho",
        Frame::Sleep => "Sleep",
        Frame::Wake => "Wake",
        Frame::Rekey(_) => "Rekey",
        Frame::Ready => "Ready",
        Frame::NewTickets(_) => "NewTickets",
        Frame::Extension { .. } => "Extension",
    }
}

const SC: &[&str] = &["MaxStreamData", "MaxStreams", "StopSending", "ResetStream"];

/// The slots of `fill_frames` for a mode, in the order it fills them: the kinds each slot writes and whether it
/// writes any number of frames (a loop) or at most one.
fn slots(mode: PackMode) -> Vec<(Vec<&'static str>, bool)> {
    let one = |k: &'static str| (vec![k], false);
    match mode {
        PackMode::Normal => vec![
            one("Ack"),
            one("Sleep"),
            one("Wake"),
            one("MtuProbeEcho"),
            one("Ready"),
            one("NewTickets"),
            one("Rekey"),
            (vec!["Extension"], true),
            (SC.to_vec(), true),
            one("PathResponse"),
            one("Ping"),
            one("PathChallenge"),
            (vec!["Stream"], true),
            (vec!["Datagram"], true),
            (SC.to_vec(), true),
            one("Ping"),
        ],
        PackMode::PingOnly => vec![one("Ack"), one("Wake"), one("Ping")],
        PackMode::Probe => vec![one("Ack"), one("Ping")],
        PackMode::Repair => vec![one("Ack"), (vec!["Stream"], true)],
        PackMode::Close => vec![one("Close")],
    }
}

/// Whether the kinds come in the order of the slots: each frame takes the first slot at or after the current one
/// that writes its kind, and a slot that writes at most one frame is then passed.
fn ordered(mode: PackMode, kinds: &[&str]) -> bool {
    let s = slots(mode);
    let mut at = 0;
    for k in kinds {
        let Some(j) = (at..s.len()).find(|j| s[*j].0.contains(k)) else {
            return false;
        };
        at = if s[j].1 { j } else { j + 1 };
    }
    true
}

fn mode_name(m: PackMode) -> &'static str {
    match m {
        PackMode::Normal => "normal",
        PackMode::PingOnly => "pingonly",
        PackMode::Probe => "probe",
        PackMode::Repair => "repair",
        PackMode::Close => "close",
    }
}

/// The frames of `b` with the offset each starts at and where it ends; `None` at the first error.
fn parse(b: &[u8]) -> Option<Vec<(usize, usize, Frame<'_>)>> {
    let mut r = Reader::new(b);
    let mut v = Vec::new();
    while !r.is_empty() {
        let at = b.len() - r.remaining();
        let f = Frame::decode(&mut r).ok()?;
        v.push((at, b.len() - r.remaining(), f));
    }
    Some(v)
}

/// Every number a decoder reads in the frame is below 2^28.
fn narrow_frame(f: &Frame<'_>) -> bool {
    let small = |v: &[u64]| v.iter().all(|x| *x < NARROW);
    match f {
        Frame::Ack(a) => small(&[a.largest()]),
        Frame::ResetStream { id, error, final_size } => small(&[*id, *error, *final_size]),
        Frame::StopSending { id, error } => small(&[*id, *error]),
        Frame::Stream { id, offset, data, .. } => small(&[*id, *offset, data.len() as u64]),
        Frame::MaxStreamData { id, max } => small(&[*id, *max]),
        Frame::MaxStreams { limit } => small(&[*limit]),
        Frame::Close { error } => small(&[*error]),
        Frame::Datagram { data, .. } => small(&[data.len() as u64]),
        Frame::Rekey(r) => small(&[r.switch_pn]),
        Frame::Extension { ty, body } => small(&[*ty, body.len() as u64]),
        _ => true,
    }
}

/// The tail of `build_packet`, read naively: the payload is padded to the least payload, or the length of the kept
/// STREAM frame is dropped (it ends the payload: otherwise the code would have given the packet up, and it would
/// not be recorded), or it is left as it is. The payload and what was done: the padding, or the bytes dropped.
fn finish(frames: &[u8], hint: Hint, min: usize) -> (Vec<u8>, usize, usize) {
    if frames.len() < min {
        let mut v = frames.to_vec();
        v.resize(min, 0);
        return (v, min - frames.len(), 0);
    }
    if let Some((at, head)) = hint.filter(|(at, head)| at + head <= frames.len()) {
        let (len, n) = varint::decode(&frames[at + head..]).expect("the kept STREAM frame has a length");
        assert_eq!(
            len as usize,
            frames.len() - (at + head + n),
            "the kept STREAM frame does not end the payload"
        );
        let mut v = frames[..at + head].to_vec();
        v[at] &= !0x02;
        v.extend_from_slice(&frames[at + head + n..]);
        return (v, 0, n);
    }
    (frames.to_vec(), 0, 0)
}

/// Check a sealed packet against the naive reading of the code and record it.
fn packet(out: &mut Out, r: &PackRecord) {
    let fs = parse(&r.frames).unwrap_or_else(|| panic!("the fill does not parse: {r:?}"));
    let kinds: Vec<&str> = fs.iter().map(|(_, _, f)| kind(f)).collect();
    assert!(!fs.is_empty(), "an empty packet was sealed: {r:?}");
    for (_, _, f) in &fs {
        assert!(!matches!(f, Frame::Padding { .. }), "the fill wrote PADDING: {kinds:?}");
        assert!(
            !matches!(
                f,
                Frame::Stream { implicit_len: true, .. } | Frame::Datagram { implicit_len: true, .. }
            ),
            "the fill left a length out: {kinds:?}"
        );
    }
    assert!(ordered(r.mode, &kinds), "out of order for {:?}: {kinds:?}", r.mode);
    if r.mode == PackMode::Close {
        assert!(matches!(kinds[..], ["Close"]), "the CLOSE packet carries {kinds:?}");
    } else {
        assert!(!kinds.contains(&"Close"), "CLOSE outside the CLOSE packet");
    }
    assert!(r.kind == PackKind::Short || r.client, "a server sealed a 0-RTT packet");
    // The place kept is the last frame, an explicit STREAM frame whose data runs to the end, exactly in a normal fill
    // that ends with a STREAM frame.
    let last = fs.last().unwrap();
    let want_hint = match (&last.2, r.mode) {
        (Frame::Stream { id, offset, data, .. }, PackMode::Normal) => Some((
            last.0,
            stream_overhead(*id, *offset, data.len(), false) - varint::encoded_len(data.len() as u64),
        )),
        _ => None,
    };
    assert_eq!(
        r.hint, want_hint,
        "the place kept is not the last STREAM frame: {kinds:?}"
    );
    let (pay, pad, dropped) = finish(&r.frames, r.hint, r.min_payload);
    assert_eq!(r.payload, pay, "the payload sealed is not the fill finished: {kinds:?}");
    assert!(r.payload.len() + r.pn_len >= 4, "no header-protection sample");
    // The payload reads back as the frames written, the last without its length, then the padding.
    let back = parse(&r.payload).expect("the payload does not parse");
    let mut want: Vec<Frame<'_>> = fs.iter().map(|(_, _, f)| f.clone()).collect();
    if dropped > 0 {
        let Some(Frame::Stream { implicit_len, .. }) = want.last_mut() else {
            panic!("dropped a length of no STREAM")
        };
        *implicit_len = true;
    }
    if pad > 0 {
        want.push(Frame::Padding { len: pad });
    }
    let got: Vec<Frame<'_>> = back.into_iter().map(|(_, _, f)| f).collect();
    assert_eq!(got, want, "the payload does not read back as the frames written");
    assert!(FrameIter::new(&r.payload).all(|f| f.is_ok()));
    // Record.
    out.see(mode_name(r.mode));
    out.see(if r.kind == PackKind::ZeroRtt { "0-RTT" } else { "1-RTT" });
    out.see(if pad > 0 {
        "padded"
    } else if dropped > 0 {
        "implicit"
    } else {
        "as written"
    });
    for k in &kinds {
        out.see(k);
    }
    if fs.len() > 1 && dropped > 0 {
        out.see("implicit behind other frames");
    }
    let narrow = fs.iter().all(|(_, _, f)| narrow_frame(f));
    let hint = r.hint.map_or("[]".to_string(), |(a, h)| format!("[{a},{h}]"));
    let line = format!(
        r#"{{"t":"txpk","op":"pkt","kind":"{}","mode":"{}","client":{},"pnl":{},"frames":{},"hint":{hint},"min":{},"pay":{}}}"#,
        if r.kind == PackKind::ZeroRtt { "zrtt" } else { "short" },
        mode_name(r.mode),
        r.client,
        r.pn_len,
        arr(&r.frames),
        r.min_payload,
        arr(&r.payload)
    );
    out.push(narrow, &line);
    if out.fills.len() < 400 && r.frames.len() <= 400 {
        out.fills.push((r.frames.clone(), r.hint));
    }
}

/// Take what both connections sealed.
fn take<const C: usize, const F: usize>(out: &mut Out, net: &mut Net<'_, '_, C, F>) {
    for r in net
        .a
        .conn
        .trace_pack_take()
        .iter()
        .chain(net.b.conn.trace_pack_take().iter())
    {
        packet(out, r);
    }
}

fn enable<const C: usize, const F: usize>(net: &mut Net<'_, '_, C, F>) {
    net.a.conn.trace_pack_enable();
    net.b.conn.trace_pack_enable();
}

// ---- the scenarios ----

/// Streams at several urgencies written with datagrams and extension frames between them, until all are read.
fn bulk(out: &mut Out, seed: u64, loss: f64, gso: usize, total: usize) {
    let mut w = World::new(IdentityAlg::Ed25519);
    w.cfg.max_gso = gso;
    if loss > 1.0 {
        // A small stream window, so the receiver grants credit often.
        w.cfg.credit = CreditRecord::new(32 * 1024, w.cfg.credit.max_streams, w.cfg.credit.max_datagram);
    }
    let (mut sa, mut sb) = (Store::with_chunks(true, 4096), Store::with_chunks(false, 4096));
    let mut net = setup(
        &mut w,
        &mut sa,
        &mut sb,
        Link::new(seed, Params::new(5 * MS).loss(loss)),
    );
    enable(&mut net);
    assert!(net.connect(net.now + 10 * SEC));
    let mut rng = SplitMix64::new(seed);
    let ids: Vec<u64> = (0..4).map(|_| net.a.conn.open_bi().unwrap()).collect();
    for (i, id) in ids.iter().enumerate() {
        net.a.conn.set_urgency(*id, [3, 1, 3, 6][i]).unwrap();
    }
    let data: Vec<Vec<u8>> = (0..4).map(|i| pattern(total / 4 + i * 777, seed + i as u64)).collect();
    let mut off = [0usize; 4];
    let mut fin = [false; 4];
    let mut ticks = 0u32;
    let done = net.run(net.now + 120 * SEC, |n| {
        ticks += 1;
        for i in 0..4 {
            while off[i] < data[i].len() {
                let end = (off[i] + 3000 + (rng.next_u64() % 9000) as usize).min(data[i].len());
                let k = n.a.conn.write(ids[i], &data[i][off[i]..end]).unwrap();
                if k == 0 {
                    break;
                }
                off[i] += k;
            }
            if off[i] == data[i].len() && !fin[i] {
                n.a.conn.finish(ids[i]).unwrap();
                fin[i] = true;
            }
        }
        if ticks.is_multiple_of(3) {
            let len = 1 + (rng.next_u64() % 300) as usize;
            let _ = n.a.conn.send_datagram(&pattern(len, u64::from(ticks)));
            let _ = n.b.conn.send_datagram(&pattern(len / 2 + 1, u64::from(ticks) + 1));
        }
        if ticks.is_multiple_of(7) {
            let _ = n.a.conn.send_extension(
                ext::TEST_FIRST + u64::from(ticks % 3),
                &pattern(1 + (ticks as usize % 90), 9),
            );
        }
        ids.iter().all(|id| n.b.fin.contains(id))
    });
    assert!(done, "the transfer did not finish");
    net.run(net.now + 2 * SEC, |_| false);
    take(out, &mut net);
}

/// Requests answered by the peer: the answer's last packet carries the credit the finished stream gives back.
fn requests(out: &mut Out, seed: u64, loss: f64) {
    let mut w = World::new(IdentityAlg::Ed25519);
    let (mut sa, mut sb) = (Store::with_chunks(true, 4096), Store::with_chunks(false, 4096));
    let mut net = setup(
        &mut w,
        &mut sa,
        &mut sb,
        Link::new(seed, Params::new(5 * MS).loss(loss)),
    );
    enable(&mut net);
    assert!(net.connect(net.now + 10 * SEC));
    let mut answered: BTreeMap<u64, usize> = BTreeMap::new();
    let mut opened = Vec::new();
    let mut k = 0u64;
    let done = net.run(net.now + 60 * SEC, |n| {
        while opened.len() < 40 && n.a.conn.open_ready(true).is_ok() {
            let id = n.a.conn.open_bi().unwrap();
            n.a.conn.write(id, &pattern(20 + (k as usize * 37) % 400, k)).unwrap();
            n.a.conn.finish(id).unwrap();
            opened.push(id);
            k += 1;
        }
        let ready: Vec<u64> = n.b.fin.iter().copied().collect();
        for id in ready {
            let ans = pattern(10 + (id as usize * 53) % 1500, id);
            let at = answered.entry(id).or_default();
            if *at < ans.len() {
                *at += n.b.conn.write(id, &ans[*at..]).unwrap();
                if *at == ans.len() {
                    n.b.conn.finish(id).unwrap();
                }
            }
        }
        opened.len() == 40 && opened.iter().all(|id| n.a.fin.contains(id))
    });
    assert!(done, "the requests were not all answered");
    // A stream reset and a stop request, each answered.
    let id = net.a.conn.open_bi().unwrap();
    net.a.conn.write(id, &pattern(5000, 1)).unwrap();
    net.run(net.now + 50 * MS, |_| false);
    net.a.conn.reset(id, 7).unwrap();
    let id2 = net.a.conn.open_bi().unwrap();
    net.a.conn.write(id2, b"stop me").unwrap();
    net.run(net.now + 50 * MS, |_| false);
    let _ = net.b.conn.stop_sending(id2, 9);
    net.run(net.now + SEC, |_| false);
    take(out, &mut net);
}

/// A second path, sleep and wake, a keepalive, READY, a key roll, a lost tail, then CLOSE.
fn life(out: &mut Out, seed: u64) {
    let mut w = World::new(IdentityAlg::Ed25519);
    w.cfg.key_update_after = 150;
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut link = Link::new(seed, Params::new(10 * MS));
    link.add_route(PathId(3), PathId(4), Params::new(10 * MS), Params::new(10 * MS));
    let mut net = setup(&mut w, &mut sa, &mut sb, link);
    enable(&mut net);
    assert!(net.connect(net.now + 10 * SEC));
    let now = net.now;
    net.a
        .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
        .unwrap();
    net.run(net.now + 2 * SEC, |n| n.a.conn.path_validated(PathId(3)));
    let _ = net.a.conn.ping_path(PathId(3));
    net.run(net.now + SEC, |_| false);
    net.a.conn.send_ready();
    let id = net.a.conn.open_bi().unwrap();
    for i in 0..200u64 {
        let _ = net.a.conn.write(id, &pattern(700, i));
        net.run(net.now + 2 * MS, |_| false);
    }
    net.run(net.now + SEC, |_| false);
    // Sleep and wake.
    let now = net.now;
    net.a.with_env(now, vinc_transport::conn::Connection::sleep);
    net.run(net.now + 3 * SEC, |_| false);
    let now = net.now;
    net.a.with_env(now, vinc_transport::conn::Connection::wake);
    net.run(net.now + 5 * SEC, |_| false);
    // A keepalive on an idle connection.
    net.a.conn.set_keepalive(Some(200 * MS));
    net.run(net.now + 2 * SEC, |_| false);
    net.a.conn.set_keepalive(None);
    // A lost tail: the probe timeout sends its PING.
    net.a.conn.write(id, &pattern(3000, 5)).unwrap();
    net.link.route(PathId(1)).ab.drop_next(6);
    net.link.route(PathId(3)).ab.drop_next(6);
    net.run(net.now + 5 * SEC, |_| false);
    net.a.conn.ping();
    net.run(net.now + SEC, |_| false);
    let now = net.now;
    net.b.with_env(now, |c, env| c.close(env, 3));
    net.run(net.now + SEC, |_| false);
    take(out, &mut net);
}

/// A full session that delivers tickets, then a resumption whose client sends stream data in 0-RTT packets.
fn resume(out: &mut Out, seed: u64) {
    let mut w = World::new(IdentityAlg::Ed25519);
    w.seed = seed as u8;
    let mut tickets = {
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, Params::new(10 * MS)));
        enable(&mut net);
        assert!(net.connect(net.now + 10 * SEC));
        assert!(
            net.run(net.now + 5 * SEC, |n| !n.a.tickets.is_empty()),
            "no tickets arrived"
        );
        take(out, &mut net);
        std::mem::take(&mut net.a.tickets)
    };
    let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let a = w.client(&mut sa, Some(ticket), vinc_security::ClientTickets::new());
    let b = w.server(&mut sb);
    let mut net = Net::new(a, b, Link::new(seed + 1, Params::new(10 * MS)), &mut w.stores);
    enable(&mut net);
    for i in 0..3u64 {
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, &pattern(200 + 2500 * i as usize, i)).unwrap();
        net.a.conn.finish(id).unwrap();
    }
    let _ = net.a.conn.send_datagram(b"early datagram");
    assert!(net.connect(net.now + 5 * SEC));
    net.run(net.now + SEC, |_| false);
    take(out, &mut net);
}

/// Bursts of one stream each on a lossy link, until the connection is old enough and the loss average high enough
/// for tail repairs (a packet that sends the stream frames of the last packet of a burst again).
fn repair(out: &mut Out, seed: u64) {
    let mut w = World::new(IdentityAlg::Ed25519);
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(
        &mut w,
        &mut sa,
        &mut sb,
        Link::new(seed, Params::new(10 * MS).loss(8.0)),
    );
    enable(&mut net);
    assert!(net.connect(net.now + 10 * SEC));
    for round in 0..300u64 {
        let data = pattern(if round % 2 == 0 { 3_000 } else { 100 }, round);
        let id = net.a.conn.open_uni().unwrap();
        net.a.conn.write(id, &data).unwrap();
        net.a.conn.finish(id).unwrap();
        assert!(net.run(net.now + 60 * SEC, |n| n.b.fin.contains(&id)), "round {round}");
        net.run(net.now + 30 * MS, |_| false);
        if net.a.conn.stats().repairs >= 8 {
            break;
        }
    }
    assert!(
        net.a.conn.stats().repairs > 0,
        "no tail repair: {:?}",
        net.a.conn.stats()
    );
    take(out, &mut net);
}

// ---- the byte functions ----

/// One call of `implicit_stream_len` on `b`, checked against a naive reading and recorded.
fn imp(out: &mut Out, b: &[u8], at: usize, head: usize) -> Option<usize> {
    let mut buf = b.to_vec();
    let r = PackProbe::implicit_stream_len(&mut buf, at, head);
    // The naive reading: the varint at `at + head` must give the bytes from its end to the end of `b`.
    let want = (at + head <= b.len())
        .then(|| varint::decode(&b[at + head..]).ok())
        .flatten()
        .filter(|(len, n)| *len as usize == b.len() - (at + head + n))
        .map(|(_, n)| n);
    assert_eq!(r, want, "implicit_stream_len at {at}+{head} of {b:?}");
    let got = if let Some(n) = r {
        let mut v = b[..at + head].to_vec();
        if head > 0 {
            v[at] &= !0x02;
        }
        v.extend_from_slice(&b[at + head + n..]);
        assert_eq!(&buf[..b.len() - n], &v[..], "the frames after dropping the length");
        v
    } else {
        assert_eq!(buf, b, "a refusal changed the frames");
        b.to_vec()
    };
    // TLC reads the varint with numbers below 2^28: at most four bytes of it, or a refusal within them.
    let narrow = at + head > b.len() || b[at + head..].iter().take(4).any(|x| *x < 0x80);
    out.see(if r.is_some() { "imp accepted" } else { "imp refused" });
    let line = format!(
        r#"{{"t":"txpk","op":"imp","b":{},"at":{at},"head":{head},"ok":{},"n":{},"out":{}}}"#,
        arr(b),
        r.is_some(),
        r.unwrap_or(0),
        arr(&got)
    );
    out.push(narrow, &line);
    r
}

/// One call of `put_stream_header` into a buffer of `cap` bytes, checked against `Frame::write` and recorded.
fn hdr(out: &mut Out, id: u64, offset: u64, len: usize, fin: bool, cap: usize) {
    let mut dst = vec![SENTINEL; cap];
    let ok = PackProbe::put_stream_header(&mut dst, id, offset, len, fin);
    // The naive reading: the header of the STREAM frame `write` gives, with its length, written in full when it fits
    // exactly; the varints that fit, in order, otherwise.
    let mut full = Vec::new();
    let flags = if offset == 0 { 0 } else { 4 } | 2 | u64::from(fin);
    let mut fits = true;
    for v in [
        Some(8 | flags),
        Some(id),
        (offset != 0).then_some(offset),
        Some(len as u64),
    ]
    .into_iter()
    .flatten()
    {
        let mut b = [0u8; 10];
        match varint::encode(v, &mut b) {
            Ok(n) if full.len() + n <= cap => full.extend_from_slice(&b[..n]),
            _ => {
                fits = false;
                break;
            }
        }
    }
    assert_eq!(
        ok,
        fits && full.len() == cap,
        "put_stream_header {id} {offset} {len} {fin} into {cap}"
    );
    assert_eq!(&dst[..full.len()], &full[..]);
    assert!(dst[full.len()..].iter().all(|x| *x == SENTINEL));
    // `put_stream_header` does not look at the stream end, which the stream layer keeps below 2^62.
    if ok && len < 64 && offset.saturating_add(len as u64) <= MAX_STREAM_END {
        let data = vec![7u8; len];
        let f = Frame::Stream {
            id,
            offset,
            fin,
            data: &data,
            implicit_len: false,
        };
        let mut b = vec![0u8; f.encoded_len()];
        f.write(&mut Writer::new(&mut b)).unwrap();
        assert_eq!(&b[..cap], &dst[..], "the header is not the one write gives");
        assert_eq!(cap, stream_overhead(id, offset, len, false));
    }
    out.see(if ok { "hdr written" } else { "hdr refused" });
    let narrow = id < NARROW && offset < NARROW && (len as u64) < NARROW;
    let line = format!(
        r#"{{"t":"txpk","op":"hdr","id":{id},"off":{offset},"len":{len},"fin":{fin},"cap":{cap},"ok":{ok},"b":{}}}"#,
        arr(&dst)
    );
    out.push(narrow, &line);
}

fn edge(rng: &mut SplitMix64, wide: bool) -> u64 {
    let j = rng.next_u64() % if wide { 64 } else { 28 };
    let base = 1u64 << j;
    match rng.next_u64() % 4 {
        0 => base - 1,
        1 => base,
        2 => base + 1,
        _ => rng.next_u64() % base.max(1),
    }
}

fn byte_functions(out: &mut Out) {
    let mut rng = SplitMix64::new(0x7061_636b);
    // The fills of real packets: the kept place, every other frame start, and the kept place one off.
    let fills = std::mem::take(&mut out.fills);
    for (frames, hint) in &fills {
        let starts: Vec<(usize, usize)> = parse(frames).unwrap().iter().map(|(a, e, _)| (*a, *e)).collect();
        if let Some((at, head)) = *hint {
            assert!(imp(out, frames, at, head).is_some(), "the kept place is refused");
            imp(out, frames, at, head + 1);
            imp(out, frames, at, head.saturating_sub(1));
            let mut cut = frames.clone();
            cut.pop();
            imp(out, &cut, at, head);
            let mut more = frames.clone();
            more.push(1);
            imp(out, &more, at, head);
        }
        if rng.next_u64().is_multiple_of(8) {
            for (a, _) in starts.iter().take(3) {
                imp(out, frames, *a, 1 + (rng.next_u64() % 3) as usize);
            }
        }
    }
    // Seeded frames: a STREAM frame with a length behind a prefix, then nothing, one byte, or cut.
    for _ in 0..3000 {
        let wide = rng.next_u64().is_multiple_of(4);
        let id = edge(&mut rng, wide) & ((1 << 62) - 1);
        let offset = if rng.next_u64().is_multiple_of(3) {
            0
        } else {
            edge(&mut rng, wide) & ((1 << 62) - 1)
        };
        let len = (rng.next_u64() % 300) as usize;
        let fin = rng.next_u64().is_multiple_of(2);
        let mut prefix = vec![0u8; (rng.next_u64() % 6) as usize];
        rng.fill(&mut prefix);
        let head = stream_overhead(id, offset, len, false) - varint::encoded_len(len as u64);
        let mut b = prefix.clone();
        let mut h = vec![0u8; head + varint::encoded_len(len as u64)];
        assert!(PackProbe::put_stream_header(&mut h, id, offset, len, fin));
        b.extend_from_slice(&h);
        b.extend((0..len).map(|i| (i * 31 % 256) as u8));
        match rng.next_u64() % 5 {
            0 => b.push((rng.next_u64() % 256) as u8),
            1 => {
                b.pop();
            }
            _ => {}
        }
        let at = prefix.len();
        match rng.next_u64() % 6 {
            0 => imp(out, &b, at, (rng.next_u64() % (b.len() as u64 + 2)) as usize),
            1 => imp(out, &b, (rng.next_u64() % (b.len() as u64 + 2)) as usize, head),
            _ => imp(out, &b, at, head),
        };
    }
    // Random bytes at random places, and the empty input.
    for _ in 0..1000 {
        let mut b = vec![0u8; (rng.next_u64() % 12) as usize];
        rng.fill(&mut b);
        let at = (rng.next_u64() % (b.len() as u64 + 2)) as usize;
        let head = (rng.next_u64() % 4) as usize;
        imp(out, &b, at, head);
    }
    imp(out, &[], 0, 0);
    // `put_stream_header` at the varint edges into buffers of the exact size, one byte off, and empty.
    for _ in 0..3000 {
        let wide = rng.next_u64().is_multiple_of(4);
        let id = edge(&mut rng, wide);
        let offset = if rng.next_u64().is_multiple_of(3) {
            0
        } else {
            edge(&mut rng, wide)
        };
        let len = edge(&mut rng, wide) as usize;
        let fin = rng.next_u64().is_multiple_of(2);
        let exact = stream_overhead(id, offset, len, false);
        let cap = match rng.next_u64() % 6 {
            0 => exact + 1,
            1 => exact.saturating_sub(1),
            2 => (rng.next_u64() % (exact as u64 + 1)) as usize,
            3 => 0,
            _ => exact,
        };
        hdr(out, id, offset, len, fin, cap);
    }
    for v in [(1u64 << 63) - 1, 1 << 63, u64::MAX] {
        hdr(out, v, 0, 3, false, 12);
        hdr(out, 1, v, 3, true, 12);
        hdr(out, 1, 0, v as usize, false, 12);
    }
}

#[test]
fn trace_framepack() {
    let out = big_stack(|| {
        let mut out = Out::default();
        bulk(&mut out, 11, 0.0, 1, 150_000);
        bulk(&mut out, 12, 2.0, 1, 150_000);
        bulk(&mut out, 13, 1.0, 4, 300_000);
        requests(&mut out, 21, 0.0);
        requests(&mut out, 22, 3.0);
        life(&mut out, 31);
        life(&mut out, 32);
        resume(&mut out, 41);
        resume(&mut out, 42);
        repair(&mut out, 14);
        byte_functions(&mut out);
        out
    });
    // Every mode, header, finish and frame kind of the builder was reached.
    for what in [
        "normal",
        "pingonly",
        "probe",
        "repair",
        "close",
        "0-RTT",
        "1-RTT",
        "padded",
        "implicit",
        "implicit behind other frames",
        "as written",
        "Ack",
        "Sleep",
        "Wake",
        "MtuProbeEcho",
        "Ready",
        "NewTickets",
        "Rekey",
        "Extension",
        "MaxStreamData",
        "MaxStreams",
        "StopSending",
        "ResetStream",
        "PathResponse",
        "Ping",
        "PathChallenge",
        "Stream",
        "Datagram",
        "Close",
        "imp accepted",
        "imp refused",
        "hdr written",
        "hdr refused",
    ] {
        assert!(
            out.seen.contains_key(what),
            "never reached: {what} (seen {:?})",
            out.seen
        );
    }
    println!(
        "trace_framepack: {} events, {} narrow; {:?}",
        out.events, out.narrow_events, out.seen
    );
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(format!("{dir}/framepack.ndjson"), &out.narrow).unwrap();
        std::fs::write(format!("{dir}/framepack_wide.ndjson"), &out.wide).unwrap();
    }
}
