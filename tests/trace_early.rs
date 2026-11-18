//! Trace generation for the buffer of packets that arrive before their keys: seeded runs of the real buffer and of
//! real connections (`pinc-transport`, built with the `trace` feature), recorded as ndjson (`early.ndjson`) for the
//! TLA+ trace check (`TraceEarly.tla`) and the Lean replay (`Pinc/TraceEarly.lean`).
//!
//! Two kinds of event. `txea` is the buffer itself (`EarlyData`, through `EarlyProbe`): pushes of packets of many
//! sizes into pools of one to eight chunks, pops and clears, against a naive list of what it should hold (at most 8,
//! oldest first, a refused packet is the new one, none refused while a chunk is free). `txeb` is a real connection in
//! its handshake: a client and a server are connected through a [`Net`], and before the session is established
//! junk 0-RTT and 1-RTT packets are handed to one side (more than the buffer holds), the session is established, more
//! junk arrives, and the connection is closed and gets some more; or a resumed server is handed the first datagram of
//! a client with a ticket split in two, the Hello alone (`hello`: it raises the early keys and establishes the
//! session) and then the client's first 0-RTT packet alone, carrying ACK, CLOSE, REKEY, `NEW_TICKETS` or
//! `PATH_RESPONSE` (refused) or only the frames a client sends there (applied). The connection shows what it holds,
//! its phase and its keys through the `trace` feature (`early_view`), and its counters through `stats()`.
//!
//! The test asserts the rules itself, against a naive rule for each packet (held, refused as full, refused for want
//! of keys, refused for a frame only an established session sends, or refused because the connection is over; the
//! bytes counted on arrival whichever it is, a refusal for a frame changing nothing else and applying none of the
//! packet, and nothing held once the connection is up or closed), so it is meaningful without the proof tools. The
//! trace is written to `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::large_stack_arrays,
    unreachable_pub
)]

use std::cell::RefCell;
use std::fmt::Write as _;
use std::rc::Rc;

use pinc_crypto::IdentityAlg;
use pinc_security::{Rekey, TicketBatch, TicketEntry};
use pinc_tests::*;
use pinc_transport::conn::{Drop as RxDrop, PathId};
use pinc_transport::frame::{Frame, write_ack};
use pinc_transport::packet::{LongHeader, LongType, PN_LEN_BASE};
use pinc_transport::stream::pool::CHUNK_SIZE;
use pinc_transport::stream::trace::EarlyProbe;
use pinc_wire::Writer;

pinc_tests::install_counting_allocator!();

// ---- the buffer itself ----

fn probe_view(p: &EarlyProbe, front: Option<&[u8]>) -> String {
    let f = front.map_or(-1, |b| i64::from_le_bytes(b[..8].try_into().unwrap()));
    format!(r#"{{"n":{},"nd":{},"front":{f}}}"#, p.len(), p.dropped())
}

fn packet(id: u64, size: usize) -> Vec<u8> {
    let mut b = vec![0u8; size.max(8)];
    b[..8].copy_from_slice(&id.to_le_bytes());
    for (i, x) in b.iter_mut().enumerate().skip(8) {
        *x = (id as u8).wrapping_add(i as u8);
    }
    b
}

fn buffer_run(rng: &mut SplitMix64, out: &mut String, run: u32) {
    let chunks = [8usize, 8, 3, 2, 1][run as usize % 5];
    let regime = (run / 5) % 3;
    let mut p = EarlyProbe::new(chunks);
    let cap = EarlyProbe::MAX;
    let mut held: Vec<Vec<u8>> = Vec::new();
    let mut refused = 0u64;
    let mut next = 1u64;
    let _ = writeln!(
        out,
        r#"{{"t":"txea","run":{run},"op":"init","cap":{cap},"v":{}}}"#,
        probe_view(&p, None)
    );
    for _ in 0..90 {
        match rng.next_u64() % 20 {
            0..=11 => {
                let size = match regime {
                    0 => 20 + (rng.next_u64() % 1400) as usize,
                    1 => 9000,
                    _ => [16, 700, 8192, 8193, CHUNK_SIZE, CHUNK_SIZE + 1][(rng.next_u64() % 6) as usize],
                };
                let id = next;
                next += 1;
                let pkt = packet(id, size);
                let was = held.len();
                let used = p.used_chunks();
                let ok = p.push(&pkt);
                if was >= cap {
                    assert!(!ok, "a full buffer kept a packet");
                } else if pkt.len() > CHUNK_SIZE {
                    assert!(!ok, "a packet larger than a chunk was kept");
                } else if used < chunks {
                    assert!(
                        ok,
                        "a packet was refused while the pool had a chunk and the buffer a place"
                    );
                }
                if ok {
                    held.push(pkt.clone());
                } else {
                    refused += 1;
                    if was < cap && pkt.len() <= CHUNK_SIZE {
                        assert_eq!(used, chunks, "refused for want of room with a chunk free");
                    }
                }
                assert_eq!(p.dropped(), refused);
                // the pool had room unless the real push refused a packet that the buffer had a place for
                let room = ok || was >= cap;
                let _ = writeln!(
                    out,
                    r#"{{"t":"txea","run":{run},"op":"push","id":{id},"size":{},"room":{room},"ok":{ok},"v":{}}}"#,
                    pkt.len(),
                    probe_view(&p, p.front().as_deref())
                );
            }
            12..=18 => {
                // the oldest packet comes out, as stored
                let f = p.front();
                assert_eq!(
                    f.as_deref(),
                    held.first().map(Vec::as_slice),
                    "the oldest packet is not the first kept"
                );
                p.pop();
                if !held.is_empty() {
                    held.remove(0);
                }
                let _ = writeln!(
                    out,
                    r#"{{"t":"txea","run":{run},"op":"pop","v":{}}}"#,
                    probe_view(&p, p.front().as_deref())
                );
            }
            _ => {
                p.clear();
                held.clear();
                let _ = writeln!(
                    out,
                    r#"{{"t":"txea","run":{run},"op":"clear","v":{}}}"#,
                    probe_view(&p, p.front().as_deref())
                );
            }
        }
        assert_eq!(p.len(), held.len());
        assert_eq!(p.front().as_deref(), held.first().map(Vec::as_slice));
        if p.is_empty() {
            assert_eq!(p.used_chunks(), 0, "an empty buffer holds a chunk");
        }
    }
}

// ---- a real connection ----

struct Ids {
    a: Option<pinc_security::ConnId>,
    b: Option<pinc_security::ConnId>,
}

fn dgram(rng: &mut SplitMix64, zero: bool, cid: pinc_security::ConnId, other: pinc_security::ConnId) -> Vec<u8> {
    let dlen = 60 + (rng.next_u64() % 900) as usize;
    if zero {
        let body = dlen - 30;
        let h = LongHeader {
            ty: LongType::ZeroRtt,
            dcid: cid,
            scid: other,
            body_len: body,
        };
        let mut buf = vec![0u8; 2048];
        let mut w = Writer::new(&mut buf);
        h.write(&mut w, PN_LEN_BASE).unwrap();
        let mut d = w.written().to_vec();
        let mut junk = vec![0u8; body];
        rng.fill(&mut junk);
        d.extend_from_slice(&junk);
        d
    } else {
        let mut d = vec![0x40u8];
        d.extend_from_slice(cid.as_bytes());
        let mut junk = vec![0u8; dlen - 1 - cid.as_bytes().len()];
        rng.fill(&mut junk);
        d.extend_from_slice(&junk);
        d
    }
}

#[derive(Clone, Copy, Debug)]
struct Snap {
    ph: u8,
    er: bool,
    rv: bool,
    n: usize,
    nb: u64,
    nd: u64,
    nu: u64,
    nr: u64,
    rx: u64,
}

impl Snap {
    fn of(v: pinc_transport::conn::EarlyView, s: &pinc_transport::conn::Stats) -> Self {
        Self {
            ph: v.phase,
            er: v.early_keys,
            rv: v.recv_keys,
            n: v.held,
            nb: s.early_buffered,
            nd: s.early_dropped,
            nu: s.undecryptable,
            nr: s.early_refused,
            rx: s.bytes_received,
        }
    }

    fn json(&self) -> String {
        format!(
            r#"{{"ph":{},"er":{},"rv":{},"n":{},"nb":{},"nd":{},"nu":{},"nr":{},"rx":{}}}"#,
            self.ph, self.er, self.rv, self.n, self.nb, self.nd, self.nu, self.nr, self.rx
        )
    }
}

/// One side of the pair, and what it takes: handing it a datagram.
struct Side<'n, 'a, 'b> {
    net: &'n mut Net<'a, 'b>,
    client: bool,
}

impl Side<'_, '_, '_> {
    fn snap(&self) -> Snap {
        let c = if self.client {
            &self.net.a.conn
        } else {
            &self.net.b.conn
        };
        Snap::of(c.early_view(), &c.stats())
    }

    fn give(&mut self, mut d: Vec<u8>) -> Result<(), RxDrop> {
        let now = self.net.now;
        if self.client {
            self.net
                .a
                .with_lent(now, |c, env, l| c.handle_datagram(env, l, PathId(1), &mut d))
        } else {
            let stores = &mut *self.net.stores;
            self.net.b.with_lent(now, |c, env, l| {
                c.handle_datagram_with(env, l, stores, PathId(2), &mut d)
            })
        }
    }
}

struct Rec<'o> {
    out: &'o mut String,
    run: u32,
    last: Snap,
    held_shorts: u64,
}

/// Hand one junk packet, check the outcome against the naive rule, and record it.
fn inject(
    side: &mut Side<'_, '_, '_>,
    rec: &mut Rec<'_>,
    rng: &mut SplitMix64,
    zero: bool,
    cid: pinc_security::ConnId,
) {
    let before = side.snap();
    let d = dgram(rng, zero, cid, cid);
    let dlen = d.len() as u64;
    let r = side.give(d);
    let after = side.snap();
    let out = match r {
        Ok(()) => "ok",
        Err(RxDrop::Buffered) => "held",
        Err(RxDrop::Undecryptable) if after.nd == before.nd + 1 => "full",
        Err(RxDrop::Undecryptable) => "undec",
        Err(RxDrop::Closed) => "closed",
        Err(e) => panic!("unexpected {e:?}"),
    };
    // the naive rule
    let hold = before.ph == 0 && if zero { !side.client && !before.er } else { !before.rv };
    let expect = if before.ph >= 2 {
        "closed"
    } else if hold {
        if before.n < 8 { "held" } else { "full" }
    } else {
        "undec"
    };
    assert_eq!(out, expect, "before {before:?}, zero {zero}, client {}", side.client);
    assert_eq!(
        after.rx,
        before.rx + if before.ph >= 2 { 0 } else { dlen },
        "a datagram counts on arrival"
    );
    assert_eq!(after.n, before.n + usize::from(out == "held"));
    assert_eq!(after.nb, before.nb + u64::from(out == "held"));
    assert_eq!(after.nd, before.nd + u64::from(out == "full"));
    let failed_short = before.ph == 1 && !zero;
    assert_eq!(
        after.nu,
        before.nu + u64::from(failed_short),
        "a failed 1-RTT packet is counted, a 0-RTT one is not"
    );
    assert_eq!(after.nr, before.nr, "junk is never refused for its frames");
    if out == "held" && !zero {
        rec.held_shorts += 1;
    }
    let _ = writeln!(
        rec.out,
        r#"{{"t":"txeb","run":{},"op":"rx","kind":"{}","fate":"fail","dlen":{dlen},"out":"{out}","v":{}}}"#,
        rec.run,
        if zero { "z" } else { "s" },
        after.json()
    );
    rec.last = after;
}

fn conn_run(rng: &mut SplitMix64, out: &mut String, run: u32, client: bool) {
    let mut w = World::new(IdentityAlg::Ed25519);
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(
        &mut w,
        &mut sa,
        &mut sb,
        Link::new(u64::from(run) + 300, Params::new(10 * MS)),
    );
    let ids = Rc::new(RefCell::new(Ids { a: None, b: None }));
    let ids2 = ids.clone();
    net.on_tx = Some(Box::new(move |is_a, d, _| {
        if let Ok((h, _)) = LongHeader::parse(d) {
            let mut i = ids2.borrow_mut();
            let slot = if is_a { &mut i.a } else { &mut i.b };
            slot.get_or_insert(h.scid);
        }
    }));
    // the server has answered the Hello and the client has not heard it yet; or the client has sent its Hello
    net.run(net.now + if client { MS } else { 15 * MS }, |_| false);
    let cid = if client {
        ids.borrow().a.unwrap()
    } else {
        ids.borrow().b.unwrap()
    };
    let mut side = Side { net: &mut net, client };
    let first = side.snap();
    assert_eq!(first.ph, 0, "the handshake is still going");
    let mut rec = Rec {
        out,
        run,
        last: first,
        held_shorts: 0,
    };
    let _ = writeln!(
        rec.out,
        r#"{{"t":"txeb","run":{run},"op":"init","client":{client},"cap":8,"v":{}}}"#,
        first.json()
    );
    let before_est = [0, 3, 8, 9, 12, 14, (rng.next_u64() % 15) as usize][run as usize % 7];
    for _ in 0..before_est {
        let zero = rng.next_u64().is_multiple_of(3);
        inject(&mut side, &mut rec, rng, zero, cid);
    }
    // establish the session: what is held is tried, once each, and none is left
    let up = side.net.run(side.net.now + 30 * SEC, |n| {
        if client {
            n.a.conn.is_connected()
        } else {
            n.b.conn.is_connected()
        }
    });
    assert!(up, "the handshake did not finish");
    let after = side.snap();
    assert_eq!((after.ph, after.n, after.rv), (1, 0, true));
    assert_eq!(
        (after.nb, after.nd, after.nr),
        (rec.last.nb, rec.last.nd, rec.last.nr),
        "establishing counts no hold and refuses no junk"
    );
    assert_eq!(
        after.nu,
        rec.last.nu + rec.held_shorts,
        "the 1-RTT packets held fail and are counted, the 0-RTT ones are not"
    );
    let real = after.rx - rec.last.rx;
    let _ = writeln!(
        rec.out,
        r#"{{"t":"txeb","run":{run},"op":"est","real":{real},"v":{}}}"#,
        after.json()
    );
    rec.last = after;
    for _ in 0..(rng.next_u64() % 5) {
        let zero = rng.next_u64().is_multiple_of(2);
        inject(&mut side, &mut rec, rng, zero, cid);
    }
    if rng.next_u64().is_multiple_of(2) {
        let now = side.net.now;
        if client {
            side.net.a.with_lent(now, |c, env, l| c.close(env, l, 0));
        } else {
            side.net.b.with_lent(now, |c, env, l| c.close(env, l, 0));
        }
        let after = side.snap();
        assert!(after.ph >= 2 && after.n == 0);
        let _ = writeln!(
            rec.out,
            r#"{{"t":"txeb","run":{run},"op":"close","v":{}}}"#,
            after.json()
        );
        rec.last = after;
        for _ in 0..(rng.next_u64() % 3) {
            let zero = rng.next_u64().is_multiple_of(2);
            inject(&mut side, &mut rec, rng, zero, cid);
        }
    }
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

/// The frames only an established session sends, one set each: ACK, CLOSE, REKEY, `NEW_TICKETS` and `PATH_RESPONSE`.
fn established_only() -> Vec<(&'static str, Vec<u8>)> {
    let mut ack = vec![0u8; 16];
    let mut w = Writer::new(&mut ack);
    write_ack(&mut w, std::iter::once(0..=0)).unwrap();
    let n = w.written().len();
    ack.truncate(n);
    let mut tickets = TicketBatch::new();
    tickets.push(TicketEntry {
        tid: [3; 16],
        lifetime_s: 60,
    });
    let rekey = Rekey {
        answer: false,
        share: [1; 32],
        echo: [0; pinc_security::keyroll::ECHO_LEN],
        switch_pn: 0,
    };
    vec![
        ("ACK", ack),
        ("CLOSE", encoded(&[Frame::Close { error: 0 }])),
        ("REKEY", encoded(&[Frame::Rekey(rekey)])),
        ("NEW_TICKETS", encoded(&[Frame::NewTickets(tickets)])),
        ("PATH_RESPONSE", encoded(&[Frame::PathResponse([1; 8])])),
    ]
}

/// A resumed server handed the first datagram of a client with a ticket, split in two: the Hello alone (it raises the
/// early keys and establishes the session), then the client's first 0-RTT packet alone, sealed by the real client
/// with the encoded frames `raw` in front of its stream data. With a frame only an established session sends
/// (`refuse`) the packet is dropped whole and counted, and nothing of it is applied; with the frames a client sends
/// in 0-RTT it is applied.
fn resumed_run(out: &mut String, run: u32, name: &str, raw: &[u8], refuse: bool) {
    let mut world = World::new(IdentityAlg::Ed25519);
    let mut tickets = first_session(&mut world);
    let ticket = tickets.take(&world.rp.id.node_id(), ALPN, T0).unwrap();
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let dialer = world.client(&mut sa, Some(ticket), pinc_security::ClientTickets::new());
    let resumed = world.server(&mut sb);
    let mut net = Net::new(
        dialer,
        resumed,
        Link::new(u64::from(run) + 500, Params::new(10 * MS)),
        &mut world.stores,
    );
    net.a.conn.inject_frames(raw);
    let id = net.a.open_bi().unwrap();
    net.a.write(id, b"early bytes").unwrap();
    net.a.conn.finish(id).unwrap();
    // The client's first datagram, built by hand and never sent on the link: the Hello, then one 0-RTT packet.
    let now = net.now;
    let mut buf = vec![0u8; 65_536];
    let len = net
        .a
        .with_lent(now, |conn, env, l| conn.poll_transmit(env, l, &mut buf))
        .unwrap()
        .len;
    let dgram = &buf[..len];
    let (hs, hs_len) = LongHeader::parse(dgram).unwrap();
    assert_eq!(hs.ty, LongType::Handshake, "{name}");
    let cut = hs_len + hs.body_len;
    let (zh, zh_len) = LongHeader::parse(&dgram[cut..]).unwrap();
    assert_eq!(zh.ty, LongType::ZeroRtt, "{name}");
    assert_eq!(
        cut + zh_len + zh.body_len,
        len,
        "{name}: the datagram is the Hello and one 0-RTT packet"
    );
    let (hello, zero) = (dgram[..cut].to_vec(), dgram[cut..].to_vec());
    let mut side = Side {
        net: &mut net,
        client: false,
    };
    let first = side.snap();
    assert_eq!((first.ph, first.n, first.rx), (0, 0, 0));
    let _ = writeln!(
        out,
        r#"{{"t":"txeb","run":{run},"op":"init","client":false,"cap":8,"v":{}}}"#,
        first.json()
    );
    // The Hello alone: counted, the early keys raised and the session established by the same Hello.
    let hlen = hello.len() as u64;
    side.give(hello).unwrap();
    let up = side.snap();
    assert_eq!(
        (up.ph, up.er, up.rv, up.n, up.nr, up.rx),
        (1, true, true, 0, 0, first.rx + hlen),
        "{name}: a resumed Hello raises the early keys and establishes the session"
    );
    let _ = writeln!(
        out,
        r#"{{"t":"txeb","run":{run},"op":"hello","dlen":{hlen},"v":{}}}"#,
        up.json()
    );
    // The 0-RTT packet alone.
    let zlen = zero.len() as u64;
    let got = side.give(zero);
    let after = side.snap();
    let outcome = match got {
        Ok(()) => "ok",
        Err(RxDrop::EarlyFrame) => "refused",
        Err(e) => panic!("{name}: unexpected {e:?}"),
    };
    assert_eq!(outcome, if refuse { "refused" } else { "ok" }, "{name}");
    // A refusal changes nothing but its count; the datagram was counted on arrival, as every one.
    assert_eq!(after.nr, up.nr + u64::from(refuse), "{name}");
    assert_eq!(
        (
            after.ph, after.er, after.rv, after.n, after.nb, after.nd, after.nu, after.rx
        ),
        (up.ph, up.er, up.rv, up.n, up.nb, up.nd, up.nu, up.rx + zlen),
        "{name}"
    );
    let now = side.net.now;
    side.net.b.service(now);
    assert_eq!(
        side.net.b.read.get(&id).map(Vec::as_slice),
        if refuse { None } else { Some(&b"early bytes"[..]) },
        "{name}: the stream frame of the packet"
    );
    let _ = writeln!(
        out,
        r#"{{"t":"txeb","run":{run},"op":"rx","kind":"z","fate":"{}","dlen":{zlen},"out":"{outcome}","v":{}}}"#,
        if refuse { "estonly" } else { "open" },
        after.json()
    );
}

#[test]
fn early_packets_match_the_models() {
    big_stack(|| {
        let mut rng = SplitMix64::new(0x4541_0001);
        let mut out = String::new();
        for run in 0..30u32 {
            buffer_run(&mut rng, &mut out, run);
        }
        for run in 0..14u32 {
            conn_run(&mut rng, &mut out, run, run % 2 == 1);
        }
        for (k, (name, raw)) in established_only().iter().enumerate() {
            resumed_run(&mut out, 14 + k as u32, name, raw, true);
        }
        let client_frames = encoded(&[
            Frame::Ping,
            Frame::Padding { len: 3 },
            Frame::MaxStreams { limit: 100 },
            Frame::Datagram {
                data: b"dgram",
                implicit_len: false,
            },
        ]);
        resumed_run(&mut out, 19, "the frames a client sends", &client_frames, false);
        assert!(out.contains(r#""op":"hello""#) && out.contains(r#""out":"refused""#));
        assert!(out.contains(r#""op":"push""#) && out.contains(r#""ok":false"#));
        assert!(
            out.contains(r#""out":"held""#) && out.contains(r#""out":"full""#),
            "the buffer was never filled"
        );
        assert!(out.contains(r#""op":"est""#) && out.contains(r#""op":"close""#));
        assert!(out.contains(r#""kind":"z","fate":"fail","dlen"#) && out.contains(r#""out":"closed""#));
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("early.ndjson"), &out).unwrap();
        }
    });
}
